# Copyright 2015 Cisco Systems, Inc.  All rights reserved.
#
#    Licensed under the Apache License, Version 2.0 (the "License"); you may
#    not use this file except in compliance with the License. You may obtain
#    a copy of the License at
#
#         http://www.apache.org/licenses/LICENSE-2.0
#
#    Unless required by applicable law or agreed to in writing, software
#    distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
#    WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
#    License for the specific language governing permissions and limitations
#    under the License.

import eventlet
import logging
import netaddr
import re
import time
import xml.etree.ElementTree as ET

import ciscoconfparse

eventlet.monkey_patch(socket=True, select=True)

from ncclient import manager
from ncclient import transport as nctransport

from oslo.config import cfg

from neutron.common import constants
from neutron.plugins.cisco.cfg_agent import cfg_exceptions as cfg_exc
from neutron.plugins.cisco.cfg_agent.device_drivers.asr1k import (
    asr1k_cfg_syncer as asr1k_cfg_syncer)
from neutron.plugins.cisco.cfg_agent.device_drivers.asr1k import (
    asr1k_snippets as asr_snippets)
from neutron.plugins.cisco.cfg_agent.device_drivers.csr1kv import (
    cisco_csr1kv_snippets as snippets)
from neutron.plugins.cisco.cfg_agent.device_drivers.csr1kv import (
    csr1kv_routing_driver as csr1kv_driver)

LOG = logging.getLogger(__name__)


############################################################
# override some CSR1kv methods to work with physical ASR1k #
############################################################
class ASR1kConfigInfo(object):
    """ASR1k Driver Cisco Configuration class."""

    def __init__(self):
        self.asr_dict = {}
        self.asr_list = None
        self._asr_name_dict = {}
        self._db_synced = False
        self.deployment_id = None
        self.other_dep_ids = []
        self._create_asr_device_dictionary()

    def _create_asr_device_dictionary(self):
        """Create the ASR device cisco dictionary.

        Read data from the cisco_router_plugin.ini device supported sections.
        """
        multi_parser = cfg.MultiConfigParser()
        read_ok = multi_parser.read(cfg.CONF.config_file)

        if len(read_ok) != len(cfg.CONF.config_file):
            raise cfg.Error(_("Some config files were not parsed properly"))

        for parsed_file in multi_parser.parsed:
            for parsed_item in parsed_file.keys():
                if parsed_item == 'deployment_ids':
                    for dev_key, value in parsed_file[parsed_item].items():
                        if dev_key == 'mine':
                            self.deployment_id = value[0].strip()
                        if dev_key == 'others':
                            dep_ids = value[0].split(",")
                            for dep_id in dep_ids:
                                self.other_dep_ids.append(dep_id.strip())
                    continue

                dev_id, sep, dev_ip = parsed_item.partition(':')
                if dev_id.lower() == 'asr':
                    if dev_ip not in self.asr_dict:
                        self.asr_dict[dev_ip] = {}

                    asr_entry = self.asr_dict[dev_ip]
                    asr_entry['ip'] = dev_ip
                    asr_entry['conn'] = None

                    for dev_key, value in parsed_file[parsed_item].items():
                        asr_entry[dev_key] = value[0]

                    asr_entry['order'] = int(asr_entry['order'])

                    self._asr_name_dict[asr_entry['name']] = asr_entry

        LOG.debug("ASR dict: %s" % self.asr_dict)
        LOG.debug("Deployment IDs mine: %s others: %s" %
                  (self.deployment_id, self.other_dep_ids))

    def get_asr_by_name(self, asr_name):
        if asr_name in self._asr_name_dict:
            return self._asr_name_dict[asr_name]
        else:
            return None

    def get_first_asr(self):
        return self.asr_dict.values()[0]

    def get_asr_list(self):
        if self.asr_list is None:
            self.asr_list = sorted(self.asr_dict.values(),
                                   key=lambda ent: ent['order'])
        return self.asr_list


class NetConfErrorListener(nctransport.SessionListener):

    def set_phy_context(self, phy_context):
        self._phy_context = phy_context

    def callback(self, root, raw):
        pass

    def err(self, ex):
        if self._phy_context:
            self._phy_context.connection_err_callback(ex)


class ASR1kRoutingDriver(csr1kv_driver.CSR1kvRoutingDriver):

    def __init__(self, target_asr):
        self._asr_config = ASR1kConfigInfo()
        self._csr_conn = None
        self._intfs_enabled = False
        self._ignore_cfg_check = False
        self.hsrp_group_base = 200
        self.hsrp_real_ip_base = 200
        self.target_asr = target_asr
        self._err_listener = None
        self._fullsync = False
        self._existing_cfg_dict = {}
        return

    def prepare_fullsync(self, existing_cfg_dict):
        self._fullsync = True
        #ioscfg = self._get_running_config(self.target_asr)
        #parse = ciscoconfparse.CiscoConfParse(ioscfg)
        self._existing_cfg_dict = existing_cfg_dict

    def clear_fullsync(self):
        self._fullsync = False

    def _get_asr_list(self):
        asr_ent = self.target_asr
        return [asr_ent]
        #return self._asr_config.get_asr_list()

    def _get_asr_ent_from_port(self, port):
        try:
            asr_name = port['phy_router_db']['name']
            asr_ent = self._asr_config.get_asr_by_name(asr_name)
        except Exception:
            LOG.error(_("couldn't get target ASR name, port: %s") % port)
            raise

        return asr_ent

    def _port_is_hsrp(self, port):
        hsrp_types = [constants.DEVICE_OWNER_ROUTER_HA_GW,
                      constants.DEVICE_OWNER_ROUTER_HA_INTF]
        return port['device_owner'] in hsrp_types

    def _v6_port_needs_config(self, port):
        valid_port_types = [constants.DEVICE_OWNER_ROUTER_GW,
                            constants.DEVICE_OWNER_ROUTER_INTF]
        return port['device_owner'] in valid_port_types

    def _port_needs_config(self, port):
        if not self._port_is_hsrp(port):
            LOG.info(_("ignoring non-HSRP interface"))
            return False

        if not port['phy_router_db']:
            return False

        asr_ent = self._get_asr_ent_from_port(port)
        if asr_ent['name'] != self.target_asr['name']:
            LOG.info(_("ignoring interface for non-target ASR"))
            return False

        return True

    def _get_virtual_gw_port_for_ext_net(self, ri, ex_gw_port):
        subnet_id = ex_gw_port['subnet']['id']
        gw_ports = ri.router.get(constants.HA_GW_KEY, [])
        for gw_port in gw_ports:
            if gw_port['subnet']['id'] == subnet_id:
                if gw_port['device_owner'] == constants.DEVICE_OWNER_ROUTER_GW:
                    return gw_port
        return None

    def _is_global_router(self, ri):
        if ri.router['id'] == "PHYSICAL_GLOBAL_ROUTER_ID":
            return True
        else:
            return False

    def _is_port_v6(self, port):
        prefix = port['subnet']['cidr']
        if netaddr.IPNetwork(prefix).version == 6:
            return True
        else:
            return False

    def _get_hsrp_grp_num_from_ri(self, ri):
        ri_name = ri.router_name()[8:self.DEV_NAME_LEN]
        hsrp_num = int(ri_name, 16) % asr1k_cfg_syncer.TENANT_HSRP_GRP_RANGE
        hsrp_num += asr1k_cfg_syncer.TENANT_HSRP_GRP_OFFSET
        return hsrp_num

    def _get_hsrp_grp_num_from_net_id(self, network_id):
        net_id_digits = network_id[:6]
        hsrp_num = int(net_id_digits, 16) % asr1k_cfg_syncer.EXT_HSRP_GRP_RANGE
        hsrp_num += asr1k_cfg_syncer.EXT_HSRP_GRP_OFFSET
        return hsrp_num

    def _get_short_router_id_from_port(self, port):
        dev_owner = port['device_owner']
        short_id = dev_owner[:6]
        return short_id

    ###### Public Functions ########
    def set_err_listener_context(self, phy_context):
        self._err_listener = NetConfErrorListener()
        self._err_listener.set_phy_context(phy_context)

    def set_ignore_cfg_check(self, is_set):
        self._ignore_cfg_check = is_set

    def internal_network_added(self, ri, port):
        gw_ip = port['subnet']['gateway_ip']
        if self._is_port_v6(port):
            LOG.debug("ADDING IPV6 NETWORK port: %s" % port)
            self._csr_create_subinterface_v6(ri, port, False, gw_ip)
        else:
            self._csr_create_subinterface(ri, port, False, gw_ip)

    def external_gateway_added(self, ri, ex_gw_port):
        # global router handles IP assignment, HSRP setup
        # tenant router handles intf creation and default route within VRFs

        if self._is_global_router(ri):
            ex_gw_ip = ex_gw_port['subnet']['gateway_ip']
            virtual_gw_port = self._get_virtual_gw_port_for_ext_net(ri,
                ex_gw_port)
            subintf_ip = virtual_gw_port['fixed_ips'][0]['ip_address']
            if self._is_port_v6(ex_gw_port):
                self._csr_create_subinterface_v6(ri, ex_gw_port, True,
                                                 subintf_ip)
            else:
                self._csr_create_subinterface(ri, ex_gw_port, True,
                                              subintf_ip)
        else:
            # Need this else case because default routes are mapped to
            # VRFs (tenant routers)
            # Global Router is not aware of Tenant Routers with ext
            # network assigned
            # Thus, default route must be handled per Tenant Router
            ex_gw_ip = ex_gw_port['subnet']['gateway_ip']
            subinterface = self._get_interface_name_from_hosting_port(
                ex_gw_port)
            vlan_id = self._get_interface_vlan_from_hosting_port(ex_gw_port)
            if (self._fullsync and int(vlan_id) in
                self._existing_cfg_dict['interfaces']):
                LOG.info(_("Subinterface already exists, don't create "
                         "interface"))
            else:
                self._create_ext_subinterface_enable_only(subinterface)

            if ex_gw_ip:
                # Set default route via this network's gateway ip
                if self._is_port_v6(ex_gw_port):
                    self._asr_add_default_route_v6(ri, ex_gw_ip, ex_gw_port)
                else:
                    self._set_nat_pool(ri, ex_gw_port, False)
                    self._csr_add_default_route(ri, ex_gw_ip, ex_gw_port)

    def external_gateway_removed(self, ri, ex_gw_port):
        if self._is_global_router(ri):
            self._csr_remove_subinterface(ex_gw_port)
        else:
            ex_gw_ip = ex_gw_port['subnet']['gateway_ip']
            if (ex_gw_ip and
                    ex_gw_port['device_owner'] ==
                    constants.DEVICE_OWNER_ROUTER_GW):
                # LOG.debug("REMOVE ROUTE PORT %s" % ex_gw_port)
                # Remove default route via this network's gateway ip
                if self._is_port_v6(ex_gw_port):
                    self._asr_remove_default_route_v6(ri, ex_gw_ip, ex_gw_port)
                else:
                    self._set_nat_pool(ri, ex_gw_port, True)
                    self._csr_remove_default_route(ri, ex_gw_ip, ex_gw_port)

    def floating_ip_added(self, ri, ex_gw_port, floating_ip, fixed_ip):
        self._csr_add_floating_ip(ri, ex_gw_port, floating_ip, fixed_ip)

    def disable_internal_network_NAT(self, ri, port, ex_gw_port,
                                     intf_delete=False):
        self._csr_remove_internalnw_nat_rules(ri, [port], ex_gw_port,
                                              intf_delete)

    def delete_invalid_cfg(self, router_db_info):
        conn = self._get_connection()
        cfg_syncer = asr1k_cfg_syncer.ConfigSyncer(router_db_info,
            self._asr_config.deployment_id, self._asr_config.other_dep_ids,
            self.target_asr['name'], self.target_asr['target_intf'])
        cfg_syncer.delete_invalid_cfg(conn)
        return cfg_syncer.existing_cfg_dict

    def send_empty_cfg(self):
        confstr = asr_snippets.EMPTY_SNIPPET
        self._edit_running_config(confstr, "EMPTY_SNIPPET")

    def get_show_clock(self):
        conn = self._get_connection()
        filter_str = asr_snippets.GET_SHOW_CLOCK
        rpc_obj = conn.get(filter=filter_str)
        LOG.info(_("show clock resp: %s") % rpc_obj.__dict__)

    ###### Internal "Preparation" Functions ########
    def _csr_create_subinterface_v6(self, ri, port,
                                    is_external=False, gw_ip=""):
        if not self._v6_port_needs_config(port):
            return

        vrf_name = self._csr_get_vrf_name(ri)
        ip_cidr = port['ip_cidr']
        vlan = self._get_interface_vlan_from_hosting_port(port)
        subinterface = self._get_interface_name_from_hosting_port(port)

        self._create_subinterface_v6(subinterface, vlan, vrf_name,
                                     ip_cidr, is_external)
        # Always do HSRP
        self._csr_add_ha_HSRP_v6(ri, port, ip_cidr, is_external)

    def _csr_add_ha_HSRP_v6(self, ri, port, ip, is_external=False):
        if not self._v6_port_needs_config(port):
            return

        vlan = self._get_interface_vlan_from_hosting_port(port)
        group = vlan

        asr_ent = self.target_asr

        priority = asr_ent['order']
        subinterface = self._get_interface_name_from_hosting_port(port)

        self._set_ha_HSRP_v6(subinterface, priority, group, is_external)

    def _csr_create_subinterface(self, ri, port, is_external=False, gw_ip=""):

        if not self._port_needs_config(port):
            return

        vrf_name = self._csr_get_vrf_name(ri)
        ip_cidr = port['ip_cidr']
        netmask = netaddr.IPNetwork(ip_cidr).netmask

        gateway_ip = gw_ip

        vlan = self._get_interface_vlan_from_hosting_port(port)
        if (self._fullsync and int(vlan) in
                self._existing_cfg_dict['interfaces']):
            LOG.info(_("Subinterface already exists, skipping"))
            return

        hsrp_ip = port['fixed_ips'][0]['ip_address']

        subinterface = self._get_interface_name_from_hosting_port(port)
        self._create_subinterface(subinterface, vlan, vrf_name,
                                  hsrp_ip, netmask, is_external)
        # Always do HSRP
        self._csr_add_ha_HSRP(ri, port, gateway_ip, is_external)

    def _csr_remove_subinterface(self, port):

        if not self._port_needs_config(port):
            return

        subinterface = self._get_interface_name_from_hosting_port(port)
        self._remove_subinterface(subinterface)

    def _csr_add_internalnw_nat_rules(self, ri, port, ex_port):
        if self._is_port_v6(port) or self._is_port_v6(ex_port):
            LOG.debug("IPv6 port, no NAT add needed")
            return

        if not self._port_needs_config(port):
            return

        vrf_name = self._csr_get_vrf_name(ri)
        in_vlan = self._get_interface_vlan_from_hosting_port(port)
        out_vlan = self._get_interface_vlan_from_hosting_port(ex_port)
        acl_no = 'neutron_acl_%s_%s' % (self._asr_config.deployment_id,
                                        str(in_vlan))
        internal_cidr = port['ip_cidr']
        internal_net = netaddr.IPNetwork(internal_cidr).network
        netmask = netaddr.IPNetwork(internal_cidr).hostmask

        inner_intfc = self._get_interface_name_from_hosting_port(port)
        outer_intfc = self._get_interface_name_from_hosting_port(ex_port)
        self._nat_rules_for_internet_access(acl_no, internal_net,
                                            netmask, inner_intfc,
                                            outer_intfc, vrf_name,
                                            in_vlan, out_vlan)

    def _csr_remove_internalnw_nat_rules(self, ri, ports, ex_port,
                                         intf_delete=False):
        if self._is_port_v6(ex_port):
            LOG.debug("IPv6 port, no NAT delete needed")
            return

        acls = []
        #First disable nat in all inner ports
        for port in ports:

            if not self._port_needs_config(port):
                continue

            in_intfc_name = self._get_interface_name_from_hosting_port(port)
            inner_vlan = self._get_interface_vlan_from_hosting_port(port)
            acls.append("neutron_acl_%s_%s" % (self._asr_config.deployment_id,
                                               str(inner_vlan)))

            if not intf_delete:
                confstr = snippets.REMOVE_NAT % (in_intfc_name, 'inside')
                self._edit_running_config(confstr, "REMOVE_NAT")

            #Wait for two second
            LOG.debug("Sleep for 2 seconds before clearing NAT rules")
            time.sleep(2)

            #Clear the NAT translation table
            confstr = snippets.CLEAR_DYN_NAT_TRANS
            self._edit_running_config(confstr, "CLEAR_DYN_NAT_TRANS")

            # Remove dynamic NAT rules and ACLs
            vrf_name = self._csr_get_vrf_name(ri)
            ext_intf_name = self._get_interface_name_from_hosting_port(ex_port)
            for acl in acls:
                self._remove_dyn_nat_rule(acl, ext_intf_name, vrf_name)

    def _csr_add_default_route(self, ri, gw_ip, gw_port):
        router_id = self._get_short_router_id_from_port(gw_port)
        if self._fullsync and router_id in self._existing_cfg_dict['routes']:
            LOG.info(_("Default route already exists, skipping"))
            return

        vrf_name = self._csr_get_vrf_name(ri)
        confstr = asr_snippets.SET_DEFAULT_ROUTE_WITH_INTF % (vrf_name,
                                                              gw_ip)
        self._edit_running_config(confstr,
                                  "SET_DEFAULT_ROUTE_WITH_INTF")

    def _csr_remove_default_route(self, ri, gw_ip, gw_port):
        vrf_name = self._csr_get_vrf_name(ri)
        confstr = asr_snippets.REMOVE_DEFAULT_ROUTE_WITH_INTF % (vrf_name,
                                                                 gw_ip)
        self._edit_running_config(confstr,
                                  "REMOVE_DEFAULT_ROUTE_WITH_INTF")

    def _csr_add_floating_ip(self, ri, ex_gw_port, floating_ip, fixed_ip):
        vrf_name = self._csr_get_vrf_name(ri)
        #hsrp_grp = self._get_hsrp_grp_num_from_ri(ri)
        hsrp_grp = self._get_hsrp_grp_num_from_net_id(ex_gw_port['network_id'])

        self._add_floating_ip(floating_ip, fixed_ip, vrf_name,
                              hsrp_grp, ex_gw_port)

    def _csr_remove_floating_ip(self, ri, ex_gw_port, floating_ip, fixed_ip):
        vrf_name = self._csr_get_vrf_name(ri)
        hsrp_grp = self._get_hsrp_grp_num_from_net_id(ex_gw_port['network_id'])
        self._remove_floating_ip(floating_ip, fixed_ip, vrf_name, hsrp_grp,
                                 ex_gw_port)

    def _csr_update_routing_table(self, ri, action, route):
        vrf = self._csr_get_vrf_name(ri)
        destination_net = netaddr.IPNetwork(route['destination'])
        dest = destination_net.network
        dest_mask = destination_net.netmask
        next_hop = route['nexthop']

        if action is 'replace':
            confstr = snippets.SET_IP_ROUTE % (vrf, dest, dest_mask, next_hop)
            self._edit_running_config(confstr, "SET_IP_ROUTE")
        elif action is 'delete':
            confstr = snippets.REMOVE_IP_ROUTE % (vrf, dest, dest_mask,
                                                  next_hop)
            self._edit_running_config(confstr, "REMOVE_IP_ROUTE")
        else:
            LOG.error(_('Unknown route command %s'), action)

    def _csr_create_vrf(self, ri):
        vrf_name = self._csr_get_vrf_name(ri)
        self._create_vrf(vrf_name)

    def _csr_remove_vrf(self, ri):
        vrf_name = self._csr_get_vrf_name(ri)
        self._remove_vrf(vrf_name)

    def _csr_get_vrf_name(self, ri):
        name = ri.router_name()[:self.DEV_NAME_LEN]
        name = "%s-%s" % (name, self._asr_config.deployment_id)
        return name

    def _csr_add_ha_HSRP(self, ri, port, ip, is_external=False):

        if not self._port_needs_config(port):
            return

        vlan = self._get_interface_vlan_from_hosting_port(port)
        # group = vlan
        if is_external:
            group = self._get_hsrp_grp_num_from_net_id(port['network_id'])
        else:
            group = self._get_hsrp_grp_num_from_ri(ri)

        vrf_name = self._csr_get_vrf_name(ri)

        asr_ent = self.target_asr

        priority = asr_ent['order']
        subinterface = self._get_interface_name_from_hosting_port(port)
        self._set_ha_HSRP(subinterface, vrf_name, priority, group, vlan, ip,
                          is_external)

    ###### Internal "Action" Functions ########

    def _set_nat_pool(self, ri, gw_port, is_delete):
        vrf_name = self._csr_get_vrf_name(ri)
        pool_ip = gw_port['fixed_ips'][0]['ip_address']
        pool_name = "%s_nat_pool" % (vrf_name)
        pool_net = netaddr.IPNetwork(gw_port['ip_cidr'])

        if self._fullsync and pool_ip in self._existing_cfg_dict['pools']:
            LOG.info(_("Pool already exists, skipping"))
            return

        try:
            if is_delete:
                confstr = asr_snippets.DELETE_NAT_POOL % (pool_name,
                                                      pool_ip, pool_ip,
                                                      pool_net.netmask)
                self._edit_running_config(confstr,
                        '%s DELETE_NAT_POOL' % self.target_asr['name'])
            else:
                confstr = asr_snippets.CREATE_NAT_POOL % (pool_name,
                                                      pool_ip, pool_ip,
                                                      pool_net.netmask)
                self._edit_running_config(confstr,
                        '%s CREATE_NAT_POOL' % self.target_asr['name'])
        except cfg_exc.CSR1kvConfigException as cse:
            LOG.error(_("temporary disable NAT_POOL exc handling: %s") % (cse))

    def _create_subinterface_v6(self, subinterface, vlan_id, vrf_name,
                                ip_cidr, is_external=False):
        if is_external is True:
            confstr = asr_snippets.CREATE_SUBINTERFACE_V6_NO_VRF_WITH_ID % \
                        (subinterface, self._asr_config.deployment_id,
                        vlan_id, ip_cidr)
        else:
            confstr = asr_snippets.CREATE_SUBINTERFACE_V6_WITH_ID % \
                        (subinterface, self._asr_config.deployment_id,
                        vlan_id, vrf_name, ip_cidr)

        self._edit_running_config(confstr,
            '%s CREATE_SUBINTERFACE_V6' % self.target_asr['name'])

    def _set_ha_HSRP_v6(self, subinterface, priority, group,
                        is_external=False):

        confstr = asr_snippets.SET_INTC_ASR_HSRP_V6 % (subinterface, group,
                        group, priority, group, group, group, group, group)

        action = "%s SET_INTC_HSRP_V6 [Group: %s, Priority: %s]" % (
                    self.target_asr['name'], group, priority)
        self._edit_running_config(confstr, action)

    def _asr_add_default_route_v6(self, ri, gw_ip, gw_port):
        vrf = self._csr_get_vrf_name(ri)
        confstr = asr_snippets.SET_DEFAULT_ROUTE_V6_WITH_INTF % (vrf, gw_ip)
        self._edit_running_config(confstr, "SET_DEFAULT_ROUTE_V6_WITH_INTF")

    def _asr_remove_default_route_v6(self, ri, gw_ip, gw_port):
        vrf = self._csr_get_vrf_name(ri)
        confstr = asr_snippets.REMOVE_DEFAULT_ROUTE_V6_WITH_INTF % (vrf, gw_ip)
        self._edit_running_config(confstr, "REMOVE_DEFAULT_ROUTE_V6_WITH_INTF")

    def _create_ext_subinterface_enable_only(self, subinterface):
        confstr = snippets.ENABLE_INTF % (subinterface)
        self._edit_running_config(confstr,
            '%s ENABLE_INTF' % self.target_asr['name'])

    def _create_subinterface(self, subinterface, vlan_id, vrf_name, ip,
                             mask, is_external=False):
        if is_external is True:
            confstr = asr_snippets.CREATE_SUBINTERFACE_EXTERNAL_WITH_ID % (
                    subinterface, self._asr_config.deployment_id,
                    vlan_id, ip, mask)
        else:
            confstr = asr_snippets.CREATE_SUBINTERFACE_WITH_ID % (
                    subinterface, self._asr_config.deployment_id,
                    vlan_id, vrf_name, ip, mask)

        self._edit_running_config(confstr,
                    '%s CREATE_SUBINTERFACE' % self.target_asr['name'])

    def _remove_subinterface(self, subinterface):
        confstr = snippets.REMOVE_SUBINTERFACE % subinterface
        self._edit_running_config(confstr,
                    '%s REMOVE_SUBINTERFACE' % self.target_asr['name'])

    def _nat_rules_for_internet_access(self, acl_no, network,
                                       netmask,
                                       inner_intfc,
                                       outer_intfc,
                                       vrf_name, in_vlan, out_vlan):
        """Configure the NAT rules for an internal network.

           refer to comments in parent class
        """
        # Duplicate ACL creation throws error, so checking
        # it first. Remove it in future as this is not common in production
        try:
            if (self._fullsync and
                    int(in_vlan) in self._existing_cfg_dict['acls']):
                LOG.info(_("Skip cfg for existing ACL"))
                pass
            else:
                confstr = snippets.CREATE_ACL % (acl_no, network, netmask)
                self._edit_running_config(confstr, "CREATE_ACL")
        except Exception:
            LOG.error(_("CREATE_ACL error"))

        try:
            if (self._fullsync and
                    int(in_vlan) in self._existing_cfg_dict['dyn_nat']):
                LOG.info(_("Skip cfg for existing dynamic NAT rule"))
                pass
            else:
                pool_name = "%s_nat_pool" % (vrf_name)
                confstr = asr_snippets.SET_DYN_SRC_TRL_POOL % (acl_no,
                            pool_name, vrf_name)
                self._edit_running_config(confstr, "SET_DYN_SRC_TRL_POOL")
        except Exception:
            LOG.error(_("DYN NAT error"))

        if (self._fullsync and
                int(in_vlan) in self._existing_cfg_dict['interfaces']):
            LOG.info(_("Skip cfg for existing 'nat inside'"))
            pass
        else:
            confstr = snippets.SET_NAT % (inner_intfc, 'inside')
            self._edit_running_config(confstr, "SET_NAT")

        if (self._fullsync and
                int(out_vlan) in self._existing_cfg_dict['interfaces']):
            LOG.debug("Skip cfg for existing 'nat outside'")
            pass
        else:
            confstr = snippets.SET_NAT % (outer_intfc, 'outside')
            self._edit_running_config(confstr, "SET_NAT")

    def _remove_dyn_nat_rule(self, acl_no, outer_intfc_name, vrf_name):
        confstr = snippets.REMOVE_DYN_SRC_TRL_INTFC % (acl_no,
                                                       outer_intfc_name,
                                                       vrf_name)
        self._edit_running_config(confstr, "REMOVE_DYN_SRC_TRL_INTFC")
        try:
            pool_name = "%s_nat_pool" % (vrf_name)
            confstr = asr_snippets.REMOVE_DYN_SRC_TRL_POOL % (acl_no,
                pool_name, vrf_name)
        except cfg_exc.CSR1kvConfigException as cse:
            LOG.error(_("temporary disable REMOVE_DYN_SRC_TRL_INTFC "
                      "exception handling: %s") % (cse))

        confstr = snippets.REMOVE_ACL % acl_no
        self._edit_running_config(confstr, "REMOVE_ACL")

    def _remove_dyn_nat_translations(self):
        confstr = snippets.CLEAR_DYN_NAT_TRANS
        self._edit_running_config(confstr, "CLEAR_DYN_NAT_TRANS")

    def _add_floating_ip(self, floating_ip, fixed_ip, vrf,
                         hsrp_grp, ex_gw_port):
        """
        To implement a floating ip, an ip static nat is configured in the
        underlying router
        ex_gw_port contains data to derive the vlan associated with related
        subnet for the fixed ip.  The vlan in turn is applied to the
        redundancy parameter for setting the IP NAT.
        """
        vlan = ex_gw_port['hosting_info']['segmentation_id']
        nat_ips = fixed_ip + " " + floating_ip
        nat_name = "neutron-hsrp-" + str(hsrp_grp) + "-" + str(vlan)

        if (self._fullsync and floating_ip in
                self._existing_cfg_dict['static_nat']):
            LOG.info(_("Skip cfg for existing floating IP"))
            return

        confstr = asr_snippets.SET_STATIC_SRC_TRL_NO_VRF_MATCH % (
                nat_ips, vrf, nat_name)
        self._edit_running_config(confstr, "SET_STATIC_SRC_TRL_NO_VRF_MATCH")

    def _remove_floating_ip(self, floating_ip, fixed_ip, vrf, hsrp_grp,
                            ex_gw_port):
        vlan = ex_gw_port['hosting_info']['segmentation_id']
        nat_ips = fixed_ip + " " + floating_ip
        nat_name = "neutron-hsrp-" + str(hsrp_grp) + "-" + str(vlan)

        confstr = asr_snippets.REMOVE_STATIC_SRC_TRL_NO_VRF_MATCH % (
                nat_ips, vrf, nat_name)
        self._edit_running_config(confstr,
                                  "REMOVE_STATIC_SRC_TRL_NO_VRF_MATCH")

    def _set_ha_HSRP(self, subinterface, vrf_name, priority, group, vlan, ip,
                     is_external=False):
        try:
            confstr = (asr_snippets.REMOVE_INTC_ASR_HSRP_PREEMPT %
                    (subinterface, group))
            self._edit_running_config(confstr, "REMOVE_HSRP_PREEMPT")
        except Exception:
            pass

        if is_external is True:
            confstr = (asr_snippets.SET_INTC_ASR_HSRP_EXTERNAL %
                    (subinterface, group, priority, group, ip, group,
                    group, group, vlan))
        else:
            confstr = (asr_snippets.SET_INTC_ASR_HSRP % (subinterface,
                    vrf_name, group, priority, group, ip, group))

        action = "%s SET_INTC_HSRP (Group: %s, Priority: % s)" % (
                self.target_asr['name'], group, priority)
        self._edit_running_config(confstr, action)

    def _remove_ha_HSRP(self, subinterface, group):
        confstr = snippets.REMOVE_INTC_HSRP % (subinterface, group)
        action = ("REMOVE_INTC_HSRP (subinterface:%s, Group:%s)"
                  % (subinterface, group))
        self._edit_running_config(confstr, action)

    def _create_vrf(self, vrf_name):
        try:
            confstr = asr_snippets.CREATE_VRF_DEFN % vrf_name
            self._edit_running_config(confstr, "CREATE_VRF_DEFN")
            LOG.info(_("VRF %s successfully created"), vrf_name)
        except Exception:
            LOG.exception(_("Failed creating VRF %s"), vrf_name)

    def _remove_vrf(self, vrf_name):
        confstr = asr_snippets.REMOVE_VRF_DEFN % vrf_name
        self._edit_running_config(confstr, "REMOVE_VRF_DEFN")
        LOG.info(_("VRF %s removed"), vrf_name)

    def _get_vrfs(self):
        """Get the current VRFs configured in the device.

        :return: A list of vrf names as string
        """
        vrfs = []
        ioscfg = self._get_running_config()
        parse = ciscoconfparse.CiscoConfParse(ioscfg)
        vrfs_raw = parse.find_lines("^ip vrf")
        for line in vrfs_raw:
            #  raw format ['ip vrf <vrf-name>',....]
            vrf_name = line.strip().split(' ')[2]
            vrfs.append(vrf_name)
        LOG.info(_("VRFs:%s"), vrfs)
        return vrfs

    def _cfg_exists(self, cfg_str):
        """Check a partial config string exists in the running config.

        :param cfg_str: config string to check
        :return : True or False
        """
        ioscfg = self._get_running_config()
        parse = ciscoconfparse.CiscoConfParse(ioscfg)
        cfg_raw = parse.find_lines("^" + cfg_str)
        LOG.debug("_cfg_exists(): Found lines %s", cfg_raw)
        return len(cfg_raw) > 0

    def _interface_exists(self, interface):
        """Check whether interface exists."""
        ioscfg = self._get_running_config()
        parse = ciscoconfparse.CiscoConfParse(ioscfg)
        intfs_raw = parse.find_lines("^interface " + interface)
        return len(intfs_raw) > 0

    def _check_acl(self, acl_no, network, netmask):
        """Check a ACL config exists in the running config.

        :param acl_no: access control list (ACL) number
        :param network: network which this ACL permits
        :param netmask: netmask of the network
        :return:
        """
        exp_cfg_lines = ['ip access-list standard ' + str(acl_no),
                         ' permit ' + str(network) + ' ' + str(netmask)]
        ioscfg = self._get_running_config()
        parse = ciscoconfparse.CiscoConfParse(ioscfg)
        acls_raw = parse.find_children(exp_cfg_lines[0])
        if acls_raw:
            if exp_cfg_lines[1] in acls_raw:
                return True
            LOG.error(_("Mismatch in ACL configuration for %s"), acl_no)
            return False
        LOG.debug("%s is not present in config", acl_no)
        return False

    def _edit_running_config(self, confstr, snippet):
        LOG.debug(confstr)
        conn = self._get_connection()
        try:
            rpc_obj = conn.edit_config(target='running', config=confstr)
            self._check_response(rpc_obj, snippet)
        except Exception:
            if re.search(r"REMOVE_|DELETE_", snippet):
                LOG.warn(_("Pass exception for %s"), snippet)
                pass
            else:
                raise

    def _get_running_config(self):
        """Get the CSR's current running config.

        :return: Current IOS running config as multiline string
        """
        conn = self._get_connection()
        config = conn.get_config(source="running")
        if config:
            root = ET.fromstring(config._raw)
            running_config = root[0][0]
            rgx = re.compile("\r*\n+")
            ioscfg = rgx.split(running_config.text)
            return ioscfg

    def _delete_invalid_cfg(self, cfg_syncer):
        conn = self._get_connection()
        cfg_syncer.delete_invalid_cfg(conn)

    ###### Internal "Support" Functions ########

    def _get_interface_name_from_hosting_port(self, port):
        asr_ent = self.target_asr
        vlan = self._get_interface_vlan_from_hosting_port(port)
        subinterface = asr_ent['target_intf']
        intfc_name = "%s.%s" % (subinterface, vlan)
        return intfc_name

    def _get_connection(self):
        """Make SSH connection to the CSR.

           refer to comments in parent class
        """
        asr_ent = self.target_asr

        asr_host = asr_ent['ip']
        asr_ssh_port = int(asr_ent['ssh_port'])
        asr_user = asr_ent['username']
        asr_password = asr_ent['password']
        self._timeout = 30

        try:
            asr_conn = asr_ent['conn']
            if asr_conn and asr_conn.connected:
                return asr_conn
            else:
                asr_conn = manager.connect(host=asr_host,
                                           port=asr_ssh_port,
                                           username=asr_user,
                                           password=asr_password,
                                           allow_agent=False,
                                           look_for_keys=False,
                                           unknown_host_cb=lambda host,
                                           fingerprint: True,
                                           #device_params={'name': "csr"},
                                           timeout=self._timeout)
                if not self._intfs_enabled:
                    self._intfs_enabled = True

                # set timeout in seconds for synchronous netconf requests
                asr_conn.timeout = 48

                if self._err_listener is not None:
                    asr_conn._session.add_listener(self._err_listener)
                asr_ent['conn'] = asr_conn

            return asr_conn
        except Exception as e:
            conn_params = {'host': asr_host, 'port': asr_ssh_port,
                           'user': asr_user,
                           'timeout': self._timeout, 'reason': e.message}
            raise cfg_exc.CSR1kvConnectionException(**conn_params)
