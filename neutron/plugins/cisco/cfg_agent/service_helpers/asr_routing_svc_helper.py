#    Copyright 2015 Cisco Systems, Inc.  All rights reserved.
#
#    Licensed under the Apache License, Version 2.0 (the "License"); you may
#    not use this file except in compliance with the License. You may obtain
#    a copy of the License at
#
#         http://www.apache.org/licenses/LICENSE-2.0
#
#    Unless required by applicable law or agreed to in writing, software
#    distributed under the License is distributed on an "AS IS" BASIS,
#    WITHOUT
#    WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
#    License for the specific language governing permissions and limitations
#    under the License.

import collections
import eventlet

from oslo import messaging

from neutron.common import constants as l3_constants
from neutron.common import rpc as n_rpc
from neutron.common import topics
from neutron import context as n_context
from neutron.openstack.common import excutils
from neutron.openstack.common import jsonutils
from neutron.openstack.common import log as logging

from neutron.plugins.cisco.cfg_agent import cfg_exceptions
from neutron.plugins.cisco.cfg_agent.device_drivers.asr1k import (
    asr_driver_mgr as driver_mgr)
from neutron.plugins.cisco.cfg_agent import device_status
from neutron.plugins.cisco.common import cisco_constants as c_constants

from neutron.plugins.cisco.cfg_agent.device_drivers.asr1k import (
    asr1k_routing_driver as asr1kv_driver)
from neutron.plugins.cisco.cfg_agent.service_helpers import routing_svc_helper

LOG = logging.getLogger(__name__)

N_ROUTER_PREFIX = 'nrouter-'


class RouterInfo(object):
    """Wrapper class around the (neutron) router dictionary.

    Information about the neutron router is exchanged as a python dictionary
    between plugin and config agent. RouterInfo is a wrapper around that dict,
    with attributes for common parameters. These attributes keep the state
    of the current router configuration, and are used for detecting router
    state changes when an updated router dict is received.

    This is a modified version of the RouterInfo class defined in the
    (reference) l3-agent implementation, for use with cisco config agent.
    """

    def __init__(self, router_id, router):
        self.router_id = router_id
        self.ex_gw_port = None
        self._snat_enabled = None
        self._snat_action = None
        self.internal_ports = []
        self.floating_ips = []
        self._router = None
        self.router = router
        self.routes = []
        self.ha_info = router.get('ha_info')
        self.ha_gw_ports = []
        LOG.debug("__init__: RouterInfo: %s",
                 jsonutils.dumps(self.router, indent=4))

    @property
    def router(self):
        return self._router

    @property
    def id(self):
        return self.router_id

    @property
    def snat_enabled(self):
        return self._snat_enabled

    @router.setter
    def router(self, value):
        self._router = value
        if not self._router:
            return
        # enable_snat by default if it wasn't specified by plugin
        self._snat_enabled = self._router.get('enable_snat', True)

    def router_name(self):
        return N_ROUTER_PREFIX + self.router_id


class PhyCiscoRoutingPluginApi(n_rpc.RpcProxy):
    """RoutingServiceHelper(Agent) side of the  routing RPC API."""

    BASE_RPC_API_VERSION = '1.1'

    def __init__(self, topic, host):
        super(PhyCiscoRoutingPluginApi, self).__init__(
            topic=topic, default_version=self.BASE_RPC_API_VERSION)
        self.host = host

    def get_routers(self, context, router_ids=None, hd_ids=None):
        """Make a remote process call to retrieve the sync data for routers.

        :param context: session context
        :param router_ids: list of  routers to fetch
        :param hd_ids : hosting device ids, only routers assigned to these
                        hosting devices will be returned.
        """
        return self.call(context,
                         self.make_msg('cfg_sync_routers',
                                       host=self.host,
                                       router_ids=router_ids,
                                       hosting_device_ids=hd_ids),
                         topic=self.topic,
                         timeout=180)

    def update_floatingip_statuses(self, context, router_id, fip_statuses):
        """Call the plugin update floating IPs's operational status."""
        return self.call(context,
                         self.make_msg('update_floatingip_statuses',
                                       router_id=router_id,
                                       fip_statuses=fip_statuses),
                         version='1.1')

    def send_update_port_statuses(self, context, port_ids, status):
        """Call the plugin to update the port status which updates the DB."""
        return self.call(context,
                         self.make_msg('asr_update_port_statuses',
                                       port_ids=port_ids, status=status))

    def agent_heartbeat(self, context):
        """Make a remote process call to check connectivity between
           agent and neutron-server

        :param context: session context
        """
        return self.call(context,
                         self.make_msg('agent_heartbeat',
                                       host=self.host),
                         topic=self.topic,
                         timeout=6)

    def create_rpc_dispatcher(self):
        return n_rpc.PluginRpcDispatcher([self])


class PhyRouterContext(routing_svc_helper.RoutingServiceHelper):

    def __init__(self, asr_ent, plugin_rpc, context, dev_status):
        self.router_info = {}
        self.updated_routers = set()
        self.removed_routers = set()
        self.sync_devices = set()
        self.fullsync = True
        self.plugin_rpc = plugin_rpc
        self.context = context
        self._dev_status = dev_status
        self._drivermgr = driver_mgr.PhysicalDeviceDriverManager(asr_ent)
        self._drivermgr.set_driver(None)
        driver = self._drivermgr.get_driver(None)
        driver.set_err_listener_context(self)

    def connection_err_callback(self, ex):
        LOG.exception(_("NetConf connection exception: %s") % (ex))
        self.fullsync = True

    def delete_invalid_cfg(self, router_db_info):
        if not router_db_info:
            router_db_info = self._fetch_router_info(all_routers=True)
        driver = self._drivermgr.get_driver(None)
        existing_cfg_dict = driver.delete_invalid_cfg(router_db_info)
        return existing_cfg_dict

    def prepare_fullsync(self, existing_cfg_dict):
        driver = self._drivermgr.get_driver(None)
        driver.prepare_fullsync(existing_cfg_dict)

    def clear_fullsync(self):
        driver = self._drivermgr.get_driver(None)
        driver.clear_fullsync()

    def _router_added(self, router_id, router):
        """Operations when a router is added.

        Create a new RouterInfo object for this router and add it to the
        service helpers router_info dictionary.  Then `router_added()` is
        called on the device driver.

        :param router_id: id of the router
        :param router: router dict
        :return: None
        """
        ri = RouterInfo(router_id, router)
        LOG.debug("router_added: %s", jsonutils.dumps(ri.router, indent=4))
        driver = self._drivermgr.set_driver(router)
        driver.router_added(ri)
        self.router_info[router_id] = ri

    def _router_removed(self, router_id, deconfigure=True):
        """Custom operations for ASR1K when a router is removed:

        Remove the the HA interfaces from the router_info dict,
        so that the ip nat pool is removed from the ASR router

        :param router_id: id of the router
        :param deconfigure: if True, the router's configuration is deleted from
        the hosting device.
        :return: None

        """
        ri = self.router_info.get(router_id)
        if ri:
            ri.router[l3_constants.HA_GW_KEY] = []
        super(PhyRouterContext, self)._router_removed(router_id, deconfigure)
        LOG.debug("router_removed: %s", jsonutils.dumps(ri.router, indent=4))

    def _internal_network_removed(self, ri, port, ex_gw_port):
        driver = self._drivermgr.get_driver(ri.id)
        driver.internal_network_removed(ri, port)
        if ri.snat_enabled and ex_gw_port:
            driver.disable_internal_network_NAT(ri, port, ex_gw_port, True)

    def process_service(self, device_ids=None, removed_devices_info=None):
        try:
            LOG.info(_("Sending heartbeat to ASR"))
            self._drivermgr.get_driver(None).send_empty_cfg()
            # self._drivermgr.get_driver(None).get_show_clock()
            LOG.debug("Routing service processing started")
            resources = {}
            routers = []
            removed_routers = []
            all_routers_flag = False
            if self.fullsync:
                LOG.debug("FullSync flag is on. Starting fullsync")
                # Setting all_routers_flag and clear the global full_sync flag
                all_routers_flag = True
                self.fullsync = False
                self.updated_routers.clear()
                self.removed_routers.clear()
                self.sync_devices.clear()
                routers = self._fetch_router_info(all_routers=True)
                existing_cfg_dict = self.delete_invalid_cfg(routers)
                self.prepare_fullsync(existing_cfg_dict)
                self.router_info = {}
            else:
                if self.updated_routers:
                    router_ids = list(self.updated_routers)
                    LOG.debug("Updated routers:%s", router_ids)
                    self.updated_routers.clear()
                    routers = self._fetch_router_info(router_ids=router_ids)
                if self.removed_routers:
                    removed_routers_ids = list(self.removed_routers)
                    LOG.debug("Removed routers:%s", removed_routers_ids)
                    for r in removed_routers_ids:
                        if r in self.router_info:
                            removed_routers.append(self.router_info[r].router)

            # Sort on hosting device
            if routers:
                resources['routers'] = routers
            if removed_routers:
                resources['removed_routers'] = removed_routers

            # Dispatch process_services() for each hosting device
            #pool = eventlet.GreenPool()
            #pool.spawn_n(self._process_routers, routers, removed_routers,
            #             0, all_routers=all_routers_flag)
            #pool.waitall()
            self._process_routers(routers, removed_routers, 0,
                                  all_routers=all_routers_flag)
            self.clear_fullsync()
        except Exception:
            LOG.exception(_("Failed processing routers"))
            self.fullsync = True

    def _adjust_router_list(self, routers):
        for r in routers:
            if r['id'] == "PHYSICAL_GLOBAL_ROUTER_ID":
                routers.remove(r)
                routers.append(r)
                return

    def _process_routers(self, routers, removed_routers,
                         device_id=None, all_routers=False):
        """Process the set of routers.

        Iterating on the set of routers received and comparing it with the
        set of routers already in the routing service helper, new routers
        which are added are identified. Before processing check the
        reachability (via ping) of hosting device where the router is hosted.
        If device is not reachable it is backlogged.

        For routers which are only updated, call `_process_router()` on them.

        When all_routers is set to True (because of a full sync),
        this will result in the detection and deletion of routers which
        have been removed.

        Whether the router can only be assigned to a particular hosting device
        is decided and enforced by the plugin. No checks are done here.

        :param routers: The set of routers to be processed
        :param removed_routers: the set of routers which where removed
        :param device_id: Id of the hosting device
        :param all_routers: Flag for specifying a partial list of routers
        :return: None
        """
        try:
            if all_routers:
                prev_router_ids = set(self.router_info)
            else:
                prev_router_ids = set(self.router_info) & set(
                    [router['id'] for router in routers])
            cur_router_ids = set()

            deleted_id_list = []

            for r in routers:
                if not r['admin_state_up']:
                        continue
                cur_router_ids.add(r['id'])

            # identify and remove routers that no longer exist
            for router_id in prev_router_ids - cur_router_ids:
                self._router_removed(router_id)
                deleted_id_list.append(router_id)

            if removed_routers:
                for router in removed_routers:
                    self._router_removed(router['id'])
                    deleted_id_list.append(router['id'])

            self._adjust_router_list(routers)
            for r in routers:
                if r['id'] in deleted_id_list:
                    continue

                try:
                    if not r['admin_state_up']:
                        continue
                    cur_router_ids.add(r['id'])

                    if r['id'] not in self.router_info:
                        self._router_added(r['id'], r)
                    ri = self.router_info[r['id']]
                    ri.router = r
                    self._process_router(ri)
                except KeyError as e:
                    LOG.exception(_("Key Error, missing key: %s"), e)
                    # make sure the ID is in a list (for set.update)
                    self.updated_routers.update([r['id']])
                    self.fullsync = True
                    continue
                except cfg_exceptions.DriverException as e:
                    LOG.exception(_("Driver Exception on router:%(id)s. "
                                    "Error is %(e)s"), {'id': r['id'], 'e': e})
                    self.updated_routers.update([r['id']])
                    # TODO(cisco): Do fullsync on error to be safe for now,
                    # can optimize later
                    self.fullsync = True
                    continue

            # identify and remove routers that no longer exist
            #for router_id in prev_router_ids - cur_router_ids:
            #    self._router_removed(router_id)
            #if removed_routers:
            #    for router in removed_routers:
            #        self._router_removed(router['id'])

        except Exception:
            LOG.exception(_("Exception in processing routers on device:%s"),
                          device_id)
            self.sync_devices.add(device_id)

    def _get_port_set_diffs(self, existing_list, current_list):
        existing_port_ids = set([p['id'] for p in existing_list])
        current_port_ids = set([p['id'] for p in current_list
                                if p['admin_state_up']])
        new_ports = [p for p in current_list
                     if
                     p['id'] in (current_port_ids - existing_port_ids)]
        old_ports = [p for p in existing_list
                     if p['id'] not in current_port_ids]

        return old_ports, new_ports

    def _send_update_port_statuses(self, port_ids, status):
        """Sends update notifications to set the operational status of the
        list of router ports provided. To make each notification doesn't exceed
        the RPC length, each message contains a maximum of MAX_PORTS_IN_BATCH
        port ids.

        :param port_ids: List of ports to update the status
        :param status: operational status to update
                       (ex: l3_constants.PORT_STATUS_ACTIVE)
        """
        if not port_ids:
            return
        i = 0
        MAX_PORTS_IN_BATCH = 50
        list_chunks_ports = [port_ids[i:i + MAX_PORTS_IN_BATCH]
            for i in xrange(0, len(port_ids), MAX_PORTS_IN_BATCH)]
        for chunk_ports in list_chunks_ports:
            self.plugin_rpc.send_update_port_statuses(self.context,
                            chunk_ports, status)

    def _process_router(self, ri):
        """Process a router, apply latest configuration and update router_info.

        Get the router dict from  RouterInfo and proceed to detect changes
        from the last known state. When new ports or deleted ports are
        detected, `internal_network_added()` or `internal_networks_removed()`
        are called accordingly. Similarly changes in ex_gw_port causes
         `external_gateway_added()` or `external_gateway_removed()` calls.
        Next, floating_ips and routes are processed. Also, latest state is
        stored in ri.internal_ports and ri.ex_gw_port for future comparisons.

        :param ri : RouterInfo object of the router being processed.
        :return:None
        :raises: neutron.plugins.cisco.cfg_agent.cfg_exceptions.DriverException
        if the configuration operation fails.
        """
        try:
            ex_gw_port = ri.router.get('gw_port')
            ri.ha_info = ri.router.get('ha_info', None)
            internal_ports = ri.router.get(l3_constants.INTERFACE_KEY, [])
            gw_ports = ri.router.get(l3_constants.HA_GW_KEY, [])

            (old_ports, new_ports) = self._get_port_set_diffs(
                    ri.internal_ports, internal_ports)
            (old_gw_ports, new_gw_ports) = self._get_port_set_diffs(
                    ri.ha_gw_ports, gw_ports)
            list_port_ids_up = []

            for p in old_ports:
                self._internal_network_removed(ri, p, ri.ex_gw_port)
                ri.internal_ports.remove(p)

            for p in new_ports:
                self._set_subnet_info(p)
                self._internal_network_added(ri, p, ex_gw_port)
                ri.internal_ports.append(p)
                list_port_ids_up.append(p['id'])

            for p in old_gw_ports:
                self._external_gateway_removed(ri, p)
                ri.ha_gw_ports.remove(p)

            for p in new_gw_ports:
                self._set_subnet_info(p)
                self._external_gateway_added(ri, p)
                ri.ha_gw_ports.append(p)
                list_port_ids_up.append(p['id'])

            self._send_update_port_statuses(list_port_ids_up,
                l3_constants.PORT_STATUS_ACTIVE)
            self._process_router_floating_ips(ri, ex_gw_port)
            ri.ex_gw_port = ex_gw_port
            self._routes_updated(ri)
        except cfg_exceptions.DriverException as e:
            with excutils.save_and_reraise_exception():
                self.updated_routers.update([ri.router_id])
                LOG.error(e)

    def _process_router_floating_ips(self, ri, ex_gw_port):
        """Process a router's floating ips.

        Compare current floatingips (in ri.floating_ips) with the router's
        updated floating ips (in ri.router.floating_ips) and detect
        floating_ips which were added or removed. Notify driver of
        the change via `floating_ip_added()` or `floating_ip_removed()`.

        :param ri:  RouterInfo object of the router being processed.
        :param ex_gw_port: Port dict of the external gateway port.
        :return: None
        :raises: neutron.plugins.cisco.cfg_agent.cfg_exceptions.DriverException
        if the configuration operation fails.
        """
        floating_ips = ri.router.get(l3_constants.FLOATINGIP_KEY, [])
        existing_floating_ip_ids = set(
            [fip['id'] for fip in ri.floating_ips])
        cur_floating_ip_ids = set([fip['id'] for fip in floating_ips])

        id_to_fip_map = {}

        LOG.debug("CUR FLOATING IPS: %s" % floating_ips)
        LOG.debug("existing_floating_ip: %s, cur_floating_ip:%s" % (
                existing_floating_ip_ids, cur_floating_ip_ids))

        fips_to_add = []
        for fip in floating_ips:
            if fip['port_id']:
                # store to see if floatingip was remapped
                id_to_fip_map[fip['id']] = fip
                if fip['id'] not in existing_floating_ip_ids:
                    # Ensure that we add only after remove, in case same
                    # fixed_ip is mapped to different floating_ip within
                    # the same loop cycle. If add occurs before first,
                    # cfg will fail because of existing entry with
                    # identical fixed_ip
                    fips_to_add.append(fip)

        floating_ip_ids_to_remove = (existing_floating_ip_ids -
                                     cur_floating_ip_ids)
        LOG.debug("fip_ids_to_add: %s" % (fips_to_add))
        LOG.debug("fip_ids_to_remove: %s" % (floating_ip_ids_to_remove))

        fips_to_remove = []
        fip_statuses = {}
        for fip in ri.floating_ips:
            if fip['id'] in floating_ip_ids_to_remove:
                fips_to_remove.append(fip)
                self._floating_ip_removed(ri, ri.ex_gw_port,
                                          fip['floating_ip_address'],
                                          fip['fixed_ip_address'])
                fip_statuses[fip['id']] = l3_constants.FLOATINGIP_STATUS_DOWN
                LOG.debug("Add to fip_statuses DOWN id:%s fl_ip:%s fx_ip:%s",
                        fip['id'], fip['floating_ip_address'],
                        fip['fixed_ip_address'])
                self.plugin_rpc.update_floatingip_statuses(self.context,
                        ri.router_id, fip_statuses)
            else:
                # handle remapping of a floating IP
                new_fip = id_to_fip_map[fip['id']]
                new_fixed_ip = new_fip['fixed_ip_address']
                existing_fixed_ip = fip['fixed_ip_address']
                LOG.debug("FIP: %s, old FxIP: %s, new FxIP: %s\n\n" % (new_fip,
                        existing_fixed_ip, new_fixed_ip))

                if (new_fixed_ip and existing_fixed_ip and
                        new_fixed_ip != existing_fixed_ip):
                    floating_ip = fip['floating_ip_address']
                    self._floating_ip_removed(ri, ri.ex_gw_port,
                                              floating_ip,
                                              existing_fixed_ip)
                    fips_to_remove.append(fip)
                    fips_to_add.append(new_fip)
                    fip_statuses[fip['id']] = \
                        l3_constants.FLOATINGIP_STATUS_DOWN

        for fip in fips_to_remove:
            ri.floating_ips.remove(fip)

        for fip in fips_to_add:
            self._floating_ip_added(ri, ex_gw_port,
                                    fip['floating_ip_address'],
                                    fip['fixed_ip_address'])
            ri.floating_ips.append(fip)
            fip_statuses[fip['id']] = l3_constants.FLOATINGIP_STATUS_ACTIVE
            LOG.debug("Add to fip_statuses ACTIVE id:%s fl_ip:%s fx_ip:%s",
                    fip['id'], fip['floating_ip_address'],
                    fip['fixed_ip_address'])

        if fip_statuses:
            LOG.debug("Sending floatingip_statuses_update: %s", fip_statuses)
            self.plugin_rpc.update_floatingip_statuses(self.context,
                    ri.router_id, fip_statuses)

    def _get_num_routers_per_hd(self, router_infos):
        if not router_infos:
            return {}

        dict_of_asrs_by_device_ids = collections.defaultdict(set)
        for ri in router_infos:
            intfs = ri.router.get('_interfaces')
            if not intfs:
                continue
            for intf in intfs:
                asr = intf.get('phy_router_db')
                device_id = intf.get('device_id')
                if not asr or not device_id:
                    continue
                dict_of_asrs_by_device_ids[asr['id']].add(device_id)
        routers_per_hd = {}
        for r in dict_of_asrs_by_device_ids:
            routers_per_hd[r] = len(dict_of_asrs_by_device_ids[r])
        return routers_per_hd


class RoutingServiceHelperWithPhyContext(
        routing_svc_helper.RoutingServiceHelper):

    def __init__(self, host, conf, cfg_agent):
        self.conf = conf
        self.cfg_agent = cfg_agent
        self.context = n_context.get_admin_context_without_session()
        self.plugin_rpc = PhyCiscoRoutingPluginApi(topics.L3PLUGIN, host)
        self._dev_status = device_status.DeviceStatus()
        self.topic = '%s.%s' % (c_constants.CFG_AGENT_L3_ROUTING, host)
        self._setup_rpc()
        self._asr_config = asr1kv_driver.ASR1kConfigInfo()

        self._asr_contexts = {}
        for asr in self._asr_config.get_asr_list():
            self._asr_contexts[asr['name']] = PhyRouterContext(asr,
                    self.plugin_rpc, self.context, self._dev_status)

    ### Notifications from Plugin ####

    def router_deleted(self, context, routers):
        """Deal with router deletion RPC message."""
        LOG.debug('Got asr router deleted notification for %s', routers)
        for asr_name, asr_ctx in self._asr_contexts.iteritems():
            asr_ctx.removed_routers.update(routers)

    def routers_updated(self, context, routers):
        """Deal with routers modification and creation RPC message."""
        LOG.debug('Got asr routers updated notification :%s', routers)
        if routers:
            # This is needed for backward compatibility
            if isinstance(routers[0], dict):
                routers = [router['id'] for router in routers]
            for asr_name, asr_ctx in self._asr_contexts.iteritems():
                asr_ctx.updated_routers.update(routers)

    def router_removed_from_agent(self, context, payload):
        LOG.debug('Got asr router removed from agent :%r', payload)
        for asr_name, asr_ctx in self._asr_contexts.iteritems():
            asr_ctx.removed_routers.add(payload['router_id'])

    def router_added_to_agent(self, context, payload):
        LOG.debug('Got asr router added to agent :%r', payload)
        self.routers_updated(context, payload)

    ### General Notifications  ####
    def resync_asrs(self, context):
        for asr_name, asr_ctx in self._asr_contexts.iteritems():
            asr_ctx.fullsync = True

    # Routing service helper public methods
    def process_service(self, device_ids=None, removed_devices_info=None):

        try:
            self.plugin_rpc.agent_heartbeat(self.context)
        except messaging.MessagingTimeout:
            LOG.exception(_("Server heartbeat timeout"))
            self.resync_asrs(self.context)
            return  # don't try to configure ASRs, can't get latest DB info

        pool = eventlet.GreenPool()
        for asr_name, asr_ctx in self._asr_contexts.iteritems():
            pool.spawn_n(asr_ctx.process_service, device_ids,
                        removed_devices_info)
        pool.waitall()

    def collect_state(self, configurations):
        if len(self._asr_contexts) < 1:
            return configurations

        asr_ctx = self._asr_contexts.values()[0]
        return asr_ctx.collect_state(configurations)
