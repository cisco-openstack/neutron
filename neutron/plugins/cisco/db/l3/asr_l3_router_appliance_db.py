# Copyright 2014 Cisco Systems, Inc.  All rights reserved.
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

import copy
import sqlalchemy as sa
import time

from oslo.config import cfg

from neutron.api.v2 import attributes
from neutron.common import constants as l3_constants
from neutron.common import exceptions as n_exc
from neutron import context as n_context
from neutron.db import l3_db
from neutron.db import model_base
from neutron.db import models_v2
from neutron.extensions import l3
from neutron.extensions import providernet as pr_net
from neutron import manager
from neutron.openstack.common import lockutils
from neutron.openstack.common import log as logging
from neutron.plugins.cisco.cfg_agent.device_drivers.asr1k import (
    asr1k_routing_driver as asr1k_driver)
from neutron.plugins.cisco.common import cisco_constants as c_const
from neutron.plugins.cisco.db.l3 import l3_router_appliance_db
from neutron.plugins.cisco.l3.rpc import asr_l3_router_rpc_joint_agent_api
from neutron.plugins.common import constants

PHYSICAL_GLOBAL_ROUTER_ID = "PHYSICAL_GLOBAL_ROUTER_ID"

LOG = logging.getLogger(__name__)


class CiscoPhysicalRouter(model_base.BASEV2, models_v2.HasId):
    """Represents a physical cisco router."""

    __tablename__ = 'cisco_phy_routers'

    name = sa.Column(sa.String(255))
    status = sa.Column(sa.String(16))
    # other columns TBD


class CiscoPhyRouterPortBinding(model_base.BASEV2):
    """ HSRP interface mappings to physical ASRs """

    __tablename__ = 'cisco_phy_router_port_bindings'

    port_id = sa.Column(sa.String(36),
                        sa.ForeignKey('ports.id', ondelete="CASCADE"),
                        primary_key=True)

    subnet_id = sa.Column(sa.String(36),
                          sa.ForeignKey("subnets.id", ondelete='CASCADE'))

    router_id = sa.Column(sa.String(36),
                          sa.ForeignKey("routers.id", ondelete='CASCADE'))

    phy_router_id = sa.Column(sa.String(36),
                          sa.ForeignKey("cisco_phy_routers.id",
                              ondelete='CASCADE'))


class PhysicalL3RouterApplianceDBMixin(
        l3_router_appliance_db.L3RouterApplianceDBMixin,
        l3_db.L3RpcNotifierMixin):

    @property
    def l3_cfg_rpc_notifier(self):
        if not hasattr(self, '_l3_cfg_rpc_notifier'):
            self._l3_cfg_rpc_notifier = (asr_l3_router_rpc_joint_agent_api.
                    PhysicalL3RouterJointAgentNotifyAPI(self))
        return self._l3_cfg_rpc_notifier

    def _phy_l3_mixin_init(self):
        self._db_synced = False
        self.asr_cfg_info = asr1k_driver.ASR1kConfigInfo()

    def notify_routers_updated(self, context, router_ids,
                               operation=None, data=None):
        if router_ids:
            filters = {'id': router_ids}
            router_dicts = self.get_routers(context, filters=filters)
            self.l3_cfg_rpc_notifier.routers_updated(context, router_dicts,
                                                     operation, data)

    def sync_asr_list_with_db(self, context, asr_list):

        if self._db_synced is True:
            return

        db_names = []
        cfg_names = []
        missing_db_asr_list = []
        #asr_list = self.get_asr_list()

        phy_router_qry = context.session.query(CiscoPhysicalRouter).all()

        # Build list of names that exist in cfg
        for asr in asr_list:
            cfg_names.append(asr['name'])

        # Build list of names that exist in DB
        # Build list of db objects that do not have names in cfg
        for db_asr in phy_router_qry:
            db_names.append(db_asr.name)
            if db_asr.name not in cfg_names:
                missing_db_asr_list.append(db_asr)

        # Update DB
        with context.session.begin(subtransactions=True):

            # Add ASRs from cfg with names not in db
            for asr in asr_list:
                if asr['name'] not in db_names:
                    new_db_asr = CiscoPhysicalRouter(name=asr['name'])
                    context.session.add(new_db_asr)

            # Delete missing ASRs from db
            for missing_asr in missing_db_asr_list:
                context.session.delete(missing_asr)
                # missing_asr.delete()

        self._db_synced = True

    def _create_hsrp_interfaces(self, context, router_id, subnet, dev_owner):
        context = context.elevated()
        # Create HSRP standby interfaces
        port_list = []
        num_asr = len(self.asr_cfg_info.get_asr_list())
        with context.session.begin(subtransactions=True):
            for asr_idx in range(0, num_asr):
                # Hide these ports from non-admin, assign a blank tenant_id
                asr_port = self._core_plugin.create_port(context, {
                    'port':
                    {'tenant_id': '',
                     'network_id': subnet['network_id'],
                     'fixed_ips': attributes.ATTR_NOT_SPECIFIED,
                     'mac_address': attributes.ATTR_NOT_SPECIFIED,
                     'admin_state_up': True,
                     'device_id': router_id,
                     'device_owner': dev_owner,
                     'name': ''}})

                LOG.info(_("added new port %s") % (asr_port))
                port_list.append(asr_port)
                router_port = l3_db.RouterPort(
                    router_id=router_id,
                    port_id=asr_port['id'],
                    port_type=dev_owner
                )
                context.session.add(router_port)

            self._bind_hsrp_interfaces_to_router(context, router_id,
                                                 port_list)

        for port in port_list:
            ha_info = {'id': router_id,
                       'tenant_id': subnet['tenant_id'],
                       'port_id': port['id'],
                       'subnet_id': port['fixed_ips'][0]['subnet_id']}
            routers = [self.get_router(context, router_id)]
            self.notify_router_interface_action(context, ha_info, routers,
                                                'add')

    def _delete_hsrp_interfaces(self, context, router_id, subnet, dev_owner):
        context = context.elevated()
        # Delete HSRP standby interfaces
        port_list = []
        rport_qry = context.session.query(models_v2.Port)
        if router_id is None:
            asr_ports = rport_qry.filter_by(device_owner=dev_owner,
                                            network_id=subnet['network_id'])
        else:
            asr_ports = rport_qry.filter_by(device_id=router_id,
                                            device_owner=dev_owner,
                                            network_id=subnet['network_id'])

        for asr_port in asr_ports:
            port_list.append(asr_port)
            self._core_plugin.delete_port(context, asr_port['id'],
                                          l3_port_check=False)
            LOG.debug("_delete_hsrp_interfaces: deleted port %s" % asr_port)

        # don't notify if gw hsrp interfaces are deleted
        if dev_owner == l3_constants.DEVICE_OWNER_ROUTER_HA_GW:
            return

        for port in port_list:
            ha_info = {'id': router_id,
                       'tenant_id': subnet['tenant_id'],
                       'port_id': port['id'],
                       'subnet_id': subnet['id']}
            routers = [self.get_router(context, router_id)]
            self.notify_router_interface_action(context, ha_info, routers,
                                                'remove')

    @lockutils.synchronized('router-change', 'neutron-')
    def add_router_interface(self, context, router_id, interface_info):
        info = super(PhysicalL3RouterApplianceDBMixin,
                    self).add_router_interface(context, router_id,
                    interface_info)

        LOG.info(_("finished parent add_router_interface, info:%s") % (info))

        # If no exception has been raised, we're good to go
        subnet_id = info['subnet_id']
        subnet = self._core_plugin._get_subnet(context, subnet_id)

        self._create_hsrp_interfaces(context, router_id, subnet,
                                     l3_constants.DEVICE_OWNER_ROUTER_HA_INTF)
        return info

    @lockutils.synchronized('router-change', 'neutron-')
    def remove_router_interface(self, context, router_id, interface_info):
        info = super(PhysicalL3RouterApplianceDBMixin,
                    self).remove_router_interface(context, router_id,
                        interface_info)

        LOG.info(_("remove_router_interface paremt ended, info:%s") % (info))

        # If no exception has been raised, we're good to go
        subnet_id = info['subnet_id']
        subnet = self._core_plugin._get_subnet(context, subnet_id)

        self._delete_hsrp_interfaces(context, router_id, subnet,
                                     l3_constants.DEVICE_OWNER_ROUTER_HA_INTF)
        return info

    def _bind_hsrp_interfaces_to_router(self, context, router_id, port_list):
        # go ahead and map these interfaces to physical ASRs
        self.sync_asr_list_with_db(context, self.asr_cfg_info.get_asr_list())

        phy_router_qry = context.session.query(CiscoPhysicalRouter).all()

        for db_asr, port in zip(phy_router_qry, port_list):
            port_binding = CiscoPhyRouterPortBinding(port_id=port['id'],
                                subnet_id=port['fixed_ips'][0]['subnet_id'],
                                router_id=router_id, phy_router_id=db_asr.id)
            context.session.add(port_binding)

    '''
    How many routers have a port associated with a particular external network?
    '''
    def _count_ha_routers_on_network(self, context, network_id):
        context = context.elevated()
        rport_qry = context.session.query(models_v2.Port)
        asr_ports = rport_qry.filter_by(
                            device_owner=l3_constants.DEVICE_OWNER_ROUTER_GW,
                            network_id=network_id)

        num_ports = asr_ports.count()
        LOG.debug("num routers on network: %s, %s" % (network_id, num_ports))
        for port in asr_ports:
            LOG.debug("port: %s" % (port))
        return num_ports

    def _send_physical_global_router_updated_notification(self, context):
        phy_router = self.get_router(context, PHYSICAL_GLOBAL_ROUTER_ID)
        if phy_router:
            self.l3_cfg_rpc_notifier.routers_updated(context,
                                                     [phy_router])
    '''
    Create a router construct used to hold "global" external network
    HSRP interfaces of type DEVICE_OWNER_ROUTER_HA_GW
    '''
    def _create_physical_global_router(self, context):
        global_rtr_qry = context.session.query(l3_db.Router)
        global_rtr_qry = global_rtr_qry.filter_by(id=PHYSICAL_GLOBAL_ROUTER_ID)
        if global_rtr_qry.count() > 0:
            return

        with context.session.begin(subtransactions=True):
            router_db = l3_db.Router(id=PHYSICAL_GLOBAL_ROUTER_ID,
                                     tenant_id='',
                                     name=PHYSICAL_GLOBAL_ROUTER_ID,
                                     admin_state_up=True,
                                     status="ACTIVE")
            context.session.add(router_db)
            self._send_physical_global_router_updated_notification(context)

        return
        #return self._make_router_dict(router_db, process_extensions=False)

    '''
    Create HSRP standby interfaces for external network.

    As these are 'global' resources, shared across tenants and routers,
    they will not have a device_id associated.

    They will only be created when an external network is assigned to a router
    for the first time.

    They will be deleted when an external network is no longer assigned to any
    virtual router.
    '''
    def _create_router_gw_hsrp_interfaces(self, context, router, network_id,
                                          existing_port_list):
        # Port has no 'tenant-id', as it is hidden from user

        with context.session.begin(subtransactions=True):
            num_asr = len(self.asr_cfg_info.get_asr_list())
            for asr_idx in range(0, num_asr):

                gw_port = self._core_plugin.create_port(context.elevated(), {
                    'port': {'tenant_id': '',  # intentionally not set
                    'network_id': network_id,
                    'mac_address': attributes.ATTR_NOT_SPECIFIED,
                    'fixed_ips': attributes.ATTR_NOT_SPECIFIED,
                    #'device_id': router['id'],
                    #'device_id': network_id,
                    'device_id': PHYSICAL_GLOBAL_ROUTER_ID,
                    'device_owner': l3_constants.DEVICE_OWNER_ROUTER_HA_GW,
                    'admin_state_up': True,
                    'name': ''}})

                existing_port_list.append(gw_port)

                if not gw_port['fixed_ips']:
                    for deleted_port in existing_port_list:
                        self._core_plugin.delete_port(context.elevated(),
                                                      deleted_port['id'],
                                                      l3_port_check=False)
                        msg = (_('No IPs available for external network %s') %
                               network_id)

                    raise n_exc.BadRequest(resource='router', msg=msg)

                router_port = l3_db.RouterPort(
                    router_id=PHYSICAL_GLOBAL_ROUTER_ID,
                    port_id=gw_port['id'],
                    port_type=l3_constants.DEVICE_OWNER_ROUTER_HA_GW
                )
                context.session.add(router_port)

            self._bind_hsrp_interfaces_to_router(context, router['id'],
                    existing_port_list[1:])

    def _create_phy_router_gw_port(self, context, router, network_id):
        # Port has no 'tenant-id', as it is hidden from user
        gw_port = self._core_plugin.create_port(context.elevated(), {
            'port': {'tenant_id': '',  # intentionally not set
                     'network_id': network_id,
                     'mac_address': attributes.ATTR_NOT_SPECIFIED,
                     'fixed_ips': attributes.ATTR_NOT_SPECIFIED,
                     #'device_id': router['id'],
                     'device_id': PHYSICAL_GLOBAL_ROUTER_ID,
                     'device_owner': l3_constants.DEVICE_OWNER_ROUTER_GW,
                     'admin_state_up': True,
                     'name': ''}})

        if not gw_port['fixed_ips']:
            self._core_plugin.delete_port(context.elevated(), gw_port['id'],
                                          l3_port_check=False)
            msg = (_('No IPs available for external network %s') %
                   network_id)
            raise n_exc.BadRequest(resource='router', msg=msg)

        with context.session.begin(subtransactions=True):
            router_port = l3_db.RouterPort(
                    router_id=PHYSICAL_GLOBAL_ROUTER_ID,
                    port_id=gw_port['id'],
                    port_type=l3_constants.DEVICE_OWNER_ROUTER_GW)
            context.session.add(router_port)

    def _update_router_gw_info(self, context, router_id, info, router=None):

        context = context.elevated()
        self._create_physical_global_router(context)

        # TODO(salvatore-orlando): guarantee atomic behavior also across
        # operations that span beyond the model classes handled by this
        # class (e.g.: delete_port)
        router = router or self._get_router(context, router_id)
        gw_port = router.gw_port
        # network_id attribute is required by API, so it must be present
        network_id = info['network_id'] if info else None
        if network_id:
            network_db = self._core_plugin._get_network(context, network_id)
            if not network_db.external:
                msg = _("Network %s is not a valid external "
                        "network") % network_id
                raise n_exc.BadRequest(resource='router', msg=msg)

        # figure out if we need to delete existing port
        if gw_port and gw_port['network_id'] != network_id:
            fip_count = self.get_floatingips_count(context.elevated(),
                                                   {'router_id': [router_id]})
            if fip_count:
                raise l3.RouterExternalGatewayInUseByFloatingIp(
                    router_id=router_id, net_id=gw_port['network_id'])
            with context.session.begin(subtransactions=True):
                router.gw_port = None
                context.session.add(router)

            subnet_id = gw_port['fixed_ips'][0]['subnet_id']
            subnet = self._core_plugin._get_subnet(context.elevated(),
                                                   subnet_id)

            self._core_plugin.delete_port(context.elevated(),
                                          gw_port['id'],
                                          l3_port_check=False)

            # No external gateway assignments left, clear the HSRP interfaces
            if self._count_ha_routers_on_network(context,
                                                 gw_port['network_id']) == 1:
                self._delete_hsrp_interfaces(context.elevated(), None, subnet,
                                        l3_constants.DEVICE_OWNER_ROUTER_HA_GW)
                self._delete_hsrp_interfaces(context.elevated(),
                                        PHYSICAL_GLOBAL_ROUTER_ID, subnet,
                                        l3_constants.DEVICE_OWNER_ROUTER_GW)
                self._send_physical_global_router_updated_notification(context)

        if network_id is not None and (gw_port is None or
                                       gw_port['network_id'] != network_id):
            subnets = self._core_plugin._get_subnets_by_network(context,
                                                                network_id)
            for subnet in subnets:
                self._check_for_dup_router_subnet(context, router,
                                                  network_id, subnet['id'],
                                                  subnet['cidr'])

            # Only create HA ports if we are the first to create VLAN
            # subinterface for this ext network
            needs_hsrp_create = False
            if self._count_ha_routers_on_network(context, network_id) == 0:
                needs_hsrp_create = True

            self._create_router_gw_port(context, router, network_id)

            if needs_hsrp_create is True:
                self._create_phy_router_gw_port(context, router, network_id)
                self._create_router_gw_hsrp_interfaces(context, router,
                                    network_id, [router.gw_port])
                self._send_physical_global_router_updated_notification(context)

    @lockutils.synchronized('router-change', 'neutron-')
    def delete_router(self, context, id):
        LOG.debug("DELETING ROUTER WITH ID: %s" % id)
        context = context.elevated()
        with context.session.begin(subtransactions=True):
            router = self._get_router(context, id)

            # Ensure that the router is not used
            fips = self.get_floatingips_count(context.elevated(),
                                              filters={'router_id': [id]})
            if fips:
                raise l3.RouterInUse(router_id=id)

            device_filter = {'device_id': [id],
                     'device_owner': [l3_constants.DEVICE_OWNER_ROUTER_INTF]}
            ports = self._core_plugin.get_ports_count(context.elevated(),
                                                      filters=device_filter)
            if ports:
                raise l3.RouterInUse(router_id=id)

            #TODO(nati) Refactor here when we have router insertion model
            vpnservice = manager.NeutronManager.get_service_plugins().get(
                constants.VPN)
            if vpnservice:
                vpnservice.check_router_in_use(context, id)

            # Delete the gw port after the router has been removed to
            # avoid a constraint violation.
            router.gw_port = None
            device_filter = {'device_id': [id],
                             'device_owner':
                             [l3_constants.DEVICE_OWNER_ROUTER_GW]}
            ports = self._core_plugin.get_ports(context.elevated(),
                                                filters=device_filter)
            for port in ports:
                self._core_plugin._delete_port(context.elevated(),
                                               port['id'])

            context.session.delete(router)
            self.l3_cfg_rpc_notifier.router_deleted(context, router)

            # if this router had no gw port, we are done
            if len(ports) <= 0:
                return

            # If this router was the last one with a gw port on this
            # network delete the HSRP gw ports
            network_id = ports[0]['network_id']
            if self._count_ha_routers_on_network(context, network_id) == 1:
                device_filter = {'network_id': [network_id],
                    'device_owner': [l3_constants.DEVICE_OWNER_ROUTER_HA_GW,
                    l3_constants.DEVICE_OWNER_ROUTER_GW]}
                gw_ha_ports = self._core_plugin.get_ports(context.elevated(),
                                                      filters=device_filter)
                for gw_ha_port in gw_ha_ports:
                    self._core_plugin._delete_port(context.elevated(),
                                                   gw_ha_port['id'])
                self._send_physical_global_router_updated_notification(
                            context.elevated())

    @lockutils.synchronized('router-change', 'neutron-', external=True)
    def create_router(self, context, router):
        with context.session.begin(subtransactions=True):
            router_created = (super(
                            l3_router_appliance_db.L3RouterApplianceDBMixin,
                            self).create_router(context, router))
            self.l3_cfg_rpc_notifier.routers_updated(context,
                                                     [router_created])
        return router_created

    @lockutils.synchronized('router-change', 'neutron-')
    def update_router(self, context, id, router):
        r = router['router']
        # Check if external gateway has changed so we may have to
        # update trunking
        o_r_db = self._get_router(context, id)
        old_ext_gw = (o_r_db.gw_port or {}).get('network_id')
        new_ext_gw = (r.get('external_gateway_info', {}) or {}).get(
            'network_id')
        with context.session.begin(subtransactions=True):
            e_context = context.elevated()
            if old_ext_gw is not None and old_ext_gw != new_ext_gw:
                o_r = self._make_router_dict(o_r_db,
                                            process_extensions=False)
                # no need to schedule now since we're only doing this to
                # tear-down connectivity and there won't be any if not
                # already scheduled.
                self._add_type_and_hosting_device_info(e_context, o_r,
                                                       schedule=False)
            router_updated = (
                super(l3_router_appliance_db.L3RouterApplianceDBMixin,
                    self).update_router(context, id, router))
            routers = [copy.deepcopy(router_updated)]
            self._add_type_and_hosting_device_info(e_context, routers[0])

        self.l3_cfg_rpc_notifier.routers_updated(context, routers)
        return router_updated

    def _process_sync_data(self, routers, interfaces, floating_ips,
                           ha_gw_interfaces=[]):
        # begin benchmarking
        start_time = time.time()

        routers_dict = {}
        for router in routers:
            routers_dict[router['id']] = router

        for floating_ip in floating_ips:
            router = routers_dict.get(floating_ip['router_id'])
            if router:
                router_floatingips = router.get(l3_constants.FLOATINGIP_KEY,
                                                [])
                router_floatingips.append(floating_ip)
                router[l3_constants.FLOATINGIP_KEY] = router_floatingips
        for interface in interfaces:
            router = routers_dict.get(interface['device_id'])
            if router:
                router_interfaces = router.get(l3_constants.INTERFACE_KEY, [])
                router_interfaces.append(interface)
                router[l3_constants.INTERFACE_KEY] = router_interfaces

        for interface in ha_gw_interfaces:
            router = routers_dict.get(interface['device_id'])
            if router:
                router_interfaces = router.get(l3_constants.HA_GW_KEY, [])
                router_interfaces.append(interface)
                router[l3_constants.HA_GW_KEY] = router_interfaces

        # end benchmarking
        current_time = time.time()
        elapsed_time = current_time - start_time

        LOG.debug("*** elapsed time for _process_sync_data routers, %s" %
                  (elapsed_time))
        return routers_dict.values()

    def get_sync_data(self, context, router_ids=None, active=None):
        """Query routers and their related floating_ips, interfaces."""
        with context.session.begin(subtransactions=True):
            start_time = time.time()
            time1 = time.time()
            LOG.info(_("TIMING DATA FOR get_sync_data"))
            routers = self._get_sync_routers(context,
                                             router_ids=router_ids,
                                             active=active)
            time2 = time.time()
            LOG.info(_("  _get_sync_routers: %ss") % (time2 - time1))
            time1 = time2

            router_ids = [router['id'] for router in routers]
            floating_ips = self._get_sync_floating_ips(context, router_ids)

            time2 = time.time()
            LOG.info(_("_get_sync_floating_ips: %ss") % (time2 - time1))
            time1 = time2

            interfaces = self.get_sync_interfaces(context, router_ids)

            time2 = time.time()
            LOG.debug("_get_sync_interfaces normal: %ss" % (time2 - time1))
            time1 = time2

            ha_interfaces = self.get_sync_interfaces(context, router_ids,
                                 [l3_constants.DEVICE_OWNER_ROUTER_HA_INTF])

            time2 = time.time()
            LOG.info(_("_get_sync_interfaces HA: %ss") % (time2 - time1))
            time1 = time2

            ha_gw_interfaces = self.get_sync_interfaces(context, router_ids,
                                     [l3_constants.DEVICE_OWNER_ROUTER_HA_GW])

            time2 = time.time()
            LOG.info(_("_get_sync_routers HA_GW: %ss") % (time2 - time1))
            time1 = time2
            gw_interfaces = self.get_sync_interfaces(context, router_ids,
                                     [l3_constants.DEVICE_OWNER_ROUTER_GW])

            time2 = time.time()
            LOG.info(_("_get_sync_interfaces GW: %ss") % (time2 - time1))
            time1 = time2

            # Retrieve physical router port bindings
            all_ha_interfaces = ha_interfaces + ha_gw_interfaces
            for ha_intf in all_ha_interfaces:
                port_id = ha_intf['id']
                phy_port_qry = context.session.query(CiscoPhyRouterPortBinding,
                                      CiscoPhysicalRouter)
                phy_port_qry = phy_port_qry.filter(
                    CiscoPhyRouterPortBinding.port_id == port_id)
                router_id = CiscoPhysicalRouter.id
                phy_port_qry = phy_port_qry.filter(
                    CiscoPhyRouterPortBinding.phy_router_id == router_id)
                try:
                    port_binding_db, phy_router_db = phy_port_qry.first()
                except TypeError:
                    LOG.debug("_get_sync_interfaces: Unable to get phy_port")
                    port_binding_db = {}
                    phy_router_db = {}

                ha_intf['port_binding_db'] = port_binding_db
                ha_intf['phy_router_db'] = phy_router_db

            time2 = time.time()
            LOG.info(_("  _phy_port_binding: %ss") % (time2 - time1))
            time1 = time2

            interfaces += ha_interfaces
            ha_gw_interfaces += gw_interfaces

            time2 = time.time()
            LOG.info(_("get_sync_data total time: %s") % (time2 - start_time))

        return self._process_sync_data(routers, interfaces, floating_ips,
                                       ha_gw_interfaces)

    @lockutils.synchronized('router-change', 'neutron-', external=True)
    def get_sync_data_ext(self, context, router_ids=None, active=None):
        """Query routers and their related floating_ips, interfaces.

        Adds information about hosting device as well as trunking.
        """
        with context.session.begin(subtransactions=True):
            sync_data = self.get_sync_data(context, router_ids, active)

            start_time = time.time()

            LOG.info(_("TIMING DATA for get_sync_data_ext"))
            network_cache_dict = {}
            for router in sync_data:
                loop_start_time = time.time()
                self._add_type_and_hosting_device_info(context, router)
                add_type_time = time.time()
                self._add_hosting_port_info(context, router, None,
                                            network_cache_dict)
                add_host_port_time = time.time()

                LOG.debug(" per router, type_time: %s, host_port_time: %s" %
                    (add_type_time - loop_start_time,
                    add_host_port_time - loop_start_time))

            LOG.debug("Total time all loops: %s" % (time.time() - start_time))

            return sync_data

    @lockutils.synchronized('routerbacklog', 'neutron-')
    def _process_backlogged_routers(self):
        if self._refresh_router_backlog:
            self._sync_router_backlog()
        if not self._backlogged_routers:
            return
        context = n_context.get_admin_context()
        scheduled_routers = []
        LOG.info(_('Processing router (scheduling) backlog'))
        # try to reschedule
        for r_id, router in self._backlogged_routers.items():
            self._add_type_and_hosting_device_info(context, router)

            scheduled_routers.append(router)
            self._backlogged_routers.pop(r_id, None)

        # notify cfg agents so the scheduled routers are instantiated
        if scheduled_routers:
            self.l3_cfg_rpc_notifier.routers_updated(context,
                                                     scheduled_routers)

    def _get_phy_router_port_db(self, context, rid):
        query = context.session.query(CiscoPhyRouterPortBinding)
        query = query.filter(CiscoPhyRouterPortBinding.router_id == rid)
        try:
            phy_router_db = query.first()
        except TypeError:
            LOG.debug("_get_phy_router_port_db: Unable to get phy_router")
            phy_router_db = {}

        return phy_router_db

    def _get_router_info_for_agent(self, context, router):
        """Returns information about <router> needed by config agent.

            Convenience function that service plugins can use to populate
            their resources with information about the device hosting their
            logical resource.
        """
        rid = router['id']
        credentials = {'username': cfg.CONF.hosting_devices.csr1kv_username,
                       'password': cfg.CONF.hosting_devices.csr1kv_password}
        mgmt_ip = "1.1.1.1"
        return {'id': rid,
                'credentials': credentials,
                'management_ip_address': mgmt_ip,
                'protocol_port': 443,
                'created_at': str("AAA"),
                'booting_time': 10,
                'cfg_agent_id': 0}

    def _add_type_and_hosting_device_info(self, context, router,
                                          binding_info=None, schedule=True):
        """Adds type and hosting device information to a router."""
        LOG.debug("_add_type_and_hosting_device_info router:%s" % router)
        router['router_type'] = {'id': None,
                                'name': 'CSR1kv_router',
                                'cfg_agent_driver': (cfg.CONF.hosting_devices
                                            .csr1kv_cfgagent_router_driver)}
        router['hosting_device'] = self._get_router_info_for_agent(context,
                                                                   router)
        return

    def _add_hosting_port_info(self, context, router, plugging_driver,
                               network_cache_dict):
        """Adds hosting port information to router ports.

        We only populate hosting port info, i.e., reach here, if the
        router has been scheduled to a hosting device. Hence this
        a good place to allocate hosting ports to the router ports.
        """
        # cache of hosting port information: {mac_addr: {'name': port_name}}
        hosting_pdata = {}

        if router['external_gateway_info'] is not None:
            self._get_hosting_info_for_port_no_vm(context,
                                                  router['id'],
                                                  router['gw_port'],
                                                  hosting_pdata,
                                                  network_cache_dict)

        for itfc in router.get(l3_constants.INTERFACE_KEY, []):
            self._get_hosting_info_for_port_no_vm(context,
                                                  router['id'], itfc,
                                                  hosting_pdata,
                                                  network_cache_dict)

        for itfc in router.get(l3_constants.HA_GW_KEY, []):
            self._get_hosting_info_for_port_no_vm(context,
                                                  router['id'], itfc,
                                                  hosting_pdata,
                                                  network_cache_dict)

    def _get_hosting_info_for_port_no_vm(self, context, router_id, port,
                                         hosting_pdata, network_cache_dict):
        LOG.info(_("Get host info, network_id: %s") % port['network_id'])
        if port['network_id'] not in network_cache_dict:
            network = self._core_plugin.get_networks(context,
                    {'id': [port['network_id']]}, [pr_net.SEGMENTATION_ID])

            LOG.info(_("CACHE MISS, network: %s") % (network))
            if len(network) < 1:
                allocated_vlan = None
            else:
                network_cache_dict[port['network_id']] = network[0]
                allocated_vlan = network[0].get(pr_net.SEGMENTATION_ID)
        else:
            LOG.info(_("CACHE HIT"))
            network = network_cache_dict[port['network_id']]
            allocated_vlan = network.get(pr_net.SEGMENTATION_ID)

        if hosting_pdata.get('mac') is None:
            hosting_pdata['mac'] = "mac_placeholder"
            hosting_pdata['name'] = "intf_name_placeholder"

        port['hosting_info'] = {'hosting_port_id': 0,
                                'segmentation_id': allocated_vlan,
                                'hosting_mac': hosting_pdata['mac'],
                                'hosting_port_name': hosting_pdata['name']}

    def list_active_sync_routers_on_hosting_devices(self, context, host,
                                                    router_ids=None,
                                                    hosting_device_ids=None):
        agent = self._get_agent_by_type_and_host(
            context, c_const.AGENT_TYPE_CFG, host)
        if not agent.admin_state_up:
            return []

        if router_ids is None:
            router_ids = []
            routers = self.get_routers(context)
            for router in routers:
                router_ids.append(router['id'])

        LOG.info(_("active sync router_ids: %s") % (router_ids))

        return self.get_sync_data_ext(context, router_ids=router_ids,
                                      active=True)
