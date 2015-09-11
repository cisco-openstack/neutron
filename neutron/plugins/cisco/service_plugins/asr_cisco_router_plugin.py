# Copyright 2011 Cisco Systems, Inc.  All rights reserved.
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

from neutron.common import constants as l3_constants
from neutron.common import rpc as n_rpc
from neutron.common import topics
from neutron.db import agents_db
from neutron.db import common_db_mixin
from neutron.extensions import l3
from neutron import manager
from neutron.openstack.common import log as logging
from neutron.plugins.cisco.db.l3 import asr_l3_router_appliance_db
from neutron.plugins.cisco.db.l3 import device_handling_db
from neutron.plugins.cisco.l3.rpc import (l3_router_cfgagent_rpc_cb as
                                          l3_router_rpc)
from neutron.plugins.cisco.l3.rpc import devices_cfgagent_rpc_cb as devices_rpc
from neutron.plugins.common import constants

DEVICE_OWNER_ROUTER_HA_INTF = "network:router_ha_interface"
DEVICE_OWNER_ROUTER_HA_GW = "network:router_ha_gateway"
PHYSICAL_GLOBAL_ROUTER_ID = "PHYSICAL_GLOBAL_ROUTER_ID"

LOG = logging.getLogger(__name__)


class CiscoRouterPluginRpcCallbacks(n_rpc.RpcCallback,
                                    l3_router_rpc.L3RouterCfgRpcCallbackMixin,
                                    devices_rpc.DeviceCfgRpcCallbackMixin):
    RPC_API_VERSION = '1.1'

    def __init__(self, l3plugin):
        super(CiscoRouterPluginRpcCallbacks, self).__init__()
        self._l3plugin = l3plugin

    @property
    def _core_plugin(self):
        return manager.NeutronManager.get_plugin()

    def create_rpc_dispatcher(self):
        return n_rpc.PluginRpcDispatcher([self])

    def agent_heartbeat(self, context, **kwargs):
        """Handle heartbeat from cfg_agent

        @param context: contains user information
        @param host - originator of callback
        @return: String with value "OK"
        """
        try:
            host = kwargs.get('host')
        except AttributeError:
            LOG.error(_("Received heartbeat without host info"))

        LOG.debug("host %s", host)
        return "OK"

    def update_floatingip_statuses(self, context, router_id, fip_statuses):
        """Update operational status for a floating IP."""

        with context.session.begin(subtransactions=True):
            for (floatingip_id, status) in fip_statuses.iteritems():
                LOG.debug(_("New status for floating IP %(floatingip_id)s: "
                        "%(status)s"), {'floatingip_id': floatingip_id,
                                        'status': status})
                try:
                    self._l3plugin.update_floatingip_status(context,
                                                           floatingip_id,
                                                           status)
                except l3.FloatingIPNotFound:
                    LOG.debug(_("Floating IP: %s no longer present."),
                              floatingip_id)
            known_router_fips = self._l3plugin.get_floatingips(
                context, {'last_known_router_id': [router_id]})
            fips_to_disable = (fip['id'] for fip in known_router_fips
                               if not fip['router_id'])
            for fip_id in fips_to_disable:
                LOG.debug("update_fip_statuses: disable: %s", fip_id)
                self._l3plugin.update_floatingip_status(
                    context, fip_id, l3_constants.FLOATINGIP_STATUS_DOWN)

    def asr_update_port_statuses(self, context, port_ids, status):
        """Update the operational statuses of a list of router ports."""
        with context.session.begin(subtransactions=True):
            self._l3plugin.update_router_port_statuses(context, port_ids,
                                                       status)


class PhysicalCiscoRouterPlugin(common_db_mixin.CommonDbMixin,
        agents_db.AgentDbMixin,
        asr_l3_router_appliance_db.PhysicalL3RouterApplianceDBMixin,
        device_handling_db.DeviceHandlingMixin):

    """Implementation of Cisco L3 Router Service Plugin for Neutron.

    This class implements a L3 service plugin that provides
    router and floatingip resources and manages associated
    request/response.
    All DB functionality is implemented in class
    l3_router_appliance_db.L3RouterApplianceDBMixin.
    """
    supported_extension_aliases = ["router", "extraroute"]

    def __init__(self):
        self.setup_rpc()
        # for backlogging of non-scheduled routers
        self._setup_backlog_handling()
        self._setup_device_handling()

        self._phy_l3_mixin_init()

    def setup_rpc(self):
        # RPC support
        self.topic = topics.L3PLUGIN
        self.conn = n_rpc.create_connection(new=True)
        self.endpoints = [CiscoRouterPluginRpcCallbacks(self)]
        self.conn.create_consumer(self.topic, self.endpoints,
                                  fanout=False)
        # Consume from all consumers in threads
        self.conn.consume_in_threads()

    def get_plugin_type(self):
        return constants.L3_ROUTER_NAT

    def get_plugin_description(self):
        return ("Cisco Router Service Plugin for basic L3 forwarding"
                " between (L2) Neutron networks and access to external"
                " networks via a NAT gateway.")

    @property
    def _core_plugin(self):
        try:
            return self._plugin
        except AttributeError:
            self._plugin = manager.NeutronManager.get_plugin()
            return self._plugin
