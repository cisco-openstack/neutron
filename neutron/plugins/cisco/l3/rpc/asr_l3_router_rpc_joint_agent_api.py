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
#

from neutron.openstack.common import log as logging
from neutron.plugins.cisco.common import cisco_constants as c_constants
from neutron.plugins.cisco.l3.rpc import l3_router_rpc_joint_agent_api

LOG = logging.getLogger(__name__)


class PhysicalL3RouterJointAgentNotifyAPI(
        l3_router_rpc_joint_agent_api.L3RouterJointAgentNotifyAPI):
    """API for plugin to notify Cisco cfg agent."""
    BASE_RPC_API_VERSION = '1.0'

    def _agent_notification(self, context, method, routers, operation, data):
        """Notify individual Cisco cfg agents."""
        admin_context = context.is_admin and context or context.elevated()
        for router in routers:

            agents = self._l3plugin._get_cfg_agents(admin_context, active=True)

            for agent in agents:
                LOG.debug('Notify %(agent_type)s at %(topic)s.%(host)s the '
                          'message %(method)s',
                          {'agent_type': agent.agent_type,
                           'topic': c_constants.CFG_AGENT_L3_ROUTING,
                           'host': agent.host,
                           'method': method})
                self.cast(context,
                          self.make_msg(method, routers=[router['id']]),
                          topic='%s.%s' % (c_constants.CFG_AGENT_L3_ROUTING,
                                           agent.host))
