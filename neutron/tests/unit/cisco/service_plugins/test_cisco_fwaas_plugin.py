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

import contextlib
import mock
import neutron

from neutron.api.v2 import attributes as attr
from neutron import context
from neutron.extensions import firewall
from neutron import manager
from neutron.plugins.cisco.db import cisco_fwaas_db as csrfw_db
from neutron.plugins.cisco.extensions import csrfirewallinsertion
from neutron.plugins.common import constants as const
from neutron.services.firewall.plugins.cisco import cisco_fwaas_plugin
from neutron.tests.unit.cisco.l3 import device_handling_test_support
from neutron.tests.unit.cisco.l3 import test_l3_router_appliance_plugin
from neutron.tests.unit.db.firewall import test_db_firewall
from neutron.tests.unit import test_l3_plugin
from neutron.tests.unit import testlib_plugin
from oslo.config import cfg

CORE_PLUGIN_KLASS = ('neutron.tests.unit.cisco.l3.'
                     'test_l3_router_appliance_plugin.TestNoL3NatPlugin')
L3_PLUGIN_KLASS = (
    "neutron.tests.unit.cisco.l3.test_l3_router_appliance_plugin."
    "TestApplianceL3RouterServicePlugin")
CSR_FW_PLUGIN_KLASS = (
    "neutron.services.firewall.plugins.cisco.cisco_fwaas_plugin."
    "CSRFirewallPlugin"
)
extensions_path = neutron.plugins.__path__[0] + '/cisco/extensions'


class CSR1kvFirewallTestExtensionManager(
    test_l3_router_appliance_plugin.L3RouterApplianceTestExtensionManager):

    def get_resources(self):
        res = super(CSR1kvFirewallTestExtensionManager, self).get_resources()
        firewall.RESOURCE_ATTRIBUTE_MAP['firewalls'].update(
            csrfirewallinsertion.EXTENDED_ATTRIBUTES_2_0['firewalls'])
        return res + firewall.Firewall.get_resources()

    def get_actions(self):
        return []

    def get_request_extensions(self):
        return []


class CSR1kvFirewallTestCaseBase(test_db_firewall.FirewallPluginDbTestCase,
        testlib_plugin.NotificationSetupHelper,
        test_l3_plugin.L3NatTestCaseMixin,
        device_handling_test_support.DeviceHandlingTestSupportMixin):

    def setUp(self, core_plugin=None, l3_plugin=None, fw_plugin=None,
            ext_mgr=None):
        self.agentapi_delf_p = mock.patch(test_db_firewall.DELETEFW_PATH,
            create=True, new=test_db_firewall.FakeAgentApi().delete_firewall)
        self.agentapi_delf_p.start()
        cfg.CONF.set_override('api_extensions_path', extensions_path)
        # for these tests we need to enable overlapping ips
        cfg.CONF.set_default('allow_overlapping_ips', True)
        cfg.CONF.set_default('max_routes', 3)
        self.saved_attr_map = {}
        for resource, attrs in attr.RESOURCE_ATTRIBUTE_MAP.iteritems():
            self.saved_attr_map[resource] = attrs.copy()
        if not core_plugin:
            core_plugin = CORE_PLUGIN_KLASS
        if l3_plugin is None:
            l3_plugin = L3_PLUGIN_KLASS
        if not fw_plugin:
            fw_plugin = CSR_FW_PLUGIN_KLASS
        service_plugins = {'l3_plugin_name': l3_plugin,
            'fw_plugin_name': fw_plugin}
        if not ext_mgr:
            ext_mgr = CSR1kvFirewallTestExtensionManager()
        super(test_db_firewall.FirewallPluginDbTestCase, self).setUp(
            plugin=core_plugin, service_plugins=service_plugins,
            ext_mgr=ext_mgr)

        self.core_plugin = manager.NeutronManager.get_plugin()
        self.l3_plugin = manager.NeutronManager.get_service_plugins().get(
            const.L3_ROUTER_NAT)
        self.plugin = manager.NeutronManager.get_service_plugins().get(
            const.FIREWALL)
        self.callbacks = self.plugin.endpoints[0]

        self.setup_notification_driver()
        test_opts = [
            cfg.StrOpt('auth_protocol', default='http'),
            cfg.StrOpt('auth_host', default='localhost'),
            cfg.IntOpt('auth_port', default=35357),
            cfg.StrOpt('admin_user', default='neutron'),
            cfg.StrOpt('admin_password', default='secrete')]
        cfg.CONF.register_opts(test_opts, 'keystone_authtoken')
        self._mock_l3_admin_tenant()
        self._create_mgmt_nw_for_tests(self.fmt)
        self._mock_svc_vm_create_delete(self.l3_plugin)
        self._mock_io_file_ops()

    def restore_attribute_map(self):
        # Remove the csrfirewallinsertion extension
        firewall.RESOURCE_ATTRIBUTE_MAP['firewalls'].pop('port_id')
        firewall.RESOURCE_ATTRIBUTE_MAP['firewalls'].pop('direction')
        # Restore the original RESOURCE_ATTRIBUTE_MAP
        attr.RESOURCE_ATTRIBUTE_MAP = self.saved_attr_map

    def tearDown(self):
        self._remove_mgmt_nw_for_tests()
        (neutron.tests.unit.cisco.l3.test_l3_router_appliance_plugin.
            TestApplianceL3RouterServicePlugin._mgmt_nw_uuid) = None
        (neutron.tests.unit.cisco.l3.test_l3_router_appliance_plugin.
            TestApplianceL3RouterServicePlugin._refresh_router_backlog) = True
        (neutron.tests.unit.cisco.l3.test_l3_router_appliance_plugin.
            TestApplianceL3RouterServicePlugin._nova_running) = False
        plugin = manager.NeutronManager.get_service_plugins()[
            const.L3_ROUTER_NAT]
        plugin._heartbeat.stop()
        self.restore_attribute_map()
        super(CSR1kvFirewallTestCaseBase, self).tearDown()

    def _create_firewall(self, fmt, name, description, firewall_policy_id,
                         admin_state_up=True, expected_res_status=None,
                         **kwargs):
        tenant_id = kwargs.get('tenant_id', self._tenant_id)
        port_id = kwargs.get('port_id')
        direction = kwargs.get('direction')
        data = {'firewall': {'name': name,
                             'description': description,
                             'firewall_policy_id': firewall_policy_id,
                             'admin_state_up': admin_state_up,
                             'tenant_id': tenant_id}}
        if port_id:
            data['firewall']['port_id'] = port_id
        if direction:
            data['firewall']['direction'] = direction
        firewall_req = self.new_create_request('firewalls', data, fmt)
        firewall_res = firewall_req.get_response(self.ext_api)
        if expected_res_status:
            self.assertEqual(firewall_res.status_int, expected_res_status)
        return firewall_res


class TestCiscoFirewallCallbacks(test_db_firewall.FirewallPluginDbTestCase):

    def setUp(self):
        super(TestCiscoFirewallCallbacks, self).setUp()
        self.plugin = cisco_fwaas_plugin.CSRFirewallPlugin()
        self.callbacks = self.plugin.endpoints[0]

    def test_firewall_deleted(self):
        ctx = context.get_admin_context()
        with self.firewall_policy(do_delete=False) as fwp:
            fwp_id = fwp['firewall_policy']['id']
            with self.firewall(firewall_policy_id=fwp_id,
                               admin_state_up=test_db_firewall.ADMIN_STATE_UP,
                               do_delete=False) as fw:
                fw_id = fw['firewall']['id']
                with ctx.session.begin(subtransactions=True):
                    fw_db = self.plugin._get_firewall(ctx, fw_id)
                    fw_db['status'] = const.PENDING_DELETE
                    ctx.session.flush()
                    res = self.callbacks.firewall_deleted(ctx, fw_id,
                                                          host='dummy')
                    self.assertTrue(res)
                    self.assertRaises(firewall.FirewallNotFound,
                                      self.plugin.get_firewall,
                                      ctx, fw_id)


# We reuse plugin tests from community implementation
class TestFirewallPluginBase(test_db_firewall.TestFirewallDBPlugin):

    def setUp(self):
        super(TestFirewallPluginBase, self).setUp()
        self.agent_rpc_cls_p = mock.patch(
            'neutron.services.firewall.plugins.cisco.'
            'cisco_fwaas_plugin.FirewallAgentApi')
        self.agent_rpc_cls = self.agent_rpc_cls_p.start()
        self.agent_rpc = mock.Mock()
        self.agent_rpc.create_firewall = mock.MagicMock()
        self.agent_rpc.update_firewall = mock.MagicMock()
        self.agent_rpc.delete_firewall = mock.MagicMock()

        self.plugin = cisco_fwaas_plugin.CSRFirewallPlugin()


class TestCiscoFirewallPlugin(CSR1kvFirewallTestCaseBase,
                              csrfw_db.CiscoFirewall_db_mixin):

    def setUp(self):
        super(TestCiscoFirewallPlugin, self).setUp()
        self.fake_vendor_ext = {
            'host_mngt_ip': '1.2.3.4',
            'host_usr_nm': 'admin',
            'host_usr_pw': 'cisco',
            'if_list': {'port': {'id': 0, 'hosting_info': 'csr'},
                        'direction': 'default'}
        }
        self.mock_get_hosting_info = mock.patch.object(
            self.plugin, '_get_hosting_info').start()

    def test_create_csr_firewall(self):
        with self.router(tenant_id=self._tenant_id) as r:
            with self.subnet() as s:
                body = self._router_interface_action('add',
                                                     r['router']['id'],
                                                     s['subnet']['id'],
                                                     None)
                port_id = body['port_id']
                with self.firewall(port_id=body['port_id'],
                        direction='inside') as fw:
                    ctx = context.get_admin_context()
                    fw_id = fw['firewall']['id']
                    csrfw = self.lookup_firewall_csr_association(ctx, fw_id)
                    # cant be in PENDING_XXX state for delete clean up
                    with ctx.session.begin(subtransactions=True):
                        fw_db = self.plugin._get_firewall(ctx, fw_id)
                        fw_db['status'] = const.ACTIVE
                        ctx.session.flush()
                self._router_interface_action('remove',
                                              r['router']['id'],
                                              s['subnet']['id'],
                                              None)
                self.assertEqual(fw['firewall']['name'], 'firewall_1')
                self.assertEqual(csrfw['port_id'], port_id)
                self.assertEqual(csrfw['direction'], 'inside')

    def test_update_csr_firewall(self):

        with contextlib.nested(
            self.router(tenant_id=self._tenant_id),
            self.subnet(),
        ) as (r, s):

            body = self._router_interface_action(
                'add',
                r['router']['id'],
                s['subnet']['id'],
                None)
            port_id = body['port_id']

            self.fake_vendor_ext['if_list']['port']['id'] = port_id
            self.fake_vendor_ext['if_list']['direction'] = 'inside'
            self.mock_get_hosting_info.return_value = self.fake_vendor_ext

            with self.firewall(port_id=body['port_id'],
                 direction='both') as fw:
                ctx = context.get_admin_context()
                fw_id = fw['firewall']['id']
                csrfw = self.lookup_firewall_csr_association(
                    ctx, fw_id)
                status_data = {'acl_id': 100}

                res = self.callbacks.set_firewall_status(ctx, fw_id,
                    const.ACTIVE, status_data)

                # update direction on same port
                data = {'firewall': {'name': 'firewall_2',
                    'direction': 'both', 'port_id': port_id}}
                req = self.new_update_request('firewalls', data,
                    fw['firewall']['id'])
                req.environ['neutron.context'] = context.Context(
                    '', 'test-tenant')
                res = self.deserialize(self.fmt,
                req.get_response(self.ext_api))

                csrfw = self.lookup_firewall_csr_association(ctx,
                    fw['firewall']['id'])

                self.assertEqual('firewall_2', res['firewall']['name'])
                self.assertEqual(port_id, csrfw['port_id'])
                self.assertEqual('both', csrfw['direction'])

                # cant be in PENDING_XXX state for delete clean up
                with ctx.session.begin(subtransactions=True):
                    fw_db = self.plugin._get_firewall(ctx, fw_id)
                    fw_db['status'] = const.ACTIVE
                    ctx.session.flush()
            self._router_interface_action(
                'remove',
                r['router']['id'],
                s['subnet']['id'],
                None)

    def __test_update_csr_firewall(self):
        with self.router(tenant_id=self._tenant_id) as r:
            with self.subnet() as s:
                body = self._router_interface_action('add',
                                                     r['router']['id'],
                                                     s['subnet']['id'],
                                                     None)
                port_id = body['port_id']
                with self.firewall(port_id=body['port_id'],
                        direction='inside') as fw:
                    ctx = context.get_admin_context()
                    fw_id = fw['firewall']['id']
                    status_data = {'acl_id': 100}
                    res = self.callbacks.set_firewall_status(ctx, fw_id,
                        const.ACTIVE, status_data)
                    data = {'firewall': {'name': 'firewall_2',
                        'direction': 'both', 'port_id': port_id}}
                    req = self.new_update_request('firewalls', data,
                        fw['firewall']['id'])
                    res = self.deserialize(self.fmt,
                        req.get_response(self.ext_api))
                    csrfw = self.lookup_firewall_csr_association(ctx,
                        fw['firewall']['id'])
                    self.assertEqual(res['firewall']['name'], 'firewall_2')
                    self.assertEqual(csrfw['port_id'], port_id)
                    self.assertEqual(csrfw['direction'], 'both')
                    # cant be in PENDING_XXX state for delete clean up
                    with ctx.session.begin(subtransactions=True):
                        fw_db = self.plugin._get_firewall(ctx, fw_id)
                        fw_db['status'] = const.ACTIVE
                        ctx.session.flush()
                self._router_interface_action('remove',
                                              r['router']['id'],
                                              s['subnet']['id'],
                                              None)

    def test_delete_csr_firewall(self):
        with self.router(tenant_id=self._tenant_id) as r:
            with self.subnet() as s:
                body = self._router_interface_action('add',
                                                     r['router']['id'],
                                                     s['subnet']['id'],
                                                     None)
                with self.firewall(port_id=body['port_id'],
                        direction='inside', do_delete=False) as fw:
                    fw_id = fw['firewall']['id']
                    ctx = context.get_admin_context()
                    csrfw = self.lookup_firewall_csr_association(ctx,
                        fw_id)
                    self.assertNotEqual(csrfw, None)
                    req = self.new_delete_request('firewalls', fw_id)
                    req.get_response(self.ext_api)
                    with ctx.session.begin(subtransactions=True):
                        fw_db = self.plugin._get_firewall(ctx, fw_id)
                        fw_db['status'] = const.PENDING_DELETE
                        ctx.session.flush()
                    self.callbacks.firewall_deleted(ctx, fw_id)
                    csrfw = self.lookup_firewall_csr_association(ctx,
                        fw_id)
                    self.assertEqual(csrfw, None)
                self._router_interface_action('remove',
                                              r['router']['id'],
                                              s['subnet']['id'],
                                              None)
