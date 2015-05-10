# Copyright (c) 2014 Cisco Systems
# All Rights Reserved.
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

import mock

from neutron import context
from neutron.plugins.ml2.drivers.cisco.nexus import config as cisco_config
from neutron.plugins.ml2.drivers.cisco.nexus import exceptions as cexc
from neutron.plugins.ml2.drivers.cisco.nexus import nexus_network_driver
from neutron.services.l3_router import l3_cisco_nexus
from neutron.tests import base
from neutron.tests.unit import test_db_plugin


ROUTER = 'router1'
SUBNET = 'subnet1'
NETWORK = 'network1'
NETWORK_NAME = 'one_network'
SUBNET_GATEWAY = '10.3.2.1'
SUBNET_CIDR = '10.3.1.0/24'
VLAN = 100


class TestCiscoNexusL3Plugin(test_db_plugin.NeutronDbPluginV2TestCase,
                             base.BaseTestCase):

    def setUp(self):
        super(TestCiscoNexusL3Plugin, self).setUp()
        self.context = context.get_admin_context()

        self.interface_info = {'subnet_id': SUBNET,
                               'network_id': NETWORK,
                               'name': NETWORK_NAME,
                               'gateway_ip': SUBNET_GATEWAY,
                               'cidr': SUBNET_CIDR}

        # Mock the nexus switch dictionary and initialization method.
        # Don't need all switch values, just IP addresses for these tests.
        mock.patch.object(cisco_config.ML2MechCiscoConfig,
                          '__init__',
                          return_value=None).start()

        self.nexus_config = {('1.1.1.1', 'username'): 'admin',
                             ('2.2.2.2', 'username'): 'admin'}
        self.nexus_patch = mock.patch.dict(
            cisco_config.ML2MechCiscoConfig.nexus_dict,
            self.nexus_config)
        self.nexus_patch.start()
        self.addCleanup(self.nexus_patch.stop)

        # Mock nexus switch driver method called right before netconf calls.
        self.mock_edit_config = mock.Mock()
        mock.patch.object(nexus_network_driver.CiscoNexusDriver,
                          '_edit_config',
                          return_value=self.mock_edit_config).start()

        self.plugin = l3_cisco_nexus.CiscoNexusL3ServicePlugin()
        self.plugin.get_subnet = mock.Mock(return_value=self.interface_info)
        self.plugin._get_vlanid = mock.Mock(return_value=VLAN)

        mock.patch('neutron.db.l3_gwmode_db.L3_NAT_db_mixin.'
                   'add_router_interface').start()
        mock.patch('neutron.db.l3_gwmode_db.L3_NAT_db_mixin.'
                   'remove_router_interface').start()
        mock.patch('neutron.openstack.common.excutils.'
                   'save_and_reraise_exception').start()

    def _check_xml_keywords(self, expected_words, xml_words):
        if all(word in xml_words for word in expected_words):
            return True

    def test_add_router_interface(self):
        """Test add router interface call."""

        # Test verifies that calls made from the add router method to the
        # nexus driver are correct. Note that if database failures occur
        # then these tests would also fail since these XML results would only
        # happen if all the database transactions succeed.
        driver = self.plugin.driver

        self.plugin.add_router_interface(self.context, ROUTER,
                                         self.interface_info)

        self.assertTrue(self._check_xml_keywords(['name', 'q-100'],
            driver._edit_config.mock_calls[0][2]['config']))
        self.assertTrue(self._check_xml_keywords(['state', 'active'],
            driver._edit_config.mock_calls[1][2]['config']))
        self.assertTrue(self._check_xml_keywords(['no', 'shutdown'],
            driver._edit_config.mock_calls[2][2]['config']))
        self.assertTrue(self._check_xml_keywords(['interface', 'vlan'],
            driver._edit_config.mock_calls[3][2]['config']))

        self.plugin.remove_router_interface(self.context, ROUTER,
                                            self.interface_info)

    def test_remove_router_interface(self):
        """Test remove router interface call."""

        # Test verifies that calls made from the remove router method to the
        # nexus driver are correct. Note that if database failures occur
        # then these tests would also fail since these XML results would only
        # happen if all the database transactions succeed.
        driver = self.plugin.driver

        self.plugin.add_router_interface(self.context, ROUTER,
                                         self.interface_info)

        self.plugin.remove_router_interface(self.context, ROUTER,
                                            self.interface_info)

        self.assertTrue(self._check_xml_keywords(['no', 'interface'],
            driver._edit_config.mock_calls[4][2]['config']))
        self.assertTrue(self._check_xml_keywords(['no', 'vlan'],
            driver._edit_config.mock_calls[5][2]['config']))

    def test_add_router_interface_excep_noportid(self):
        self.interface_info['port_id'] = 'Invalid'
        self.assertRaises(cexc.PortIdForNexusSvi,
                          self.plugin.add_router_interface,
                          self.context, ROUTER, self.interface_info)

    def test_add_router_interface_excep_nosubnet(self):
        del self.interface_info['subnet_id']
        self.assertRaises(cexc.SubnetNotSpecified,
                          self.plugin.add_router_interface,
                          self.context, ROUTER, self.interface_info)

    def test_add_router_interface_excep_subnetpresent(self):
        self.plugin.add_router_interface(self.context, ROUTER,
                                         self.interface_info)

        self.assertRaises(cexc.SubnetInterfacePresent,
                          self.plugin.add_router_interface,
                          self.context, ROUTER, self.interface_info)

        self.plugin.remove_router_interface(self.context, ROUTER,
                                            self.interface_info)

    def test_add_router_interface_excep(self):
        # Verify that the database entries are removed on a failure on
        # adding the configuration to the switch.
        with mock.patch('neutron.services.l3_router.'
                        'l3_cisco_nexus.CiscoNexusL3ServicePlugin.'
                        '_add_router_db'):
            with mock.patch('neutron.services.l3_router.'
                        'l3_cisco_nexus.CiscoNexusL3ServicePlugin.'
                        '_remove_router_db') as remove_router_db:
                with mock.patch('neutron.services.l3_router.l3_cisco_nexus.'
                        'CiscoNexusL3ServicePlugin._add_nexus_svi_interface',
                        side_effect=KeyError()):
                    self.plugin.add_router_interface(self.context, ROUTER,
                                             self.interface_info)
                    remove_router_db.assert_called_once_with(self.context,
                                ROUTER, self.interface_info, mock.ANY, VLAN)

    def test_remove_router_interface_excep(self):
        # Verify that the database entries are added back in on a failure
        # on removing the configuration from the switch.
        with mock.patch('neutron.plugins.ml2.drivers.cisco.nexus.nexus_db_v2.'
                        'get_nexusvm_bindings'):
            with mock.patch('neutron.services.l3_router.'
                            'l3_cisco_nexus.CiscoNexusL3ServicePlugin.'
                            '_remove_router_db'):
                with mock.patch('neutron.services.l3_router.'
                                'l3_cisco_nexus.CiscoNexusL3ServicePlugin.'
                                '_add_router_db') as add_router_db:
                    with mock.patch('neutron.services.l3_router.'
                        'l3_cisco_nexus.CiscoNexusL3ServicePlugin.'
                        '_remove_nexus_svi_interface', side_effect=KeyError()):
                        self.plugin.remove_router_interface(self.context,
                                                ROUTER, self.interface_info)
                        add_router_db.assert_called_once_with(self.context,
                                                ROUTER, self.interface_info,
                                                mock.ANY, VLAN, mock.ANY)
