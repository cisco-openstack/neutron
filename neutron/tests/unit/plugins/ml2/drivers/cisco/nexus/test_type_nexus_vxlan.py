# Copyright (c) 2014 OpenStack Foundation
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

import neutron.db.api as db
from neutron.plugins.common import constants as p_const
from neutron.plugins.ml2 import driver_api as api
from neutron.plugins.ml2.drivers.cisco.nexus import type_nexus_vxlan
from neutron.tests.unit import testlib_api

VNI_RANGES = [(100, 102), (200, 202)]
MCAST_GROUP_RANGES = ['224.0.0.1:224.0.0.2', '224.0.1.1:224.0.1.2']


class NexusVxlanTypeTest(testlib_api.SqlTestCase):

    def setUp(self):
        super(NexusVxlanTypeTest, self).setUp()
        self.driver = type_nexus_vxlan.NexusVxlanTypeDriver()
        self.driver.conf_mcast_ranges = MCAST_GROUP_RANGES
        self.driver.tunnel_ranges = VNI_RANGES
        self.driver.sync_allocations()
        self.session = db.get_session()

    def test_allocate_tenant_segment(self):
        segment = self.driver.allocate_tenant_segment(self.session)
        self.assertEqual(segment[api.NETWORK_TYPE], p_const.TYPE_NEXUS_VXLAN)
        self.assertEqual(segment[api.PHYSICAL_NETWORK], '224.0.0.1')
        self.assertEqual(segment[api.SEGMENTATION_ID], 100)

    def test_allocate_shared_mcast_group(self):
        segments = []
        for i in range(0, 6):
            segments.append(self.driver.allocate_tenant_segment(self.session))
        self.assertEqual(segments[0][api.NETWORK_TYPE],
                         p_const.TYPE_NEXUS_VXLAN)
        self.assertEqual(segments[0][api.PHYSICAL_NETWORK], '224.0.0.1')
        self.assertEqual(segments[0][api.SEGMENTATION_ID], 100)
        self.assertEqual(segments[-1][api.NETWORK_TYPE],
                         p_const.TYPE_NEXUS_VXLAN)
        self.assertEqual(segments[-1][api.PHYSICAL_NETWORK], '224.0.0.1')
        self.assertEqual(segments[-1][api.SEGMENTATION_ID], 202)

    def test_reserve_provider_segment_full_specs(self):
        segment = {api.NETWORK_TYPE: p_const.TYPE_NEXUS_VXLAN,
                   api.PHYSICAL_NETWORK: '224.0.0.1',
                   api.SEGMENTATION_ID: '5000'}
        result = self.driver.reserve_provider_segment(self.session, segment)
        alloc = self.driver.get_allocation(self.session,
                                           result[api.SEGMENTATION_ID])
        mcast_group = self.driver._get_mcast_group_for_vni(self.session,
                                                           alloc.vxlan_vni)
        self.assertTrue(alloc.allocated)
        self.assertEqual(alloc.vxlan_vni, 5000)
        self.assertEqual(mcast_group, '224.0.0.1')

    def test_reserve_provider_segment_partial_specs(self):
        segment = {api.NETWORK_TYPE: p_const.TYPE_NEXUS_VXLAN,
                   api.PHYSICAL_NETWORK: '224.0.0.1'}

        result = self.driver.reserve_provider_segment(self.session, segment)
        alloc = self.driver.get_allocation(self.session,
                                           result[api.SEGMENTATION_ID])
        mcast_group = self.driver._get_mcast_group_for_vni(self.session,
                                                           alloc.vxlan_vni)
        self.assertTrue(alloc.allocated)
        self.assertEqual(alloc.vxlan_vni, 100)
        self.assertEqual(mcast_group, '224.0.0.1')
