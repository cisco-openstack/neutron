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

from neutron.openstack.common import excutils
from neutron.openstack.common import importutils
from neutron.openstack.common import log as logging
from neutron.plugins.cisco.cfg_agent import cfg_exceptions

from neutron.plugins.cisco.cfg_agent.device_drivers import driver_mgr

LOG = logging.getLogger(__name__)


class PhysicalDeviceDriverManager(driver_mgr.DeviceDriverManager):

    def __init__(self, asr_ent):
        self._drivers = {}
        self._global_driver = None
        self._asr_ent = asr_ent

    def get_driver(self, resource_id):
        try:
            return self._global_driver
        except KeyError:
            with excutils.save_and_reraise_exception(reraise=False):
                raise cfg_exceptions.DriverNotFound(id=resource_id)

    def set_driver(self, resource):
        """Set the driver for a neutron resource.

        :param resource: Neutron resource in dict format. Expected keys:
                        { 'id': <value>
                          'hosting_device': { 'id': <value>, }
                          'router_type': {'cfg_agent_driver': <value>,  }
                        }
        :return driver : driver object
        """
        try:
            if self._global_driver is not None:
                return self._global_driver
            else:
                driver_class = "neutron.plugins.cisco.cfg_agent.device_drivers." \
                               "asr1k.asr1k_routing_driver.ASR1kRoutingDriver"
                driver = importutils.import_object(driver_class,
                                                   self._asr_ent)
                self._global_driver = driver

            return driver
        except ImportError:
            LOG.exception(_("Error loading cfg agent driver."))
            with excutils.save_and_reraise_exception(reraise=False):
                raise cfg_exceptions.DriverNotExist(driver=driver_class)
        except KeyError as e:
            with excutils.save_and_reraise_exception(reraise=False):
                raise cfg_exceptions.DriverNotSetForMissingParameter(e)
