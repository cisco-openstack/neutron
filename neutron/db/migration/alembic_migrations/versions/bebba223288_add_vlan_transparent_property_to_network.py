# Copyright 2015 OpenStack Foundation
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

"""Add vlan transparent property to network

Revision ID: bebba223288
Revises: juno
Create Date: 2015-02-04 18:07:29.670554

"""

# revision identifiers, used by Alembic.
revision = 'bebba223288'
down_revision = 'juno'

from alembic import op
import sqlalchemy as sa


def upgrade():
    op.add_column('networks', sa.Column('vlan_transparent', sa.Boolean(),
                  nullable=True))


def downgrade():
    op.drop_column('networks', 'vlan_transparent')
