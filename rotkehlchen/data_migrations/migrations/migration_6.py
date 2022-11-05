import json
from pathlib import Path
from typing import TYPE_CHECKING

from rotkehlchen.fval import FVal
from rotkehlchen.types import SupportedBlockchain

if TYPE_CHECKING:
    from rotkehlchen.db.drivers.gevent import DBCursor
    from rotkehlchen.rotkehlchen import Rotkehlchen


def read_and_write_polygon_nodes_in_database(write_cursor: 'DBCursor') -> None:
    dir_path = Path(__file__).resolve().parent.parent.parent
    with open(dir_path / 'data' / 'nodes.json', 'r') as f:
        nodes_info = json.loads(f.read())
        for node in nodes_info:
            if node['blockchain'] == 'MATIC':
                write_cursor.execute(
                    'INSERT OR IGNORE INTO web3_nodes(name, endpoint, owned, active, weight, blockchain) VALUES (?, ?, ?, ?, ?, ?);',  # noqa: E501
                    (
                        node['name'],
                        node['endpoint'],
                        node['owned'],
                        node['active'],
                        str(FVal(node['weight'])),
                        node['blockchain'],
                    ),
                )


def data_migration_6(write_cursor: 'DBCursor', rotki: 'Rotkehlchen') -> None:
    """
    - Add polygon nodes to connect to the database in 1.27
    """
    read_and_write_polygon_nodes_in_database(write_cursor=write_cursor)
    # Connect to the nodes since the migration happens after the ethereum manager initialization
    nodes_to_connect = rotki.data.db.get_web3_nodes(blockchain=SupportedBlockchain.POLYGON, only_active=True)  # noqa: E501
    rotki.chains_aggregator.polygon.connect_to_multiple_nodes(nodes_to_connect)
