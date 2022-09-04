import json
import logging
import random
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    Dict,
    List,
    Literal,
    Optional,
    Sequence,
    Tuple,
    Union,
    overload,
)
from urllib.parse import urlparse

import requests
from ens import ENS
from ens.abis import ENS as ENS_ABI, RESOLVER as ENS_RESOLVER_ABI
from ens.exceptions import InvalidName
from ens.main import ENS_MAINNET_ADDR
from ens.utils import is_none_or_zero_address, normal_name_to_hash, normalize_name
from eth_abi.exceptions import InsufficientDataBytes
from eth_typing import BlockNumber, HexStr
from web3 import HTTPProvider, Web3
from web3._utils.abi import get_abi_output_types
from web3._utils.contracts import find_matching_event_abi
from web3._utils.filters import construct_event_filter_params
from web3.datastructures import MutableAttributeDict
from web3.exceptions import (
    BadFunctionCallOutput,
    BadResponseFormat,
    BlockNotFound,
    TransactionNotFound,
)
from web3.types import BlockIdentifier, FilterParams

from rotkehlchen.chain.constants import DEFAULT_EVM_RPC_TIMEOUT
from rotkehlchen.chain.ethereum.constants import ETHERSCAN_NODE
from rotkehlchen.chain.ethereum.contracts import EthereumContract
from rotkehlchen.chain.ethereum.graph import Graph
from rotkehlchen.chain.ethereum.manager import EthereumManager, _is_synchronized
from rotkehlchen.chain.ethereum.modules.eth2.constants import ETH2_DEPOSIT
from rotkehlchen.chain.ethereum.types import (
    ETHERSCAN_NODE_NAME,
    NodeName,
    WeightedNode,
    string_to_evm_address,
)
from rotkehlchen.chain.ethereum.utils import ENS_RESOLVER_ABI_MULTICHAIN_ADDRESS, multicall_2
from rotkehlchen.constants import ONE
from rotkehlchen.constants.ethereum import (
    ENS_REVERSE_RECORDS,
    ERC20TOKEN_ABI,
    ETH_SCAN,
    UNIV1_LP_ABI,
)
from rotkehlchen.errors.misc import (
    BlockchainQueryError,
    InputError,
    RemoteError,
    UnableToDecryptRemoteData,
)
from rotkehlchen.errors.serialization import DeserializationError
from rotkehlchen.externalapis.etherscan import Etherscan
from rotkehlchen.fval import FVal
from rotkehlchen.greenlets import GreenletManager
from rotkehlchen.logging import RotkehlchenLogsAdapter
from rotkehlchen.serialization.deserialize import (
    deserialize_ethereum_address,
    deserialize_ethereum_transaction,
    deserialize_int_from_hex,
)
from rotkehlchen.serialization.serialize import process_result
from rotkehlchen.types import (
    ChecksumEvmAddress,
    EthereumTransaction,
    EVMTxHash,
    SupportedBlockchain,
    Timestamp,
)
from rotkehlchen.user_messages import MessagesAggregator
from rotkehlchen.utils.misc import from_wei, get_chunks, hex_or_bytes_to_str
from rotkehlchen.utils.network import request_get_dict

if TYPE_CHECKING:
    from rotkehlchen.db.dbhandler import DBHandler

logger = logging.getLogger(__name__)
log = RotkehlchenLogsAdapter(logger)


# from rotkehlchen.externalapis.covalent import Covalent

# TODO: Accept Covalent appart from RPC nodes and Polygonscan

# XXX: Parece que se están mezclando los nodos de eth con los de polygon:
# Error at querying blockchain balances: Failed to query 
# <bound method EthereumManager._call_contract of <rotkehlchen.chain.polygon.manager.PolygonManager object at 0x7f5fd19a3430>> 
# after trying the following nodes: 
# ["WeightedNode(node_info=NodeName(name='mycrypto', endpoint='https://api.mycryptoapi.com/eth', owned=False), active=True, weight=FVal(0.15), identifier=2)",
# "WeightedNode(node_info=NodeName(name='ark-eth', endpoint='https://eth.public-rpc.com', owned=False), active=True, weight=FVal(0.3), identifier=3)"].
# Check logs for details.

class PolygonManager(EthereumManager):
    def __init__(
            self,
            etherscan: Etherscan,
            msg_aggregator: MessagesAggregator,
            greenlet_manager: GreenletManager,
            connect_at_start: Sequence[WeightedNode],
            database: 'DBHandler',
            # covalent: None,  # XXX: temp
            eth_rpc_timeout: int = DEFAULT_EVM_RPC_TIMEOUT,
    ) -> None:
        log.debug(f'Initializing Polygon Manager. Nodes to connect {connect_at_start}')
        self.greenlet_manager = greenlet_manager
        self.web3_mapping: Dict[NodeName, Web3] = {}
        self.etherscan = etherscan
        self.msg_aggregator = msg_aggregator
        self.eth_rpc_timeout = eth_rpc_timeout
        self.archive_connection = False
        self.queried_archive_connection = False
        self.connect_to_multiple_nodes(connect_at_start)
        # TODO: Use subraph for polygon?
        self.blocks_subgraph = Graph(
            'https://api.thegraph.com/subgraphs/name/blocklytics/ethereum-blocks',
        )
        # A cache for the erc20 contract info to not requery same one
        self.contract_info_cache: Dict[ChecksumEvmAddress, Dict[str, Any]] = {}
        self.database = database
        # self.covalent = covalent

    def connect_to_multiple_nodes(self, nodes: Sequence[WeightedNode]) -> None:
        self.web3_mapping = {}
        for weighted_node in nodes:
            if weighted_node.node_info.name == ETHERSCAN_NODE_NAME:
                continue

            task_name = f'Attempt connection to {str(weighted_node.node_info.name)} polygon node'
            self.greenlet_manager.spawn_and_track(
                after_seconds=None,
                task_name=task_name,
                exception_is_error=True,
                method=self.attempt_connect,
                node=weighted_node.node_info,
                mainnet_check=True,
            )

    def attempt_connect(
            self,
            node: NodeName,
            mainnet_check: bool = True,
    ) -> Tuple[bool, str]:
        """Attempt to connect to a particular node type

        For our own node if the given rpc endpoint is not the same as the saved one
        the connection is re-attempted to the new one
        """
        message = ''
        node_connected = self.web3_mapping.get(node, None) is not None
        if node_connected:
            return True, f'Already connected to {node} polygon node'

        try:
            ethrpc_endpoint = node.endpoint
            parsed_eth_rpc_endpoint = urlparse(node.endpoint)
            if not parsed_eth_rpc_endpoint.scheme:
                ethrpc_endpoint = f'http://{node.endpoint}'
            provider = HTTPProvider(
                endpoint_uri=node.endpoint,
                request_kwargs={'timeout': self.eth_rpc_timeout},
            )
            ens = ENS(provider)
            web3 = Web3(provider, ens=ens)
        except requests.exceptions.RequestException:
            message = f'Failed to connect to polygon node {node} at endpoint {ethrpc_endpoint}'
            log.warning(message)
            return False, message

        try:
            is_connected = web3.isConnected()
        except AssertionError:
            # Terrible, terrible hack but needed due to https://github.com/rotki/rotki/issues/1817
            is_connected = False

        if is_connected:
            # Also make sure we are actually connected to the Polygon mainnet
            synchronized = True
            msg = ''
            try:
                if mainnet_check:
                    network_id = int(web3.net.version)

                    if network_id != 137:
                        message = (
                            f'Connected to polygon node {node} at endpoint {ethrpc_endpoint} but '
                            f'it is not on the polygon mainnet. The chain id '
                            f'the node is in is {network_id}.'
                        )
                        log.warning(message)
                        return False, message

                    try:
                        current_block = web3.eth.block_number  # pylint: disable=no-member
                        latest_block = self.query_eth_highest_block()
                    except (requests.exceptions.RequestException, RemoteError) as e:
                        msg = f'Could not query latest block due to {str(e)}'
                        log.warning(msg)
                        synchronized = False
                    else:
                        synchronized, msg = _is_synchronized(current_block, latest_block)
            except ValueError as e:
                message = (
                    f'Failed to connect to polygon node {node} at endpoint '
                    f'{ethrpc_endpoint} due to {str(e)}'
                )
                return False, message

            if not synchronized:
                self.msg_aggregator.add_warning(
                    f'We could not verify that polygon node {node} is '
                    'synchronized with the polygon mainnet. Balances and other queries '
                    'may be incorrect.',
                )

            log.info(f'Connected polygon node {node} at {ethrpc_endpoint}')
            self.web3_mapping[node] = web3
            return True, ''

        # else
        message = f'Failed to connect to polygon node {node} at endpoint {ethrpc_endpoint}'
        log.warning(message)
        return False, message