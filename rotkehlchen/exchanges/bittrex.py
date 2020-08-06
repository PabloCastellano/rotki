import hashlib
import hmac
import json
import logging
from http import HTTPStatus
from json.decoder import JSONDecodeError
from typing import TYPE_CHECKING, Any, Dict, List, Optional, Tuple, Union
from urllib.parse import urlencode

import gevent
import requests
from typing_extensions import Literal

from rotkehlchen.assets.asset import Asset
from rotkehlchen.assets.converters import asset_from_bittrex
from rotkehlchen.constants.misc import ZERO
from rotkehlchen.errors import (
    DeserializationError,
    RemoteError,
    UnknownAsset,
    UnprocessableTradePair,
    UnsupportedAsset,
)
from rotkehlchen.exchanges.data_structures import (
    AssetMovement,
    Trade,
    get_pair_position_asset,
    trade_pair_from_assets,
)
from rotkehlchen.exchanges.exchange import ExchangeInterface
from rotkehlchen.fval import FVal
from rotkehlchen.inquirer import Inquirer
from rotkehlchen.logging import RotkehlchenLogsAdapter
from rotkehlchen.serialization.deserialize import (
    deserialize_asset_amount,
    deserialize_fee,
    deserialize_price,
    deserialize_timestamp_from_date,
    deserialize_trade_type,
    get_pair_position_str,
    pair_get_assets,
)
from rotkehlchen.typing import (
    ApiKey,
    ApiSecret,
    AssetMovementCategory,
    Fee,
    Location,
    Timestamp,
    TradePair,
)
from rotkehlchen.user_messages import MessagesAggregator
from rotkehlchen.utils.interfaces import cache_response_timewise, protect_with_lock
from rotkehlchen.utils.misc import timestamp_to_iso8601, ts_now_in_ms
from rotkehlchen.utils.serialization import rlk_jsonloads_list

if TYPE_CHECKING:
    from rotkehlchen.db.dbhandler import DBHandler


logger = logging.getLogger(__name__)
log = RotkehlchenLogsAdapter(logger)

BITTREX_V3_PUBLIC_ENDPOINTS = ('currencies',)


def bittrex_pair_to_world(given_pair: str) -> TradePair:
    """
    Turns a pair written in the bittrex way to Rotkehlchen way

    Throws:
        - UnsupportedAsset due to asset_from_bittrex()
        - UnprocessableTradePair if the pair can't be split into its parts
    """
    if not isinstance(given_pair, str):
        raise DeserializationError(
            f'Could not deserialize bittrex trade pair. Expected a string '
            f'but found {type(given_pair)}',
        )
    pair = TradePair(given_pair.replace('-', '_'))
    base_currency = asset_from_bittrex(get_pair_position_str(pair, 'first'))
    quote_currency = asset_from_bittrex(get_pair_position_str(pair, 'second'))

    # Since in Bittrex the base currency is the cost currency, iow in Bittrex
    # for BTC_ETH we buy ETH with BTC and sell ETH for BTC, we need to turn it
    # into the Rotkehlchen way which is following the base/quote approach.
    pair = trade_pair_from_assets(quote_currency, base_currency)
    return pair


def world_pair_to_bittrex(pair: TradePair) -> str:
    """Turns a rotkehlchen pair to a bittrex pair"""
    base_asset, quote_asset = pair_get_assets(pair)

    base_asset_str = base_asset.to_bittrex()
    quote_asset_str = quote_asset.to_bittrex()

    # In bittrex the pairs are inverted and use '-'
    return f'{quote_asset_str}-{base_asset_str}'


def trade_from_bittrex(bittrex_trade: Dict[str, Any]) -> Trade:
    """Turn a bittrex trade returned from bittrex trade history to our common trade
    history format

    As we saw in https://github.com/rotki/rotki/issues/1281 it's quite possible
    that some keys don't exist in a trade. The required fields are here:
    https://bittrex.github.io/api/v3#definition-Order

    Throws:
        - UnknownAsset/UnsupportedAsset due to bittrex_pair_to_world()
        - DeserializationError due to unexpected format of dict entries
        - KeyError due to dict entries missing an expected entry
    """
    amount = deserialize_asset_amount(bittrex_trade['fillQuantity'])
    timestamp = deserialize_timestamp_from_date(
        date=bittrex_trade.get('closedAt', 'createdAt'),
        formatstr='iso8601',
        location='bittrex',
    )
    if 'limit' in bittrex_trade:
        rate = deserialize_price(bittrex_trade['limit'])
    else:
        rate = bittrex_trade['proceeds'] / bittrex_trade['fillQuantity']
    order_type = deserialize_trade_type(bittrex_trade['direction'])
    fee = deserialize_fee(bittrex_trade['commission'])
    pair = bittrex_pair_to_world(bittrex_trade['marketSymbol'])
    quote_currency = get_pair_position_asset(pair, 'second')

    log.debug(
        'Processing bittrex Trade',
        sensitive_log=True,
        amount=amount,
        rate=rate,
        order_type=order_type,
        fee=fee,
        bittrex_pair=bittrex_trade['marketSymbol'],
        pair=pair,
    )

    return Trade(
        timestamp=timestamp,
        location=Location.BITTREX,
        pair=pair,
        trade_type=order_type,
        amount=amount,
        rate=rate,
        fee=fee,
        fee_currency=quote_currency,
        link=str(bittrex_trade['id']),
    )


class Bittrex(ExchangeInterface):
    def __init__(
            self,
            api_key: ApiKey,
            secret: ApiSecret,
            database: 'DBHandler',
            msg_aggregator: MessagesAggregator,
            initial_backoff: int = 4,
            backoff_limit: int = 180,
    ):
        super(Bittrex, self).__init__('bittrex', api_key, secret, database)
        self.uri = 'https://api.bittrex.com/v3/'
        self.msg_aggregator = msg_aggregator
        self.session.headers.update({
            'Api-Key': self.api_key,
            'Content-Type': 'Application/JSON',
        })
        self.initial_backoff = initial_backoff
        self.backoff_limit = backoff_limit

    def first_connection(self) -> None:
        self.first_connection_made = True

    def validate_api_key(self) -> Tuple[bool, str]:
        try:
            self.api_query('balances')
        except RemoteError as e:
            error = str(e)
            if 'APIKEY_INVALID' in error:
                return False, 'Provided API Key is invalid'
            elif 'INVALID_SIGNATURE' in error:
                return False, 'Provided API Secret is invalid'
            else:
                raise
        return True, ''

    def api_query(  # noqa: F811
            self,
            endpoint: str,
            method: Literal['get', 'put', 'delete'] = 'get',
            options: Optional[Dict[str, Any]] = None,
    ) -> List[Dict[str, Any]]:
        """
        Queries Bittrex api v3 for given endpoint, method and options
        """
        given_options = options.copy() if options else {}
        backoff = self.initial_backoff

        request_url = self.uri + endpoint
        if given_options:
            # iso8601 dates need special handling in bittrex since they can't parse them urlencoded
            # https://github.com/Bittrex/bittrex.github.io/issues/72#issuecomment-498335240
            start_date = given_options.pop('startDate', None)
            end_date = given_options.pop('endDate', None)
            request_url += '?' + urlencode(given_options)
            if start_date is not None:
                request_url += f'&startDate={start_date}'
            if end_date is not None:
                request_url += f'&endDate={end_date}'

        while True:
            response = self._single_api_query(
                request_url=request_url,
                options=given_options,
                method=method,
                public_endpoint=endpoint in BITTREX_V3_PUBLIC_ENDPOINTS,
            )
            should_backoff = (
                response.status_code == HTTPStatus.TOO_MANY_REQUESTS and
                backoff < self.backoff_limit
            )
            if should_backoff:
                log.debug('Got 429 from Bittrex. Backing off', seconds=backoff)
                gevent.sleep(backoff)
                backoff = backoff * 2
                continue

            # else we got a result
            break

        if response.status_code != HTTPStatus.OK:
            raise RemoteError(
                f'Bittrex query responded with error status code: {response.status_code}'
                f' and text: {response.text}',
            )

        try:
            result = rlk_jsonloads_list(response.text)
        except JSONDecodeError:
            raise RemoteError(f'Bittrex returned invalid JSON response: {response.text}')

        return result

    def _single_api_query(
            self,
            request_url: str,
            options: Dict[str, Any],
            method: Literal['get', 'put', 'delete'],
            public_endpoint: bool = False,
    ) -> requests.Response:
        payload = '' if method == 'get' else json.dumps(options)
        if not public_endpoint:
            api_content_hash = hashlib.sha512(payload.encode()).hexdigest()
            api_timestamp = str(ts_now_in_ms())
            presign_str = api_timestamp + request_url + method.upper() + api_content_hash
            signature = hmac.new(
                self.secret,
                presign_str.encode(),
                hashlib.sha512,
            ).hexdigest()
            self.session.headers.update({
                'Api-Key': self.api_key,
                'Api-Timestamp': api_timestamp,
                'Api-Content-Hash': api_content_hash,
                'Api-Signature': signature,
            })
        else:
            self.session.headers.pop('Api-Key')

        log.debug('Bittrex v3 API query', request_url=request_url)
        try:
            response = self.session.request(
                method=method,
                url=request_url,
                json=options if method != 'get' else None,
            )
        except requests.exceptions.ConnectionError as e:
            raise RemoteError(f'Bittrex API request failed due to {str(e)}')

        return response

    def get_currencies(self) -> List[Dict[str, Any]]:
        """Gets a list of all currencies supported by Bittrex"""
        result = self.api_query('currencies')
        return result

    @protect_with_lock()
    @cache_response_timewise()
    def query_balances(self) -> Tuple[Optional[Dict[Asset, Dict[str, Any]]], str]:
        try:
            resp = self.api_query('balances')
        except RemoteError as e:
            msg = (
                'Bittrex API request failed. Could not reach bittrex due '
                'to {}'.format(e)
            )
            log.error(msg)
            return None, msg

        returned_balances = {}
        for entry in resp:
            try:
                asset = asset_from_bittrex(entry['currencySymbol'])
            except UnsupportedAsset as e:
                self.msg_aggregator.add_warning(
                    f'Found unsupported bittrex asset {e.asset_name}. '
                    f' Ignoring its balance query.',
                )
                continue
            except UnknownAsset as e:
                self.msg_aggregator.add_warning(
                    f'Found unknown bittrex asset {e.asset_name}. '
                    f' Ignoring its balance query.',
                )
                continue
            except DeserializationError:
                self.msg_aggregator.add_error(
                    f'Found bittrex asset with non-string type {type(entry["Currency"])}'
                    f' Ignoring its balance query.',
                )
                continue

            if entry['currencySymbol'] == 'BTXCRD':
                # skip BTXCRD balance, since it's bittrex internal and we can't query usd price
                continue

            try:
                usd_price = Inquirer().find_usd_price(asset=asset)
            except RemoteError as e:
                self.msg_aggregator.add_error(
                    f'Error processing bittrex balance entry due to inability to '
                    f'query USD price: {str(e)}. Skipping balance entry',
                )
                continue

            balance = {}
            balance['amount'] = FVal(entry['total'])
            balance['usd_value'] = FVal(balance['amount']) * usd_price
            returned_balances[asset] = balance

            log.debug(
                'bittrex balance query result',
                sensitive_log=True,
                currency=asset,
                amount=balance['amount'],
                usd_value=balance['usd_value'],
            )

        return returned_balances, ''

    def _paginated_api_query(
            self,
            endpoint: str,
            method: Literal['get', 'put', 'delete'] = 'get',
            options: Optional[Dict[str, Any]] = None,
    ) -> List[Dict[str, Any]]:
        """Handle pagination for bittrex v3 api queries

        Docs: https://bittrex.github.io/api/v3#topic-REST-API-Overview
        """
        if not options:
            options = {}

        all_data = []
        while True:
            query_data = self.api_query(endpoint=endpoint, method=method, options=options)
            if len(query_data) == 0:  # no more data
                break

            all_data.extend(query_data)
            if len(query_data) != options['pageSize']:  # less data than page size
                break

            options['nextPageToken'] = query_data[-1]['id']

        return all_data

    def query_online_trade_history(
            self,
            start_ts: Timestamp,
            end_ts: Timestamp,
            market: Optional[TradePair] = None,
    ) -> List[Trade]:
        options: Dict[str, Union[str, int]] = {
            'pageSize': 200,  # max page size according to their docs
            'startDate': timestamp_to_iso8601(start_ts, utc_as_z=True),
            'endDate': timestamp_to_iso8601(end_ts, utc_as_z=True),
        }
        if market is not None:
            options['marketSymbol'] = world_pair_to_bittrex(market)

        raw_data = self._paginated_api_query(endpoint='orders/closed', options=options)
        log.debug('bittrex order history result', results_num=len(raw_data))

        trades = []
        for raw_trade in raw_data:
            try:
                trade = trade_from_bittrex(raw_trade)
            except UnknownAsset as e:
                self.msg_aggregator.add_warning(
                    f'Found bittrex trade with unknown asset '
                    f'{e.asset_name}. Ignoring it.',
                )
                continue
            except UnsupportedAsset as e:
                self.msg_aggregator.add_warning(
                    f'Found bittrex trade with unsupported asset '
                    f'{e.asset_name}. Ignoring it.',
                )
                continue
            except UnprocessableTradePair as e:
                self.msg_aggregator.add_error(
                    f'Found bittrex trade with unprocessable pair '
                    f'{e.pair}. Ignoring it.',
                )
                continue
            except (DeserializationError, KeyError) as e:
                msg = str(e)
                if isinstance(e, KeyError):
                    msg = f'Missing key entry for {msg}.'
                self.msg_aggregator.add_error(
                    'Error processing a bittrex trade. Check logs '
                    'for details. Ignoring it.',
                )
                log.error(
                    'Error processing a bittrex trade',
                    trade=raw_trade,
                    error=msg,
                )
                continue

            trades.append(trade)

        return trades

    def _deserialize_asset_movement(self, raw_data: Dict[str, Any]) -> Optional[AssetMovement]:
        """Processes a single deposit/withdrawal from bittrex and deserializes it

        Can log error/warning and return None if something went wrong at deserialization
        """
        try:
            if 'source' in raw_data:
                category = AssetMovementCategory.DEPOSIT
                fee = Fee(ZERO)
            else:
                category = AssetMovementCategory.WITHDRAWAL
                fee = deserialize_fee(raw_data['txCost'])

            timestamp = deserialize_timestamp_from_date(
                raw_data['completedAt'],
                'iso8601',
                'bittrex',
            )
            asset = asset_from_bittrex(raw_data['currencySymbol'])
            return AssetMovement(
                location=Location.BITTREX,
                category=category,
                timestamp=timestamp,
                asset=asset,
                amount=deserialize_asset_amount(raw_data['quantity']),
                fee_asset=asset,
                fee=fee,
                link=str(raw_data['txId']),
            )
        except UnknownAsset as e:
            self.msg_aggregator.add_warning(
                f'Found bittrex deposit/withdrawal with unknown asset '
                f'{e.asset_name}. Ignoring it.',
            )
        except UnsupportedAsset as e:
            self.msg_aggregator.add_warning(
                f'Found bittrex deposit/withdrawal with unsupported asset '
                f'{e.asset_name}. Ignoring it.',
            )
        except (DeserializationError, KeyError) as e:
            msg = str(e)
            if isinstance(e, KeyError):
                msg = f'Missing key entry for {msg}.'
            self.msg_aggregator.add_error(
                'Unexpected data encountered during deserialization of a bittrex '
                'asset movement. Check logs for details and open a bug report.',
            )
            log.error(
                f'Unexpected data encountered during deserialization of bittrex '
                f'asset_movement {raw_data}. Error was: {str(e)}',
            )

        return None

    def query_online_deposits_withdrawals(
            self,
            start_ts: Timestamp,
            end_ts: Timestamp,
    ) -> List[AssetMovement]:
        options: Dict[str, Union[str, int]] = {
            'pageSize': 200,  # max page size according to their docs
            'startDate': timestamp_to_iso8601(start_ts, utc_as_z=True),
            'endDate': timestamp_to_iso8601(end_ts, utc_as_z=True),
        }

        raw_data = self._paginated_api_query(endpoint='deposits/closed', options=options.copy())
        raw_data.extend(
            self._paginated_api_query(endpoint='withdrawals/closed', options=options.copy()),
        )
        log.debug('bittrex deposit/withdrawal history result', results_num=len(raw_data))

        movements = []
        for raw_movement in raw_data:
            movement = self._deserialize_asset_movement(raw_movement)
            if movement and movement.timestamp >= start_ts and movement.timestamp <= end_ts:
                movements.append(movement)

        return movements
