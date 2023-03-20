from rotkehlchen.accounting.structures.balance import Balance
from rotkehlchen.accounting.structures.base import HistoryEvent
from rotkehlchen.accounting.structures.evm_event import EvmEvent, EvmProduct
from rotkehlchen.accounting.structures.types import HistoryEventSubType, HistoryEventType
from rotkehlchen.constants.assets import A_ETH
from rotkehlchen.db.constants import HISTORY_MAPPING_KEY_STATE, HISTORY_MAPPING_STATE_CUSTOMIZED
from rotkehlchen.db.filtering import EvmEventFilterQuery, HistoryEventFilterQuery
from rotkehlchen.db.history_events import DBHistoryEvents
from rotkehlchen.types import ChainID, EVMTxHash, Location, TimestampMS


def test_get_customized_event_identifiers(database):
    db = DBHistoryEvents(database)
    with db.db.user_write() as write_cursor:
        db.add_history_event(
            write_cursor=write_cursor,
            event=HistoryEvent(
                event_identifier=EVMTxHash('0x75ceef8e258c08fc2724c1286da0426cb6ec8df208a9ec269108430c30262791'),  # noqa: E501
                sequence_index=1,
                timestamp=TimestampMS(1),
                location=Location.ETHEREUM,
                event_type=HistoryEventType.TRADE,
                event_subtype=HistoryEventSubType.NONE,
                asset=A_ETH,
                balance=Balance(1),
            ),
            mapping_values={HISTORY_MAPPING_KEY_STATE: HISTORY_MAPPING_STATE_CUSTOMIZED},
        )
        db.add_history_events(
            write_cursor=write_cursor,
            history=[
                HistoryEvent(
                    event_identifier=EVMTxHash('0x15ceef8e258c08fc2724c1286da0426cb6ec8df208a9ec269108430c30262791'),  # noqa: E501
                    sequence_index=1,
                    timestamp=TimestampMS(1),
                    location=Location.OPTIMISM,
                    event_type=HistoryEventType.TRADE,
                    event_subtype=HistoryEventSubType.NONE,
                    asset=A_ETH,
                    balance=Balance(1),
                ), HistoryEvent(
                    event_identifier=EVMTxHash('0x25ceef8e258c08fc2724c1286da0426cb6ec8df208a9ec269108430c30262791'),  # noqa: E501
                    sequence_index=1,
                    timestamp=TimestampMS(2),
                    location=Location.OPTIMISM,
                    event_type=HistoryEventType.TRADE,
                    event_subtype=HistoryEventSubType.NONE,
                    asset=A_ETH,
                    balance=Balance(2),
                ),
            ],
        )
        db.add_history_event(
            write_cursor=write_cursor,
            event=HistoryEvent(
                event_identifier=EVMTxHash('0x35ceef8e258c08fc2724c1286da0426cb6ec8df208a9ec269108430c30262791'),  # noqa: E501
                sequence_index=1,
                timestamp=TimestampMS(3),
                location=Location.OPTIMISM,
                event_type=HistoryEventType.TRADE,
                event_subtype=HistoryEventSubType.NONE,
                asset=A_ETH,
                balance=Balance(1),
            ),
            mapping_values={HISTORY_MAPPING_KEY_STATE: HISTORY_MAPPING_STATE_CUSTOMIZED},
        )

    with db.db.conn.read_ctx() as cursor:
        assert db.get_customized_event_identifiers(cursor, chain_id=None) == [1, 4]
        assert db.get_customized_event_identifiers(cursor, chain_id=ChainID.ETHEREUM) == [1]
        assert db.get_customized_event_identifiers(cursor, chain_id=ChainID.OPTIMISM) == [4]


def test_read_write_events_from_db(database):
    db = DBHistoryEvents(database)
    history_data = {  # mapping of identifier to unique data
        1: (b'TEST1', TimestampMS(1), 1),
        2: (b'TEST2', TimestampMS(2), 2),
        3: (b'TEST3', TimestampMS(3), 3),
    }

    evm_data = {  # mapping of identifier to unique data
        4: (EVMTxHash('0x75ceef8e258c08fc2724c1286da0426cb6ec8df208a9ec269108430c30262791'), TimestampMS(4), 4, 'gas', EvmProduct.POOL, '0x95222290DD7278Aa3Ddd389Cc1E1d165CC4BAfe5'),  # noqa: E501
        5: (EVMTxHash('0x12ceef8e258c08fc2724c1286da0426cb6ec8df208a9ec269108430c302627f7'), TimestampMS(5), 5, 'liquity', EvmProduct.STAKING, '0x85222290DD7278Aa3Ddd389Cc1E1d165CC4BAfe5'),  # noqa: E501
        6: (EVMTxHash('0x12cefa8e258c08fc2724c1286da0426cb6e488df208a9ec269108430c302627f7'), TimestampMS(6), 6, 'aave', EvmProduct.POOL, '0x95222290DD7278Aa3Ddd389Cc1E1d165CC4BAfe4'),  # noqa: E501
        7: (EVMTxHash('0x1acefa8e258c08fc2724c1286da0426cb6e8f2df208a9ec269108430c302627f7'), TimestampMS(7), 7, 'compound', EvmProduct.POOL, '0x19222290DD7278Aa3Ddd389Cc1E1d165CC4BAf34'),  # noqa: E501
    }

    with db.db.user_write() as write_cursor:
        for _, entry in history_data.items():
            db.add_history_event(
                write_cursor=write_cursor,
                event=HistoryEvent(
                    event_identifier=entry[0],
                    sequence_index=1,
                    timestamp=entry[1],
                    location=Location.ETHEREUM,
                    event_type=HistoryEventType.TRADE,
                    event_subtype=HistoryEventSubType.NONE,
                    asset=A_ETH,
                    balance=Balance(entry[2]),
                ),
            )
        for _, entry in evm_data.items():
            db.add_history_event(
                write_cursor=write_cursor,
                event=EvmEvent(
                    event_identifier=entry[0],
                    sequence_index=1,
                    timestamp=entry[1],
                    location=Location.ETHEREUM,
                    event_type=HistoryEventType.TRADE,
                    event_subtype=HistoryEventSubType.NONE,
                    asset=A_ETH,
                    balance=Balance(entry[2]),
                    counterparty=entry[3],
                    product=entry[4],
                    address=entry[5],
                ),
            )

    with db.db.conn.read_ctx() as cursor:
        for query_fn, filter_query, limit_to_entry_type in (
                (db.get_all_history_events, HistoryEventFilterQuery, False),
                (db.get_history_events, HistoryEventFilterQuery, True),
                (db.get_history_events, EvmEventFilterQuery, True),
        ):
            all_events = query_fn(cursor, filter_query.make(limit_to_entry_type=limit_to_entry_type), True)  # noqa: E501
            for event in all_events:
                if isinstance(event, HistoryEvent):
                    data_entry = history_data[event.identifier]
                    expected_event = HistoryEvent(
                        identifier=event.identifier,
                        event_identifier=data_entry[0],
                        sequence_index=1,
                        timestamp=data_entry[1],
                        location=Location.ETHEREUM,
                        event_type=HistoryEventType.TRADE,
                        event_subtype=HistoryEventSubType.NONE,
                        asset=A_ETH,
                        balance=Balance(data_entry[2]),
                    )
                else:
                    data_entry = evm_data[event.identifier]
                    expected_event = EvmEvent(
                        identifier=event.identifier,
                        event_identifier=data_entry[0],
                        sequence_index=1,
                        timestamp=data_entry[1],
                        location=Location.ETHEREUM,
                        event_type=HistoryEventType.TRADE,
                        event_subtype=HistoryEventSubType.NONE,
                        asset=A_ETH,
                        balance=Balance(data_entry[2]),
                        counterparty=data_entry[3],
                        product=data_entry[4],
                        address=data_entry[5],
                    )
                assert event == expected_event
