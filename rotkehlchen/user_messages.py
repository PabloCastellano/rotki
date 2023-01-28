import json
import logging
from collections import deque
from typing import TYPE_CHECKING, Any, Deque, Optional, Union

from rotkehlchen.api.websockets.typedefs import WSMessageType
from rotkehlchen.logging import RotkehlchenLogsAdapter

if TYPE_CHECKING:
    from rotkehlchen.api.websockets.notifier import RotkiNotifier


logger = logging.getLogger(__name__)
log = RotkehlchenLogsAdapter(logger)
ERROR_MESSAGE_TYPES = {WSMessageType.LEGACY, WSMessageType.BALANCE_SNAPSHOT_ERROR}


class MessagesAggregator():
    """
    This class is passed around where needed and aggregates messages for the user
    """

    def __init__(self) -> None:
        self.warnings: Deque = deque()
        self.errors: Deque = deque()
        self.rotki_notifier: Optional['RotkiNotifier'] = None

    def _append_warning(self, msg: str) -> None:
        self.warnings.appendleft(msg)

    def add_warning(self, msg: str) -> None:
        log.warning(msg)
        if self.rotki_notifier is not None:
            data = {'verbosity': 'warning', 'value': msg}
            self.rotki_notifier.broadcast(
                message_type=WSMessageType.LEGACY,
                to_send_data=data,
                failure_callback=self._append_warning,
                failure_callback_args={'msg': msg},
            )
            return
        # else
        self.warnings.appendleft(msg)

    def consume_warnings(self) -> list[str]:
        result = []
        while len(self.warnings) != 0:
            result.append(self.warnings.pop())
        return result

    def _append_error(self, msg: str) -> None:
        self.errors.appendleft(msg)

    def add_error(self, msg: str) -> None:
        log.error(msg)
        if self.rotki_notifier is not None:
            data = {'verbosity': 'error', 'value': msg}
            self.rotki_notifier.broadcast(
                message_type=WSMessageType.LEGACY,
                to_send_data=data,
                failure_callback=self._append_error,
                failure_callback_args={'msg': msg},
            )
            return
        self.errors.appendleft(msg)

    def add_message(
            self,
            message_type: WSMessageType,
            data: Union[dict[str, Any], list[Any]],
    ) -> None:
        """Sends a websocket message

        Specify its type and data.

        `wait_on_send` is used to determine if the message should be sent asynchronously
        by spawning a greenlet or if it should just do it synchronously.
        """
        fallback_msg = json.dumps({'type': str(message_type), 'data': data})  # noqa: E501  # kind of silly to repeat it here. Same code in broadcast

        if self.rotki_notifier is not None:
            self.rotki_notifier.broadcast(
                message_type=message_type,
                to_send_data=data,
                failure_callback=self._append_error,
                failure_callback_args={'msg': fallback_msg},
            )
        else:  # Fallback to polling for error messages
            if message_type in ERROR_MESSAGE_TYPES:
                self.errors.appendleft(fallback_msg)

    def consume_errors(self) -> list[str]:
        result = []
        while len(self.errors) != 0:
            result.append(self.errors.pop())
        return result
