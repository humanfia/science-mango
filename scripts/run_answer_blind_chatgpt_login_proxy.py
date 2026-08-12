#!/usr/bin/env python3
"""One-shot trusted transport proxy for a ChatGPT-login Codex invocation.

The caller body is deliberately discarded.  Before listening, the root
controller registers one immutable canonical Responses request.  The proxy
forwards only that request and only the in-memory Authorization and
``chatgpt-account-id`` headers needed by the pinned ChatGPT Codex endpoint.
No credential value is ever written to a receipt or log.
"""

from __future__ import annotations

import hashlib
import http.client
import http.server
import json
import os
import re
import stat
import threading
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Mapping, NoReturn, Sequence


SCHEMA_VERSION = 1
PROTOCOL = "icho-answer-blind-v1"
UPSTREAM_HOST = "chatgpt.com"
UPSTREAM_PATH = "/backend-api/codex/responses"
MAX_BODY_BYTES = 256 * 1024 * 1024
SHA256 = re.compile(r"^[0-9a-f]{64}$")
SSE_METADATA_TOKEN = re.compile(r"[^A-Za-z0-9_.:-]")
MAX_SSE_METADATA_EVENTS = 8
MAX_SSE_METADATA_TOKEN_CHARS = 32


class LoginProxyError(RuntimeError):
    pass


def _fail(message: str) -> NoReturn:
    raise LoginProxyError(message)


def _sha(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            _fail(f"JSON repeats key {key!r}")
        result[key] = value
    return result


def strict_json(payload: bytes, *, label: str) -> dict[str, Any]:
    try:
        value = json.loads(
            payload.decode("utf-8", errors="strict"),
            object_pairs_hook=_pairs,
            parse_constant=lambda value: _fail(f"{label} contains {value}"),
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise LoginProxyError(f"{label} is not strict UTF-8 JSON") from exc
    if not isinstance(value, dict):
        _fail(f"{label} must be a JSON object")
    return value


def canonical(value: Mapping[str, Any]) -> bytes:
    return (
        json.dumps(
            value, ensure_ascii=False, sort_keys=True, separators=(",", ":"),
            allow_nan=False,
        ) + "\n"
    ).encode("utf-8")


def _registered_request(path: Path, *, model: str) -> tuple[Path, bytes]:
    if path.is_symlink() or not path.is_file():
        _fail("pre-registered request must be a plain file")
    resolved = path.resolve(strict=True)
    metadata = resolved.stat()
    if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) != 0o400:
        _fail("pre-registered request must be root-owned mode 0400")
    payload = resolved.read_bytes()
    value = strict_json(payload, label="pre-registered request")
    expected_fields = {
        "model", "input", "tools", "tool_choice", "store", "stream", "text",
        "reasoning",
    }
    if (
        set(value) != expected_fields
        or value.get("model") != model
        or value.get("tools") != []
        or value.get("tool_choice") != "none"
        or value.get("store") is not False
        or value.get("stream") is not True
        or value.get("reasoning") != {"effort": "max", "summary": "auto"}
        or not isinstance(value.get("input"), list)
        or len(value["input"]) != 1
    ):
        _fail("pre-registered request is not the canonical tool-free profile")
    text = value.get("text")
    output_format = text.get("format") if isinstance(text, Mapping) else None
    if (
        not isinstance(output_format, Mapping)
        or output_format.get("type") != "json_schema"
        or output_format.get("strict") is not True
        or not isinstance(output_format.get("schema"), Mapping)
    ):
        _fail("pre-registered request lacks a strict output schema")
    if payload != canonical(value):
        _fail("pre-registered request is not canonical JSON")
    return resolved, payload


def _forbidden_output(value: Any) -> bool:
    if isinstance(value, Mapping):
        kind = value.get("type")
        if isinstance(kind, str) and (
            "tool" in kind.lower() or "function" in kind.lower()
            or "refusal" in kind.lower()
        ):
            return True
        for key in ("tool_calls", "function_call", "refusal"):
            if value.get(key) not in (None, [], ""):
                return True
        return any(_forbidden_output(child) for child in value.values())
    if isinstance(value, list):
        return any(_forbidden_output(child) for child in value)
    return False


def _sse_metadata_token(value: Any) -> str:
    if not isinstance(value, str):
        return "unknown"
    sanitized = SSE_METADATA_TOKEN.sub("?", value)[:MAX_SSE_METADATA_TOKEN_CHARS]
    return sanitized or "unknown"


def _sse_event_metadata(event: Mapping[str, Any]) -> str:
    event_type = _sse_metadata_token(event.get("type"))
    response = event.get("response")
    status = response.get("status") if isinstance(response, Mapping) else event.get("status")
    if status is None:
        return event_type
    return f"{event_type}[status={_sse_metadata_token(status)}]"


def normalize_completed_sse(raw: bytes) -> tuple[bytes, int]:
    """Mechanically rebuild the sole assistant message from strict SSE events."""

    try:
        text = raw.decode("utf-8", errors="strict").replace("\r\n", "\n")
    except UnicodeDecodeError as exc:
        raise LoginProxyError("upstream SSE is not UTF-8") from exc
    events: list[dict[str, Any]] = []
    observed: list[str] = []
    omitted_event_count = 0
    done_seen = False
    for block in text.split("\n\n"):
        lines = block.splitlines()
        if not lines:
            continue
        event_lines = [line[6:].lstrip() for line in lines if line.startswith("event:")]
        data_lines = [line[5:].lstrip() for line in lines if line.startswith("data:")]
        if not data_lines:
            continue
        data = "\n".join(data_lines)
        if data == "[DONE]":
            if done_seen:
                _fail("upstream SSE repeats [DONE]")
            done_seen = True
            continue
        event = strict_json(data.encode("utf-8"), label="upstream SSE event")
        if (
            len(event_lines) != 1 or event_lines[0] != event.get("type")
            or len(data_lines) != 1 or lines != [
                f"event: {event_lines[0]}", f"data: {data_lines[0]}",
            ]
        ):
            _fail("upstream SSE event/data framing is not canonical")
        sequence = event.get("sequence_number")
        if not isinstance(sequence, int) or isinstance(sequence, bool) or sequence != len(events):
            _fail("upstream SSE sequence numbers are not contiguous from zero")
        if done_seen:
            _fail("upstream SSE contains an event after [DONE]")
        events.append(event)
        if len(observed) < MAX_SSE_METADATA_EVENTS:
            observed.append(_sse_event_metadata(event))
        else:
            omitted_event_count += 1
    if not events:
        _fail("upstream SSE contains no response events")

    allowed_types = {
        "response.created", "response.in_progress",
        "response.output_item.added", "response.output_item.done",
        "response.reasoning_summary_part.added",
        "response.reasoning_summary_text.delta",
        "response.reasoning_summary_text.done",
        "response.reasoning_summary_part.done",
        "response.content_part.added", "response.output_text.delta",
        "response.output_text.done", "response.content_part.done",
        "response.completed", "keepalive",
    }
    response_id: str | None = None
    created = 0
    in_progress = 0
    completed: list[dict[str, Any]] = []
    added_items: dict[int, tuple[str, str]] = {}
    done_items: dict[int, dict[str, Any]] = {}
    reasoning_summary_parts: dict[int, dict[int, dict[str, Any]]] = {}
    message_index: int | None = None
    message_id: str | None = None
    message_done: dict[str, Any] | None = None
    content_added = False
    text_done: str | None = None
    content_done: dict[str, Any] | None = None
    deltas: list[str] = []
    delta_bytes = 0

    def strict_index(value: object) -> bool:
        return isinstance(value, int) and not isinstance(value, bool) and value >= 0

    def message_coordinates(event: Mapping[str, Any]) -> bool:
        output_index = event.get("output_index")
        content_index = event.get("content_index")
        return (
            strict_index(output_index) and output_index == message_index
            and event.get("item_id") == message_id
            and strict_index(content_index) and content_index == 0
        )

    for position, event in enumerate(events):
        event_type = event.get("type")
        if event_type not in allowed_types or _forbidden_output(event):
            _fail("upstream SSE contains an unknown, refusal, or tool/function event")
        if event_type == "keepalive":
            if (
                set(event) != {"type", "sequence_number"}
                or created != 1 or in_progress != 1 or completed
                or not (set(added_items) - set(done_items))
            ):
                _fail("upstream SSE keepalive is malformed or outside active generation")
            continue
        response = event.get("response")
        if (
            event.get("error") not in (None, "", [], {})
            or (isinstance(response, Mapping) and response.get("error") is not None)
        ):
            _fail("upstream SSE contains an error response")
        if event_type in {"response.created", "response.in_progress", "response.completed"}:
            if not isinstance(response, dict) or not isinstance(response.get("id"), str):
                _fail("upstream SSE response lifecycle event is malformed")
            if response_id is None:
                response_id = response["id"]
            elif response["id"] != response_id:
                _fail("upstream SSE response id changed")
        if event_type == "response.created":
            created += 1
            if position != 0 or created != 1 or response.get("status") != "in_progress":
                _fail("upstream SSE response.created is duplicated or misplaced")
            continue
        if event_type == "response.in_progress":
            in_progress += 1
            if position != 1 or in_progress != 1 or response.get("status") != "in_progress":
                _fail("upstream SSE response.in_progress is duplicated or misplaced")
            continue
        if event_type == "response.completed":
            if position != len(events) - 1 or response.get("status") != "completed":
                _fail("upstream SSE response.completed is not the terminal event")
            completed.append(response)
            continue
        if event_type == "response.output_item.added":
            index = event.get("output_index")
            item = event.get("item")
            if (
                not isinstance(index, int) or isinstance(index, bool) or index < 0
                or index != len(added_items) or index in added_items
                or not isinstance(item, Mapping)
                or not isinstance(item.get("id"), str) or not item["id"]
                or item.get("type") not in {"reasoning", "message"}
            ):
                _fail("upstream SSE output_item.added is malformed")
            added_items[index] = (item["id"], item["type"])
            if item["type"] == "reasoning":
                if item.get("summary") != []:
                    _fail("upstream SSE must add reasoning with an empty summary")
                reasoning_summary_parts[index] = {}
            if item["type"] == "message":
                if (
                    message_id is not None or item.get("role") != "assistant"
                    or item.get("phase") != "final_answer"
                    or item.get("status") != "in_progress" or item.get("content") != []
                ):
                    _fail("upstream SSE must add exactly one empty assistant message")
                message_index, message_id = index, item["id"]
            continue
        if event_type == "response.output_item.done":
            index = event.get("output_index")
            item = event.get("item")
            if (
                not strict_index(index) or index not in added_items or index in done_items
                or not isinstance(item, Mapping)
                or (item.get("id"), item.get("type")) != added_items[index]
            ):
                _fail("upstream SSE output_item.done does not match its added item")
            if item.get("type") == "reasoning":
                parts = reasoning_summary_parts.get(index)
                if parts is None or any(
                    part_state.get("part_done") is None for part_state in parts.values()
                ):
                    _fail("upstream SSE reasoning summary is incomplete")
                rebuilt_summary = [
                    parts[summary_index]["part_done"]
                    for summary_index in range(len(parts))
                ]
                if item.get("summary") != rebuilt_summary:
                    _fail("upstream SSE reasoning item summary differs from its events")
            done_items[index] = dict(item)
            if item.get("type") == "message":
                joined = "".join(deltas)
                content = item.get("content")
                if (
                    index != message_index or item.get("role") != "assistant"
                    or item.get("phase") != "final_answer"
                    or item.get("status") != "completed" or content_done is None
                    or text_done != joined or not isinstance(content, list)
                    or len(content) != 1 or content[0] != content_done
                ):
                    _fail("upstream SSE completed assistant message is inconsistent")
                message_done = dict(item)
            continue
        if event_type == "response.content_part.added":
            part = event.get("part")
            if (
                content_added or not message_coordinates(event)
                or not isinstance(part, Mapping) or part.get("type") != "output_text"
                or part.get("text") != ""
            ):
                _fail("upstream SSE output_text content part is malformed")
            content_added = True
            continue
        if event_type == "response.output_text.delta":
            delta = event.get("delta")
            if (
                not content_added or text_done is not None or not message_coordinates(event)
                or not isinstance(delta, str)
            ):
                _fail("upstream SSE output_text delta is malformed or misplaced")
            delta_bytes += len(delta.encode("utf-8"))
            if delta_bytes > MAX_BODY_BYTES:
                _fail("upstream SSE output_text exceeds the response bound")
            deltas.append(delta)
            continue
        if event_type == "response.output_text.done":
            joined = "".join(deltas)
            if (
                text_done is not None or not message_coordinates(event)
                or event.get("text") != joined
            ):
                _fail("upstream SSE output_text.done differs from its deltas")
            text_done = joined
            continue
        if event_type == "response.content_part.done":
            part = event.get("part")
            if (
                content_done is not None or text_done is None
                or not message_coordinates(event) or not isinstance(part, Mapping)
                or part.get("type") != "output_text" or part.get("text") != text_done
            ):
                _fail("upstream SSE content_part.done differs from output_text.done")
            content_done = dict(part)
            continue
        # Reasoning summaries do not contribute answer text, but their complete
        # lifecycle is replayed and bound to the final reasoning item.
        index = event.get("output_index")
        item_id = event.get("item_id")
        if (
            not strict_index(index) or index not in added_items
            or index in done_items or added_items[index] != (item_id, "reasoning")
        ):
            _fail("upstream SSE reasoning event is detached from its item")
        summary_index = event.get("summary_index")
        if not strict_index(summary_index):
            _fail("upstream SSE reasoning summary index is malformed")
        parts = reasoning_summary_parts[index]
        if event_type == "response.reasoning_summary_part.added":
            part = event.get("part")
            if (
                summary_index != len(parts) or summary_index in parts
                or not isinstance(part, Mapping)
                or part.get("type") != "summary_text" or part.get("text") != ""
            ):
                _fail("upstream SSE reasoning summary part.added is malformed")
            parts[summary_index] = {
                "deltas": [], "text_done": None, "part_done": None,
            }
            continue
        if summary_index not in parts:
            _fail("upstream SSE reasoning summary event precedes part.added")
        part_state = parts[summary_index]
        if event_type == "response.reasoning_summary_text.delta":
            delta = event.get("delta")
            if (
                part_state["text_done"] is not None
                or part_state["part_done"] is not None
                or not isinstance(delta, str)
            ):
                _fail("upstream SSE reasoning summary delta is malformed or misplaced")
            part_state["deltas"].append(delta)
            continue
        if event_type == "response.reasoning_summary_text.done":
            joined = "".join(part_state["deltas"])
            if (
                part_state["text_done"] is not None
                or part_state["part_done"] is not None
                or event.get("text") != joined
            ):
                _fail("upstream SSE reasoning summary text.done differs from its deltas")
            part_state["text_done"] = joined
            continue
        if event_type == "response.reasoning_summary_part.done":
            part = event.get("part")
            if (
                part_state["text_done"] is None or part_state["part_done"] is not None
                or not isinstance(part, Mapping)
                or part.get("type") != "summary_text"
                or part.get("text") != part_state["text_done"]
            ):
                _fail("upstream SSE reasoning summary part.done is inconsistent")
            part_state["part_done"] = dict(part)
            continue
        _fail("upstream SSE reasoning summary event is unsupported")

    if len(completed) != 1:
        summary = ",".join(observed) if observed else "none"
        if omitted_event_count:
            summary += f",+{omitted_event_count}-more"
        _fail(
            "upstream SSE must contain exactly one response.completed event "
            f"(observed={summary})"
        )
    response = completed[0]
    existing_output = response.get("output")
    rebuilt_output = [done_items[index] for index in range(len(done_items))]
    if (
        created != 1 or in_progress != 1 or set(added_items) != set(done_items)
        or message_done is None or message_id is None or message_index is None
        or text_done is None or content_done is None
        or not isinstance(existing_output, list)
        or (existing_output != [] and existing_output != rebuilt_output)
        or response.get("incomplete_details") is not None
        or response.get("tools") != [] or response.get("tool_choice") != "none"
        or _forbidden_output(response)
    ):
        _fail("completed response is not a successful tool-free response")
    rebuilt = dict(response)
    rebuilt["output"] = rebuilt_output
    return canonical(rebuilt), 1


UpstreamCall = Callable[[bytes, Mapping[str, str]], tuple[int, Mapping[str, str], bytes]]


def https_upstream(payload: bytes, headers: Mapping[str, str]) -> tuple[int, Mapping[str, str], bytes]:
    connection = http.client.HTTPSConnection(UPSTREAM_HOST, 443, timeout=900)
    forwarded = {
        "Authorization": headers["authorization"],
        "chatgpt-account-id": headers["chatgpt-account-id"],
        "Content-Type": "application/json",
        "Accept": "text/event-stream",
    }
    connection.request("POST", UPSTREAM_PATH, body=payload, headers=forwarded)
    response = connection.getresponse()
    raw = response.read(MAX_BODY_BYTES + 1)
    response_headers = {key.lower(): value for key, value in response.getheaders()}
    status = response.status
    connection.close()
    return status, response_headers, raw


@dataclass(frozen=True)
class ProxyExchange:
    caller_body_sha256: str
    forwarded_request_sha256: str
    upstream_status: int
    upstream_raw_sse: bytes
    normalized_response: bytes
    caller_header_names: tuple[str, ...]
    forwarded_header_names: tuple[str, ...]
    completed_event_count: int


@dataclass(frozen=True)
class ProxyFailureEvidence:
    upstream_status: int
    upstream_raw_response: bytes
    response_header_names: tuple[str, ...]
    response_structure: Mapping[str, Any]


def bounded_sse_structure(raw: bytes) -> dict[str, Any]:
    """Return bounded event metadata only; never include provider text fields."""

    result: dict[str, Any] = {
        "byte_count": len(raw), "utf8": False, "block_count": 0,
        "data_block_count": 0, "done_count": 0, "parsed_event_count": 0,
        "event_types": [], "omitted_event_types": 0,
    }
    try:
        text = raw.decode("utf-8", errors="strict").replace("\r\n", "\n")
    except UnicodeDecodeError:
        return result
    result["utf8"] = True
    types: list[str] = []
    blocks = [block for block in text.split("\n\n") if block]
    result["block_count"] = len(blocks)
    for block in blocks:
        data_lines = [
            line[5:].lstrip() for line in block.splitlines()
            if line.startswith("data:")
        ]
        if not data_lines:
            continue
        result["data_block_count"] += 1
        data = "\n".join(data_lines)
        if data == "[DONE]":
            result["done_count"] += 1
            continue
        try:
            event = strict_json(data.encode("utf-8"), label="diagnostic SSE event")
        except LoginProxyError:
            continue
        result["parsed_event_count"] += 1
        kind = _sse_metadata_token(event.get("type"))
        if len(types) < 64:
            types.append(kind)
        else:
            result["omitted_event_types"] += 1
    result["event_types"] = types
    return result


class OneShotLoginProxy:
    """A one-POST loopback server whose result can be joined by a controller.

    Codex may probe the configured base URL before sending its Responses POST.
    Such non-POST requests are answered locally and do not consume the single
    permitted exchange.
    """

    def __init__(
        self, *, registered_request: Path, model: str,
        upstream_call: UpstreamCall = https_upstream,
    ) -> None:
        self.request_path, self.request_payload = _registered_request(
            registered_request, model=model,
        )
        self.upstream_call = upstream_call
        self.exchange: ProxyExchange | None = None
        self.failure_evidence: ProxyFailureEvidence | None = None
        self.error: BaseException | None = None
        self._post_complete = threading.Event()
        self._stop_requested = threading.Event()
        self._started = False
        owner = self

        class Handler(http.server.BaseHTTPRequestHandler):
            server_version = "AnswerBlindLoginProxy/1"
            sys_version = ""

            def log_message(self, _format: str, *args: object) -> None:
                del args

            def _answer_probe(self) -> None:
                body = b'{"error":"answer-blind login proxy accepts POST only"}\n'
                self.send_response(405)
                self.send_header("Allow", "POST")
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                if self.command != "HEAD":
                    self.wfile.write(body)

            def do_GET(self) -> None:  # noqa: N802
                self._answer_probe()

            def do_HEAD(self) -> None:  # noqa: N802
                self._answer_probe()

            def do_OPTIONS(self) -> None:  # noqa: N802
                self._answer_probe()

            def do_POST(self) -> None:  # noqa: N802
                try:
                    if self.path != "/v1/responses":
                        _fail("login proxy accepts only /v1/responses")
                    raw_length = self.headers.get("Content-Length")
                    if raw_length is None or not raw_length.isdigit():
                        _fail("caller request needs a bounded Content-Length")
                    length = int(raw_length)
                    if length < 0 or length > MAX_BODY_BYTES:
                        _fail("caller body exceeds proxy limit")
                    caller_body = self.rfile.read(length)
                    lowered = {key.lower(): value for key, value in self.headers.items()}
                    if not lowered.get("authorization") or not lowered.get("chatgpt-account-id"):
                        _fail("Codex login headers are missing")
                    # In particular, x-openai-internal-codex-responses-lite is
                    # never copied to the upstream request.
                    status, response_headers, raw_sse = owner.upstream_call(
                        owner.request_payload,
                        {
                            "authorization": lowered["authorization"],
                            "chatgpt-account-id": lowered["chatgpt-account-id"],
                        },
                    )
                    owner.failure_evidence = ProxyFailureEvidence(
                        upstream_status=status,
                        upstream_raw_response=raw_sse,
                        response_header_names=tuple(sorted(response_headers)),
                        response_structure=bounded_sse_structure(raw_sse),
                    )
                    if status != 200 or len(raw_sse) > MAX_BODY_BYTES:
                        _fail(f"pinned ChatGPT upstream returned HTTP {status}")
                    normalized, count = normalize_completed_sse(raw_sse)
                    owner.exchange = ProxyExchange(
                        caller_body_sha256=_sha(caller_body),
                        forwarded_request_sha256=_sha(owner.request_payload),
                        upstream_status=status,
                        upstream_raw_sse=raw_sse,
                        normalized_response=normalized,
                        caller_header_names=tuple(sorted(lowered)),
                        forwarded_header_names=(
                            "accept", "authorization", "chatgpt-account-id", "content-type",
                        ),
                        completed_event_count=count,
                    )
                    self.send_response(200)
                    self.send_header("Content-Type", response_headers.get("content-type", "text/event-stream"))
                    self.send_header("Content-Length", str(len(raw_sse)))
                    self.end_headers()
                    self.wfile.write(raw_sse)
                except BaseException as exc:
                    owner.error = exc
                    body = b'{"error":"answer-blind login proxy rejected request"}\n'
                    try:
                        self.send_response(502)
                        self.send_header("Content-Type", "application/json")
                        self.send_header("Content-Length", str(len(body)))
                        self.end_headers()
                        self.wfile.write(body)
                    except OSError:
                        pass
                finally:
                    owner._post_complete.set()

        self.server = http.server.HTTPServer(("127.0.0.1", 0), Handler)
        self.server.timeout = 0.25

        def serve_until_post() -> None:
            try:
                while not self._post_complete.is_set() and not self._stop_requested.is_set():
                    self.server.handle_request()
            finally:
                # Do not leave an unserved listener behind while the controller
                # waits for Codex.  A client retry after this terminal POST must
                # receive connection refusal rather than hang in accept/backlog.
                self.server.server_close()

        self.thread = threading.Thread(target=serve_until_post, daemon=True)

    @property
    def base_url(self) -> str:
        return f"http://127.0.0.1:{self.server.server_port}"

    def start(self) -> None:
        if self._started:
            _fail("login proxy can be started only once")
        self._started = True
        self.thread.start()

    def wait(self, timeout: float = 30.0) -> ProxyExchange:
        self.thread.join(timeout)
        if self.thread.is_alive():
            self.close()
            _fail("login proxy did not receive exactly one POST before timeout")
        self.server.server_close()
        if self.error is not None:
            raise LoginProxyError("login proxy exchange failed") from self.error
        if self.exchange is None:
            _fail("login proxy completed without an exchange")
        return self.exchange

    def close(self) -> None:
        self._stop_requested.set()
        if self._started and self.thread.is_alive():
            self.thread.join(1.0)
        self.server.server_close()


if __name__ == "__main__":
    raise SystemExit(
        "This module is an invocation-scoped controller component; use "
        "run_answer_blind_structured_solver.py rather than starting it persistently."
    )
