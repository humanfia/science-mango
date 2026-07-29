#!/usr/bin/env python3
"""Transparent, secret-safe observer for Moonshot OpenAI Chat Completions.

The proxy exists only to diagnose and repair the legacy Codex 0.80 Chat
history shape. It never logs headers, message content, tool arguments, or tool
results. Upstream traffic remains standard POST /v1/chat/completions.
"""

from __future__ import annotations

import argparse
import http.client
import json
import threading
import time
import uuid
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any


class AuditLog:
    def __init__(self, path: Path) -> None:
        self.path = path
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self._lock = threading.Lock()

    def write(self, event: dict[str, Any]) -> None:
        row = {"ts": time.time(), **event}
        encoded = json.dumps(row, ensure_ascii=False, separators=(",", ":"))
        with self._lock:
            with self.path.open("a", encoding="utf-8") as handle:
                handle.write(encoded + "\n")


def _content_size(content: Any) -> int:
    if isinstance(content, str):
        return len(content)
    if content is None:
        return 0
    return len(json.dumps(content, ensure_ascii=False))


def summarize_request(payload: dict[str, Any]) -> dict[str, Any]:
    messages_summary: list[dict[str, Any]] = []
    pending: list[str] = []
    protocol_issues: list[str] = []

    for index, message in enumerate(payload.get("messages") or []):
        if not isinstance(message, dict):
            messages_summary.append({"i": index, "kind": type(message).__name__})
            continue

        role = message.get("role")
        item: dict[str, Any] = {
            "i": index,
            "role": role,
            "content_len": _content_size(message.get("content")),
        }
        tool_calls = message.get("tool_calls")
        if role == "assistant" and isinstance(tool_calls, list) and tool_calls:
            calls: list[dict[str, Any]] = []
            if pending:
                protocol_issues.append(
                    f"assistant[{index}] starts tool calls with unresolved {pending}"
                )
            pending = []
            for call in tool_calls:
                if not isinstance(call, dict):
                    continue
                function = call.get("function")
                function = function if isinstance(function, dict) else {}
                call_id = str(call.get("id") or "")
                pending.append(call_id)
                calls.append(
                    {
                        "id": call_id,
                        "name": function.get("name"),
                        "arguments_len": _content_size(function.get("arguments")),
                    }
                )
            item["tool_calls"] = calls
        elif role == "tool":
            call_id = str(message.get("tool_call_id") or "")
            item["tool_call_id"] = call_id
            item["name"] = message.get("name")
            if call_id in pending:
                pending.remove(call_id)
            else:
                protocol_issues.append(
                    f"tool[{index}] id {call_id!r} has no pending assistant call"
                )
        elif pending:
            protocol_issues.append(
                f"{role}[{index}] appears before tool responses for {pending}"
            )

        messages_summary.append(item)

    if pending:
        protocol_issues.append(f"request ends with unresolved calls {pending}")

    return {
        "model": payload.get("model"),
        "stream": payload.get("stream"),
        "parallel_tool_calls": payload.get("parallel_tool_calls"),
        "message_count": len(payload.get("messages") or []),
        "messages": messages_summary,
        "protocol_issues": protocol_issues,
    }


def normalize_tool_history(payload: dict[str, Any]) -> dict[str, Any]:
    """Move delayed tool results directly behind their assistant tool call.

    Legacy Codex can inject an internal ``user`` notice after an assistant tool
    call but before the corresponding ``tool`` result. OpenAI Chat requires all
    tool results to appear first. Preserve every message and its relative order,
    moving only the matching tool result(s) ahead of intervening notices.
    """

    messages = payload.get("messages")
    if not isinstance(messages, list):
        return {"repaired": False, "turns": 0, "moved_messages": 0}

    normalized: list[Any] = []
    repaired_turns = 0
    moved_messages = 0
    index = 0

    while index < len(messages):
        message = messages[index]
        normalized.append(message)
        if not isinstance(message, dict) or message.get("role") != "assistant":
            index += 1
            continue

        calls = message.get("tool_calls")
        if not isinstance(calls, list) or not calls:
            index += 1
            continue
        call_ids = [
            str(call.get("id") or "")
            for call in calls
            if isinstance(call, dict) and call.get("id")
        ]
        if not call_ids:
            index += 1
            continue

        found: dict[str, int] = {}
        cursor = index + 1
        while cursor < len(messages):
            candidate = messages[cursor]
            if (
                isinstance(candidate, dict)
                and candidate.get("role") == "assistant"
                and candidate.get("tool_calls")
            ):
                break
            if isinstance(candidate, dict) and candidate.get("role") == "tool":
                call_id = str(candidate.get("tool_call_id") or "")
                if call_id in call_ids and call_id not in found:
                    found[call_id] = cursor
                    if len(found) == len(call_ids):
                        break
            cursor += 1

        if len(found) != len(call_ids):
            index += 1
            continue

        match_positions = set(found.values())
        segment = messages[index + 1 : cursor + 1]
        matching = [
            candidate
            for position, candidate in enumerate(segment, start=index + 1)
            if position in match_positions
        ]
        deferred = [
            candidate
            for position, candidate in enumerate(segment, start=index + 1)
            if position not in match_positions
        ]
        if deferred:
            normalized.extend(matching)
            normalized.extend(deferred)
            repaired_turns += 1
            moved_messages += len(deferred)
        else:
            normalized.extend(segment)
        index = cursor + 1

    if repaired_turns:
        payload["messages"] = normalized
    return {
        "repaired": repaired_turns > 0,
        "turns": repaired_turns,
        "moved_messages": moved_messages,
    }


def summarize_sse(raw: bytes) -> dict[str, Any]:
    calls: dict[int, dict[str, Any]] = {}
    content_len = 0
    finish_reasons: list[str] = []
    for line in raw.splitlines():
        if not line.startswith(b"data:"):
            continue
        data = line[5:].strip()
        if not data or data == b"[DONE]":
            continue
        try:
            event = json.loads(data)
        except (json.JSONDecodeError, UnicodeDecodeError):
            continue
        for choice in event.get("choices") or []:
            delta = choice.get("delta") or {}
            content = delta.get("content")
            if isinstance(content, str):
                content_len += len(content)
            for call in delta.get("tool_calls") or []:
                call_index = int(call.get("index") or 0)
                target = calls.setdefault(
                    call_index,
                    {"index": call_index, "id": "", "name": "", "arguments_len": 0},
                )
                if call.get("id"):
                    target["id"] += str(call["id"])
                function = call.get("function") or {}
                if function.get("name"):
                    target["name"] += str(function["name"])
                arguments = function.get("arguments")
                if isinstance(arguments, str):
                    target["arguments_len"] += len(arguments)
            finish = choice.get("finish_reason")
            if finish:
                finish_reasons.append(str(finish))
    return {
        "assistant_content_len": content_len,
        "tool_calls": [calls[key] for key in sorted(calls)],
        "finish_reasons": finish_reasons,
    }


def sanitize_tool_call_sse(raw: bytes) -> tuple[bytes, dict[str, Any]]:
    """Make legacy Codex-safe Chat tool turns.

    Codex 0.80 cannot replay a Chat assistant message that contains both
    natural-language content and tool calls, nor one containing multiple tool
    calls. K3 can emit either shape even when asked not to. Buffer one upstream
    SSE response and, only when it contains tool calls, remove assistant
    content and retain the first tool call. The next model turn can request any
    additional tool after seeing the first result.
    """

    parsed: list[tuple[bytes, dict[str, Any] | None]] = []
    call_indices: set[int] = set()
    dropped_content_chars = 0

    for line in raw.splitlines():
        event: dict[str, Any] | None = None
        if line.startswith(b"data:"):
            data = line[5:].strip()
            if data and data != b"[DONE]":
                try:
                    candidate = json.loads(data)
                    if isinstance(candidate, dict):
                        event = candidate
                        for choice in event.get("choices") or []:
                            delta = choice.get("delta") or {}
                            for call in delta.get("tool_calls") or []:
                                call_indices.add(int(call.get("index") or 0))
                except (json.JSONDecodeError, UnicodeDecodeError, ValueError):
                    event = None
        parsed.append((line, event))

    if not call_indices:
        return raw, {
            "sanitized": False,
            "dropped_content_chars": 0,
            "dropped_tool_call_indices": [],
        }

    keep_index = min(call_indices)
    output_lines: list[bytes] = []
    for original, event in parsed:
        if event is None:
            output_lines.append(original)
            continue

        for choice in event.get("choices") or []:
            delta = choice.get("delta")
            if not isinstance(delta, dict):
                continue
            content = delta.pop("content", None)
            if isinstance(content, str):
                dropped_content_chars += len(content)
            calls = delta.get("tool_calls")
            if isinstance(calls, list):
                kept = [
                    call
                    for call in calls
                    if int(call.get("index") or 0) == keep_index
                ]
                if kept:
                    delta["tool_calls"] = kept
                else:
                    delta.pop("tool_calls", None)

        output_lines.append(
            b"data: "
            + json.dumps(event, ensure_ascii=False, separators=(",", ":")).encode()
        )

    transformed = b"\n".join(output_lines) + b"\n"
    return transformed, {
        "sanitized": True,
        "dropped_content_chars": dropped_content_chars,
        "dropped_tool_call_indices": sorted(call_indices - {keep_index}),
    }


class ProxyHandler(BaseHTTPRequestHandler):
    server_version = "ArchonMoonshotChatProxy/1.0"
    protocol_version = "HTTP/1.1"

    @property
    def proxy_server(self) -> "ProxyServer":
        return self.server  # type: ignore[return-value]

    def log_message(self, _format: str, *_args: Any) -> None:
        return

    def do_GET(self) -> None:  # noqa: N802
        if self.path == "/healthz":
            body = json.dumps(
                {
                    "status": "ok",
                    "upstream": self.proxy_server.upstream_host,
                    "wire_api": "chat/completions",
                    "normalize_tool_history": self.proxy_server.sanitize_tool_stream,
                }
            ).encode()
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return
        self.send_error(404)

    def do_POST(self) -> None:  # noqa: N802
        request_id = uuid.uuid4().hex[:16]
        if self.path.rstrip("/") not in {
            "/v1/chat/completions",
            "/chat/completions",
        }:
            self._json_error(404, "only OpenAI Chat Completions is supported")
            return

        try:
            content_length = int(self.headers.get("Content-Length") or "0")
        except ValueError:
            self._json_error(400, "invalid Content-Length")
            return
        raw_body = self.rfile.read(content_length)
        try:
            payload = json.loads(raw_body)
        except json.JSONDecodeError:
            self._json_error(400, "request body is not JSON")
            return

        original_summary = summarize_request(payload)
        history_repair = {
            "repaired": False,
            "turns": 0,
            "moved_messages": 0,
        }
        if self.proxy_server.sanitize_tool_stream:
            history_repair = normalize_tool_history(payload)
            if history_repair["repaired"]:
                raw_body = json.dumps(
                    payload, ensure_ascii=False, separators=(",", ":")
                ).encode()
        request_summary = summarize_request(payload)
        self.proxy_server.audit.write(
            {
                "event": "request",
                "request_id": request_id,
                **request_summary,
                "history_repair": history_repair,
                "original_protocol_issues": original_summary["protocol_issues"],
            }
        )

        authorization = self.headers.get("Authorization")
        if not authorization:
            self._json_error(401, "missing Authorization header")
            return

        headers = {
            "Authorization": authorization,
            "Content-Type": "application/json",
            "Accept": self.headers.get("Accept") or "text/event-stream",
            "User-Agent": self.headers.get("User-Agent")
            or "archon-moonshot-chat-proxy",
        }

        connection = http.client.HTTPSConnection(
            self.proxy_server.upstream_host,
            self.proxy_server.upstream_port,
            timeout=self.proxy_server.timeout,
        )
        try:
            connection.request(
                "POST",
                self.proxy_server.upstream_path,
                body=raw_body,
                headers=headers,
            )
            upstream = connection.getresponse()
            content_type = upstream.getheader("Content-Type") or "application/json"

            if upstream.status >= 400:
                error_body = upstream.read()
                error_message = ""
                try:
                    error_payload = json.loads(error_body)
                    error = error_payload.get("error")
                    if isinstance(error, dict):
                        error_message = str(error.get("message") or "")
                except (json.JSONDecodeError, UnicodeDecodeError):
                    pass
                self.proxy_server.audit.write(
                    {
                        "event": "upstream_error",
                        "request_id": request_id,
                        "status": upstream.status,
                        "message": error_message[:1000],
                    }
                )
                self.send_response(upstream.status)
                self.send_header("Content-Type", content_type)
                self.send_header("Content-Length", str(len(error_body)))
                self.send_header("Connection", "close")
                self.end_headers()
                self.wfile.write(error_body)
                self.close_connection = True
                return

            upstream_body = upstream.read()
            response_summary = summarize_sse(
                upstream_body[: self.proxy_server.capture_limit]
            )
            transform = {
                "sanitized": False,
                "dropped_content_chars": 0,
                "dropped_tool_call_indices": [],
            }
            response_body = upstream_body
            if (
                self.proxy_server.sanitize_tool_stream
                and "text/event-stream" in content_type
            ):
                response_body, transform = sanitize_tool_call_sse(upstream_body)

            self.send_response(upstream.status)
            self.send_header("Content-Type", content_type)
            self.send_header("Content-Length", str(len(response_body)))
            self.send_header("Cache-Control", "no-cache")
            self.send_header("Connection", "close")
            self.end_headers()
            self.wfile.write(response_body)
            self.wfile.flush()
            self.close_connection = True
            self.proxy_server.audit.write(
                {
                    "event": "upstream_success",
                    "request_id": request_id,
                    "status": upstream.status,
                    **response_summary,
                    **transform,
                }
            )
        except (OSError, http.client.HTTPException) as exc:
            self.proxy_server.audit.write(
                {
                    "event": "proxy_error",
                    "request_id": request_id,
                    "type": type(exc).__name__,
                    "message": str(exc)[:1000],
                }
            )
            if not self.wfile.closed:
                self._json_error(502, f"upstream connection failed: {type(exc).__name__}")
        finally:
            connection.close()

    def _json_error(self, status: int, message: str) -> None:
        body = json.dumps(
            {"error": {"type": "proxy_error", "message": message}}
        ).encode()
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Connection", "close")
        self.end_headers()
        self.wfile.write(body)
        self.close_connection = True


class ProxyServer(ThreadingHTTPServer):
    daemon_threads = True

    def __init__(
        self,
        bind: tuple[str, int],
        handler: type[BaseHTTPRequestHandler],
        *,
        audit: AuditLog,
        upstream_host: str,
        upstream_port: int,
        upstream_path: str,
        timeout: float,
        capture_limit: int,
        sanitize_tool_stream: bool,
    ) -> None:
        super().__init__(bind, handler)
        self.audit = audit
        self.upstream_host = upstream_host
        self.upstream_port = upstream_port
        self.upstream_path = upstream_path
        self.timeout = timeout
        self.capture_limit = capture_limit
        self.sanitize_tool_stream = sanitize_tool_stream


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=8767)
    parser.add_argument("--upstream-host", default="api.moonshot.ai")
    parser.add_argument("--upstream-port", type=int, default=443)
    parser.add_argument("--upstream-path", default="/v1/chat/completions")
    parser.add_argument("--timeout", type=float, default=900.0)
    parser.add_argument("--capture-limit", type=int, default=2_000_000)
    parser.add_argument(
        "--observe-only",
        action="store_true",
        help="Log requests without sanitizing mixed or parallel tool responses.",
    )
    parser.add_argument(
        "--audit-log",
        type=Path,
        default=Path(".archon/runtime/moonshot_chat_proxy.jsonl"),
    )
    args = parser.parse_args()

    audit = AuditLog(args.audit_log.resolve())
    server = ProxyServer(
        (args.host, args.port),
        ProxyHandler,
        audit=audit,
        upstream_host=args.upstream_host,
        upstream_port=args.upstream_port,
        upstream_path=args.upstream_path,
        timeout=args.timeout,
        capture_limit=args.capture_limit,
        sanitize_tool_stream=not args.observe_only,
    )
    audit.write(
        {
            "event": "proxy_start",
            "bind": f"{args.host}:{args.port}",
            "upstream": f"https://{args.upstream_host}{args.upstream_path}",
            "sanitize_tool_stream": not args.observe_only,
            "normalize_tool_history": not args.observe_only,
        }
    )
    server.serve_forever()


if __name__ == "__main__":
    main()
