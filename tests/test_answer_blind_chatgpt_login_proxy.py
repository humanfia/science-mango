from __future__ import annotations

import http.client
import importlib.util
import json
import os
import shutil
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/run_answer_blind_chatgpt_login_proxy.py"
SPEC = importlib.util.spec_from_file_location("answer_blind_login_proxy", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
import sys
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


@unittest.skipUnless(os.geteuid() == 0, "trusted proxy fixture is root-only")
class LoginProxyTests(unittest.TestCase):
    @staticmethod
    def _sse(*, text: str = "{}", completed_output: object = None) -> bytes:
        response_id = "resp_fixture"
        message_id = "msg_fixture"
        part = {"type": "output_text", "annotations": [], "logprobs": [], "text": text}
        message = {
            "id": message_id, "type": "message", "status": "completed",
            "role": "assistant", "phase": "final_answer", "content": [part],
        }
        output = [] if completed_output is None else completed_output
        events = [
            {"type": "response.created", "sequence_number": 0, "response": {
                "id": response_id, "status": "in_progress", "error": None,
                "output": [], "tools": [], "tool_choice": "none",
            }},
            {"type": "response.in_progress", "sequence_number": 1, "response": {
                "id": response_id, "status": "in_progress", "error": None,
                "output": [], "tools": [], "tool_choice": "none",
            }},
            {"type": "response.output_item.added", "sequence_number": 2,
             "output_index": 0, "item": {
                 "id": message_id, "type": "message", "status": "in_progress",
                 "role": "assistant", "phase": "final_answer", "content": [],
             }},
            {"type": "response.content_part.added", "sequence_number": 3,
             "output_index": 0, "item_id": message_id, "content_index": 0,
             "part": {**part, "text": ""}},
            {"type": "response.output_text.delta", "sequence_number": 4,
             "output_index": 0, "item_id": message_id, "content_index": 0,
             "delta": text},
            {"type": "response.output_text.done", "sequence_number": 5,
             "output_index": 0, "item_id": message_id, "content_index": 0,
             "text": text},
            {"type": "response.content_part.done", "sequence_number": 6,
             "output_index": 0, "item_id": message_id, "content_index": 0,
             "part": part},
            {"type": "response.output_item.done", "sequence_number": 7,
             "output_index": 0, "item": message},
            {"type": "response.completed", "sequence_number": 8, "response": {
                "id": response_id, "status": "completed", "error": None,
                "incomplete_details": None, "output": output,
                "tools": [], "tool_choice": "none",
            }},
        ]
        return b"".join(
            f"event: {event['type']}\ndata: ".encode()
            + json.dumps(event, separators=(",", ":")).encode() + b"\n\n"
            for event in events
        )

    @classmethod
    def _reasoning_sse(cls, *, text: str = "{}", summary: str = "summary") -> bytes:
        events = [
            json.loads(line[6:]) for line in cls._sse(text=text).decode().splitlines()
            if line.startswith("data: ") and line != "data: [DONE]"
        ]
        for event in events[2:-1]:
            if event.get("output_index") == 0:
                event["output_index"] = 1
        reasoning_id = "rs_fixture"
        summary_part = {"type": "summary_text", "text": summary}
        reasoning_events = [
            {"type": "response.output_item.added", "output_index": 0,
             "item": {
                 "id": reasoning_id, "type": "reasoning", "summary": [],
                 "content": [], "encrypted_content": "opaque-added",
             }},
            {"type": "response.reasoning_summary_part.added", "output_index": 0,
             "item_id": reasoning_id, "summary_index": 0,
             "part": {"type": "summary_text", "text": ""}},
            {"type": "response.reasoning_summary_text.delta", "output_index": 0,
             "item_id": reasoning_id, "summary_index": 0, "delta": summary},
            {"type": "response.reasoning_summary_text.done", "output_index": 0,
             "item_id": reasoning_id, "summary_index": 0, "text": summary},
            {"type": "response.reasoning_summary_part.done", "output_index": 0,
             "item_id": reasoning_id, "summary_index": 0, "part": summary_part},
            {"type": "response.output_item.done", "output_index": 0,
             "item": {
                 "id": reasoning_id, "type": "reasoning",
                 "summary": [summary_part], "content": [],
                 "encrypted_content": "opaque-done",
             }},
        ]
        events = events[:2] + reasoning_events + events[2:]
        for sequence, event in enumerate(events):
            event["sequence_number"] = sequence
        return b"".join(
            f"event: {event['type']}\ndata: ".encode()
            + json.dumps(event, separators=(",", ":")).encode() + b"\n\n"
            for event in events
        )

    def setUp(self) -> None:
        self.root = Path(tempfile.mkdtemp(prefix="answer-blind-login-proxy-", dir="/var/lib"))
        os.chown(self.root, 0, 0)
        os.chmod(self.root, 0o700)
        self.request = self.root / "request.json"
        self.request_value = {
            "model": "gpt-5.6-sol",
            "input": [{"role": "user", "content": [{"type": "input_text", "text": "problem only"}]}],
            "tools": [], "tool_choice": "none", "store": False, "stream": True,
            "reasoning": {"effort": "max", "summary": "auto"},
            "text": {"format": {
                "type": "json_schema", "name": "answer_blind_submission",
                "strict": True,
                "schema": {"type": "object", "properties": {}, "required": [], "additionalProperties": False},
            }},
        }
        self.request.write_bytes(MODULE.canonical(self.request_value))
        os.chown(self.request, 0, 0)
        os.chmod(self.request, 0o400)

    def tearDown(self) -> None:
        shutil.rmtree(self.root)

    def test_discards_caller_body_and_forwards_only_registered_request(self) -> None:
        seen: list[tuple[bytes, dict[str, str]]] = []
        raw_sse = self._sse()

        def upstream(payload: bytes, headers: object):
            assert isinstance(headers, dict)
            seen.append((payload, headers))
            return 200, {"content-type": "text/event-stream"}, raw_sse

        proxy = MODULE.OneShotLoginProxy(
            registered_request=self.request, model="gpt-5.6-sol",
            upstream_call=upstream,
        )
        proxy.start()
        caller = b'{"input":"attacker-controlled","tools":[{"type":"web_search"}]}'
        connection = http.client.HTTPConnection("127.0.0.1", proxy.server.server_port)
        connection.request("POST", "/v1/responses", body=caller, headers={
            "Authorization": "Bearer secret-sentinel",
            "chatgpt-account-id": "account-sentinel",
            "x-openai-internal-codex-responses-lite": "true",
            "Content-Type": "application/json",
        })
        response = connection.getresponse()
        self.assertEqual(response.status, 200)
        self.assertEqual(response.read(), raw_sse)
        connection.close()
        exchange = proxy.wait()
        self.assertEqual(seen[0][0], self.request.read_bytes())
        self.assertEqual(set(seen[0][1]), {"authorization", "chatgpt-account-id"})
        self.assertNotIn(b"attacker-controlled", seen[0][0])
        self.assertEqual(exchange.caller_body_sha256, MODULE._sha(caller))
        self.assertEqual(exchange.forwarded_request_sha256, MODULE._sha(self.request.read_bytes()))
        self.assertEqual(exchange.completed_event_count, 1)
        self.assertNotIn("x-openai-internal-codex-responses-lite", exchange.forwarded_header_names)
        self.assertNotIn(b"secret-sentinel", exchange.normalized_response)

    def test_get_and_options_probes_do_not_consume_the_one_post(self) -> None:
        seen: list[bytes] = []
        raw_sse = self._sse()

        def upstream(payload: bytes, _headers: object):
            seen.append(payload)
            return 200, {"content-type": "text/event-stream"}, raw_sse

        proxy = MODULE.OneShotLoginProxy(
            registered_request=self.request, model="gpt-5.6-sol",
            upstream_call=upstream,
        )
        proxy.start()
        connection = http.client.HTTPConnection("127.0.0.1", proxy.server.server_port)
        for method, path in (("GET", "/"), ("OPTIONS", "/v1/responses")):
            connection.request(method, path)
            response = connection.getresponse()
            self.assertEqual(response.status, 405)
            response.read()

        caller = b'{"probe":"finished"}'
        connection.request("POST", "/v1/responses", body=caller, headers={
            "Authorization": "Bearer secret-sentinel",
            "chatgpt-account-id": "account-sentinel",
            "Content-Type": "application/json",
        })
        response = connection.getresponse()
        self.assertEqual(response.status, 200)
        self.assertEqual(response.read(), raw_sse)
        connection.close()

        exchange = proxy.wait()
        self.assertEqual(seen, [self.request.read_bytes()])
        self.assertEqual(exchange.caller_body_sha256, MODULE._sha(caller))

    def test_malformed_post_is_terminal_and_fail_closed(self) -> None:
        upstream_called = False

        def upstream(_payload: bytes, _headers: object):
            nonlocal upstream_called
            upstream_called = True
            raise AssertionError("malformed POST must not reach upstream")

        proxy = MODULE.OneShotLoginProxy(
            registered_request=self.request, model="gpt-5.6-sol",
            upstream_call=upstream,
        )
        proxy.start()
        connection = http.client.HTTPConnection("127.0.0.1", proxy.server.server_port)
        connection.request("POST", "/wrong-path", body=b"{}", headers={
            "Authorization": "Bearer secret-sentinel",
            "chatgpt-account-id": "account-sentinel",
        })
        response = connection.getresponse()
        self.assertEqual(response.status, 502)
        response.read()
        connection.close()

        with self.assertRaises(MODULE.LoginProxyError):
            proxy.wait()
        self.assertFalse(proxy.thread.is_alive())
        self.assertFalse(upstream_called)

    def test_terminal_sse_error_closes_listener_before_wait(self) -> None:
        failed = {
            "type": "response.failed",
            "response": {
                "status": "failed",
                "error": {"message": "secret response content must not leak"},
            },
        }
        raw_sse = b"data: " + json.dumps(failed, separators=(",", ":")).encode() + b"\n\n"

        def upstream(_payload: bytes, _headers: object):
            return 200, {"content-type": "text/event-stream"}, raw_sse

        proxy = MODULE.OneShotLoginProxy(
            registered_request=self.request, model="gpt-5.6-sol",
            upstream_call=upstream,
        )
        proxy.start()
        connection = http.client.HTTPConnection("127.0.0.1", proxy.server.server_port)
        connection.request("POST", "/v1/responses", body=b"{}", headers={
            "Authorization": "Bearer secret-sentinel",
            "chatgpt-account-id": "account-sentinel",
        })
        response = connection.getresponse()
        self.assertEqual(response.status, 502)
        response.read()
        connection.close()

        proxy.thread.join(2.0)
        self.assertFalse(proxy.thread.is_alive())
        retry = http.client.HTTPConnection(
            "127.0.0.1", proxy.server.server_port, timeout=0.5,
        )
        with self.assertRaises(ConnectionRefusedError):
            retry.request("GET", "/")
        retry.close()
        with self.assertRaises(MODULE.LoginProxyError) as raised:
            proxy.wait()
        self.assertIsNotNone(proxy.failure_evidence)
        self.assertEqual(proxy.failure_evidence.upstream_raw_response, raw_sse)
        self.assertEqual(
            proxy.failure_evidence.response_header_names, ("content-type",),
        )
        self.assertNotIn(
            "secret response content",
            json.dumps(proxy.failure_evidence.response_structure),
        )
        cause = raised.exception.__cause__
        self.assertIsInstance(cause, MODULE.LoginProxyError)
        message = str(cause)
        self.assertIn("framing", message)
        self.assertNotIn("secret response content", message)

    def test_sse_failure_summary_is_bounded_and_sanitized(self) -> None:
        events = []
        for index in range(MODULE.MAX_SSE_METADATA_EVENTS + 5):
            event = {
                "type": f"response.bad event/{index}-" + "x" * 100,
                "status": "incomplete with unsafe whitespace",
                "content": "must-not-appear",
            }
            event["sequence_number"] = index
            events.append(
                f"event: {event['type']}\ndata: ".encode()
                + json.dumps(event).encode() + b"\n\n"
            )
        with self.assertRaises(MODULE.LoginProxyError) as raised:
            MODULE.normalize_completed_sse(b"".join(events))
        message = str(raised.exception)
        self.assertLess(len(message), 1000)
        self.assertIn("unknown", message)
        self.assertNotIn("must-not-appear", message)
        self.assertNotIn("unsafe whitespace", message)

    def test_sse_rejects_duplicate_completion_and_tool_output(self) -> None:
        event = {"type": "response.completed", "response": {"status": "completed", "output": []}}
        line = b"data: " + json.dumps(event).encode() + b"\n\n"
        with self.assertRaises(MODULE.LoginProxyError):
            MODULE.normalize_completed_sse(line + line)
        tool = {"type": "response.completed", "response": {
            "status": "completed", "output": [{"type": "function_call", "name": "web"}],
        }}
        with self.assertRaises(MODULE.LoginProxyError):
            MODULE.normalize_completed_sse(b"data: " + json.dumps(tool).encode() + b"\n\n")

    def test_sse_reconstruction_rejects_sequence_text_and_output_conflicts(self) -> None:
        def events(raw: bytes) -> list[dict[str, object]]:
            return [
                json.loads(line[6:]) for line in raw.decode().splitlines()
                if line.startswith("data: ") and line != "data: [DONE]"
            ]

        def encode(rows: list[dict[str, object]]) -> bytes:
            return b"".join(
                f"event: {row['type']}\ndata: ".encode()
                + json.dumps(row, separators=(",", ":")).encode() + b"\n\n"
                for row in rows
            )

        valid_rows = events(self._sse(text='{"ok":true}'))
        normalized, count = MODULE.normalize_completed_sse(encode(valid_rows))
        value = json.loads(normalized)
        self.assertEqual(count, 1)
        self.assertEqual(value["output"][0]["content"][0]["text"], '{"ok":true}')

        nonempty = json.loads(json.dumps(valid_rows))
        nonempty[-1]["response"]["output"] = [nonempty[-2]["item"]]
        self.assertEqual(
            MODULE.normalize_completed_sse(encode(nonempty))[0], normalized,
        )

        mutations = []
        gap = json.loads(json.dumps(valid_rows))
        gap[4]["sequence_number"] += 1
        mutations.append(("sequence-gap", gap))
        delta = json.loads(json.dumps(valid_rows))
        delta[4]["delta"] += "x"
        mutations.append(("delta-mismatch", delta))
        conflict = json.loads(json.dumps(valid_rows))
        conflict[-1]["response"]["output"] = [{
            **conflict[-2]["item"], "status": "in_progress",
        }]
        mutations.append(("completed-output-conflict", conflict))
        forbidden = json.loads(json.dumps(valid_rows))
        forbidden[2]["item"]["type"] = "function_call"
        mutations.append(("forbidden-item", forbidden))
        for label, rows in mutations:
            with self.subTest(label=label):
                with self.assertRaises(MODULE.LoginProxyError):
                    MODULE.normalize_completed_sse(encode(rows))

        framed = encode(valid_rows).replace(
            b"event: response.output_text.delta",
            b"event: response.output_text.done", 1,
        )
        with self.assertRaises(MODULE.LoginProxyError):
            MODULE.normalize_completed_sse(framed)

    def test_sse_replays_reasoning_summary_and_rejects_lifecycle_mutations(self) -> None:
        def events(raw: bytes) -> list[dict[str, object]]:
            return [
                json.loads(line[6:]) for line in raw.decode().splitlines()
                if line.startswith("data: ") and line != "data: [DONE]"
            ]

        def encode(rows: list[dict[str, object]]) -> bytes:
            for sequence, row in enumerate(rows):
                row["sequence_number"] = sequence
            return b"".join(
                f"event: {row['type']}\ndata: ".encode()
                + json.dumps(row, separators=(",", ":")).encode() + b"\n\n"
                for row in rows
            )

        valid_rows = events(self._reasoning_sse(text='{"ok":true}'))
        normalized, count = MODULE.normalize_completed_sse(encode(valid_rows))
        self.assertEqual(count, 1)
        value = json.loads(normalized)
        self.assertEqual(value["output"][0]["type"], "reasoning")
        self.assertEqual(value["output"][0]["summary"][0]["type"], "summary_text")

        with_keepalive = json.loads(json.dumps(valid_rows))
        with_keepalive.insert(3, {"type": "keepalive"})
        self.assertEqual(
            MODULE.normalize_completed_sse(encode(with_keepalive))[0], normalized,
        )

        mutations: list[tuple[str, list[dict[str, object]]]] = []
        keepalive_extra = json.loads(json.dumps(with_keepalive))
        keepalive_extra[3]["payload"] = "not-empty"
        mutations.append(("keepalive-extra-field", keepalive_extra))
        keepalive_before_active = json.loads(json.dumps(valid_rows))
        keepalive_before_active.insert(2, {"type": "keepalive"})
        mutations.append(("keepalive-before-active-item", keepalive_before_active))
        missing_done = json.loads(json.dumps(valid_rows))
        missing_done = [
            row for row in missing_done
            if row["type"] != "response.reasoning_summary_part.done"
        ]
        mutations.append(("missing-summary-part-done", missing_done))
        delta_mismatch = json.loads(json.dumps(valid_rows))
        next(
            row for row in delta_mismatch
            if row["type"] == "response.reasoning_summary_text.delta"
        )["delta"] += "x"
        mutations.append(("summary-delta-done-mismatch", delta_mismatch))
        bool_done_index = json.loads(json.dumps(valid_rows))
        next(
            row for row in bool_done_index
            if row["type"] == "response.output_item.done"
            and row["item"]["type"] == "reasoning"
        )["output_index"] = False
        mutations.append(("bool-output-index", bool_done_index))
        bool_summary_index = json.loads(json.dumps(valid_rows))
        next(
            row for row in bool_summary_index
            if row["type"] == "response.reasoning_summary_text.delta"
        )["summary_index"] = False
        mutations.append(("bool-summary-index", bool_summary_index))
        bool_content_index = json.loads(json.dumps(valid_rows))
        next(
            row for row in bool_content_index
            if row["type"] == "response.content_part.added"
        )["content_index"] = False
        mutations.append(("bool-content-index", bool_content_index))

        for label, rows in mutations:
            with self.subTest(label=label):
                with self.assertRaises(MODULE.LoginProxyError):
                    MODULE.normalize_completed_sse(encode(rows))

    def test_registered_request_must_be_canonical_and_tool_free(self) -> None:
        self.request.chmod(0o600)
        with self.assertRaises(MODULE.LoginProxyError):
            MODULE.OneShotLoginProxy(registered_request=self.request, model="gpt-5.6-sol")


if __name__ == "__main__":
    unittest.main()
