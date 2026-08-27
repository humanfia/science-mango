#!/usr/bin/env python3
"""Run the credential-holding loopback broker for answer-blind model calls.

The solver process receives only a fixed public dummy token and a loopback
URL.  This controller keeps the real provider token out of the solver's
environment, home directory, argv, logs, and process tree.  A root supervisor
passes the token over an anonymous pipe to a dedicated non-root worker, writes
the immutable ready receipt, and writes a hash-only transcript after shutdown.

The broker is deliberately not a general HTTP proxy.  It accepts only the
Responses endpoint for the GPT variant and the Messages/count-tokens endpoints
for the Kimi-K3 variant, requires the configured model in every JSON request,
and forwards to one pinned HTTPS upstream.
"""

from __future__ import annotations

import argparse
import base64
import binascii
import encodings.idna  # preload before the worker drops access to controller paths
import hashlib
import http.client
import http.server
import json
import os
import pwd
import resource
import selectors
import signal
import socket
import stat
import sys
import threading
import time
import urllib.parse
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping, NoReturn


SCHEMA_VERSION = 1
PROTOCOL = "icho-answer-blind-v1"
PUBLIC_DUMMY_TOKEN = "answer-blind-public-dummy-token"
MAX_REQUEST_BYTES = 64 * 1024 * 1024
MAX_RESPONSE_BYTES = 256 * 1024 * 1024
SAFE_RUN_ID = __import__("re").compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,127}$")
SHA256 = __import__("re").compile(r"^[0-9a-f]{64}$")

VARIANTS: Mapping[str, Mapping[str, Any]] = {
    "gpt": {
        "paths": frozenset({"/v1/responses"}),
        "default_upstream": "https://chatgpt.com/backend-api/codex/responses",
    },
    "kimi-k3": {
        "paths": frozenset({"/v1/messages", "/v1/messages/count_tokens"}),
        "default_upstream": "https://api.moonshot.cn/anthropic",
    },
}

READY_FIELDS = {
    "schema_version",
    "protocol",
    "phase",
    "variant",
    "run_id",
    "listen_url",
    "upstream_origin",
    "allowed_model",
    "request_profile",
    "public_dummy_key_sha256",
    "broker_uid",
    "broker_binary_sha256",
    "started_at",
}
TRANSCRIPT_FIELDS = {
    "schema_version",
    "protocol",
    "phase",
    "variant",
    "run_id",
    "request_profile",
    "ready_receipt_sha256",
    "request_count",
    "request_response_chain_sha256",
    "started_at",
    "stopped_at",
    "broker_stopped",
}

REQUEST_PROFILES = frozenset({
    "agent_harness_v1",
    "tool_free_structured_solver_v1",
    "tool_free_structured_independent_review_v1",
})

_FORBIDDEN_REMOTE_KEY_TOKENS = {
    "url",
    "uri",
    "file",
    "fileid",
    "fileurl",
    "imageurl",
    "previousresponseid",
    "conversation",
    "conversationid",
    "websearch",
    "browser",
    "computer",
    "codeinterpreter",
    "mcp",
    "connector",
}
_GPT_LOCAL_TOOL_TYPES = frozenset({"function", "custom", "local_shell"})
_KIMI_LOCAL_TOOL_TYPES = frozenset({"function", "custom"})


class BrokerError(RuntimeError):
    """A fail-closed broker/controller invariant was violated."""


def _fail(message: str) -> NoReturn:
    raise BrokerError(message)


def _utcnow() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _canonical_json_bytes(value: Mapping[str, Any]) -> bytes:
    return (
        json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n"
    ).encode("utf-8")


def _pretty_json_bytes(value: Mapping[str, Any]) -> bytes:
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=False) + "\n").encode(
        "utf-8"
    )


def _sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _plain_file(path: Path, *, label: str) -> Path:
    if path.is_symlink() or not path.is_file():
        _fail(f"{label} must be a plain file: {path}")
    return path.resolve(strict=True)


def _controller_dir(path: Path) -> Path:
    if path.is_symlink() or not path.is_dir():
        _fail(f"controller directory must be a plain directory: {path}")
    root = path.resolve(strict=True)
    metadata = root.stat()
    if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) != 0o700:
        _fail("controller directory must be root-owned mode 0700")
    return root


def _atomic_root_file(path: Path, payload: bytes, *, mode: int = 0o400) -> None:
    if path.exists() or path.is_symlink():
        _fail(f"controller artifact must be new: {path}")
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    descriptor = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        with os.fdopen(descriptor, "wb", closefd=False) as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
    finally:
        os.close(descriptor)
    os.chown(temporary, 0, 0)
    os.chmod(temporary, mode)
    os.replace(temporary, path)


def _process_start_ticks(pid: int) -> int:
    """Return Linux /proc start ticks, robust to spaces in ``comm``."""

    raw = Path(f"/proc/{pid}/stat").read_text(encoding="utf-8")
    closing = raw.rfind(")")
    if closing < 0:
        _fail(f"malformed process stat for pid {pid}")
    fields_after_comm = raw[closing + 2 :].split()
    # The first token after comm is field 3 (state); starttime is field 22.
    if len(fields_after_comm) < 20:
        _fail(f"truncated process stat for pid {pid}")
    return int(fields_after_comm[19])


def _load_token(path: Path, *, token_format: str, token_name: str | None) -> str:
    source = _plain_file(path, label="provider credential file")
    metadata = source.stat()
    if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) & 0o077:
        _fail("provider credential file must be root-owned with no group/other access")
    payload = source.read_text(encoding="utf-8")
    value: object
    if token_format == "raw":
        value = payload.strip()
    elif token_format == "json":
        if not token_name:
            _fail("--token-name is required for JSON credentials")
        document = json.loads(payload)
        value = document.get(token_name) if isinstance(document, dict) else None
    elif token_format == "env":
        if not token_name:
            _fail("--token-name is required for env credentials")
        found: list[str] = []
        for raw in payload.splitlines():
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            if line.startswith("export "):
                line = line[7:]
            name, separator, candidate = line.partition("=")
            if separator and name.strip() == token_name:
                found.append(candidate.strip().strip("'\""))
        value = found[0] if len(found) == 1 else None
    else:  # pragma: no cover - argparse closes this path
        _fail(f"unsupported credential format: {token_format}")
    if not isinstance(value, str) or not value or "\n" in value or "\r" in value:
        _fail("provider credential is missing or malformed")
    if value == PUBLIC_DUMMY_TOKEN:
        _fail("real provider credential may not equal the public dummy token")
    return value


def _validate_upstream(variant: str, raw: str) -> urllib.parse.SplitResult:
    parsed = urllib.parse.urlsplit(raw)
    if (
        parsed.scheme != "https"
        or not parsed.hostname
        or parsed.username
        or parsed.password
        or parsed.fragment
        or parsed.query
    ):
        _fail("upstream must be an absolute credential-free HTTPS URL")
    expected = urllib.parse.urlsplit(str(VARIANTS[variant]["default_upstream"]))
    if (parsed.scheme, parsed.hostname, parsed.port, parsed.path.rstrip("/")) != (
        expected.scheme,
        expected.hostname,
        expected.port,
        expected.path.rstrip("/"),
    ):
        _fail(f"unexpected {variant} upstream; release endpoint must be pinned")
    return parsed


def _target_path(variant: str, upstream: urllib.parse.SplitResult, request_path: str) -> str:
    if variant == "gpt":
        return upstream.path
    suffix = request_path.removeprefix("/v1/")
    return upstream.path.rstrip("/") + "/v1/" + suffix


def _dummy_authorized(headers: http.client.HTTPMessage) -> bool:
    authorization = headers.get("Authorization", "")
    api_key = headers.get("x-api-key", "")
    return authorization == f"Bearer {PUBLIC_DUMMY_TOKEN}" or api_key == PUBLIC_DUMMY_TOKEN


def _request_model(payload: object) -> str | None:
    if not isinstance(payload, dict):
        return None
    model = payload.get("model")
    return model if isinstance(model, str) and model else None


def _reject_duplicate_object_pairs(
    pairs: list[tuple[str, object]],
) -> dict[str, object]:
    """Build one JSON object while rejecting parser-differential duplicates."""

    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            _fail(f"provider request repeats JSON object key: {key}")
        result[key] = value
    return result


def _reject_json_constant(value: str) -> NoReturn:
    _fail(f"provider request contains a non-JSON numeric constant: {value}")


def _parse_provider_json(body: bytes) -> tuple[dict[str, object], bytes]:
    """Parse strict UTF-8 JSON and return a canonical body for forwarding.

    Forwarding the parsed-and-reencoded object, rather than the client bytes,
    prevents a provider parser from resolving duplicate keys or non-finite
    number extensions differently from this authorization layer.
    """

    try:
        text = body.decode("utf-8", errors="strict")
        value = json.loads(
            text,
            object_pairs_hook=_reject_duplicate_object_pairs,
            parse_constant=_reject_json_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise BrokerError("request body must be strict UTF-8 JSON") from exc
    if not isinstance(value, dict):
        _fail("provider request root must be a JSON object")
    canonical = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")
    if len(canonical) > MAX_REQUEST_BYTES:
        _fail("canonical provider request exceeds the broker limit")
    return value, canonical


def _normalized_key(value: object) -> str:
    return "".join(character.lower() for character in str(value) if character.isalnum())


def _validate_local_tools(value: object, *, variant: str) -> None:
    """Allow only schemas for tools that the local harness must execute.

    This is intentionally an allowlist.  A denylist would silently authorize
    newly introduced provider-hosted tools such as ``tool_search``, web fetch,
    or code execution.
    """

    if value is None:
        return
    if not isinstance(value, list):
        _fail("provider request tools must be a JSON array")
    for index, item in enumerate(value):
        if not isinstance(item, dict):
            _fail(f"provider request tool {index} must be an object")
        raw_type = item.get("type")
        if variant == "gpt":
            if raw_type not in _GPT_LOCAL_TOOL_TYPES:
                _fail(f"GPT tool {index} is not a local function/custom tool")
            if raw_type != "local_shell" and (
                not isinstance(item.get("name"), str) or not item["name"].strip()
            ):
                _fail(f"GPT tool {index} has no local tool name")
            if raw_type == "function" and not isinstance(item.get("parameters"), dict):
                _fail(f"GPT function tool {index} has no JSON parameter schema")
        else:
            # Anthropic client-side tools conventionally omit ``type`` and
            # carry a name/input_schema.  Explicit function/custom is accepted
            # for compatible clients, but every other present/future hosted
            # type is rejected.
            if raw_type is not None and raw_type not in _KIMI_LOCAL_TOOL_TYPES:
                _fail(f"Kimi tool {index} is not a local client tool")
            if not isinstance(item.get("name"), str) or not item["name"].strip():
                _fail(f"Kimi tool {index} has no local tool name")
            if not isinstance(item.get("input_schema"), dict):
                _fail(f"Kimi tool {index} has no JSON input schema")


def _safe_inline_image(value: object) -> bool:
    if not isinstance(value, str):
        return False
    prefixes = (
        "data:image/png;base64,",
        "data:image/jpeg;base64,",
        "data:image/webp;base64,",
    )
    prefix = next((item for item in prefixes if value.startswith(item)), None)
    if prefix is None:
        return False
    encoded = value[len(prefix) :]
    if not encoded or len(encoded) > 48 * 1024 * 1024:
        return False
    try:
        base64.b64decode(encoded, validate=True)
    except (ValueError, binascii.Error):
        return False
    return True


def _validate_structured_profile(value: object, *, variant: str) -> None:
    """Require a tool-free, stateless, schema-constrained model request."""

    if not isinstance(value, dict):
        _fail("structured solver request root must be an object")
    if value.get("tools") != []:
        _fail("structured solver request must contain tools=[]")
    for key in ("previous_response_id", "conversation", "conversation_id"):
        if key in value:
            _fail(f"structured solver request may not contain {key}")
    if variant == "gpt":
        if value.get("store") is not False:
            _fail("structured GPT request requires store=false")
        text = value.get("text")
        output_format = text.get("format") if isinstance(text, dict) else None
        if (
            not isinstance(output_format, dict)
            or output_format.get("type") != "json_schema"
            or output_format.get("strict") is not True
            or not isinstance(output_format.get("name"), str)
            or not isinstance(output_format.get("schema"), dict)
        ):
            _fail("structured GPT request requires strict text.format json_schema")
    else:
        # Kimi's Anthropic-compatible endpoint does not consistently expose a
        # provider-enforced JSON-schema field.  The trusted controller still
        # parses one exact JSON object against the same local schema; the
        # broker's security property is that no provider/server tool or state
        # handle is available.
        messages = value.get("messages")
        if not isinstance(messages, list) or not messages:
            _fail("structured Kimi request requires a nonempty messages array")


def _validate_provider_request(
    value: object, *, variant: str, request_profile: str = "agent_harness_v1",
    path: str = "$"
) -> None:
    """Reject provider-hosted retrieval/tools and remote resource references.

    The broker cannot rely on an agent prompt to prevent a model from asking
    its provider to browse or fetch a URL.  Only client-side function tools are
    allowed; all URL/file/stateful-response fields fail closed recursively.
    """

    if path == "$":
        if not isinstance(value, dict):
            _fail("provider request root must be a JSON object")
        if request_profile in {
            "tool_free_structured_solver_v1",
            "tool_free_structured_independent_review_v1",
        }:
            _validate_structured_profile(value, variant=variant)
        _validate_local_tools(value.get("tools"), variant=variant)

    if isinstance(value, dict):
        for key, child in value.items():
            token = _normalized_key(key)
            if (
                request_profile in {
                    "tool_free_structured_solver_v1",
                    "tool_free_structured_independent_review_v1",
                }
                and variant == "gpt"
                and token == "imageurl"
                and _safe_inline_image(child)
            ):
                continue
            if token in _FORBIDDEN_REMOTE_KEY_TOKENS or any(
                marker in token
                for marker in (
                    "websearch",
                    "remoteurl",
                    "fileurl",
                    "imageurl",
                    "previousresponse",
                    "codeinterpreter",
                )
            ):
                _fail(f"provider request contains forbidden remote field {path}.{key}")
            _validate_provider_request(
                child, variant=variant, request_profile=request_profile,
                path=f"{path}.{key}",
            )
        return
    if isinstance(value, list):
        for index, child in enumerate(value):
            _validate_provider_request(
                child, variant=variant, request_profile=request_profile,
                path=f"{path}[{index}]",
            )
        return
    if isinstance(value, str):
        # Claude Code annotates each local tool's input schema with this exact
        # JSON Schema dialect URI.  It is inert schema metadata, not a
        # provider-side fetch/resource handle.  Permit only the fixed value at
        # the fixed local-tool schema location; every other URL remains closed.
        if (
            variant == "kimi-k3"
            and request_profile == "agent_harness_v1"
            and value == "https://json-schema.org/draft/2020-12/schema"
            and __import__("re").fullmatch(
                r"\$\.tools\[\d+\]\.input_schema\.\$schema", path
            )
        ):
            return
        stripped = value.strip().lower()
        if stripped.startswith(("http://", "https://", "file://", "data:")):
            _fail(f"provider request contains a remote/resource reference at {path}")


class _BrokerState:
    def __init__(
        self,
        *,
        variant: str,
        run_id: str,
        model: str,
        upstream: urllib.parse.SplitResult,
        token: str,
        event_fd: int,
        binary_sha256: str,
        broker_uid: int,
        request_profile: str,
    ) -> None:
        self.variant = variant
        self.run_id = run_id
        self.model = model
        self.upstream = upstream
        self.token = token
        self.event_fd = event_fd
        self.binary_sha256 = binary_sha256
        self.broker_uid = broker_uid
        self.request_profile = request_profile
        self.started_at = _utcnow()
        self.sequence = 0
        self.lock = threading.Lock()

    def next_sequence(self) -> int:
        with self.lock:
            self.sequence += 1
            return self.sequence

    def event(self, payload: Mapping[str, Any]) -> None:
        data = _canonical_json_bytes(dict(payload))
        if len(data) > 4096:
            raise BrokerError("internal broker event exceeds atomic pipe limit")
        with self.lock:
            os.write(self.event_fd, data)


class _BrokerServer(http.server.ThreadingHTTPServer):
    daemon_threads = True
    allow_reuse_address = False

    def __init__(self, address: tuple[str, int], state: _BrokerState):
        self.state = state
        super().__init__(address, _BrokerHandler)


class _BrokerHandler(http.server.BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "AnswerBlindModelBroker/1"

    @property
    def state(self) -> _BrokerState:
        return self.server.state  # type: ignore[attr-defined,no-any-return]

    def log_message(self, _format: str, *args: object) -> None:
        del args

    def _json_error(self, status: int, message: str) -> None:
        payload = _canonical_json_bytes({"error": {"message": message, "type": "broker_error"}})
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(payload)))
        self.send_header("Connection", "close")
        self.end_headers()
        self.wfile.write(payload)
        self.close_connection = True

    def do_GET(self) -> None:  # noqa: N802 - BaseHTTPRequestHandler API
        path = urllib.parse.urlsplit(self.path).path
        if path != "/__answer_blind_health" or not _dummy_authorized(self.headers):
            self._json_error(404, "not found")
            return
        payload = _canonical_json_bytes(
            {
                "schema_version": SCHEMA_VERSION,
                "protocol": PROTOCOL,
                "phase": "model_broker_health",
                "variant": self.state.variant,
                "run_id": self.state.run_id,
                "allowed_model": self.state.model,
                "broker_binary_sha256": self.state.binary_sha256,
                "request_profile": self.state.request_profile,
            }
        )
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(payload)))
        self.send_header("Connection", "close")
        self.end_headers()
        self.wfile.write(payload)
        self.close_connection = True

    def do_POST(self) -> None:  # noqa: N802 - BaseHTTPRequestHandler API
        parsed_path = urllib.parse.urlsplit(self.path)
        # Claude Code 2.1.x appends this fixed compatibility query to its
        # Anthropic Messages calls. It carries no resource, state, or hosted
        # tool authority. Keep every other query fail-closed.
        allowed_query = (
            self.state.variant == "kimi-k3"
            and self.state.request_profile == "agent_harness_v1"
            and parsed_path.query == "beta=true"
        )
        if (
            parsed_path.query not in {"", "beta=true"}
            or (parsed_path.query and not allowed_query)
            or parsed_path.path not in VARIANTS[self.state.variant]["paths"]
        ):
            self._json_error(404, "endpoint is not allowlisted")
            return
        if not _dummy_authorized(self.headers):
            self._json_error(401, "invalid public broker credential")
            return
        raw_length = self.headers.get("Content-Length")
        try:
            length = int(raw_length or "")
        except ValueError:
            self._json_error(411, "a valid Content-Length is required")
            return
        if length <= 0 or length > MAX_REQUEST_BYTES:
            self._json_error(413, "request body size is invalid")
            return
        body = self.rfile.read(length)
        if len(body) != length:
            self._json_error(400, "truncated request body")
            return
        try:
            document, body = _parse_provider_json(body)
        except BrokerError:
            self._json_error(400, "request body must be UTF-8 JSON")
            return
        if _request_model(document) != self.state.model:
            self._json_error(400, "request model differs from the pinned model")
            return
        try:
            _validate_provider_request(
                document, variant=self.state.variant,
                request_profile=self.state.request_profile,
            )
        except BrokerError:
            self._json_error(400, "request contains forbidden hosted retrieval/state")
            return
        if self.state.variant == "gpt":
            if not isinstance(document, dict) or document.get("store") not in {False, None}:
                self._json_error(400, "GPT broker requires store=false or omitted")
                return

        sequence = self.state.next_sequence()
        request_sha = _sha256_bytes(body)
        response_digest = hashlib.sha256()
        response_bytes = 0
        response_status = 502
        completed = False
        try:
            port = self.state.upstream.port or 443
            connection = http.client.HTTPSConnection(
                self.state.upstream.hostname, port=port, timeout=600
            )
            upstream_headers = {
                "Authorization": f"Bearer {self.state.token}",
                "Content-Type": "application/json",
                "Accept": self.headers.get("Accept", "application/json"),
                "Accept-Encoding": "identity",
                "User-Agent": "answer-blind-model-broker/1",
            }
            for name in ("anthropic-version", "anthropic-beta", "openai-beta"):
                value = self.headers.get(name)
                if value:
                    upstream_headers[name] = value
            target = _target_path(self.state.variant, self.state.upstream, parsed_path.path)
            if parsed_path.query:
                target += "?" + parsed_path.query
            connection.request("POST", target, body=body, headers=upstream_headers)
            response = connection.getresponse()
            response_status = response.status
            self.send_response(response.status, response.reason)
            for name in ("content-type", "cache-control", "x-request-id", "request-id"):
                value = response.getheader(name)
                if value:
                    self.send_header(name, value)
            self.send_header("Connection", "close")
            self.end_headers()
            while True:
                block = response.read(64 * 1024)
                if not block:
                    break
                response_bytes += len(block)
                if response_bytes > MAX_RESPONSE_BYTES:
                    raise BrokerError("upstream response exceeded the broker limit")
                response_digest.update(block)
                self.wfile.write(block)
                self.wfile.flush()
            completed = True
            connection.close()
        except (OSError, http.client.HTTPException, BrokerError) as exc:
            if response_bytes == 0:
                try:
                    self._json_error(502, f"upstream request failed: {type(exc).__name__}")
                except OSError:
                    pass
        finally:
            self.close_connection = True
            self.state.event(
                {
                    "type": "request",
                    "sequence": sequence,
                    "path": parsed_path.path,
                    "request_sha256": request_sha,
                    "response_sha256": response_digest.hexdigest(),
                    "response_status": response_status,
                    "response_bytes": response_bytes,
                    "completed": completed,
                }
            )


def _drop_to_user(user: str) -> tuple[int, int]:
    record = pwd.getpwnam(user)
    if record.pw_uid == 0:
        _fail("broker worker must use a dedicated non-root UID")
    os.setgroups([])
    os.setgid(record.pw_gid)
    os.setuid(record.pw_uid)
    return record.pw_uid, record.pw_gid


def _harden_worker_process(*, keep_fds: set[int]) -> None:
    """Strip inherited authority before a credential enters the worker."""

    library = __import__("ctypes").CDLL(None, use_errno=True)
    # Parent death must synchronously remove the only process holding the real
    # token/listener.  DUMPABLE=0 blocks same-UID ptrace and /proc environ.
    if library.prctl(1, signal.SIGKILL, 0, 0, 0) != 0:  # PR_SET_PDEATHSIG
        error = __import__("ctypes").get_errno()
        raise OSError(error, os.strerror(error))
    if library.prctl(4, 0, 0, 0, 0) != 0:  # PR_SET_DUMPABLE
        error = __import__("ctypes").get_errno()
        raise OSError(error, os.strerror(error))
    if os.getppid() == 1:
        raise BrokerError("broker supervisor died before worker hardening")
    for name in list(os.environ):
        os.environ.pop(name, None)
    os.environ.update(
        {
            "HOME": "/nonexistent",
            "PATH": "",
            "LANG": "C.UTF-8",
            "LC_ALL": "C.UTF-8",
            "PYTHONNOUSERSITE": "1",
            "PYTHONDONTWRITEBYTECODE": "1",
        }
    )
    soft_limit = resource.getrlimit(resource.RLIMIT_NOFILE)[0]
    max_fd = min(int(soft_limit if soft_limit != resource.RLIM_INFINITY else 65536), 65536)
    for descriptor in range(3, max_fd):
        if descriptor not in keep_fds:
            try:
                os.close(descriptor)
            except OSError:
                pass


def _rearm_worker_lifecycle() -> None:
    """Credential worker lifecycle controls must be set after setuid/setgid.

    Linux clears the parent-death signal across credential changes, so setting
    it only while root would leave an orphanable token-holding worker.
    """

    library = __import__("ctypes").CDLL(None, use_errno=True)
    for option, value, label in (
        (1, signal.SIGKILL, "PR_SET_PDEATHSIG"),
        (4, 0, "PR_SET_DUMPABLE"),
    ):
        if library.prctl(option, value, 0, 0, 0) != 0:
            error = __import__("ctypes").get_errno()
            raise OSError(error, f"{label}: {os.strerror(error)}")
    if os.getppid() == 1:
        raise BrokerError("broker supervisor died while worker dropped privilege")


def _worker(
    *,
    variant: str,
    run_id: str,
    model: str,
    upstream_raw: str,
    token_fd: int,
    event_fd: int,
    broker_user: str,
    port: int,
    binary_sha256: str,
    request_profile: str,
) -> NoReturn:
    _harden_worker_process(keep_fds={token_fd, event_fd})
    upstream = _validate_upstream(variant, upstream_raw)
    uid, _gid = _drop_to_user(broker_user)
    _rearm_worker_lifecycle()
    token_payload = b""
    while len(token_payload) <= 64 * 1024:
        block = os.read(token_fd, 4096)
        if not block:
            break
        token_payload += block
    os.close(token_fd)
    try:
        token = token_payload.decode("utf-8").strip()
    finally:
        token_payload = b""
    if not token or token == PUBLIC_DUMMY_TOKEN:
        _fail("worker did not receive a real provider credential")
    state = _BrokerState(
        variant=variant,
        run_id=run_id,
        model=model,
        upstream=upstream,
        token=token,
        event_fd=event_fd,
        binary_sha256=binary_sha256,
        broker_uid=uid,
        request_profile=request_profile,
    )
    server = _BrokerServer(("127.0.0.1", port), state)

    def stop(_signum: int, _frame: object) -> None:
        server.server_close()
        raise SystemExit(0)

    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    actual_port = int(server.server_address[1])
    base_url = f"http://127.0.0.1:{actual_port}"
    # Codex and the tool-free structured clients take an API-prefix URL.
    # Claude Code treats ANTHROPIC_BASE_URL as an origin/base path and appends
    # /v1/messages itself, so a trailing /v1 would become /v1/v1/messages.
    listen_url = (
        base_url
        if variant == "kimi-k3" and request_profile == "agent_harness_v1"
        else base_url + "/v1"
    )
    state.event(
        {
            "type": "ready",
            "listen_url": listen_url,
            "started_at": state.started_at,
            "broker_uid": uid,
        }
    )
    try:
        server.serve_forever(poll_interval=0.25)
    finally:
        server.server_close()
        state.token = ""
        try:
            state.event({"type": "stopped", "stopped_at": _utcnow()})
        finally:
            os.close(event_fd)
    raise SystemExit(0)


def _supervisor(
    *,
    controller: Path,
    variant: str,
    run_id: str,
    model: str,
    upstream: str,
    token: str,
    broker_user: str,
    port: int,
    binary_sha256: str,
    notify_fd: int,
    lease_parent_pid: int,
    lease_parent_start_ticks: int,
    request_profile: str,
) -> NoReturn:
    # The broker is an invocation-scoped credential proxy.  It must not
    # outlive the root launcher that created it, even if that launcher is
    # SIGKILLed before its normal ``finally: stop`` path can run.
    library = __import__("ctypes").CDLL(None, use_errno=True)
    if library.prctl(1, signal.SIGKILL, 0, 0, 0) != 0:  # PR_SET_PDEATHSIG
        error = __import__("ctypes").get_errno()
        raise OSError(error, f"broker supervisor PR_SET_PDEATHSIG: {os.strerror(error)}")
    if (
        os.getppid() != lease_parent_pid
        or _process_start_ticks(lease_parent_pid) != lease_parent_start_ticks
    ):
        raise BrokerError("broker launcher died or changed before lease arming")

    token_read, token_write = os.pipe()
    event_read, event_write = os.pipe()
    worker_pid = os.fork()
    if worker_pid == 0:
        os.close(token_write)
        os.close(event_read)
        try:
            _worker(
                variant=variant,
                run_id=run_id,
                model=model,
                upstream_raw=upstream,
                token_fd=token_read,
                event_fd=event_write,
                broker_user=broker_user,
                port=port,
                binary_sha256=binary_sha256,
                request_profile=request_profile,
            )
        except SystemExit as exc:
            code = exc.code if isinstance(exc.code, int) else 1
            os._exit(code)
        except BaseException as exc:
            try:
                os.write(
                    event_write,
                    _canonical_json_bytes(
                        {
                            "type": "fatal",
                            "error": type(exc).__name__,
                            "detail": str(exc)[:512],
                        }
                    ),
                )
            except OSError:
                pass
            os._exit(125)

    os.close(token_read)
    os.close(event_write)
    os.write(token_write, token.encode("utf-8"))
    os.close(token_write)
    token = ""

    ready_path = controller / f"{variant}-model-broker-ready.json"
    transcript_path = controller / f"{variant}-model-broker-transcript.json"
    state_path = controller / f"{variant}-model-broker-state.json"
    started_at = ""
    ready_sha = ""
    request_count = 0
    chain = "0" * 64
    stopping = False
    fatal_error = ""
    selector = selectors.DefaultSelector()
    selector.register(event_read, selectors.EVENT_READ)
    buffer = b""

    def request_stop(_signum: int, _frame: object) -> None:
        nonlocal stopping
        stopping = True
        try:
            os.kill(worker_pid, signal.SIGTERM)
        except ProcessLookupError:
            pass

    signal.signal(signal.SIGTERM, request_stop)
    signal.signal(signal.SIGINT, request_stop)
    _atomic_root_file(
        state_path,
        _pretty_json_bytes(
            {
                "schema_version": SCHEMA_VERSION,
                "protocol": PROTOCOL,
                "phase": "model_broker_state",
                "variant": variant,
                "run_id": run_id,
                "supervisor_pid": os.getpid(),
                "supervisor_start_ticks": _process_start_ticks(os.getpid()),
                "lease_parent_pid": lease_parent_pid,
                "lease_parent_start_ticks": lease_parent_start_ticks,
                "worker_pid": worker_pid,
            }
        ),
        mode=0o400,
    )

    exit_status: int | None = None
    readiness_started = time.monotonic()
    try:
        while exit_status is None:
            for _key, _mask in selector.select(timeout=0.25):
                block = os.read(event_read, 8192)
                if not block:
                    selector.unregister(event_read)
                    break
                buffer += block
                while b"\n" in buffer:
                    raw, buffer = buffer.split(b"\n", 1)
                    if not raw:
                        continue
                    event = json.loads(raw)
                    kind = event.get("type")
                    if kind == "ready":
                        if ready_sha:
                            raise BrokerError("broker emitted duplicate readiness")
                        started_at = str(event["started_at"])
                        parsed_upstream = urllib.parse.urlsplit(upstream)
                        origin = f"{parsed_upstream.scheme}://{parsed_upstream.hostname}"
                        if parsed_upstream.port:
                            origin += f":{parsed_upstream.port}"
                        ready = {
                            "schema_version": SCHEMA_VERSION,
                            "protocol": PROTOCOL,
                            "phase": "model_broker_ready",
                            "variant": variant,
                            "run_id": run_id,
                            "listen_url": event["listen_url"],
                            "upstream_origin": origin,
                            "allowed_model": model,
                            "request_profile": request_profile,
                            "public_dummy_key_sha256": _sha256_bytes(PUBLIC_DUMMY_TOKEN.encode()),
                            "broker_uid": event["broker_uid"],
                            "broker_binary_sha256": binary_sha256,
                            "started_at": started_at,
                        }
                        if set(ready) != READY_FIELDS:
                            raise AssertionError("ready schema drift")
                        payload = _pretty_json_bytes(ready)
                        ready_sha = _sha256_bytes(payload)
                        _atomic_root_file(ready_path, payload)
                        os.write(notify_fd, _canonical_json_bytes({"ok": True, "ready": str(ready_path), "sha256": ready_sha}))
                        os.close(notify_fd)
                        notify_fd = -1
                    elif kind == "request":
                        if not ready_sha:
                            raise BrokerError("request arrived before broker readiness")
                        request_count += 1
                        material = {
                            key: event[key]
                            for key in (
                                "sequence", "path", "request_sha256", "response_sha256",
                                "response_status", "response_bytes", "completed",
                            )
                        }
                        chain = _sha256_bytes(bytes.fromhex(chain) + _canonical_json_bytes(material))
                    elif kind == "fatal":
                        fatal_error = (
                            f"{event.get('error', 'Error')}: "
                            f"{event.get('detail', '')}"
                        ).strip()
                        stopping = True
                    elif kind == "stopped":
                        stopping = True
            waited, status = os.waitpid(worker_pid, os.WNOHANG)
            if waited == worker_pid:
                exit_status = status
            if not ready_sha and time.monotonic() - readiness_started > 20:
                request_stop(signal.SIGTERM, None)
        broker_stopped = bool(os.WIFEXITED(exit_status) and os.WEXITSTATUS(exit_status) == 0)
        if ready_sha:
            transcript = {
                "schema_version": SCHEMA_VERSION,
                "protocol": PROTOCOL,
                "phase": "model_broker_transcript",
                "variant": variant,
                "run_id": run_id,
                "request_profile": request_profile,
                "ready_receipt_sha256": ready_sha,
                "request_count": request_count,
                "request_response_chain_sha256": chain,
                "started_at": started_at,
                "stopped_at": _utcnow(),
                "broker_stopped": broker_stopped,
            }
            if set(transcript) != TRANSCRIPT_FIELDS:
                raise AssertionError("transcript schema drift")
            _atomic_root_file(transcript_path, _pretty_json_bytes(transcript))
    finally:
        if notify_fd >= 0:
            try:
                os.write(
                    notify_fd,
                    _canonical_json_bytes(
                        {
                            "ok": False,
                            "error": fatal_error or "broker failed before readiness",
                        }
                    ),
                )
                os.close(notify_fd)
            except OSError:
                pass
        try:
            selector.close()
        finally:
            os.close(event_read)
    raise SystemExit(0 if ready_sha and broker_stopped else 1)


def start_broker(
    *,
    controller_dir: Path,
    variant: str,
    run_id: str,
    model: str,
    upstream: str,
    credential_file: Path,
    credential_format: str,
    token_name: str | None,
    broker_user: str,
    port: int,
    request_profile: str = "agent_harness_v1",
) -> dict[str, Any]:
    if os.geteuid() != 0:
        _fail("broker controller must run as root")
    if variant not in VARIANTS or SAFE_RUN_ID.fullmatch(run_id) is None:
        _fail("invalid broker variant/run id")
    if request_profile not in REQUEST_PROFILES:
        _fail("unsupported model broker request profile")
    if not model or any(character.isspace() for character in model):
        _fail("model id is empty or malformed")
    _validate_upstream(variant, upstream)
    pwd.getpwnam(broker_user)
    controller = _controller_dir(controller_dir)
    for suffix in ("ready.json", "transcript.json", "state.json"):
        path = controller / f"{variant}-model-broker-{suffix}"
        if path.exists() or path.is_symlink():
            _fail(f"broker controller artifact already exists: {path}")
    token = _load_token(
        credential_file, token_format=credential_format, token_name=token_name
    )
    binary = _plain_file(Path(__file__), label="broker binary")
    binary_sha = _sha256_file(binary)
    lease_parent_pid = os.getpid()
    lease_parent_start_ticks = _process_start_ticks(lease_parent_pid)
    notify_read, notify_write = os.pipe()
    supervisor_pid = os.fork()
    if supervisor_pid == 0:
        os.close(notify_read)
        try:
            os.setsid()
            _supervisor(
                controller=controller,
                variant=variant,
                run_id=run_id,
                model=model,
                upstream=upstream,
                token=token,
                broker_user=broker_user,
                port=port,
                binary_sha256=binary_sha,
                notify_fd=notify_write,
                lease_parent_pid=lease_parent_pid,
                lease_parent_start_ticks=lease_parent_start_ticks,
                request_profile=request_profile,
            )
        except BaseException:
            try:
                os.write(notify_write, _canonical_json_bytes({"ok": False, "error": "supervisor failed"}))
            except OSError:
                pass
            os._exit(125)
    os.close(notify_write)
    token = ""
    selector = selectors.DefaultSelector()
    selector.register(notify_read, selectors.EVENT_READ)
    deadline = time.monotonic() + 25
    payload = b""
    while time.monotonic() < deadline and b"\n" not in payload:
        if selector.select(timeout=0.25):
            block = os.read(notify_read, 8192)
            if not block:
                break
            payload += block
    selector.close()
    os.close(notify_read)
    if b"\n" not in payload:
        try:
            os.kill(supervisor_pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        _fail("broker did not become ready within 25 seconds")
    result = json.loads(payload.split(b"\n", 1)[0])
    if result.get("ok") is not True:
        _fail(
            "broker supervisor failed before readiness: "
            + str(result.get("error") or "unknown error")
        )
    return result


def stop_broker(*, controller_dir: Path, variant: str, timeout_s: int = 30) -> Path:
    if os.geteuid() != 0:
        _fail("broker controller must run as root")
    controller = _controller_dir(controller_dir)
    state_path = _plain_file(
        controller / f"{variant}-model-broker-state.json", label="broker state"
    )
    state = json.loads(state_path.read_text(encoding="utf-8"))
    if (
        not isinstance(state, dict)
        or state.get("phase") != "model_broker_state"
        or state.get("variant") != variant
    ):
        _fail("broker state provenance is invalid")
    pid = state.get("supervisor_pid")
    start_ticks = state.get("supervisor_start_ticks")
    if (
        not isinstance(pid, int)
        or pid <= 1
        or not isinstance(start_ticks, int)
        or start_ticks <= 0
    ):
        _fail("broker supervisor pid is invalid")
    try:
        if _process_start_ticks(pid) != start_ticks:
            _fail("broker supervisor pid has been reused")
        pidfd = os.pidfd_open(pid, 0)
    except (FileNotFoundError, ProcessLookupError):
        _fail("broker supervisor is no longer running and published no transcript")
    try:
        # Pin the process identity before signalling it.  A separate
        # ``start_ticks`` check followed by ``kill(pid)`` has a PID-reuse
        # window; pidfd_send_signal does not.
        signal.pidfd_send_signal(pidfd, signal.SIGTERM, None, 0)
    finally:
        os.close(pidfd)
    transcript = controller / f"{variant}-model-broker-transcript.json"
    deadline = time.monotonic() + timeout_s
    while time.monotonic() < deadline:
        if transcript.is_file() and not transcript.is_symlink():
            document = json.loads(transcript.read_text(encoding="utf-8"))
            if set(document) != TRANSCRIPT_FIELDS or document.get("broker_stopped") is not True:
                _fail("broker transcript is incomplete or invalid")
            return transcript
        time.sleep(0.1)
    _fail("broker did not publish a stopped transcript before timeout")


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    start = subparsers.add_parser("start")
    start.add_argument("--controller-dir", type=Path, required=True)
    start.add_argument("--variant", choices=sorted(VARIANTS), required=True)
    start.add_argument("--run-id", required=True)
    start.add_argument("--model", required=True)
    start.add_argument("--upstream", required=True)
    start.add_argument("--credential-file", type=Path, required=True)
    start.add_argument("--credential-format", choices=("raw", "json", "env"), default="raw")
    start.add_argument("--token-name")
    start.add_argument("--broker-user", required=True)
    start.add_argument("--port", type=int, default=0)
    start.add_argument(
        "--request-profile", choices=sorted(REQUEST_PROFILES),
        default="agent_harness_v1",
    )
    stop = subparsers.add_parser("stop")
    stop.add_argument("--controller-dir", type=Path, required=True)
    stop.add_argument("--variant", choices=sorted(VARIANTS), required=True)
    stop.add_argument("--timeout-s", type=int, default=30)
    return parser


def main() -> int:
    args = _parser().parse_args()
    try:
        if args.command == "start":
            result = start_broker(
                controller_dir=args.controller_dir,
                variant=args.variant,
                run_id=args.run_id,
                model=args.model,
                upstream=args.upstream,
                credential_file=args.credential_file,
                credential_format=args.credential_format,
                token_name=args.token_name,
                broker_user=args.broker_user,
                port=args.port,
                request_profile=args.request_profile,
            )
            print(json.dumps(result, sort_keys=True))
        else:
            print(stop_broker(controller_dir=args.controller_dir, variant=args.variant, timeout_s=args.timeout_s))
    except (BrokerError, OSError, KeyError, ValueError, json.JSONDecodeError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
