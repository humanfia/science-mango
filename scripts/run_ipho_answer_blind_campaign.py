#!/usr/bin/env python3
"""Run one IPhO answer-blind campaign behind the pinned Kimi-K3 broker.

This root-side controller deliberately remains the broker lease parent for the
whole confined run.  It passes the real credential *path* only to the broker;
the solver receives only a loopback URL and the broker's fixed public token.
"""

from __future__ import annotations

import argparse
import datetime as dt
import email.utils
import http.client
import importlib.util
import json
import os
import random
import stat
import sys
import time
import urllib.parse
from pathlib import Path
from types import ModuleType
from typing import Any, Iterable, Mapping


BROKER_SCRIPT = Path(
    "/root/icho-answer-blind-overlay-49360f26-univ-kimi-k3/"
    "scripts/run_answer_blind_model_broker.py"
)
CONFINED_LOOP_SCRIPT = Path(__file__).with_name(
    "run_ipho_answer_blind_confined_loop.py"
)
SEALED_RUNTIME = Path("/opt/icho-answer-blind-runtime-10b04c62-rebuilt1-idle1800")
UPSTREAM = "https://api.unipatai.com"
MODEL = "anthropic-kimi-k3"
VARIANT = "kimi-k3"
BROKER_USER = "ichokimib1"
REQUEST_PROFILE = "agent_harness_v1"
DUMMY_TOKEN = "answer-blind-public-dummy-token"
ENV_NAME = "ipho-model-broker.env"
BROKER_429_RETRY_DELAYS_S = (5.0, 15.0, 45.0)
BROKER_429_RETRY_MAX_DELAY_S = 120.0
BROKER_429_RETRY_JITTER = 0.25


class CampaignError(RuntimeError):
    """A root-side campaign invariant was not satisfied."""


def _broker_retry_delay(raw: str | None, fallback_s: float) -> float:
    delay: float | None = None
    if raw:
        value = raw.strip()
        try:
            delay = float(value)
        except ValueError:
            try:
                when = email.utils.parsedate_to_datetime(value)
                if when.tzinfo is None:
                    when = when.replace(tzinfo=dt.timezone.utc)
                delay = (when - dt.datetime.now(dt.timezone.utc)).total_seconds()
            except (TypeError, ValueError, OverflowError):
                delay = None
    if delay is None:
        delay = fallback_s * (1.0 + BROKER_429_RETRY_JITTER * random.random())
    return min(BROKER_429_RETRY_MAX_DELAY_S, max(1.0, delay))


def _install_broker_429_retry(broker: ModuleType) -> Any:
    """Retry only replay-safe 429 responses inside the forked model broker."""

    try:
        original_http = broker.http
        original_client = original_http.client
        original_https = original_client.HTTPSConnection
    except AttributeError as exc:
        raise CampaignError("pinned broker HTTP client interface drifted") from exc

    class RetryingHTTPSConnection:
        def __init__(self, *args: Any, **kwargs: Any) -> None:
            self._args = args
            self._kwargs = kwargs
            self._connection = original_https(*args, **kwargs)
            self._request: tuple[str, str, bytes, dict[str, str], bool] | None = None

        def request(
            self,
            method: str,
            url: str,
            body: Any = None,
            headers: Mapping[str, str] | None = None,
            *,
            encode_chunked: bool = False,
        ) -> None:
            if not isinstance(body, (bytes, bytearray, memoryview)):
                raise CampaignError("broker retry requires a replay-safe byte body")
            saved = (method, url, bytes(body), dict(headers or {}), encode_chunked)
            self._request = saved
            self._send(saved)

        def _send(
            self, saved: tuple[str, str, bytes, dict[str, str], bool]
        ) -> None:
            method, url, body, headers, encode_chunked = saved
            self._connection.request(
                method,
                url,
                body=body,
                headers=headers,
                encode_chunked=encode_chunked,
            )

        def getresponse(self) -> Any:
            if self._request is None:
                raise CampaignError("broker getresponse preceded request")
            for fallback_s in BROKER_429_RETRY_DELAYS_S:
                response = self._connection.getresponse()
                if int(response.status) != 429:
                    return response
                retry_after = response.getheader("Retry-After")
                response.read()
                response.close()
                self._connection.close()
                time.sleep(_broker_retry_delay(retry_after, fallback_s))
                self._connection = original_https(*self._args, **self._kwargs)
                self._send(self._request)
            return self._connection.getresponse()

        def close(self) -> None:
            self._connection.close()

        def __getattr__(self, name: str) -> Any:
            return getattr(self._connection, name)

    class AttributeProxy:
        def __init__(self, target: Any, **overrides: Any) -> None:
            self._target = target
            self.__dict__.update(overrides)

        def __getattr__(self, name: str) -> Any:
            return getattr(self._target, name)

    client_proxy = AttributeProxy(
        original_client, HTTPSConnection=RetryingHTTPSConnection
    )
    http_proxy = AttributeProxy(original_http, client=client_proxy)
    broker.http = http_proxy

    def restore() -> None:
        if broker.http is http_proxy:
            broker.http = original_http

    return restore


def _import_file(name: str, path: Path) -> ModuleType:
    source = path.resolve(strict=True)
    spec = importlib.util.spec_from_file_location(name, source)
    if spec is None or spec.loader is None:
        raise CampaignError(f"cannot import controller dependency: {source}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _load_pinned_modules() -> tuple[ModuleType, ModuleType]:
    return (
        _import_file("_ipho_pinned_model_broker", BROKER_SCRIPT),
        _import_file("_ipho_confined_loop", CONFINED_LOOP_SCRIPT),
    )


def _load_ready_receipt(
    start_result: Mapping[str, Any], *, controller_dir: Path, run_id: str
) -> tuple[Path, str]:
    raw_ready = start_result.get("ready")
    if not isinstance(raw_ready, str):
        raise CampaignError("broker start result did not name its ready receipt")
    ready = Path(raw_ready)
    if ready.is_symlink():
        raise CampaignError("broker ready receipt must not be a symbolic link")
    ready = ready.resolve(strict=True)
    expected = (
        controller_dir.resolve(strict=True)
        / f"{VARIANT}-model-broker-ready.json"
    )
    if ready != expected or not ready.is_file():
        raise CampaignError("broker ready receipt is outside the controller directory")
    try:
        receipt = json.loads(ready.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise CampaignError("broker ready receipt is invalid") from exc
    if not isinstance(receipt, dict):
        raise CampaignError("broker ready receipt must be a JSON object")
    listen_url = receipt.get("listen_url")
    parsed = urllib.parse.urlsplit(listen_url if isinstance(listen_url, str) else "")
    if (
        parsed.scheme != "http"
        or parsed.hostname != "127.0.0.1"
        or parsed.port is None
        or parsed.username
        or parsed.password
        or parsed.query
        or parsed.fragment
        or parsed.path not in {"", "/"}
    ):
        raise CampaignError("broker listen URL must be an explicit IPv4 loopback origin")
    if (
        receipt.get("phase") != "model_broker_ready"
        or receipt.get("variant") != VARIANT
        or receipt.get("run_id") != run_id
        or receipt.get("allowed_model") != MODEL
        or receipt.get("upstream_origin") != UPSTREAM
        or receipt.get("request_profile") != REQUEST_PROFILE
    ):
        raise CampaignError("broker ready receipt does not bind this fixed campaign")
    return ready, listen_url


def _write_public_broker_env(controller_dir: Path, listen_url: str) -> Path:
    path = controller_dir / ENV_NAME
    payload = (
        f"ANTHROPIC_BASE_URL={listen_url}\n"
        f"ANTHROPIC_AUTH_TOKEN={DUMMY_TOKEN}\n"
    ).encode("utf-8")
    descriptor = os.open(
        path,
        os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0),
        0o600,
    )
    try:
        os.write(descriptor, payload)
        os.fsync(descriptor)
        os.fchown(descriptor, 0, 0)
        os.fchmod(descriptor, 0o600)
    finally:
        os.close(descriptor)
    metadata = path.stat(follow_symlinks=False)
    if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) != 0o600:
        raise CampaignError("public broker environment is not root-owned mode 0600")
    return path


def _smoke_request(listen_url: str, *, timeout_s: int) -> None:
    """Send exactly one tiny model request through the public broker surface."""

    body = json.dumps(
        {
            "model": MODEL,
            "max_tokens": 1,
            "messages": [{"role": "user", "content": "Reply OK."}],
            "tools": [],
        },
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    parsed = urllib.parse.urlsplit(listen_url)
    connection = http.client.HTTPConnection(
        parsed.hostname, parsed.port, timeout=timeout_s
    )
    try:
        connection.request(
            "POST",
            "/v1/messages",
            body=body,
            headers={
                "Authorization": f"Bearer {DUMMY_TOKEN}",
                "Content-Type": "application/json",
                "Accept": "application/json",
                "anthropic-version": "2023-06-01",
            },
        )
        response = connection.getresponse()
        payload = response.read(1024 * 1024 + 1)
        if response.status != 200:
            raise CampaignError(
                f"minimal broker smoke request returned HTTP {response.status}"
            )
    except (OSError, http.client.HTTPException) as exc:
        raise CampaignError("minimal broker smoke request failed") from exc
    finally:
        connection.close()
    if len(payload) > 1024 * 1024:
        raise CampaignError("minimal broker smoke response exceeded 1 MiB")
    try:
        document = json.loads(payload)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise CampaignError("minimal broker smoke response was not JSON") from exc
    if not isinstance(document, dict):
        raise CampaignError("minimal broker smoke response was not a JSON object")


def _loop_arguments(
    args: argparse.Namespace, *, ready: Path, broker_env: Path
) -> argparse.Namespace:
    return argparse.Namespace(
        workspace=args.workspace,
        dependency_root=args.dependency_root,
        runtime_root=args.runtime_root,
        solver_user=args.solver_user,
        private_home=args.private_home,
        private_tmp=args.private_tmp,
        controller_dir=args.controller_dir,
        broker_ready=ready,
        broker_env=broker_env,
        run_id=args.run_id,
        lean_explore_cache=args.lean_explore_cache,
        lean_explore_hf_cache=args.lean_explore_hf_cache,
        lean_explore_site_packages=args.lean_explore_site_packages,
        max_iterations=args.max_iterations,
        max_parallel=args.max_parallel,
        max_objectives=args.max_objectives,
        timeout_s=args.timeout_s,
    )


def run(args: argparse.Namespace) -> tuple[dict[str, Any], int]:
    if os.geteuid() != 0:
        raise CampaignError("the IPhO campaign controller must run as root")
    broker, confined_loop = _load_pinned_modules()
    started = False
    try:
        restore_retry = _install_broker_429_retry(broker)
        try:
            start_result = broker.start_broker(
                controller_dir=args.controller_dir,
                variant=VARIANT,
                run_id=args.run_id,
                model=MODEL,
                upstream=UPSTREAM,
                credential_file=args.credential_file,
                credential_format=args.credential_format,
                token_name=args.token_name,
                broker_user=BROKER_USER,
                port=0,
                request_profile=REQUEST_PROFILE,
            )
        finally:
            restore_retry()
        started = True
        ready, listen_url = _load_ready_receipt(
            start_result,
            controller_dir=args.controller_dir,
            run_id=args.run_id,
        )
        broker_env = _write_public_broker_env(args.controller_dir, listen_url)
        if args.smoke_request:
            _smoke_request(listen_url, timeout_s=args.smoke_timeout_s)
        result, exit_code = confined_loop.run(
            _loop_arguments(args, ready=ready, broker_env=broker_env)
        )
        return {
            **result,
            "broker_env": str(broker_env),
            "broker_smoke_request": bool(args.smoke_request),
        }, exit_code
    finally:
        if started:
            broker.stop_broker(
                controller_dir=args.controller_dir,
                variant=VARIANT,
                timeout_s=args.broker_stop_timeout_s,
            )


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--credential-file", type=Path, required=True)
    parser.add_argument(
        "--credential-format", choices=("raw", "json", "env"), default="raw"
    )
    parser.add_argument("--token-name")
    parser.add_argument("--controller-dir", type=Path, required=True)
    parser.add_argument("--workspace", type=Path, required=True)
    parser.add_argument("--dependency-root", type=Path, required=True)
    parser.add_argument("--private-home", type=Path, required=True)
    parser.add_argument("--private-tmp", type=Path, required=True)
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--solver-user", required=True)
    parser.add_argument("--runtime-root", type=Path, default=SEALED_RUNTIME)
    parser.add_argument(
        "--lean-explore-cache", type=Path, default=Path("/root/.lean_explore")
    )
    parser.add_argument("--lean-explore-hf-cache", type=Path, required=True)
    parser.add_argument("--lean-explore-site-packages", type=Path)
    parser.add_argument("--max-iterations", type=int, default=100)
    parser.add_argument("--max-parallel", type=int, default=4)
    parser.add_argument("--max-objectives", type=int, default=28)
    parser.add_argument("--timeout-s", type=int, default=86400)
    parser.add_argument("--smoke-request", action="store_true")
    parser.add_argument("--smoke-timeout-s", type=int, default=120)
    parser.add_argument("--broker-stop-timeout-s", type=int, default=30)
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    parser = _parser()
    args = parser.parse_args(argv)
    try:
        result, exit_code = run(args)
    except (CampaignError, RuntimeError, OSError, ValueError, KeyError) as exc:
        parser.error(str(exc))
    print(json.dumps(result, ensure_ascii=False, sort_keys=True))
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
