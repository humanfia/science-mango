#!/usr/bin/env python3
"""Trusted tool-free two-pass answer-blind independent Review controller.

``source-first`` runs before the solver.  Its only model-visible inputs are
canonical questions-only projections and their problem images; it commits the
exact request, response, and minimal model submission to controller-owned
mode-0400 files and exits.

``artifact-submit`` runs after the structured solver and before the final
snapshot/verifier.  It replays the immutable Pass-A submission into a
controller-only records commitment, exposes only that commitment plus the
sealed solver artifacts to a distinct tool-free Pass-B exchange, freezes the
minimal Pass-B submission, and writes both project gate files from the
deterministically constructed certificate records.

``artifact-finalize`` runs after those gate files have been included in the
final project snapshot and a low-privilege verifier has checked an external
clean copy.  It performs no model call: it only replays the two immutable
model submissions and controller records into the final semantic envelopes,
attempt receipts, and aggregate consumed by ``blind_evaluation``.

No model process receives a shell, project path, or filesystem capability.
GPT uses the one-shot ChatGPT-login header proxy; Kimi uses a fresh one-request
broker lifecycle for each pass.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import re
import shutil
import stat
import sys
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Callable, Mapping, NoReturn, Sequence

from archon.commands import blind_evaluation as blind


SCHEMA_VERSION = 1
PROTOCOL = "icho-answer-blind-v1"
REQUEST_PROFILE = "tool_free_structured_independent_review_v1"
SAFE_ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,127}$")
SHA256 = re.compile(r"^[0-9a-f]{64}$")
MODELS: Mapping[str, tuple[str, str]] = {
    "gpt": ("openai", "gpt-5.6-sol"),
    "kimi-k3": ("moonshot", "kimi-k3"),
}
PRECOMMIT_FIELDS = {
    "schema_version", "protocol", "phase", "variant", "model_family",
    "model_id", "run_id", "request_profile", "tools_enabled", "store",
    "scope_ids", "controller_binary_sha256", "input_inventory",
    "review_projection_sha256", "adapter_provenance", "adapter", "transport",
    "request", "response", "model_submission", "normalized_response_sha256",
    "request_response_chain_sha256", "status", "finalized_before_solver",
}
ATTEMPT_COMMON_FIELDS = {
    "schema_version", "protocol", "phase", "variant", "model_family",
    "model_id", "run_id", "request_profile", "tools_enabled", "store",
    "scope_ids", "snapshot_inventory_sha256", "controller_binary_sha256",
    "input_inventory", "review_projection_sha256", "adapter_provenance",
    "adapter", "transport", "request", "response", "model_submission",
    "constructed_semantic_receipt", "normalized_response_sha256",
    "request_response_chain_sha256", "status",
}
SOURCE_ATTEMPT_FIELDS = ATTEMPT_COMMON_FIELDS | {
    "source_first_precommit", "source_records_commitment",
}
ARTIFACT_ATTEMPT_FIELDS = ATTEMPT_COMMON_FIELDS | {
    "source_records_commitment", "source_first_attempt_sha256",
}
AGGREGATE_FIELDS = {
    "schema_version", "protocol", "phase", "variant", "model_family",
    "model_id", "run_id", "request_profile", "tools_enabled", "store",
    "scope_ids", "snapshot_inventory_sha256", "controller_binary_sha256",
    "source_first_attempt", "artifact_review_attempt",
    "source_records_sha256", "source_commitment_sha256",
    "semantic_review_sha256",
    "all_passes_finalized",
}
ARTIFACT_RECORDS_FIELDS = {
    "schema_version", "protocol", "phase", "evaluation_mode",
    "official_answer_seen", "variant", "model_family", "model_id", "run_id",
    "request_profile", "review_input_inventory_sha256",
    "review_projection_sha256", "source_records_sha256", "scope_ids",
    "records",
}
ARTIFACT_SUBMISSION_FIELDS = {
    "schema_version", "protocol", "phase", "variant", "model_family",
    "model_id", "run_id", "request_profile", "tools_enabled", "store",
    "scope_ids", "controller_binary_sha256", "source_first_precommit",
    "structured_solver_receipt", "source_records_commitment",
    "input_inventory", "review_projection_sha256", "adapter_provenance",
    "adapter", "transport", "request", "response", "model_submission",
    "normalized_response_sha256", "request_response_chain_sha256",
    "constructed_records_receipt", "review_gates", "status",
    "submitted_before_verifier",
}
ADAPTER_FIELDS = {
    "provider_api", "response_extractor", "response_schema_sha256",
}
ROOT_GENERATED = (
    blind.CONFIG_FILE, blind.MCP_FILE, blind.PROTOCOL_FILE, blind.AGENTS_FILE,
)
MAX_BYTES = 64 * 1024 * 1024


class ReviewControllerError(RuntimeError):
    pass


def _fail(message: str) -> NoReturn:
    raise ReviewControllerError(message)


def _canonical(value: Any) -> bytes:
    try:
        return blind._json_bytes(value)
    except Exception as exc:
        raise ReviewControllerError("value is not canonical finite JSON") from exc


def _pretty(value: Any) -> bytes:
    return (
        json.dumps(
            value, ensure_ascii=False, sort_keys=True, indent=2, allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def _sha(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _file_sha(path: Path) -> str:
    return _sha(path.read_bytes())


def _strict_json(payload: bytes, *, label: str) -> dict[str, Any]:
    try:
        return blind._strict_json_object(payload, label=label)
    except Exception as exc:
        raise ReviewControllerError(f"invalid {label}") from exc


def _root_dir(path: Path, *, label: str) -> Path:
    if path.is_symlink() or not path.is_dir():
        _fail(f"{label} must be a plain directory")
    result = path.resolve(strict=True)
    metadata = result.stat(follow_symlinks=False)
    if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) & 0o022:
        _fail(f"{label} must be root-owned and not group/other writable")
    return result


def _root_file(path: Path, *, label: str, private: bool = False) -> Path:
    if path.is_symlink() or not path.is_file():
        _fail(f"{label} must be a plain file: {path}")
    result = path.resolve(strict=True)
    metadata = result.stat(follow_symlinks=False)
    forbidden = 0o077 if private else 0o022
    if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) & forbidden:
        _fail(f"{label} ownership/mode is not trusted: {result}")
    return result


def _atomic_root_file(path: Path, payload: bytes, *, mode: int = 0o400) -> Path:
    if path.exists() or path.is_symlink() or path.parent.is_symlink():
        _fail(f"controller artifact must be new: {path}")
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, mode)
    try:
        view = memoryview(payload)
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                _fail(f"short controller write: {path}")
            view = view[written:]
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    os.chown(path, 0, 0)
    os.chmod(path, mode)
    return path


def _locator(path: Path) -> dict[str, str]:
    resolved = _root_file(path, label="controller receipt", private=True)
    return {"path": str(resolved), "sha256": _file_sha(resolved)}


def _safe_relative(raw: object, *, label: str) -> str:
    value = str(raw or "")
    path = PurePosixPath(value)
    if (
        not value or "\\" in value or "\0" in value or path.is_absolute()
        or path.as_posix() != value
        or any(part in {"", ".", ".."} for part in path.parts)
    ):
        _fail(f"{label} is not a normalized relative path")
    return value


def _within(root: Path, relative: object, *, label: str) -> Path:
    value = _safe_relative(relative, label=label)
    path = root.joinpath(*PurePosixPath(value).parts)
    if path.is_symlink() or not path.is_file():
        _fail(f"{label} is missing or unsafe: {value}")
    resolved = path.resolve(strict=True)
    try:
        resolved.relative_to(root)
    except ValueError:
        _fail(f"{label} escapes its root")
    return resolved


def _copy_exact(source: Path, destination: Path) -> None:
    source = _root_file(source, label="sanitized Review source")
    destination.parent.mkdir(mode=0o755, parents=True, exist_ok=True)
    if destination.parent.is_symlink():
        _fail("sanitized Review destination parent is a symlink")
    _atomic_root_file(destination, source.read_bytes())


def _seal_tree(root: Path) -> None:
    for directory, names, _files in os.walk(root, topdown=False):
        base = Path(directory)
        for name in names:
            child = base / name
            if child.is_symlink():
                _fail("sanitized Review tree contains a symlink")
            os.chown(child, 0, 0)
            os.chmod(child, 0o755)
        os.chown(base, 0, 0)
        os.chmod(base, 0o755)


def _inventory(root: Path, *, source_first: bool) -> dict[str, str]:
    root = _root_dir(root, label="sanitized Review input")
    try:
        files = blind._regular_file_inventory(
            root, label="structured Review input",
        )
    except Exception as exc:
        raise ReviewControllerError("invalid sanitized Review inventory") from exc
    for relative in files:
        path = PurePosixPath(relative)
        if source_first and not (
            (path.parts and path.parts[0] == blind._SOURCE_FIRST_RECORD_DIRECTORY)
            or path.parts[:2] == ("icho_2026_source", "image")
        ):
            _fail("Pass A input contains a non-source artifact")
    return files


def _bundle(path: Path) -> tuple[bytes, dict[str, dict[str, Any]]]:
    payload = _root_file(path, label="questions-only bundle").read_bytes()
    result: dict[str, dict[str, Any]] = {}
    for number, line in enumerate(payload.splitlines(), 1):
        if not line.strip():
            continue
        row = _strict_json(line, label=f"questions-only row {number}")
        record_id = row.get("id")
        if (
            not isinstance(record_id, str) or SAFE_ID.fullmatch(record_id) is None
            or record_id in result
            or row.get("protocol") != PROTOCOL
            or row.get("evaluation_mode") != "answer_blind"
            or row.get("official_answer_seen") is not False
            or row.get("phase") != "solve"
        ):
            _fail(f"invalid questions-only row {number}")
        result[record_id] = row
    if not result:
        _fail("questions-only bundle is empty")
    return payload, result


def _scope(rows: Mapping[str, Any], scope_ids: Sequence[str]) -> list[str]:
    ids = sorted(scope_ids or rows)
    if not ids or len(ids) != len(set(ids)) or any(item not in rows for item in ids):
        _fail("Review scope differs from questions-only bundle")
    return ids


def _source_input(
    *, controller: Path, rows: Mapping[str, Mapping[str, Any]],
    scope_ids: Sequence[str], asset_root: Path, variant: str, run_id: str,
) -> tuple[Path, dict[str, str], dict[str, dict[str, Any]]]:
    # This function has no workspace argument and never searches reports,
    # candidates, Lean, blueprint, or solver state.
    asset_root = _root_dir(asset_root, label="problem-only asset root")
    root = controller.parent / (
        f".{controller.name}-{variant}-{run_id}-source-first-input"
    )
    if root.exists() or root.is_symlink():
        _fail("source-first input directory must be new")
    root.mkdir(mode=0o755)
    records: dict[str, dict[str, Any]] = {}
    for record_id in scope_ids:
        row = rows[record_id]
        try:
            record = blind._source_first_projection(row)
        except Exception as exc:
            raise ReviewControllerError(
                f"invalid source-first projection for {record_id}"
            ) from exc
        records[record_id] = record
        record_path = (
            root / blind._SOURCE_FIRST_RECORD_DIRECTORY / f"{record_id}.json"
        )
        record_path.parent.mkdir(mode=0o755, parents=True, exist_ok=True)
        _atomic_root_file(record_path, _canonical(record))
        assets = row.get("problem_assets")
        if not isinstance(assets, list):
            _fail(f"problem assets are missing for {record_id}")
        for item in assets:
            if not isinstance(item, Mapping) or item.get("kind") != "problem_page":
                continue
            basename = _safe_relative(item.get("path"), label="problem image")
            if len(PurePosixPath(basename).parts) != 1:
                _fail("problem image locator must be a basename")
            source = _within(asset_root, basename, label="problem image")
            if _file_sha(source) != item.get("sha256"):
                _fail(f"problem image hash drift: {basename}")
            destination = root / "icho_2026_source/image" / basename
            if destination.exists():
                if _file_sha(destination) != _file_sha(source):
                    _fail(f"conflicting shared problem image: {basename}")
            else:
                _copy_exact(source, destination)
    _seal_tree(root)
    files = _inventory(root, source_first=True)
    expected = {
        f"{blind._SOURCE_FIRST_RECORD_DIRECTORY}/{record_id}.json"
        for record_id in scope_ids
    }
    expected.update(
        f"icho_2026_source/image/{item['path']}"
        for record_id in scope_ids
        for item in rows[record_id].get("problem_assets", [])
        if isinstance(item, Mapping) and item.get("kind") == "problem_page"
    )
    if set(files) != expected:
        _fail("source-first input is not the exact source/image projection")
    return root, files, records


def _load_solver_module() -> Any:
    path = Path(__file__).with_name("run_answer_blind_structured_solver.py")
    name = "_answer_blind_structured_solver_for_review"
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        _fail("trusted structured solver transport module is unavailable")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _load_broker_module() -> Any:
    path = Path(__file__).with_name("run_answer_blind_model_broker.py")
    name = "_answer_blind_model_broker_for_review"
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        _fail("trusted model broker module is unavailable")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


@dataclass(frozen=True)
class Exchange:
    response: bytes
    submission: dict[str, Any]
    adapter: str
    transport: dict[str, Any]
    chain_sha256: str


ExchangeCall = Callable[
    [str, str, Mapping[str, Any], Path, str, int], Exchange
]


def _production_exchange(
    variant: str, run_id: str, request: Mapping[str, Any],
    transport_dir: Path, target_id: str, _pass_number: int,
    *, broker_credential_file: Path | None,
    broker_credential_format: str, broker_token_name: str | None,
    broker_user: str | None, broker_port: int,
    codex_binary: Path | None, codex_home: Path | None,
) -> Exchange:
    solver = _load_solver_module()
    family, model = MODELS[variant]
    del family
    if variant == "gpt":
        if codex_binary is None or codex_home is None:
            _fail("GPT Review requires trusted Codex binary/login home")
        request_path = transport_dir / f"gpt-{target_id}-attempt-1-request.json"
        if not request_path.is_file():
            _fail("GPT Review request was not pre-registered")
        adapter = solver.ChatGPTLoginProxyAdapter(
            codex_binary=codex_binary, codex_home=codex_home,
            controller=transport_dir, target_id=target_id, attempt=1,
            run_id=run_id,
        )
        reply = adapter("", request)
        provenance = reply.provenance
        locator = provenance.get("proxy_receipt") if isinstance(provenance, Mapping) else None
        if not isinstance(locator, Mapping):
            _fail("GPT Review exchange lacks a proxy receipt")
        exchange_locator = {"path": str(locator["path"]), "sha256": str(locator["sha256"])}
        chain = _sha(bytes.fromhex("0" * 64) + bytes.fromhex(exchange_locator["sha256"]))
        return Exchange(
            response=reply.raw_response, submission=dict(reply.submission),
            adapter="chatgpt_login_proxy_v1",
            transport={
                "kind": "chatgpt_login_proxy_v1",
                "exchanges": [exchange_locator],
                "exchange_chain_sha256": chain,
            }, chain_sha256=chain,
        )
    if broker_credential_file is None or broker_user is None:
        _fail("Kimi Review requires an invocation-scoped broker credential/user")
    broker = _load_broker_module()
    started = broker.start_broker(
        controller_dir=transport_dir, variant=variant, run_id=run_id,
        model=model, upstream="https://api.moonshot.cn/anthropic",
        credential_file=broker_credential_file,
        credential_format=broker_credential_format,
        token_name=broker_token_name, broker_user=broker_user,
        port=broker_port, request_profile=REQUEST_PROFILE,
    )
    ready_path = _root_file(
        Path(str(started["ready"])), label="Review broker ready", private=True,
    )
    ready = _strict_json(ready_path.read_bytes(), label="Review broker ready")
    reply: Any | None = None
    error: BaseException | None = None
    try:
        reply = solver.http_provider_call(str(ready["listen_url"]), request)
    except BaseException as exc:
        error = exc
    finally:
        transcript_path = broker.stop_broker(
            controller_dir=transport_dir, variant=variant,
        )
    if error is not None:
        raise error
    assert reply is not None
    transcript_path = _root_file(
        Path(transcript_path), label="Review broker transcript", private=True,
    )
    transcript = _strict_json(
        transcript_path.read_bytes(), label="Review broker transcript",
    )
    if (
        transcript.get("request_profile") != REQUEST_PROFILE
        or transcript.get("request_count") != 1
        or transcript.get("ready_receipt_sha256") != _file_sha(ready_path)
        or transcript.get("broker_stopped") is not True
        or not isinstance(transcript.get("request_response_chain_sha256"), str)
    ):
        _fail("Review broker transcript does not bind one stopped exchange")
    return Exchange(
        response=reply.raw_response, submission=dict(reply.submission),
        adapter="structured_broker_http_v1",
        transport={
            "kind": "structured_broker_http_v1",
            "ready_receipt": _locator(ready_path),
            "transcript": _locator(transcript_path),
        },
        chain_sha256=str(transcript["request_response_chain_sha256"]),
    )


def _adapter_provenance(variant: str, *, source_first: bool) -> dict[str, str]:
    provider, extractor = {
        "gpt": ("openai_responses_v1", "openai_responses_single_json_text_v1"),
        "kimi-k3": (
            "anthropic_messages_v1", "anthropic_messages_single_json_text_v1",
        ),
    }[variant]
    return {
        "provider_api": provider,
        "response_extractor": extractor,
        "response_schema_sha256": _sha(_canonical(
            blind._structured_review_response_schema(source_first=source_first)
        )),
    }


def _review_request(
    *, root: Path, files: Mapping[str, str], scope_ids: Sequence[str],
    variant: str, model: str, source_first: bool,
    source_records_sha256: str | None,
) -> tuple[dict[str, Any], str]:
    try:
        projection, gpt_images, kimi_images = blind._structured_review_projection(
            root=root, files=files, scope_ids=scope_ids,
            source_first=source_first,
            source_records_sha256=source_records_sha256,
        )
        request = blind._structured_review_request(
            variant=variant, model_id=model, projection=projection,
            gpt_images=gpt_images, kimi_images=kimi_images,
            source_first=source_first,
        )
    except Exception as exc:
        raise ReviewControllerError("cannot construct canonical Review request") from exc
    return request, _sha(_canonical(projection))


def _perform_exchange(
    *, controller: Path, transport_dir: Path, pass_name: str,
    target_id: str, variant: str, run_id: str, request: Mapping[str, Any],
    source_first: bool, exchange_call: ExchangeCall | None,
    broker_credential_file: Path | None, broker_credential_format: str,
    broker_token_name: str | None, broker_user: str | None, broker_port: int,
    codex_binary: Path | None, codex_home: Path | None,
) -> tuple[Exchange, dict[str, str], dict[str, str], dict[str, str]]:
    transport_dir.mkdir(mode=0o700)
    os.chown(transport_dir, 0, 0)
    os.chmod(transport_dir, 0o700)
    # ChatGPTLoginProxyAdapter requires this exact preregistration filename.
    request_path = transport_dir / f"{variant}-{target_id}-attempt-1-request.json"
    _atomic_root_file(request_path, _canonical(request))
    if exchange_call is None:
        exchange = _production_exchange(
            variant, run_id, request, transport_dir, target_id, 1,
            broker_credential_file=broker_credential_file,
            broker_credential_format=broker_credential_format,
            broker_token_name=broker_token_name, broker_user=broker_user,
            broker_port=broker_port, codex_binary=codex_binary,
            codex_home=codex_home,
        )
    else:
        exchange = exchange_call(
            variant, run_id, request, transport_dir, target_id, 1,
        )
    response = _strict_json(exchange.response, label=f"{pass_name} provider response")
    try:
        normalized = blind._structured_json_from_provider_response(
            response, variant=variant, label=pass_name,
        )
    except Exception as exc:
        raise ReviewControllerError(f"{pass_name} response is not one strict JSON verdict") from exc
    if normalized != exchange.submission:
        _fail(f"{pass_name} transport submission differs from provider response")
    response_path = controller / f"{variant}-{pass_name}-provider-response.json"
    model_path = controller / f"{variant}-{pass_name}-model-submission.json"
    _atomic_root_file(response_path, exchange.response)
    _atomic_root_file(model_path, _canonical(normalized))
    return exchange, _locator(request_path), _locator(response_path), _locator(model_path)


def run_source_first(
    *, controller_dir: Path, bundle_path: Path, asset_root: Path,
    variant: str, run_id: str, scope_ids: Sequence[str],
    exchange_call: ExchangeCall | None = None,
    broker_credential_file: Path | None = None,
    broker_credential_format: str = "raw", broker_token_name: str | None = None,
    broker_user: str | None = None, broker_port: int = 0,
    codex_binary: Path | None = None, codex_home: Path | None = None,
) -> dict[str, Any]:
    if os.geteuid() != 0:
        _fail("structured Review controller must run as root")
    if variant not in MODELS or SAFE_ID.fullmatch(run_id) is None:
        _fail("structured Review variant/run id is invalid")
    controller = _root_dir(controller_dir, label="Review controller directory")
    _payload, rows = _bundle(bundle_path)
    ids = _scope(rows, scope_ids)
    family, model = MODELS[variant]
    input_root, files, _records = _source_input(
        controller=controller, rows=rows, scope_ids=ids,
        asset_root=asset_root, variant=variant, run_id=run_id,
    )
    request, projection_sha = _review_request(
        root=input_root, files=files, scope_ids=ids, variant=variant,
        model=model, source_first=True, source_records_sha256=None,
    )
    transport_dir = controller / f"{variant}-{run_id}-source-first-transport"
    exchange, request_spec, response_spec, model_spec = _perform_exchange(
        controller=controller, transport_dir=transport_dir,
        pass_name="source-first-review", target_id="independent-source-first-review",
        variant=variant, run_id=run_id, request=request, source_first=True,
        exchange_call=exchange_call,
        broker_credential_file=broker_credential_file,
        broker_credential_format=broker_credential_format,
        broker_token_name=broker_token_name, broker_user=broker_user,
        broker_port=broker_port, codex_binary=codex_binary, codex_home=codex_home,
    )
    # A precommit is an accepted semantic commitment, not merely a transport
    # success.  Construct and deeply validate its controller-bound records
    # before publishing the irreversible pre-solver marker.
    source_model = _load_bound_object(
        model_spec, label="source-first model submission",
    )[1]
    try:
        source_records = blind.construct_structured_source_records_commitment(
            model_submission=source_model,
            controller_records=_source_controller_records(
                precommit={
                    "input_inventory": {
                        "files": files, "files_sha256": blind._hash_index(files),
                    }
                },
                rows=rows, scope_ids=ids,
            ),
            scope_ids=ids, variant=variant, model_family=family,
            model_id=model, run_id=run_id,
            review_input_inventory_sha256=blind._hash_index(files),
            review_projection_sha256=projection_sha,
        )
        validator = getattr(blind, "validate_structured_source_records", None)
        if validator is None:
            _fail("trusted source-first records validator is unavailable")
        validator(
            records_commitment=source_records,
            bundle_records={record_id: rows[record_id] for record_id in ids},
            input_files=files,
        )
    except Exception as exc:
        raise ReviewControllerError(
            "source-first response failed semantic validation"
        ) from exc
    # Persist the already validated Pass-A evidence DAG before the solver is
    # allowed to start. Keep the answer-bearing commitment in the root-owned
    # controller directory: the post-solver independent Review can reuse it,
    # while the Formalizer/Prover workspace never sees result_spec values.
    source_records_path = controller / f"{variant}-source-first-records.json"
    _atomic_root_file(source_records_path, _pretty(source_records))

    precommit = {
        "schema_version": SCHEMA_VERSION, "protocol": PROTOCOL,
        "phase": "structured_source_first_precommit",
        "variant": variant, "model_family": family, "model_id": model,
        "run_id": run_id, "request_profile": REQUEST_PROFILE,
        "tools_enabled": False, "store": False, "scope_ids": ids,
        "controller_binary_sha256": _file_sha(Path(__file__).resolve()),
        "input_inventory": {
            "root": str(input_root), "files": files,
            "files_sha256": blind._hash_index(files),
        },
        "review_projection_sha256": projection_sha,
        "adapter_provenance": _adapter_provenance(variant, source_first=True),
        "adapter": exchange.adapter, "transport": exchange.transport,
        "request": request_spec, "response": response_spec,
        "model_submission": model_spec,
        "normalized_response_sha256": model_spec["sha256"],
        "request_response_chain_sha256": exchange.chain_sha256,
        "status": "accepted", "finalized_before_solver": True,
    }
    if set(precommit) != PRECOMMIT_FIELDS:
        _fail("internal source-first precommit schema drift")
    output = controller / f"{variant}-source-first-precommit.json"
    _atomic_root_file(output, _pretty(precommit))
    return precommit


def _load_precommit(
    *, path: Path, variant: str, run_id: str, scope_ids: Sequence[str],
) -> tuple[Path, dict[str, Any], bytes]:
    result = _root_file(path, label="source-first precommit", private=True)
    payload = result.read_bytes()
    value = _strict_json(payload, label="source-first precommit")
    family, model = MODELS[variant]
    if set(value) != PRECOMMIT_FIELDS or (
        value.get("phase") != "structured_source_first_precommit"
        or value.get("protocol") != PROTOCOL
        or value.get("variant") != variant
        or value.get("model_family") != family
        or value.get("model_id") != model
        or value.get("run_id") != run_id
        or value.get("scope_ids") != list(scope_ids)
        or value.get("request_profile") != REQUEST_PROFILE
        or value.get("tools_enabled") is not False
        or value.get("store") is not False
        or value.get("status") != "accepted"
        or value.get("finalized_before_solver") is not True
    ):
        _fail("source-first precommit provenance/scope is stale")
    return result, value, payload


def _load_solver_aggregate(
    *, path: Path, precommit_sha: str, variant: str, run_id: str,
    scope_ids: Sequence[str],
) -> dict[str, Any]:
    result = _root_file(path, label="structured solver aggregate", private=True)
    value = _strict_json(result.read_bytes(), label="structured solver aggregate")
    family, model = MODELS[variant]
    if (
        value.get("phase") != "structured_solver_aggregate"
        or value.get("variant") != variant
        or value.get("model_family") != family
        or value.get("model_id") != model
        or value.get("run_id") != run_id
        or value.get("scope_ids") != list(scope_ids)
        or value.get("source_first_precommit_sha256") != precommit_sha
        or value.get("all_targets_finalized") is not True
    ):
        _fail("structured solver aggregate does not bind the source-first precommit")
    targets = value.get("targets")
    if not isinstance(targets, list) or [item.get("id") for item in targets if isinstance(item, Mapping)] != list(scope_ids):
        _fail("structured solver aggregate target coverage is stale")
    return value


def _load_bound_object(spec: object, *, label: str) -> tuple[Path, dict[str, Any]]:
    if not isinstance(spec, Mapping) or set(spec) != {"path", "sha256"}:
        _fail(f"{label} locator is invalid")
    path = _root_file(
        Path(str(spec.get("path") or "")), label=label, private=True,
    )
    if _file_sha(path) != spec.get("sha256"):
        _fail(f"{label} hash drift")
    return path, _strict_json(path.read_bytes(), label=label)


def _source_controller_records(
    *, precommit: Mapping[str, Any], rows: Mapping[str, Mapping[str, Any]],
    scope_ids: Sequence[str],
) -> dict[str, dict[str, Any]]:
    inventory = precommit.get("input_inventory")
    files = inventory.get("files") if isinstance(inventory, Mapping) else None
    if not isinstance(files, Mapping):
        _fail("source-first precommit input inventory is missing")
    records: dict[str, dict[str, Any]] = {}
    for record_id in scope_ids:
        relative = f"{blind._SOURCE_FIRST_RECORD_DIRECTORY}/{record_id}.json"
        digest = files.get(relative)
        if not isinstance(digest, str) or SHA256.fullmatch(digest) is None:
            _fail(f"source-first input lacks canonical record {record_id}")
        records[record_id] = {
            "blind_record_sha256": _sha(_canonical(rows[record_id])),
            "source_record_sha256": digest,
            "requested_outputs": rows[record_id].get("requested_outputs"),
        }
    return records


def _replace_root_file(path: Path, payload: bytes) -> Path:
    """Atomically replace one controller-managed file under a trusted parent."""
    parent = _root_dir(path.parent, label=f"controller parent for {path.name}")
    target = parent / path.name
    if target.is_symlink() or (target.exists() and not target.is_file()):
        _fail(f"controller target is not a regular file: {target}")
    temporary = parent / f".{target.name}.controller-new"
    if temporary.exists() or temporary.is_symlink():
        _fail(f"stale controller temporary file: {temporary}")
    descriptor = os.open(
        temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC, 0o400,
    )
    try:
        view = memoryview(payload)
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                _fail(f"short controller write: {target}")
            view = view[written:]
        os.fchown(descriptor, 0, 0)
        os.fchmod(descriptor, 0o400)
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    os.replace(temporary, target)
    directory_fd = os.open(parent, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
    try:
        os.fsync(directory_fd)
    finally:
        os.close(directory_fd)
    return target


def _write_review_gates(
    *, workspace: Path, scope_ids: Sequence[str], records: Sequence[Mapping[str, Any]],
) -> dict[str, dict[str, str]]:
    by_id = {
        str(record.get("id")): record for record in records
        if isinstance(record, Mapping) and isinstance(record.get("id"), str)
    }
    if list(by_id) != list(scope_ids):
        _fail("artifact Review records do not exactly cover gate scope")
    formal_targets: dict[str, Any] = {}
    proof_targets: dict[str, Any] = {}
    for record_id in scope_ids:
        record = by_id[record_id]
        target = _safe_relative(record.get("target"), label="Review gate target")
        formal = record.get("formalization_certificate")
        proof = record.get("proof_certificate")
        if (
            record.get("formalization_status") != "passed"
            or record.get("proof_status") != "solved"
            or not isinstance(formal, Mapping)
            or not isinstance(proof, Mapping)
        ):
            _fail(f"artifact Review record is not gate-passing: {record_id}")
        formal_targets[target] = {
            "status": "passed", "certificate": dict(formal),
        }
        proof_targets[target] = {"status": "solved", **dict(proof)}
    state = _root_dir(workspace / ".archon", label="Review gate directory")
    formal_path = _replace_root_file(
        state / "formalization-review-gate.json",
        _pretty({"version": 2, "targets": formal_targets}),
    )
    proof_path = _replace_root_file(
        state / "proof-review-gate.json",
        _pretty({"version": 2, "targets": proof_targets}),
    )
    return {"formalization": _locator(formal_path), "proof": _locator(proof_path)}


def _validate_gate_records_before_write(
    *, workspace: Path, rows: Mapping[str, Mapping[str, Any]],
    scope_ids: Sequence[str], records: Sequence[Mapping[str, Any]],
) -> None:
    by_id = {
        str(record.get("id")): record for record in records
        if isinstance(record, Mapping) and isinstance(record.get("id"), str)
    }
    if list(by_id) != list(scope_ids):
        _fail("artifact Review records do not exactly cover gate scope")
    for record_id in scope_ids:
        record = by_id[record_id]
        alignment = record.get("source_alignment")
        if (
            not isinstance(alignment, Mapping)
            or set(alignment) != {"status", "evidence"}
            or alignment.get("status") != "passed"
            or not isinstance(alignment.get("evidence"), str)
            or not alignment["evidence"].strip()
        ):
            _fail(f"artifact Review source alignment did not pass: {record_id}")
        target = _within(
            workspace, record.get("target"), label="artifact Review Lean target",
        )
        try:
            contract = blind.build_review_source_contract(
                project_path=workspace, target=target,
            )
            provenance = blind.source_contract_provenance(contract)
            formal = record.get("formalization_certificate")
            proof = record.get("proof_certificate")
            if not isinstance(formal, Mapping) or not isinstance(proof, Mapping):
                _fail(f"artifact Review certificate is missing for {record_id}")
            blind._validate_gate_record(
                gate_name="formalization Review gate",
                record={"status": "passed", "certificate": dict(formal)},
                expected_status="passed", expected_provenance=provenance,
                expected_contract=contract,
                requested_outputs=rows[record_id].get("requested_outputs"),
            )
            blind._validate_gate_record(
                gate_name="proof Review gate",
                record={"status": "solved", **dict(proof)},
                expected_status="solved", expected_provenance=provenance,
                expected_contract=contract,
                requested_outputs=rows[record_id].get("requested_outputs"),
            )
        except ReviewControllerError:
            raise
        except Exception as exc:
            raise ReviewControllerError(
                f"artifact Review gate certificate failed validation: {record_id}"
            ) from exc


def _validate_review_gates(
    *, workspace: Path, scope_ids: Sequence[str], records: Sequence[Mapping[str, Any]],
    expected: Mapping[str, Any],
) -> None:
    # Recompute into memory rather than trusting status bits in the gate files.
    by_id = {str(record.get("id")): record for record in records}
    formal_targets: dict[str, Any] = {}
    proof_targets: dict[str, Any] = {}
    for record_id in scope_ids:
        record = by_id[record_id]
        target = _safe_relative(record.get("target"), label="Review gate target")
        formal_targets[target] = {
            "status": "passed", "certificate": record["formalization_certificate"],
        }
        proof_targets[target] = {
            "status": "solved", **dict(record["proof_certificate"]),
        }
    wanted = {
        "formalization": _pretty({"version": 2, "targets": formal_targets}),
        "proof": _pretty({"version": 2, "targets": proof_targets}),
    }
    names = {
        "formalization": "formalization-review-gate.json",
        "proof": "proof-review-gate.json",
    }
    if set(expected) != set(names):
        _fail("artifact submission gate binding is invalid")
    for key, name in names.items():
        path = _within(workspace, f".archon/{name}", label=f"{key} Review gate")
        if path.read_bytes() != wanted[key] or expected[key] != _locator(path):
            _fail(f"{key} Review gate differs from constructed certificate records")


def _validate_verifier_timing(
    *, path: Path, verifier_snapshot: Path, snapshot_files: Mapping[str, str],
    snapshot_sha: str, scope_ids: Sequence[str],
) -> None:
    snapshot_root = _root_dir(
        verifier_snapshot, label="external clean verifier snapshot",
    )
    verifier_files = _inventory(snapshot_root, source_first=False)
    if verifier_files != dict(snapshot_files) or blind._hash_index(verifier_files) != snapshot_sha:
        _fail("external verifier snapshot differs from final project snapshot")
    result = _root_file(path, label="clean Lean verifier invocation", private=True)
    value = _strict_json(result.read_bytes(), label="clean Lean verifier invocation")
    if (
        value.get("phase") != "lean_verifier_invocation"
        or value.get("protocol") != PROTOCOL
        or value.get("exit_code") != 0
        or value.get("solver_stopped") is not True
        or value.get("descendants_stopped") is not True
        or value.get("snapshot_inventory_sha256") != snapshot_sha
        or value.get("snapshot_root") != str(snapshot_root)
    ):
        _fail("artifact Review requires a successful clean verifier invocation")
    receipt = value.get("verifier_receipt")
    if not isinstance(receipt, Mapping):
        _fail("clean verifier result receipt is missing")
    receipt_path = _root_file(
        Path(str(receipt.get("path") or "")), label="clean verifier result", private=True,
    )
    if _file_sha(receipt_path) != receipt.get("sha256"):
        _fail("clean verifier result hash drift")
    semantic = _strict_json(receipt_path.read_bytes(), label="clean verifier result")
    if (
        semantic.get("compiled") is not True
        or semantic.get("scope_ids") != list(scope_ids)
        or semantic.get("snapshot_inventory_sha256") != snapshot_sha
    ):
        _fail("clean verifier semantic result is stale")


def _copy_artifact_input(
    *, workspace: Path, controller: Path, variant: str, run_id: str,
    solver: Mapping[str, Any], source_records_path: Path,
    scope_ids: Sequence[str], rows: Mapping[str, Mapping[str, Any]],
) -> tuple[Path, dict[str, str], dict[str, dict[str, Any]]]:
    root = controller.parent / f".{controller.name}-{variant}-{run_id}-artifact-review-input"
    if root.exists() or root.is_symlink():
        _fail("artifact Review input directory must be new")
    root.mkdir(mode=0o755)
    manifest_path = _within(workspace, blind.SEED_MANIFEST, label="seed manifest")
    manifest = _strict_json(manifest_path.read_bytes(), label="seed manifest")
    payload_files = manifest.get("payload_files")
    if not isinstance(payload_files, Mapping) or not payload_files:
        _fail("seed manifest has no payload inventory")
    selected: dict[str, str] = {}
    for relative, digest in payload_files.items():
        source = _within(workspace, relative, label="sealed seed payload")
        if _file_sha(source) != digest:
            _fail(f"seed payload hash drift: {relative}")
        selected[str(relative)] = str(digest)
    selected[blind.SEED_MANIFEST] = _file_sha(manifest_path)
    for relative in ROOT_GENERATED:
        selected[relative] = _file_sha(
            _within(workspace, relative, label="controller-generated root file")
        )
    targets = {
        str(item["id"]): item for item in solver.get("targets", [])
        if isinstance(item, Mapping) and isinstance(item.get("id"), str)
    }
    controller_records: dict[str, dict[str, Any]] = {}
    commitment = _strict_json(
        source_records_path.read_bytes(), label="source-first records commitment",
    )
    source_records = {
        str(item["id"]): item for item in commitment.get("records", [])
        if isinstance(item, Mapping) and isinstance(item.get("id"), str)
    }
    for record_id in scope_ids:
        target_receipt = targets.get(record_id)
        if not isinstance(target_receipt, Mapping):
            _fail(f"solver aggregate is missing {record_id}")
        artifacts = target_receipt.get("final_artifacts")
        report_spec = target_receipt.get("source_report")
        if not isinstance(artifacts, Mapping) or not isinstance(report_spec, Mapping):
            _fail(f"solver aggregate lacks artifact bindings for {record_id}")
        bound: dict[str, tuple[str, Path, str]] = {}
        for name in ("candidate", "lean", "blueprint"):
            spec = artifacts.get(name)
            if not isinstance(spec, Mapping):
                _fail(f"solver aggregate lacks {name} for {record_id}")
            relative = _safe_relative(spec.get("path"), label=f"{name} locator")
            source = _within(workspace, relative, label=f"current {name}")
            digest = _file_sha(source)
            if digest != spec.get("sha256"):
                _fail(f"current {name} hash differs from solver receipt")
            selected[relative] = digest
            bound[name] = (relative, source, digest)
        raw_report = Path(str(report_spec.get("path") or ""))
        report = _root_file(raw_report, label="current source report")
        try:
            report_relative = report.relative_to(workspace).as_posix()
        except ValueError:
            _fail("source report is outside clean snapshot")
        report_digest = _file_sha(report)
        if report_digest != report_spec.get("sha256"):
            _fail("source report hash differs from solver receipt")
        selected[report_relative] = report_digest
        try:
            contract = blind.build_review_source_contract(
                project_path=workspace, target=bound["lean"][1],
            )
            if not blind.is_answer_blind_contract(contract) or not contract.get("valid"):
                _fail(f"source contract is invalid for {record_id}")
            provenance = blind.source_contract_provenance(contract)
        except ReviewControllerError:
            raise
        except Exception as exc:
            raise ReviewControllerError(
                f"cannot build source contract for {record_id}"
            ) from exc
        source_row = source_records.get(record_id)
        if not isinstance(source_row, Mapping):
            _fail(f"source-first commitment is missing {record_id}")
        controller_records[record_id] = {
            "target": bound["lean"][0],
            "target_sha256": bound["lean"][2],
            "candidate_sha256": bound["candidate"][2],
            "source_report_sha256": report_digest,
            "blueprint_sha256": bound["blueprint"][2],
            "source_contract": provenance,
            "requested_outputs": rows[record_id].get("requested_outputs"),
            "images": provenance.get("images"),
            "source_commitment_record_sha256": _sha(_canonical(source_row)),
        }
    for relative in sorted(selected):
        _copy_exact(
            _within(workspace, relative, label="artifact Review source"),
            root.joinpath(*PurePosixPath(relative).parts),
        )
    _atomic_root_file(
        root / blind._SOURCE_COMMITMENT_INPUT,
        source_records_path.read_bytes(),
    )
    _seal_tree(root)
    files = _inventory(root, source_first=False)
    expected = dict(selected)
    expected[blind._SOURCE_COMMITMENT_INPUT] = _file_sha(source_records_path)
    if files != dict(sorted(expected.items())):
        _fail("artifact Review input differs from the exact sealed projection")
    return root, files, controller_records


def _build_source_records(
    *, controller: Path, precommit_path: Path, precommit: Mapping[str, Any],
    precommit_payload: bytes, rows: Mapping[str, Mapping[str, Any]],
    scope_ids: Sequence[str], variant: str, family: str, model: str,
) -> tuple[Path, dict[str, Any]]:
    _model_path, source_model = _load_bound_object(
        precommit.get("model_submission"), label="source-first model submission",
    )
    try:
        commitment = blind.construct_structured_source_records_commitment(
            model_submission=source_model,
            controller_records=_source_controller_records(
                precommit=precommit, rows=rows, scope_ids=scope_ids,
            ),
            scope_ids=scope_ids, variant=variant, model_family=family,
            model_id=model, run_id=str(precommit["run_id"]),
            review_input_inventory_sha256=str(
                precommit["input_inventory"]["files_sha256"]
            ),
            review_projection_sha256=str(precommit["review_projection_sha256"]),
        )
    except Exception as exc:
        raise ReviewControllerError("source-first model records are invalid") from exc
    output = controller / f"{variant}-source-first-records.json"
    payload = _pretty(commitment)
    if output.exists() or output.is_symlink():
        try:
            matches = (
                not output.is_symlink()
                and output.is_file()
                and output.read_bytes() == payload
            )
        except OSError as exc:
            raise ReviewControllerError(
                "cannot read persisted pre-solver source-first records"
            ) from exc
        if not matches:
            _fail("pre-solver source-first records differ from reconstructed records")
    else:
        _atomic_root_file(output, payload)
    return output, commitment


def run_artifact_submit(
    *, workspace: Path, controller_dir: Path, bundle_path: Path,
    source_first_precommit: Path, solver_aggregate: Path,
    dependency_root: Path, variant: str, run_id: str,
    scope_ids: Sequence[str], exchange_call: ExchangeCall | None = None,
    broker_credential_file: Path | None = None,
    broker_credential_format: str = "raw", broker_token_name: str | None = None,
    broker_user: str | None = None, broker_port: int = 0,
    codex_binary: Path | None = None, codex_home: Path | None = None,
) -> dict[str, Any]:
    """Freeze Pass B and write gates before snapshot/verification."""
    if os.geteuid() != 0:
        _fail("structured Review controller must run as root")
    if variant not in MODELS or SAFE_ID.fullmatch(run_id) is None:
        _fail("structured Review variant/run id is invalid")
    workspace = _root_dir(workspace, label="structured solver workspace")
    controller = _root_dir(controller_dir, label="Review controller directory")
    _root_dir(dependency_root, label="sealed dependency root")
    _bundle_payload, rows = _bundle(bundle_path)
    ids = _scope(rows, scope_ids)
    family, model = MODELS[variant]
    precommit_path, precommit, precommit_payload = _load_precommit(
        path=source_first_precommit, variant=variant, run_id=run_id,
        scope_ids=ids,
    )
    solver_path = _root_file(
        solver_aggregate, label="structured solver aggregate", private=True,
    )
    solver = _load_solver_aggregate(
        path=solver_path, precommit_sha=_sha(precommit_payload),
        variant=variant, run_id=run_id, scope_ids=ids,
    )
    source_records_path, source_records = _build_source_records(
        controller=controller, precommit_path=precommit_path,
        precommit=precommit, precommit_payload=precommit_payload, rows=rows,
        scope_ids=ids, variant=variant, family=family, model=model,
    )
    source_records_spec = _locator(source_records_path)
    artifact_root, artifact_files, controller_records = _copy_artifact_input(
        workspace=workspace, controller=controller, variant=variant,
        run_id=run_id, solver=solver, source_records_path=source_records_path,
        scope_ids=ids, rows=rows,
    )
    request, projection_sha = _review_request(
        root=artifact_root, files=artifact_files, scope_ids=ids,
        variant=variant, model=model, source_first=False,
        source_records_sha256=source_records_spec["sha256"],
    )
    transport_dir = controller / f"{variant}-{run_id}-artifact-review-transport"
    exchange, request_spec, response_spec, model_spec = _perform_exchange(
        controller=controller, transport_dir=transport_dir,
        pass_name="artifact-review", target_id="independent-artifact-review",
        variant=variant, run_id=run_id, request=request, source_first=False,
        exchange_call=exchange_call,
        broker_credential_file=broker_credential_file,
        broker_credential_format=broker_credential_format,
        broker_token_name=broker_token_name, broker_user=broker_user,
        broker_port=broker_port, codex_binary=codex_binary, codex_home=codex_home,
    )
    _artifact_model_path, artifact_model = _load_bound_object(
        model_spec, label="artifact Review model submission",
    )
    try:
        records = blind.construct_structured_review_records(
            source_first=False, model_submission=artifact_model,
            controller_records=controller_records, scope_ids=ids,
        )
    except Exception as exc:
        raise ReviewControllerError("artifact Review model verdict is invalid") from exc
    records_document = {
        "schema_version": SCHEMA_VERSION, "protocol": PROTOCOL,
        "phase": "independent_artifact_review_records",
        "evaluation_mode": "answer_blind", "official_answer_seen": False,
        "variant": variant, "model_family": family, "model_id": model,
        "run_id": run_id, "request_profile": REQUEST_PROFILE,
        "review_input_inventory_sha256": blind._hash_index(artifact_files),
        "review_projection_sha256": projection_sha,
        "source_records_sha256": source_records_spec["sha256"],
        "scope_ids": ids, "records": records,
    }
    if set(records_document) != ARTIFACT_RECORDS_FIELDS:
        _fail("internal artifact Review records schema drift")
    records_path = controller / f"{variant}-artifact-review-records.json"
    _atomic_root_file(records_path, _pretty(records_document))
    _validate_gate_records_before_write(
        workspace=workspace, rows=rows, scope_ids=ids, records=records,
    )
    gate_specs = _write_review_gates(
        workspace=workspace, scope_ids=ids, records=records,
    )
    submission = {
        "schema_version": SCHEMA_VERSION, "protocol": PROTOCOL,
        "phase": "structured_artifact_review_submission",
        "variant": variant, "model_family": family, "model_id": model,
        "run_id": run_id, "request_profile": REQUEST_PROFILE,
        "tools_enabled": False, "store": False, "scope_ids": ids,
        "controller_binary_sha256": _file_sha(Path(__file__).resolve()),
        "source_first_precommit": _locator(precommit_path),
        "structured_solver_receipt": _locator(solver_path),
        "source_records_commitment": source_records_spec,
        "input_inventory": {
            "root": str(artifact_root), "files": artifact_files,
            "files_sha256": blind._hash_index(artifact_files),
        },
        "review_projection_sha256": projection_sha,
        "adapter_provenance": _adapter_provenance(variant, source_first=False),
        "adapter": exchange.adapter, "transport": exchange.transport,
        "request": request_spec, "response": response_spec,
        "model_submission": model_spec,
        "normalized_response_sha256": model_spec["sha256"],
        "request_response_chain_sha256": exchange.chain_sha256,
        "constructed_records_receipt": _locator(records_path),
        "review_gates": gate_specs, "status": "accepted",
        "submitted_before_verifier": True,
    }
    if set(submission) != ARTIFACT_SUBMISSION_FIELDS:
        _fail("internal artifact submission schema drift")
    output = controller / f"{variant}-artifact-review-submission.json"
    _atomic_root_file(output, _pretty(submission))
    return submission


def _load_artifact_submission(
    *, path: Path, variant: str, run_id: str, scope_ids: Sequence[str],
    precommit_path: Path, solver_path: Path,
) -> tuple[Path, dict[str, Any]]:
    result = _root_file(path, label="artifact Review submission", private=True)
    value = _strict_json(result.read_bytes(), label="artifact Review submission")
    family, model = MODELS[variant]
    if set(value) != ARTIFACT_SUBMISSION_FIELDS or (
        value.get("phase") != "structured_artifact_review_submission"
        or value.get("variant") != variant
        or value.get("model_family") != family
        or value.get("model_id") != model
        or value.get("run_id") != run_id
        or value.get("scope_ids") != list(scope_ids)
        or value.get("request_profile") != REQUEST_PROFILE
        or value.get("tools_enabled") is not False
        or value.get("store") is not False
        or value.get("status") != "accepted"
        or value.get("submitted_before_verifier") is not True
        or value.get("source_first_precommit") != _locator(precommit_path)
        or value.get("structured_solver_receipt") != _locator(solver_path)
    ):
        _fail("artifact Review submission provenance/status is stale")
    return result, value


def run_artifact_finalize(
    *, workspace: Path, controller_dir: Path, bundle_path: Path,
    source_first_precommit: Path, solver_aggregate: Path,
    artifact_submission: Path, verifier_invocation: Path,
    verifier_snapshot: Path, dependency_root: Path,
    snapshot_inventory_sha256: str, variant: str, run_id: str,
    scope_ids: Sequence[str],
) -> dict[str, Any]:
    """Replay frozen A/B records after final clean verification; no model call."""
    if os.geteuid() != 0:
        _fail("structured Review controller must run as root")
    if variant not in MODELS or SAFE_ID.fullmatch(run_id) is None:
        _fail("structured Review variant/run id is invalid")
    if SHA256.fullmatch(snapshot_inventory_sha256) is None:
        _fail("snapshot inventory digest is invalid")
    workspace = _root_dir(workspace, label="final solver snapshot")
    controller = _root_dir(controller_dir, label="Review controller directory")
    dependency = _root_dir(dependency_root, label="sealed dependency root")
    try:
        snapshot_files = blind._project_snapshot_inventory(
            workspace, dependency_root=dependency,
        )
    except Exception as exc:
        raise ReviewControllerError("final solver snapshot is invalid") from exc
    if blind._hash_index(snapshot_files) != snapshot_inventory_sha256:
        _fail("final solver snapshot digest differs from controller expectation")
    _bundle_payload, rows = _bundle(bundle_path)
    ids = _scope(rows, scope_ids)
    family, model = MODELS[variant]
    precommit_path, precommit, precommit_payload = _load_precommit(
        path=source_first_precommit, variant=variant, run_id=run_id,
        scope_ids=ids,
    )
    solver_path = _root_file(
        solver_aggregate, label="structured solver aggregate", private=True,
    )
    _load_solver_aggregate(
        path=solver_path, precommit_sha=_sha(precommit_payload),
        variant=variant, run_id=run_id, scope_ids=ids,
    )
    _submission_path, submission = _load_artifact_submission(
        path=artifact_submission, variant=variant, run_id=run_id,
        scope_ids=ids, precommit_path=precommit_path, solver_path=solver_path,
    )
    _validate_verifier_timing(
        path=verifier_invocation, verifier_snapshot=verifier_snapshot,
        snapshot_files=snapshot_files, snapshot_sha=snapshot_inventory_sha256,
        scope_ids=ids,
    )
    source_records_path, source_records = _load_bound_object(
        submission.get("source_records_commitment"),
        label="source-first records commitment",
    )
    expected_source = blind.construct_structured_source_records_commitment(
        model_submission=_load_bound_object(
            precommit.get("model_submission"),
            label="source-first model submission",
        )[1],
        controller_records=_source_controller_records(
            precommit=precommit, rows=rows, scope_ids=ids,
        ),
        scope_ids=ids, variant=variant, model_family=family, model_id=model,
        run_id=run_id,
        review_input_inventory_sha256=str(precommit["input_inventory"]["files_sha256"]),
        review_projection_sha256=str(precommit["review_projection_sha256"]),
    )
    if source_records != expected_source:
        _fail("source-first records commitment does not replay from precommit")
    source_records_sha = _file_sha(source_records_path)
    source_semantic = blind.construct_structured_review_envelope(
        source_first=True, records=source_records["records"], scope_ids=ids,
        variant=variant, model_family=family, model_id=model, run_id=run_id,
        snapshot_inventory_sha256=snapshot_inventory_sha256,
        review_input_inventory_sha256=str(precommit["input_inventory"]["files_sha256"]),
        review_projection_sha256=str(precommit["review_projection_sha256"]),
        source_first_precommit_sha256=_sha(precommit_payload),
        source_records_sha256=source_records_sha,
    )
    source_semantic_path = controller / f"{variant}-source-first-commitment.json"
    _atomic_root_file(source_semantic_path, _pretty(source_semantic))
    source_attempt = {
        **{
            key: value for key, value in precommit.items()
            if key not in {"phase", "finalized_before_solver"}
        },
        "phase": "structured_source_first_review_attempt",
        "snapshot_inventory_sha256": snapshot_inventory_sha256,
        "constructed_semantic_receipt": _locator(source_semantic_path),
        "source_first_precommit": _locator(precommit_path),
        "source_records_commitment": _locator(source_records_path),
    }
    if set(source_attempt) != SOURCE_ATTEMPT_FIELDS:
        _fail("internal source-first final attempt schema drift")
    try:
        blind._validate_source_first_commitment(
            commitment=source_semantic, attempt=source_attempt,
            seal={"freeze_scope": {"ids": ids}},
            input_files=dict(precommit["input_inventory"]["files"]),
            review_projection_sha256=str(precommit["review_projection_sha256"]),
            source_records=source_records,
            source_records_sha256=source_records_sha,
            source_first_precommit_sha256=_sha(precommit_payload),
        )
    except Exception as exc:
        raise ReviewControllerError("source-first semantic replay failed") from exc
    source_attempt_path = controller / f"{variant}-source-first-review-attempt.json"
    _atomic_root_file(source_attempt_path, _pretty(source_attempt))

    _records_path, records_document = _load_bound_object(
        submission.get("constructed_records_receipt"),
        label="artifact Review constructed records",
    )
    if set(records_document) != ARTIFACT_RECORDS_FIELDS or (
        records_document.get("phase") != "independent_artifact_review_records"
        or records_document.get("scope_ids") != ids
        or records_document.get("source_records_sha256") != source_records_sha
        or records_document.get("review_input_inventory_sha256")
        != submission["input_inventory"]["files_sha256"]
        or records_document.get("review_projection_sha256")
        != submission["review_projection_sha256"]
    ):
        _fail("artifact Review constructed records provenance is stale")
    records = records_document.get("records")
    if not isinstance(records, list):
        _fail("artifact Review constructed records are missing")
    _validate_review_gates(
        workspace=workspace, scope_ids=ids, records=records,
        expected=submission["review_gates"],
    )
    artifact_semantic = blind.construct_structured_review_envelope(
        source_first=False, records=records, scope_ids=ids,
        variant=variant, model_family=family, model_id=model, run_id=run_id,
        snapshot_inventory_sha256=snapshot_inventory_sha256,
        review_input_inventory_sha256=str(submission["input_inventory"]["files_sha256"]),
        review_projection_sha256=str(submission["review_projection_sha256"]),
        source_records_sha256=source_records_sha,
    )
    artifact_semantic_path = controller / f"{variant}-artifact-review-semantic.json"
    _atomic_root_file(artifact_semantic_path, _pretty(artifact_semantic))
    artifact_attempt = {
        "schema_version": SCHEMA_VERSION, "protocol": PROTOCOL,
        "phase": "structured_artifact_review_attempt",
        "variant": variant, "model_family": family, "model_id": model,
        "run_id": run_id, "request_profile": REQUEST_PROFILE,
        "tools_enabled": False, "store": False, "scope_ids": ids,
        "snapshot_inventory_sha256": snapshot_inventory_sha256,
        "controller_binary_sha256": submission["controller_binary_sha256"],
        "input_inventory": submission["input_inventory"],
        "review_projection_sha256": submission["review_projection_sha256"],
        "adapter_provenance": submission["adapter_provenance"],
        "adapter": submission["adapter"], "transport": submission["transport"],
        "request": submission["request"], "response": submission["response"],
        "model_submission": submission["model_submission"],
        "constructed_semantic_receipt": _locator(artifact_semantic_path),
        "normalized_response_sha256": submission["normalized_response_sha256"],
        "request_response_chain_sha256": submission["request_response_chain_sha256"],
        "status": "accepted",
        "source_records_commitment": _locator(source_records_path),
        "source_first_attempt_sha256": _file_sha(source_attempt_path),
    }
    if set(artifact_attempt) != ARTIFACT_ATTEMPT_FIELDS:
        _fail("internal artifact Review attempt schema drift")
    try:
        blind._validate_artifact_review_receipt(
            review=artifact_semantic, attempt=artifact_attempt,
            seal={"freeze_scope": {"ids": ids}},
            input_files=dict(submission["input_inventory"]["files"]),
            source_records_sha256=source_records_sha,
            review_projection_sha256=str(submission["review_projection_sha256"]),
        )
    except Exception as exc:
        raise ReviewControllerError("artifact Review semantic replay failed") from exc
    artifact_attempt_path = controller / f"{variant}-artifact-review-attempt.json"
    _atomic_root_file(artifact_attempt_path, _pretty(artifact_attempt))
    aggregate = {
        "schema_version": SCHEMA_VERSION, "protocol": PROTOCOL,
        "phase": "structured_independent_review_aggregate",
        "variant": variant, "model_family": family, "model_id": model,
        "run_id": run_id, "request_profile": REQUEST_PROFILE,
        "tools_enabled": False, "store": False, "scope_ids": ids,
        "snapshot_inventory_sha256": snapshot_inventory_sha256,
        "controller_binary_sha256": submission["controller_binary_sha256"],
        "source_first_attempt": _locator(source_attempt_path),
        "artifact_review_attempt": _locator(artifact_attempt_path),
        "source_records_sha256": source_records_sha,
        "source_commitment_sha256": _file_sha(source_semantic_path),
        "semantic_review_sha256": _file_sha(artifact_semantic_path),
        "all_passes_finalized": True,
    }
    if set(aggregate) != AGGREGATE_FIELDS:
        _fail("internal structured Review aggregate schema drift")
    output = controller / f"{variant}-structured-independent-review.json"
    _atomic_root_file(output, _pretty(aggregate))
    return aggregate


def _common_transport(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--broker-credential-file", type=Path)
    parser.add_argument(
        "--broker-credential-format", choices=("raw", "json", "env"),
        default="raw",
    )
    parser.add_argument("--broker-token-name")
    parser.add_argument("--broker-user")
    parser.add_argument("--broker-port", type=int, default=0)
    parser.add_argument("--codex-binary", type=Path)
    parser.add_argument("--codex-home", type=Path)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    source = subparsers.add_parser("source-first")
    source.add_argument("--controller-dir", type=Path, required=True)
    source.add_argument("--bundle", type=Path, required=True)
    source.add_argument("--asset-root", type=Path, required=True)
    source.add_argument("--variant", choices=sorted(MODELS), required=True)
    source.add_argument("--run-id", required=True)
    source.add_argument("--scope-id", action="append", default=[])
    _common_transport(source)
    submit = subparsers.add_parser("artifact-submit")
    submit.add_argument("--workspace", type=Path, required=True)
    submit.add_argument("--controller-dir", type=Path, required=True)
    submit.add_argument("--bundle", type=Path, required=True)
    submit.add_argument("--source-first-precommit", type=Path, required=True)
    submit.add_argument("--solver-aggregate", type=Path, required=True)
    submit.add_argument("--dependency-root", type=Path, required=True)
    submit.add_argument("--variant", choices=sorted(MODELS), required=True)
    submit.add_argument("--run-id", required=True)
    submit.add_argument("--scope-id", action="append", default=[])
    _common_transport(submit)
    final = subparsers.add_parser("artifact-finalize")
    final.add_argument("--workspace", type=Path, required=True)
    final.add_argument("--controller-dir", type=Path, required=True)
    final.add_argument("--bundle", type=Path, required=True)
    final.add_argument("--source-first-precommit", type=Path, required=True)
    final.add_argument("--solver-aggregate", type=Path, required=True)
    final.add_argument("--artifact-submission", type=Path, required=True)
    final.add_argument("--verifier-invocation", type=Path, required=True)
    final.add_argument("--verifier-snapshot", type=Path, required=True)
    final.add_argument("--dependency-root", type=Path, required=True)
    final.add_argument("--snapshot-inventory-sha256", required=True)
    final.add_argument("--variant", choices=sorted(MODELS), required=True)
    final.add_argument("--run-id", required=True)
    final.add_argument("--scope-id", action="append", default=[])
    return parser


def main() -> int:
    args = _parser().parse_args()
    try:
        if args.command == "source-first":
            transport = dict(
                broker_credential_file=args.broker_credential_file,
                broker_credential_format=args.broker_credential_format,
                broker_token_name=args.broker_token_name,
                broker_user=args.broker_user, broker_port=args.broker_port,
                codex_binary=args.codex_binary, codex_home=args.codex_home,
            )
            run_source_first(
                controller_dir=args.controller_dir, bundle_path=args.bundle,
                asset_root=args.asset_root, variant=args.variant,
                run_id=args.run_id, scope_ids=args.scope_id, **transport,
            )
        elif args.command == "artifact-submit":
            transport = dict(
                broker_credential_file=args.broker_credential_file,
                broker_credential_format=args.broker_credential_format,
                broker_token_name=args.broker_token_name,
                broker_user=args.broker_user, broker_port=args.broker_port,
                codex_binary=args.codex_binary, codex_home=args.codex_home,
            )
            run_artifact_submit(
                workspace=args.workspace, controller_dir=args.controller_dir,
                bundle_path=args.bundle,
                source_first_precommit=args.source_first_precommit,
                solver_aggregate=args.solver_aggregate,
                dependency_root=args.dependency_root,
                variant=args.variant, run_id=args.run_id,
                scope_ids=args.scope_id, **transport,
            )
        else:
            run_artifact_finalize(
                workspace=args.workspace, controller_dir=args.controller_dir,
                bundle_path=args.bundle,
                source_first_precommit=args.source_first_precommit,
                solver_aggregate=args.solver_aggregate,
                artifact_submission=args.artifact_submission,
                verifier_invocation=args.verifier_invocation,
                verifier_snapshot=args.verifier_snapshot,
                dependency_root=args.dependency_root,
                snapshot_inventory_sha256=args.snapshot_inventory_sha256,
                variant=args.variant, run_id=args.run_id,
                scope_ids=args.scope_id,
            )
    except ReviewControllerError as exc:
        raise SystemExit(f"error: {exc}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
