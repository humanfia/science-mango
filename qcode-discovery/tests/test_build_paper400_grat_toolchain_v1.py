from __future__ import annotations

import argparse
import io
import json
from pathlib import Path
import subprocess
import tarfile

import pytest

from scripts import build_paper400_grat_toolchain_v1 as build


EXPECTED_INPUTS = {
    "gratgen.tgz": {
        "url": "https://www21.in.tum.de/~lammich/grat/gratgen.tgz",
        "sha256": "27673b4a87f1651aba9a5d366de2c2bf999f7bb9e11fd84830416cb022aa017f",
    },
    "gratchk-sml.tgz": {
        "url": "https://www21.in.tum.de/~lammich/grat/gratchk-sml.tgz",
        "sha256": "0d2f1ef904c4b34711e31f7d5fcfd7f726f60c4fac5e6afa11ef6b3ea86295e1",
    },
    "mlton-20210117.tgz": {
        "url": (
            "https://github.com/MLton/mlton/releases/download/"
            "on-20210117-release/"
            "mlton-20210117-1.amd64-linux-glibc2.31.tgz"
        ),
        "sha256": "749cb59d6baccd644143709be866105228d2b6dcd40c507a90b89c9b5e0f45d2",
    },
    "libboost1.74-dev.deb": {
        "url": (
            "https://archive.ubuntu.com/ubuntu/pool/main/b/boost1.74/"
            "libboost1.74-dev_1.74.0-14ubuntu3_amd64.deb"
        ),
        "sha256": "4d9c90e43f0d25db6280d1ee326771cbb76462f73b9430f06bac1de8d05b7a78",
    },
    "libgmp-dev.deb": {
        "url": (
            "https://archive.ubuntu.com/ubuntu/pool/main/g/gmp/"
            "libgmp-dev_6.2.1+dfsg-3ubuntu1_amd64.deb"
        ),
        "sha256": "e4ce547c5c5e4efd98854d06559349b3a03272eb343f1bd8e4ccac7b783229a3",
    },
}


def _tar_member(
    archive: tarfile.TarFile,
    name: str,
    payload: bytes,
    *,
    mode: int = 0o600,
) -> None:
    member = tarfile.TarInfo(name)
    member.size = len(payload)
    member.mode = mode
    archive.addfile(member, io.BytesIO(payload))


def _completed(
    argv: list[str], returncode: int = 0, stdout: str = "",
) -> subprocess.CompletedProcess[str]:
    return subprocess.CompletedProcess(argv, returncode, stdout=stdout, stderr=None)


def test_network_inputs_are_exactly_content_addressed() -> None:
    assert build.INPUTS == EXPECTED_INPUTS
    assert all(
        len(record["sha256"]) == 64
        and set(record["sha256"]) <= set("0123456789abcdef")
        and record["url"].startswith("https://")
        for record in build.INPUTS.values()
    )


@pytest.mark.parametrize("member_name", ["../escape", "a/../../escape", "/tmp/escape"])
def test_safe_extract_rejects_path_traversal(
    tmp_path: Path, member_name: str,
) -> None:
    archive_path = tmp_path / "bad.tgz"
    with tarfile.open(archive_path, "w:gz") as archive:
        _tar_member(archive, member_name, b"escaped")
    target = tmp_path / "extract"
    with pytest.raises(build.BuildError, match="unsafe archive member"):
        build.safe_extract(archive_path, target)
    assert not (tmp_path / "escape").exists()


def test_safe_extract_keeps_regular_files_and_skips_all_links(tmp_path: Path) -> None:
    archive_path = tmp_path / "links.tgz"
    with tarfile.open(archive_path, "w:gz") as archive:
        _tar_member(archive, "tree/kept.txt", b"kept")
        symbolic = tarfile.TarInfo("tree/symbolic")
        symbolic.type = tarfile.SYMTYPE
        symbolic.linkname = "../../outside"
        archive.addfile(symbolic)
        hard = tarfile.TarInfo("tree/hard")
        hard.type = tarfile.LNKTYPE
        hard.linkname = "tree/kept.txt"
        archive.addfile(hard)
    target = tmp_path / "extract"
    build.safe_extract(archive_path, target)
    assert (target / "tree/kept.txt").read_bytes() == b"kept"
    assert not (target / "tree/symbolic").exists()
    assert not (target / "tree/symbolic").is_symlink()
    assert not (target / "tree/hard").exists()
    assert not (tmp_path / "outside").exists()


def test_safe_extract_rejects_special_members(tmp_path: Path) -> None:
    archive_path = tmp_path / "fifo.tgz"
    with tarfile.open(archive_path, "w:gz") as archive:
        fifo = tarfile.TarInfo("tree/fifo")
        fifo.type = tarfile.FIFOTYPE
        archive.addfile(fifo)
    with pytest.raises(build.BuildError, match="special archive member"):
        build.safe_extract(archive_path, tmp_path / "extract")


def test_download_hash_mismatch_fails_closed_without_network(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    payload = b"not-the-pinned-archive"

    def fake_urlopen(
        _request: object, *, timeout: int,
    ) -> io.BytesIO:
        assert timeout == 120
        return io.BytesIO(payload)

    monkeypatch.setattr(build.urllib.request, "urlopen", fake_urlopen)
    target = tmp_path / "download.tgz"
    with pytest.raises(build.BuildError, match="hash mismatch"):
        build.download(
            "https://example.invalid/input", target, "0" * 64, len(payload)
        )
    assert target.read_bytes() == payload


def test_download_rejects_content_larger_than_pinned_size(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    payload = b"one-byte-too-large"

    monkeypatch.setattr(
        build.urllib.request,
        "urlopen",
        lambda _request, *, timeout: io.BytesIO(payload),
    )
    with pytest.raises(build.BuildError, match="oversized download"):
        build.download(
            "https://example.invalid/input",
            tmp_path / "oversized.tgz",
            "0" * 64,
            len(payload) - 1,
        )


def test_rename_noreplace_never_replaces_concurrent_target(tmp_path: Path) -> None:
    source = tmp_path / "source"
    source.mkdir()
    (source / "source-marker").write_bytes(b"source")
    target = tmp_path / "target"
    target.mkdir()
    (target / "target-marker").write_bytes(b"target")

    with pytest.raises(build.BuildError, match="refusing to replace"):
        build.rename_noreplace(source, target)

    assert (source / "source-marker").read_bytes() == b"source"
    assert (target / "target-marker").read_bytes() == b"target"


def test_main_refuses_existing_output_before_any_download_or_command(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    output = tmp_path / "existing"
    output.mkdir(mode=0o700)
    marker = output / "keep"
    marker.write_bytes(b"untouched")
    monkeypatch.setattr(
        build, "parse_args", lambda: argparse.Namespace(output=output),
    )
    monkeypatch.setattr(
        build, "download",
        lambda *_args, **_kwargs: pytest.fail("download must not run"),
    )
    monkeypatch.setattr(
        build, "run",
        lambda *_args, **_kwargs: pytest.fail("command must not run"),
    )
    with pytest.raises(build.BuildError, match="refusing to overwrite"):
        build.main()
    assert marker.read_bytes() == b"untouched"


def test_mock_build_publishes_only_an_inert_pilot_manifest(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    output = tmp_path / "grat-pilot"
    calls: dict[str, list[object]] = {"downloads": [], "commands": []}
    monkeypatch.setattr(
        build, "parse_args", lambda: argparse.Namespace(output=output),
    )

    def fake_download(
        url: str, target: Path, expected: str, expected_bytes: int,
    ) -> None:
        calls["downloads"].append((url, target.name, expected, expected_bytes))
        target.write_bytes(f"mock:{target.name}".encode("ascii"))

    def fake_extract(archive: Path, target: Path) -> None:
        target.mkdir(mode=0o700)
        if archive.name == "gratgen.tgz":
            source = target / "gratgen" / "gratgen.cpp"
            source.parent.mkdir(mode=0o700)
            source.write_bytes(b"int main() { return 0; }\n")
        elif archive.name == "gratchk-sml.tgz":
            source = target / "gratchk-sml" / "gratchk.mlb"
            source.parent.mkdir(mode=0o700)
            source.write_bytes(b"mock mlb\n")
        elif archive.name == "mlton-20210117.tgz":
            mlton = target / "mlton-test" / "bin" / "mlton"
            mlton.parent.mkdir(parents=True, mode=0o700)
            mlton.write_bytes(b"#!/bin/sh\nexit 0\n")
            mlton.chmod(0o700)
        else:  # pragma: no cover - INPUTS fixes the archive calls
            pytest.fail(f"unexpected archive: {archive}")

    def fake_run(
        argv: list[str], *, cwd: Path, check: bool = True,
    ) -> subprocess.CompletedProcess[str]:
        assert cwd.is_dir()
        calls["commands"].append((list(argv), cwd, check))
        if argv[0] == "/usr/bin/dpkg-deb":
            destination = Path(argv[-1])
            (destination / "usr/include").mkdir(parents=True, exist_ok=True)
            (destination / "usr/lib/x86_64-linux-gnu").mkdir(
                parents=True, exist_ok=True,
            )
            return _completed(argv)
        if argv[0] == "/usr/bin/g++" and argv[1:] == ["--version"]:
            return _completed(argv, stdout="g++ mock 1.0\nCopyright mock\n")
        if argv[0] == "/usr/bin/g++":
            binary = Path(argv[argv.index("-o") + 1])
            binary.write_bytes(b"mock gratgen executable\n")
            binary.chmod(0o700)
            return _completed(argv, stdout="mock gratgen build\n")
        if Path(argv[0]).name == "mlton":
            binary = Path(argv[argv.index("-output") + 1])
            binary.write_bytes(b"mock gratchk executable\n")
            binary.chmod(0o700)
            return _completed(argv, stdout="mock gratchk build\n")
        if Path(argv[0]).name == "gratgen":
            return _completed(
                argv, returncode=1,
                stdout="usage: gratgen --num-parallel N --binary-drat\n",
            )
        if Path(argv[0]).name == "gratchk":
            return _completed(
                argv, returncode=1,
                stdout="usage: gratchk unsat <cnf-file> <lemma-file> <proof-file>\n",
            )
        pytest.fail(f"unexpected command: {argv}")

    monkeypatch.setattr(build, "download", fake_download)
    monkeypatch.setattr(build, "safe_extract", fake_extract)
    monkeypatch.setattr(build, "run", fake_run)

    assert build.main() == 0
    assert output.is_dir()
    assert not any(tmp_path.glob(f".{output.name}.building-*"))
    assert calls["downloads"] == [
        (record["url"], name, record["sha256"], build.INPUT_BYTES[name])
        for name, record in EXPECTED_INPUTS.items()
    ]

    manifest = json.loads((output / "BUILD-MANIFEST.json").read_text(encoding="ascii"))
    assert manifest["kind"] == build.KIND
    assert manifest["version"] == 1
    assert manifest["production_eligible"] is False
    assert manifest["purpose"] == "isolated GRAT 1.3.3 4/8-thread Paper400 pilot"
    assert manifest["forbidden_effects"] == [
        "production terminal publication",
        "aggregate publication",
        "transport cleanup",
    ]
    assert manifest["required_flow"] == [
        "gratgen CNF binary-DRAT -l CERT.gratl -o CERT.gratp -b -j 4|8",
        "gratchk unsat CNF CERT.gratl CERT.gratp",
    ]
    assert manifest["artifacts"]["gratgen"]["sha256"] == build.sha256(
        output / "bin/gratgen"
    )
    assert manifest["artifacts"]["gratchk"]["sha256"] == build.sha256(
        output / "bin/gratchk"
    )
    assert (output / "bin/gratgen").stat().st_mode & 0o777 == 0o555
    assert (output / "bin/gratchk").stat().st_mode & 0o777 == 0o555
    assert not (tmp_path / "paper400-toolchain/proof-checkers").exists()
