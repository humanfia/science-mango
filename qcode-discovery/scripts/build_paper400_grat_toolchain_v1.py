#!/usr/bin/env python3
"""Build the isolated GRAT 1.3.3 Paper400 pilot toolchain.

This builder never modifies the production proof-checker directory.  Every
network input is content-addressed, the build happens in a new sibling staging
directory, and the completed tree is published with one atomic rename.
"""

from __future__ import annotations

import argparse
import ctypes
import errno
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import urllib.request


KIND = "paper400-grat-toolchain-build-v1"
DEFAULT_OUTPUT = Path("/home/jing/paper400-toolchain/grat-1.3.3-pilot-v1")

INPUTS = {
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

INPUT_BYTES = {
    "gratgen.tgz": 335_138,
    "gratchk-sml.tgz": 22_094,
    "mlton-20210117.tgz": 24_263_626,
    "libboost1.74-dev.deb": 9_608_510,
    "libgmp-dev.deb": 336_684,
}

AT_FDCWD = -100
RENAME_NOREPLACE = 1


class BuildError(RuntimeError):
    pass


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(8 * 1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def download(url: str, target: Path, expected: str, expected_bytes: int) -> None:
    request = urllib.request.Request(url, headers={"User-Agent": KIND})
    with urllib.request.urlopen(request, timeout=120) as source, target.open("xb") as sink:
        total = 0
        while True:
            chunk = source.read(min(8 * 1024 * 1024, expected_bytes + 1 - total))
            if not chunk:
                break
            total += len(chunk)
            if total > expected_bytes:
                raise BuildError(f"oversized download for {target.name}")
            sink.write(chunk)
        sink.flush()
        os.fsync(sink.fileno())
    if total != expected_bytes:
        raise BuildError(
            f"size mismatch for {target.name}: {total} != {expected_bytes}"
        )
    actual = sha256(target)
    if actual != expected:
        raise BuildError(f"hash mismatch for {target.name}: {actual} != {expected}")


def safe_extract(archive: Path, target: Path) -> None:
    target.mkdir(mode=0o700)
    target_real = target.resolve()
    with tarfile.open(archive, "r:gz") as tar:
        members = []
        for member in tar.getmembers():
            candidate = (target / member.name).resolve()
            if target_real not in candidate.parents and candidate != target_real:
                raise BuildError(f"unsafe archive member: {member.name}")
            if member.issym() or member.islnk():
                # None of the build inputs needs archive links.  In particular,
                # the pinned MLton package has one documentation-only symlink.
                continue
            if not member.isdir() and not member.isfile():
                raise BuildError(f"special archive member is not allowed: {member.name}")
            members.append(member)
        tar.extractall(target, members=members, filter="fully_trusted")


def run(
    argv: list[str], *, cwd: Path, check: bool = True,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        argv,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=check,
        timeout=600,
    )


def fsync_directory(path: Path) -> None:
    fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def rename_noreplace(source: Path, target: Path) -> None:
    """Atomically publish a directory without replacing any target."""

    libc = ctypes.CDLL(None, use_errno=True)
    renameat2 = getattr(libc, "renameat2", None)
    if renameat2 is None:
        raise BuildError("renameat2(RENAME_NOREPLACE) is required")
    renameat2.argtypes = [
        ctypes.c_int,
        ctypes.c_char_p,
        ctypes.c_int,
        ctypes.c_char_p,
        ctypes.c_uint,
    ]
    renameat2.restype = ctypes.c_int
    result = renameat2(
        AT_FDCWD,
        os.fsencode(source),
        AT_FDCWD,
        os.fsencode(target),
        RENAME_NOREPLACE,
    )
    if result:
        error = ctypes.get_errno()
        if error == errno.EEXIST:
            raise BuildError(f"refusing to replace concurrently created output: {target}")
        raise OSError(error, os.strerror(error), str(target))


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    output = args.output.resolve()
    if output.exists():
        raise BuildError(f"refusing to overwrite existing output: {output}")
    parent = output.parent
    if not parent.is_dir():
        raise BuildError(f"output parent does not exist: {parent}")

    staging = parent / f".{output.name}.building-{os.getpid()}"
    staging.mkdir(mode=0o700)
    downloads = staging / "downloads"
    downloads.mkdir(mode=0o700)
    sources = staging / "sources"
    sources.mkdir(mode=0o700)
    dependencies = staging / "dependencies"
    dependencies.mkdir(mode=0o700)
    binaries = staging / "bin"
    binaries.mkdir(mode=0o700)

    for name, record in INPUTS.items():
        download(
            record["url"], downloads / name, record["sha256"], INPUT_BYTES[name]
        )

    gratgen_source = sources / "gratgen"
    safe_extract(downloads / "gratgen.tgz", gratgen_source)
    gratchk_source = sources / "gratchk"
    safe_extract(downloads / "gratchk-sml.tgz", gratchk_source)
    mlton_root = dependencies / "mlton"
    safe_extract(downloads / "mlton-20210117.tgz", mlton_root)

    boost_root = dependencies / "boost"
    boost_root.mkdir(mode=0o700)
    run(
        ["/usr/bin/dpkg-deb", "-x", str(downloads / "libboost1.74-dev.deb"), str(boost_root)],
        cwd=staging,
    )
    gmp_root = dependencies / "gmp"
    gmp_root.mkdir(mode=0o700)
    run(
        ["/usr/bin/dpkg-deb", "-x", str(downloads / "libgmp-dev.deb"), str(gmp_root)],
        cwd=staging,
    )

    gratgen_cpp = gratgen_source / "gratgen" / "gratgen.cpp"
    gratgen_bin = binaries / "gratgen"
    gratgen_build = run(
        [
            "/usr/bin/g++",
            "-O3",
            "-DNDEBUG",
            "-std=c++11",
            "-pthread",
            f"-I{boost_root / 'usr/include'}",
            "-o",
            str(gratgen_bin),
            str(gratgen_cpp),
        ],
        cwd=staging,
    )

    mlton_candidates = list(mlton_root.glob("mlton-*/bin/mlton"))
    if len(mlton_candidates) != 1:
        raise BuildError(f"expected one MLton executable, found {mlton_candidates}")
    mlton = mlton_candidates[0]
    gratchk_build_root = gratchk_source / "gratchk-sml"
    gratchk_bin = binaries / "gratchk"
    gratchk_build = run(
        [
            str(mlton),
            "-verbose",
            "1",
            "-default-type",
            "int64",
            "-cc-opt",
            f"-I{gmp_root / 'usr/include/x86_64-linux-gnu'}",
            "-link-opt",
            f"-L{gmp_root / 'usr/lib/x86_64-linux-gnu'}",
            "-output",
            str(gratchk_bin),
            "gratchk.mlb",
        ],
        cwd=gratchk_build_root,
    )

    gratgen_bin.chmod(0o555)
    gratchk_bin.chmod(0o555)
    compiler = run(["/usr/bin/g++", "--version"], cwd=staging).stdout.splitlines()[0]
    gratgen_help_run = run([str(gratgen_bin)], cwd=staging, check=False)
    gratchk_help_run = run([str(gratchk_bin)], cwd=staging, check=False)
    gratgen_help = gratgen_help_run.stdout
    gratchk_help = gratchk_help_run.stdout
    if gratgen_help_run.returncode not in {0, 1, 2}:
        raise BuildError(f"unexpected gratgen help status: {gratgen_help_run.returncode}")
    if gratchk_help_run.returncode not in {0, 1, 2}:
        raise BuildError(f"unexpected gratchk help status: {gratchk_help_run.returncode}")
    if "--num-parallel" not in gratgen_help or "binary-drat" not in gratgen_help:
        raise BuildError("built gratgen lacks required parallel/binary-DRAT options")
    if "unsat <cnf-file> <lemma-file> <proof-file>" not in gratchk_help:
        raise BuildError("built gratchk lacks split-certificate mode")

    manifest = {
        "kind": KIND,
        "version": 1,
        "production_eligible": False,
        "purpose": "isolated GRAT 1.3.3 4/8-thread Paper400 pilot",
        "inputs": INPUTS,
        "build": {
            "compiler": compiler,
            "gratgen_argv": [
                "/usr/bin/g++", "-O3", "-DNDEBUG", "-std=c++11", "-pthread",
            ],
            "gratgen_log_sha256": hashlib.sha256(gratgen_build.stdout.encode()).hexdigest(),
            "gratchk_compiler": "MLton 20210117",
            "gratchk_log_sha256": hashlib.sha256(gratchk_build.stdout.encode()).hexdigest(),
        },
        "artifacts": {
            "gratgen": {"relative_path": "bin/gratgen", "sha256": sha256(gratgen_bin)},
            "gratchk": {"relative_path": "bin/gratchk", "sha256": sha256(gratchk_bin)},
        },
        "required_flow": [
            "gratgen CNF binary-DRAT -l CERT.gratl -o CERT.gratp -b -j 4|8",
            "gratchk unsat CNF CERT.gratl CERT.gratp",
        ],
        "forbidden_effects": [
            "production terminal publication",
            "aggregate publication",
            "transport cleanup",
        ],
    }
    manifest_bytes = (json.dumps(manifest, sort_keys=True, indent=2) + "\n").encode()
    manifest_path = staging / "BUILD-MANIFEST.json"
    with manifest_path.open("xb") as handle:
        handle.write(manifest_bytes)
        handle.flush()
        os.fsync(handle.fileno())
    fsync_directory(staging)
    rename_noreplace(staging, output)
    fsync_directory(parent)
    print(json.dumps({"output": str(output), "artifacts": manifest["artifacts"]}, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (BuildError, OSError, subprocess.CalledProcessError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        sys.exit(2)
