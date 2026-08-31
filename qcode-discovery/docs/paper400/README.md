# paper400 cube, solve, checkpoint, and resume runbook

This directory documents the reproducible launch path for the paper400
CaDiCaL 1.9.5 experiments on branch `paper400-adaptive-resume-v1`.

The code separates three kinds of evidence:

- a cube manifest proves how a parent formula is partitioned;
- DMTCP records preserve transport state, but make no UNSAT claim;
- a leaf becomes scientific evidence only after a complete DRAT is converted
  to LRAT and both formats are independently checked against the bound CNF.

Do not commit run roots, `proof.drat`, LRAT files, or DMTCP images to ordinary
Git. They are large runtime artifacts and must be transferred through object
storage, Git LFS/Xet, or a byte-preserving host-to-host copy.

## 1. Checkout

```bash
git clone git@github.com:humanfia/science-mango.git
cd science-mango
git checkout paper400-adaptive-resume-v1
cd qcode-discovery
```

Use absolute, canonical paths for every run root and input. Runtime roots must
be owned by the invoking user and have mode `0700`.

## 2. Pinned runtime

The current manifests bind these exact components:

- CaDiCaL 1.9.5 executable SHA-256:
  `f8b70724eb0af0ea3b5c0c305fa6a959822ce680326f04ceee7b44ce970d1171`
- DMTCP 4.2.0 reference commit:
  `f8009ce7b4ad211311ca2f72a929b975e4aa1155`
- `dmtcp_launch` SHA-256:
  `63f7e80bb6ea39cf1b7fe7998a809f791aa5724ff4e77731d400b6c7ab022891`
- `dmtcp_command` SHA-256:
  `a56701f7f2ee2156437501bd3b16e5e34cdefc6e4da9b05b01d9e0ac5a56e3fe`
- `dmtcp_restart` SHA-256:
  `a57d8d05dcc78ce6b04c1c79ea703e48d3ec5dd99857cfd5066ac3f0b493432b`
- exact-resume controller SHA-256:
  `a71cb71e61061d7f925ccc04eb1ccaf48c00289d897b957394dfc8b730062505`

Before using a migrated checkpoint, reproduce the same CPU architecture,
absolute paths, dynamic loader, libc, libstdc++, CaDiCaL, and DMTCP files. The
controller rejects a mismatch rather than silently restarting a different
computation.

## 3. Tests

Run the resume and four-lane unit tests from `qcode-discovery`:

```bash
python -m pytest \
  tests/test_run_cadical_dmtcp_resume_v1.py \
  tests/test_run_cadical_dmtcp_resume_v1_spawn_cleanup.py \
  tests/test_paper400_dic5_nested_width10_launch_chain_v1.py -q
```

Build and test the optional BCP-aware cuber against the audited CaDiCaL static
library:

```bash
mkdir -p /ABS/BUILD
g++ -O2 -std=c++17 -Wall -Wextra -Werror \
  -I/ABS/CADICAL-1.9.5/src \
  native/cadical_bcp_aware_cuber_v1.cpp \
  /ABS/CADICAL-1.9.5/build/libcadical.a -lpthread \
  -o /ABS/BUILD/cadical_bcp_aware_cuber_v1

CADICAL_BCP_CUBER_BIN=/ABS/BUILD/cadical_bcp_aware_cuber_v1 \
  python -m pytest tests/test_cadical_bcp_aware_cuber_v1.py -q
```

## 4. Create a BCP-aware subcover

The BCP-aware cuber is currently an explicit `TEST_ONLY` preprocessing tool;
it is not silently wired into the proof runner.

```bash
/ABS/BUILD/cadical_bcp_aware_cuber_v1 \
  /ABS/PARENT.cnf 16 /ABS/COVER/parent 32
```

This emits a prefix-free adaptive tree, `.cubes`, `.icnf`, individual leaf
CNFs, TSV ledgers, and a coverage JSON. The tree construction validates
mutual exclusion and exhaustiveness by complementary-branch induction.
Propagation-terminal labels are heuristics until a proof checker accepts a
proof for the corresponding formula.

## 5. Start one resumable CaDiCaL leaf

The low-level exact-resume controller is:
`scripts/run_cadical_dmtcp_resume_v1.py`.

Create a new empty run root and bind the CNF, solver, DMTCP prefix, solver
arguments, and the complete runtime-library set:

```bash
python scripts/run_cadical_dmtcp_resume_v1.py init \
  --root /ABS/RUN_ROOT \
  --cnf /ABS/LEAF.cnf \
  --solver /ABS/CADICAL-1.9.5/build/cadical \
  --dmtcp-prefix /ABS/DMTCP-4.2.0 \
  --solver-arg=-q \
  --runtime-lib /ABS/ld-linux-x86-64.so.2 \
  --runtime-lib /ABS/libc.so.6 \
  --runtime-lib /ABS/libgcc_s.so.1 \
  --runtime-lib /ABS/libm.so.6 \
  --runtime-lib /ABS/libstdc++.so.6 \
  --runtime-libs-complete

python scripts/run_cadical_dmtcp_resume_v1.py start \
  --root /ABS/RUN_ROOT
```

The controller writes an ordinary append-only `proof.drat`. It deliberately
forbids DMTCP open-file checkpointing and unsafe overwrite flags.

Inspect without hashing multi-gigabyte artifacts:

```bash
python scripts/run_cadical_dmtcp_resume_v1.py status \
  --root /ABS/RUN_ROOT
```

Perform a committed checkpoint and stop the solver:

```bash
python scripts/run_cadical_dmtcp_resume_v1.py checkpoint-stop \
  --root /ABS/RUN_ROOT
```

Resume the latest committed generation:

```bash
python scripts/run_cadical_dmtcp_resume_v1.py resume \
  --root /ABS/RUN_ROOT
```

Use `inspect` before migration or publication; unlike `status`, it verifies
the bound hashes and may read the complete proof prefix:

```bash
python scripts/run_cadical_dmtcp_resume_v1.py inspect \
  --root /ABS/RUN_ROOT
```

Never copy a live run root. First obtain a successful `checkpoint-stop`
commit and confirm that no process has the proof open.

## 6. Four independent lanes

For an authenticated width-10 batch, prepare exactly four leaves:

```bash
python scripts/run_paper400_dic5_nested_width10_four_lane_v1.py prepare \
  --root /ABS/BATCH_ROOT \
  --parent-manifest /ABS/parent-manifest.json \
  --width6-campaign /ABS/width6-campaign.json \
  --width10-campaign /ABS/width10-campaign.json \
  --parent-cube-index 0 \
  --batch-index 0 \
  --cpus 0 1 2 3 \
  --proof-max-bytes 1099511627776 \
  --checkpoint-image-max-bytes 1099511627776 \
  --checkpoint-images-per-generation-max 64 \
  --checkpoint-generation-max-count 65536 \
  --checkpoint-generation-metadata-max-bytes 67108864

python scripts/run_paper400_dic5_nested_width10_four_lane_v1.py start \
  --root /ABS/BATCH_ROOT
```

The same coordinator accepts `status`, `checkpoint-stop`, `resume`,
`verify-checkpoint`, and `harvest-inactive`. It keeps four independent
single-process CaDiCaL lanes; it is not a shared-memory parallel solver.

## 7. Move a checkpoint to another machine

1. Run `checkpoint-stop` and require a committed checkpoint for every active
   root. A claim without its matching commit is not resumable evidence.
2. Transfer the entire run root, including the proof prefix, generation
   manifests, checkpoint image, logs, and restart script. Also transfer the
   exact CNF/cover manifests and pinned toolchain.
3. Preserve absolute paths, regular-file types, modes, ownership, and bytes.
4. Produce a SHA-256 manifest on the source and verify it on the destination.
5. Run `inspect` on the destination before `resume`.

For large paper400 roots, stream directly to object storage or the destination
host. Do not create a second local 70+ GB archive when disk headroom is low.

## 8. Scientific completion

A successful solver exit is not the final parent proof. Every leaf must have:

1. a terminal UNSAT marker from the bound solver;
2. a complete DRAT checked against the exact leaf CNF;
3. DRAT-to-LRAT conversion and an independent LRAT check;
4. hashes binding CNF, cube, proof, tools, and cover manifest;
5. an aggregate record showing that all mutually exclusive, exhaustive leaves
   have accepted terminal certificates.

Checkpoint records and BCP scores are transport/planning evidence only.
