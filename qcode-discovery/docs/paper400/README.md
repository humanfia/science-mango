# paper400 cube, solve, checkpoint, and resume runbook

This runbook is for branch paper400-adaptive-resume-v1:

https://github.com/humanfia/science-mango/tree/paper400-adaptive-resume-v1

The implementation keeps three kinds of evidence separate:

- cube manifests bind a mutually exclusive and exhaustive partition;
- DMTCP records preserve search transport state but make no UNSAT claim;
- a leaf becomes scientific evidence only after its complete DRAT is converted
  to LRAT and both proofs are independently checked against the exact leaf CNF.

Run roots, proof.drat, LRAT files, and DMTCP images are intentionally not stored
in ordinary Git.

## 1. Clone and install

With a configured GitHub SSH key:

~~~bash
git clone --branch paper400-adaptive-resume-v1 --single-branch \
  git@github.com:humanfia/science-mango.git
cd science-mango/qcode-discovery
uv sync --frozen --extra sat --group dev
PY="$PWD/.venv/bin/python"
~~~

Without an SSH key, use:

~~~bash
git clone --branch paper400-adaptive-resume-v1 --single-branch \
  https://github.com/humanfia/science-mango.git
cd science-mango/qcode-discovery
uv sync --frozen --extra sat --group dev
PY="$PWD/.venv/bin/python"
~~~

Use absolute canonical paths for inputs and run roots. A prepare/init target
must not exist yet; its parent must exist and be writable.

## 2. Required prepared toolchain

A Git clone alone is not sufficient for the strict four-lane production
runner. The second machine should use the prepared Ubuntu 24.04 x86-64 image
or install byte-identical files at these fixed paths:

- /root/cadical-rel-1.9.5-standalone-audit/build/cadical
- /root/cadical-rel-1.9.5-standalone-audit/build/standalone-audit-manifest.json
- the complete /root/dmtcp-v4.2.0-install prefix
- /root/qcode-proof-tools/bin/drat-trim
- /root/qcode-proof-tools/bin/lrat-check
- /root/qcode-proof-tools/trusted-checker-policy.json
- /root/science-mango-qcode-coset-two-block/qcode-discovery/.venv/bin/python,
  resolving to the pinned /usr/bin/python3.12

Important pinned hashes are:

~~~text
f8b70724eb0af0ea3b5c0c305fa6a959822ce680326f04ceee7b44ce970d1171  cadical
d9297104990410d960a11b10cb9e1facca9ea08cdfd50c1a6f843a522da11eee  standalone-audit-manifest.json
63f7e80bb6ea39cf1b7fe7998a809f791aa5724ff4e77731d400b6c7ab022891  dmtcp_launch
a56701f7f2ee2156437501bd3b16e5e34cdefc6e4da9b05b01d9e0ac5a56e3fe  dmtcp_command
a57d8d05dcc78ce6b04c1c79ea703e48d3ec5dd99857cfd5066ac3f0b493432b  dmtcp_restart
3eec60c21ed4aacaa6445a761775e03624d052703a0d54eb4771c7f5e5a67902  dmtcp_coordinator
20c7f3b5a6b0d6e4601f3044fc0ab52c4b54ac2bd8e8e24ab83243fedbf2e6ea  mtcp_restart
a48ebed7b4b6b373d3ddbeb3368dae7622a9e17bab7fe6eb751ab996757f9fbe  drat-trim
5b87b3ee157db3b1c6b0b70e23faa40ab123c8dd6db63d9518d64312da579517  lrat-check
353163220be9065fa7204ae364fd54699d34718595b38d67a9d2094210121deb  trusted-checker-policy.json
1643dacd9feaedc58f3cc581e4d22577dfe25c09b10282936186ccf0f2e61118  python3.12
~~~

The runner also hashes the DMTCP libraries, dynamic loader, libc, libgcc,
libm, libstdc++, runner sources, and trusted-checker policy. It fails closed on
a mismatch. Copy the complete prepared prefixes; do not assume a fresh rebuild
is compatible.

## 3. Preflight tests

Run from qcode-discovery:

~~~bash
PY="$PWD/.venv/bin/python"
test -x "$PY"
"$PY" -m pytest \
  tests/test_run_cadical_dmtcp_resume_v1.py \
  tests/test_run_cadical_dmtcp_resume_v1_spawn_cleanup.py \
  tests/test_paper400_dic5_nested_width10_launch_chain_v1.py -q
~~~

The optional BCP-aware cuber is TEST_ONLY preprocessing and is not silently
used by the production runner. Its separate test requires a C++17 compiler,
pthread, and the pinned CaDiCaL static library.

## 4. Authenticated campaign inputs

Copy these three small inputs from the trusted first-machine material set into
one directory, then verify their file hashes:

~~~text
2c5b188a6d7417fd2f56694c6da990ac0221adeb34f2417f5384925d7bb6debb  parent-manifest.json
887371a9c9839edf268e86901050ccf31ddd13d97788c03cc63158bcafb35c0b  width6-campaign.json
d416c6515156b443f128f36ca885dd8ee855726fe71a990097e71be7a3a12569  width10-campaign.json
~~~

The authenticated internal campaign identifiers are parent
843a6b804a08c745d0a61fd4cad885d7499dc55336e49e27d53820ca1d9a439f,
width-6 fd0ff559268fca3c6fa90fcd72924f59cf5aa85e7bb68a9de8122847b6f93814,
and width-10
98730d510cbd039b8086aff2a2816703ec6d5a64adbeb350a592acf51abd76ba.

## 5. Start unused work on a second machine

The first machine has reserved batch indices 1 through 11. Each batch contains
four independent single-process CaDiCaL lanes. The runner does not detect
duplicate work across hosts or different run roots, so record ownership of the
new range in a shared ledger before launching.

Recommended allocation on a 48-logical-CPU second host:

- batches 12 through 22: 44 solver lanes on CPUs 0 through 43, leaving four
  logical CPUs for the system;
- batches 12 through 23: 48 solver lanes on CPUs 0 through 47.

The following launches the recommended 44 lanes. Run it from the cloned
qcode-discovery directory. Set INPUT and RUN_PARENT to real absolute paths.
RUN_PARENT must exist; each generated batch root must not.

~~~bash
set -euo pipefail

REPO="$PWD"
PY="$REPO/.venv/bin/python"
RUNNER="$REPO/scripts/run_paper400_dic5_nested_width10_four_lane_v1.py"
test -x "$PY"
test -f "$RUNNER"
test "$(readlink -f /root/science-mango-qcode-coset-two-block/qcode-discovery/.venv/bin/python)" = /usr/bin/python3.12
sha256sum -c <<EOF
f8b70724eb0af0ea3b5c0c305fa6a959822ce680326f04ceee7b44ce970d1171  /root/cadical-rel-1.9.5-standalone-audit/build/cadical
d9297104990410d960a11b10cb9e1facca9ea08cdfd50c1a6f843a522da11eee  /root/cadical-rel-1.9.5-standalone-audit/build/standalone-audit-manifest.json
63f7e80bb6ea39cf1b7fe7998a809f791aa5724ff4e77731d400b6c7ab022891  /root/dmtcp-v4.2.0-install/bin/dmtcp_launch
a56701f7f2ee2156437501bd3b16e5e34cdefc6e4da9b05b01d9e0ac5a56e3fe  /root/dmtcp-v4.2.0-install/bin/dmtcp_command
a57d8d05dcc78ce6b04c1c79ea703e48d3ec5dd99857cfd5066ac3f0b493432b  /root/dmtcp-v4.2.0-install/bin/dmtcp_restart
3eec60c21ed4aacaa6445a761775e03624d052703a0d54eb4771c7f5e5a67902  /root/dmtcp-v4.2.0-install/bin/dmtcp_coordinator
20c7f3b5a6b0d6e4601f3044fc0ab52c4b54ac2bd8e8e24ab83243fedbf2e6ea  /root/dmtcp-v4.2.0-install/bin/mtcp_restart
a48ebed7b4b6b373d3ddbeb3368dae7622a9e17bab7fe6eb751ab996757f9fbe  /root/qcode-proof-tools/bin/drat-trim
5b87b3ee157db3b1c6b0b70e23faa40ab123c8dd6db63d9518d64312da579517  /root/qcode-proof-tools/bin/lrat-check
353163220be9065fa7204ae364fd54699d34718595b38d67a9d2094210121deb  /root/qcode-proof-tools/trusted-checker-policy.json
1643dacd9feaedc58f3cc581e4d22577dfe25c09b10282936186ccf0f2e61118  /root/science-mango-qcode-coset-two-block/qcode-discovery/.venv/bin/python
EOF

INPUT=/ABS/PAPER400-INPUTS
RUN_PARENT=/ABS/PAPER400-RUNS
TAG=host2-001

test -d "$RUN_PARENT"
sha256sum -c <<EOF
2c5b188a6d7417fd2f56694c6da990ac0221adeb34f2417f5384925d7bb6debb  $INPUT/parent-manifest.json
887371a9c9839edf268e86901050ccf31ddd13d97788c03cc63158bcafb35c0b  $INPUT/width6-campaign.json
d416c6515156b443f128f36ca885dd8ee855726fe71a990097e71be7a3a12569  $INPUT/width10-campaign.json
EOF

for j in $(seq 0 10); do
  batch=$((12 + j))
  cpu=$((4 * j))
  printf -v root '%s/paper400-batch-%04d-%s' "$RUN_PARENT" "$batch" "$TAG"
  test ! -e "$root"
  "$PY" "$RUNNER" prepare \
    --root "$root" \
    --parent-manifest "$INPUT/parent-manifest.json" \
    --width6-campaign "$INPUT/width6-campaign.json" \
    --width10-campaign "$INPUT/width10-campaign.json" \
    --parent-cube-index 0 \
    --batch-index "$batch" \
    --cpus "$cpu" "$((cpu + 1))" "$((cpu + 2))" "$((cpu + 3))" \
    --proof-max-bytes 68719476736 \
    --checkpoint-image-max-bytes 17179869184 \
    --checkpoint-images-per-generation-max 1 \
    --checkpoint-generation-max-count 64 \
    --checkpoint-generation-metadata-max-bytes 67108864
done

for j in $(seq 0 10); do
  batch=$((12 + j))
  printf -v root '%s/paper400-batch-%04d-%s' "$RUN_PARENT" "$batch" "$TAG"
  "$PY" "$RUNNER" start --root "$root"
done
~~~

For 48 lanes, change both seq 0 10 occurrences to seq 0 11. This adds batch 23
on CPUs 44 through 47.

These loops launch only the listed batches. They do not auto-refill the
remaining leaves of the 1024-leaf campaign.

## 6. Capacity preflight

The numeric caps above are validation ceilings per child root; they do not
reserve storage. Their per-child runtime ceiling is about 1.066 TiB.

Observed aggregate DRAT growth was about 1.7 TB/day at 48 lanes. Use a
dedicated volume with at least 3 TB free for each planned 24-hour interval,
plus checkpoint and LRAT headroom. Check df before launch and continuously
while running. A practical minimum is 64 GB RAM; 128 GB is safer.

## 7. Operate a four-lane batch

The coordinator accepts start, status, checkpoint-stop, resume,
verify-checkpoint, and harvest-inactive:

~~~bash
PY="$PWD/.venv/bin/python"
test -x "$PY"
"$PY" scripts/run_paper400_dic5_nested_width10_four_lane_v1.py status \
  --root /ABS/BATCH_ROOT

"$PY" scripts/run_paper400_dic5_nested_width10_four_lane_v1.py checkpoint-stop \
  --root /ABS/BATCH_ROOT

"$PY" scripts/run_paper400_dic5_nested_width10_four_lane_v1.py resume \
  --root /ABS/BATCH_ROOT
~~~

checkpoint-stop must produce a commit for each active lane before that lane is
considered resumable. An already-finished UNSAT lane can appear unresolved
until harvest-inactive certifies it; that does not invalidate commits for the
other lanes.

A solver appends to proof.drat. Resume may truncate only the uncommitted suffix
written after the adopted checkpoint. DMTCP transport records remain TEST_ONLY
or COVER_ONLY_TRANSPORT and do not establish UNSAT.

## 8. Checkpoint portability limitation

Current v1 records bind the run root and leaf CNF to filesystem device and
inode identities. Ordinary cp, rsync, tar, object storage, Git LFS, or Xet
creates different identities. The destination therefore fails closed during
status, inspect, or resume even if every byte and mode is identical. This
branch has no supported rebind/reseal command.

Consequently:

- on a different filesystem, start unused batches from scratch as in section
  5; do not copy a checkpoint and call it resumable;
- takeover is supported only when both hosts see the same underlying shared
  filesystem objects, at the same absolute paths, with identical stat
  device/inode values;
- before a shared-filesystem takeover, checkpoint-stop the source, require
  matching commits, confirm that no source writer remains, then run status or
  inspect on the destination before resume;
- never resume the same root on two hosts.

## 9. Low-level single-leaf controller

For non-campaign testing, choose a normalized absolute RUN_ROOT that does not
exist and run:

~~~bash
PY="$PWD/.venv/bin/python"
test -x "$PY"
"$PY" scripts/run_cadical_dmtcp_resume_v1.py init \
  --root /ABS/RUN_ROOT \
  --cnf /ABS/LEAF.cnf \
  --solver /ABS/CADICAL/build/cadical \
  --dmtcp-prefix /ABS/DMTCP \
  --solver-arg=-q \
  --runtime-lib /ABS/ld-linux-x86-64.so.2 \
  --runtime-lib /ABS/libc.so.6 \
  --runtime-lib /ABS/libgcc_s.so.1 \
  --runtime-lib /ABS/libm.so.6 \
  --runtime-lib /ABS/libstdc++.so.6 \
  --runtime-libs-complete

"$PY" scripts/run_cadical_dmtcp_resume_v1.py start --root /ABS/RUN_ROOT
"$PY" scripts/run_cadical_dmtcp_resume_v1.py status --root /ABS/RUN_ROOT
"$PY" scripts/run_cadical_dmtcp_resume_v1.py checkpoint-stop \
  --root /ABS/RUN_ROOT
"$PY" scripts/run_cadical_dmtcp_resume_v1.py resume --root /ABS/RUN_ROOT
"$PY" scripts/run_cadical_dmtcp_resume_v1.py inspect --root /ABS/RUN_ROOT
~~~

Never copy a live root. status avoids hashing multi-gigabyte artifacts;
inspect performs the expensive bound-hash verification.

## 10. Scientific completion

A successful solver exit is not the final parent proof. Every leaf needs:

1. a terminal UNSAT marker from the bound solver;
2. a complete DRAT checked against the exact leaf CNF;
3. DRAT-to-LRAT conversion and an independent LRAT check;
4. hashes binding CNF, cube, proof, tools, and cover manifest;
5. an aggregate record showing that all mutually exclusive and exhaustive
   leaves have accepted terminal certificates.

Checkpoint records, cuber scores, and partial DRAT files are transport or
planning evidence only.
