# paper400 cube, solve, checkpoint, and resume runbook

This runbook is for branch paper400-adaptive-resume-v2:

https://github.com/humanfia/science-mango/tree/paper400-adaptive-resume-v2

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
git clone --branch paper400-adaptive-resume-v2 --single-branch \
  git@github.com:humanfia/science-mango.git
cd science-mango/qcode-discovery
uv sync --frozen --extra sat --group dev
PY="$PWD/.venv/bin/python"
~~~

Without an SSH key, use:

~~~bash
git clone --branch paper400-adaptive-resume-v2 --single-branch \
  https://github.com/humanfia/science-mango.git
cd science-mango/qcode-discovery
uv sync --frozen --extra sat --group dev
PY="$PWD/.venv/bin/python"
~~~

Use absolute canonical paths for inputs and run roots. A prepare/init target
must not exist yet; its parent must exist and be writable.

## 2. Required prepared toolchain

A Git clone alone is not sufficient for the strict four-lane production
runner. This branch is pinned to the prepared Ubuntu 22.04 x86-64 toolchain
at these fixed paths:

- /home/jing/paper400-toolchain/cadical-1.9.5/bin/cadical
- /home/jing/paper400-toolchain/audit/standalone-audit-manifest.json
- the complete /home/jing/paper400-toolchain/dmtcp-4.2.0 prefix
- /home/jing/paper400-toolchain/proof-checkers/bin/drat-trim
- /home/jing/paper400-toolchain/proof-checkers/bin/lrat-check
- /home/jing/paper400-toolchain/audit/trusted-checker-policy.json
- /home/jing/science-mango/qcode-discovery/.venv/bin/python, resolving to the
  pinned standalone CPython 3.12.14 path below
- Linux local filesystems with `F_SETLEASE` support; the runner uses an
  exclusive kernel write-lease probe to fail closed if any process still has
  the proof open, including processes hidden by `/proc` permissions

Important pinned hashes are:

~~~text
6e7d53fa447d13fb962de78c7bd6a6354711151529754a5684170bd9a6a36a21  cadical
e274b8e5ab4e9456096243ad5ce3a3a8248374590a0ebf49ce36653357294e6a  standalone-audit-manifest.json
2036e98a96ca701425a4d47d86b82d0b4657cf39cbac90cd22770dc9d65480ab  dmtcp_launch
aa4eebcbdaa62abde9af5e849f93423de22ce4415871c678095613598d3c4c98  dmtcp_command
b1e72dd345660cdcb3688accb4888542df3c8d1ed97e08ebbbfc46e783da32ae  dmtcp_restart
ed76910fe215c1507ca08814a4e2f94943b44027a7410f1aa5eb17f5b6ff8e77  dmtcp_coordinator
acfb3108fd9e42cf59ebfbb2f1a59e6a2df9b066ed73f1abd97d852a2467da69  mtcp_restart
8d25091073e9295028dd4aec85acca4d9b3381d2cfcc145a5b0e14ae909ce394  drat-trim
c523189a2c4c121bc1e6d284347cbbbec0d3ebf6a1deccb99cb4752548a3ee79  lrat-check
af3a2089ebf0df9b1120e1cfd3164cc6a2e9bf07bb35f057f3f85890d0f854e2  trusted-checker-policy.json
f7c6210eb40fadcd3c2889dddd24a15fc2c9f926aec5a03bf9da66e12d581526  python3.12
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
  tests/test_paper400_dic5_nested_width10_launch_chain_v1.py \
  tests/test_paper400_dic5_nested_width10_supervisor_v1.py \
  tests/test_paper400_transport_prune_v1.py -q
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
test "$(readlink -f "$PY")" = /home/jing/.local/share/uv/python/cpython-3.12.14-linux-x86_64-gnu/bin/python3.12
sha256sum -c <<EOF
6e7d53fa447d13fb962de78c7bd6a6354711151529754a5684170bd9a6a36a21  /home/jing/paper400-toolchain/cadical-1.9.5/bin/cadical
e274b8e5ab4e9456096243ad5ce3a3a8248374590a0ebf49ce36653357294e6a  /home/jing/paper400-toolchain/audit/standalone-audit-manifest.json
2036e98a96ca701425a4d47d86b82d0b4657cf39cbac90cd22770dc9d65480ab  /home/jing/paper400-toolchain/dmtcp-4.2.0/bin/dmtcp_launch
aa4eebcbdaa62abde9af5e849f93423de22ce4415871c678095613598d3c4c98  /home/jing/paper400-toolchain/dmtcp-4.2.0/bin/dmtcp_command
b1e72dd345660cdcb3688accb4888542df3c8d1ed97e08ebbbfc46e783da32ae  /home/jing/paper400-toolchain/dmtcp-4.2.0/bin/dmtcp_restart
ed76910fe215c1507ca08814a4e2f94943b44027a7410f1aa5eb17f5b6ff8e77  /home/jing/paper400-toolchain/dmtcp-4.2.0/bin/dmtcp_coordinator
acfb3108fd9e42cf59ebfbb2f1a59e6a2df9b066ed73f1abd97d852a2467da69  /home/jing/paper400-toolchain/dmtcp-4.2.0/bin/mtcp_restart
8d25091073e9295028dd4aec85acca4d9b3381d2cfcc145a5b0e14ae909ce394  /home/jing/paper400-toolchain/proof-checkers/bin/drat-trim
c523189a2c4c121bc1e6d284347cbbbec0d3ebf6a1deccb99cb4752548a3ee79  /home/jing/paper400-toolchain/proof-checkers/bin/lrat-check
af3a2089ebf0df9b1120e1cfd3164cc6a2e9bf07bb35f057f3f85890d0f854e2  /home/jing/paper400-toolchain/audit/trusted-checker-policy.json
f7c6210eb40fadcd3c2889dddd24a15fc2c9f926aec5a03bf9da66e12d581526  /home/jing/science-mango/qcode-discovery/.venv/bin/python
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

For a crash-safe host-local campaign that continuously reuses every listed
CPU after a leaf is certified and pruned, use the supervisor. The tag must be
new, and every generated batch root must not already exist:

~~~bash
SUPERVISOR="$REPO/scripts/run_paper400_dic5_nested_width10_supervisor_v1.py"
CPUS=($(seq 0 223))

"$PY" "$SUPERVISOR" preflight --input "$INPUT"
"$PY" "$SUPERVISOR" init \
  --run-parent "$RUN_PARENT" --input "$INPUT" --tag host2-001 \
  --batch-first 12 --batch-last 255 --cpus "${CPUS[@]}" \
  --stop-free-bytes 5497558138880 \
  --resume-free-bytes 6597069766656
"$PY" "$SUPERVISOR" run \
  --root "$RUN_PARENT/.paper400-supervisor-v1-host2-001"
~~~

`run` stays in the foreground and catches SIGINT/SIGTERM by checkpoint-stopping
all live lanes. `status` reports the durable campaign state; `checkpoint-stop`
performs an explicit safe stop. Run it under a persistent service manager when
it must survive SSH disconnects or reboots.

## 6. Capacity preflight

The numeric caps above are validation ceilings per child root; they do not
reserve storage. Their per-child runtime ceiling is about 1.066 TiB.

Observed aggregate DRAT growth was about 1.7 TB/day at 48 lanes. Use a
dedicated volume with at least 3 TB free for each planned 24-hour interval,
plus checkpoint and LRAT headroom. Check df before launch and continuously
while running. A practical minimum is 64 GB RAM; 128 GB is safer.

## 7. Operate a four-lane batch

The coordinator accepts start, status, checkpoint-stop, resume,
verify-checkpoint, harvest-inactive, and prune-transport:

~~~bash
PY="$PWD/.venv/bin/python"
test -x "$PY"
"$PY" scripts/run_paper400_dic5_nested_width10_four_lane_v1.py status \
  --root /ABS/BATCH_ROOT

"$PY" scripts/run_paper400_dic5_nested_width10_four_lane_v1.py checkpoint-stop \
  --root /ABS/BATCH_ROOT

"$PY" scripts/run_paper400_dic5_nested_width10_four_lane_v1.py resume \
  --root /ABS/BATCH_ROOT

# Irreversible. Every lane must already have a fully replayed final proof.
"$PY" scripts/run_paper400_dic5_nested_width10_four_lane_v1.py prune-transport \
  --root /ABS/BATCH_ROOT
~~~

checkpoint-stop must produce a commit for each active lane before that lane is
considered resumable. An already-finished UNSAT lane can appear unresolved
until harvest-inactive certifies it; that does not invalidate commits for the
other lanes.

A solver appends to proof.drat. Resume may truncate only the uncommitted suffix
written after the adopted checkpoint. DMTCP transport records remain TEST_ONLY
or COVER_ONLY_TRANSPORT and do not establish UNSAT.

`prune-transport` first runs the same fresh final-root DRAT/LRAT replay used by
`verify-final`, writes a durable manifest of every entry authorized for
deletion, and then removes only `runtime/dmtcp`. It retains the exact leaf CNF,
copied DRAT, converted LRAT, certificates, validation, and predecessor records.
The action is fail-closed, resumable after an interrupted deletion, and
idempotent after its prune commit. It refuses unfinished leaves, changed
transport entries, symlink escapes, hard links, and non-plain entries. Pruning
is irreversible: the leaf cannot be resumed afterward, although `status` and
`verify-final` continue to work from the retained proof evidence.

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
