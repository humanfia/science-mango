# Stage 2 rank-0 rerun handoff — 2026-08-17

## Objective and live run

- Run ID: `qcode-twisted-torus-ansatz-v3-science-strategy-v4-stage2-inclusive-rank0-rerun-v1`
- Production checkout: `/root/qcode-structural-screen-speedup/qcode-discovery`
- The run reuses the sealed Stage 1 candidate inputs and starts Stage 2 from a fresh generation-0 rank-0 ledger.
- Do not merge or deploy the interrupted receipt work in `.adaptive-page-scheduler-worktree`; it is unrelated WIP.

At 2026-08-17 13:33 UTC:

- Main Stage 2: PID/PGID/SID `1985330`, healthy heartbeat, generation `0`, 8 completed pages, cursor/committed `9792`, no reset.
- Strict discovery: PID/PGID/SID `2163862`, nice `10`, affinity `12-30,44-62`, 24 cooperative leases.
- Strict portfolio: 99,897 rows in 201 batches; no strict win yet.
- Deep/exact sidecars have not been started for this fresh run.

## Strict parent-ACK incident and fix

The proof CLI owns creation of a pending selection page; the strict parent wrapper owns the ACK. The old wrapper incorrectly expected the child to ACK, so batch 0 completed successfully but strict reported `FAILED` with a valid pending page.

Production hotfix commit: `39d571899334496548742e637c96d31c127e092e`

The fix:

- validates summary, ranked output, pending page, counts, digest uniqueness/subset and exact page order;
- records child completion durably;
- uses the canonical `acknowledge_selection_page` helper in the parent;
- recovers both pre-ACK and post-ACK crash windows without rerunning the backend;
- performs foreground-overlap fences before ACK and before progress commit;
- pins batch directories with no-follow dirfds and uses token/hash CAS plus same-directory `renameat`/`fsync` for the ledger update.

Verification:

- 75 focused strict tests passed in production.
- Two independent reviews returned GO with no P0/P1.
- A real batch-0 copy recovered with zero backend calls.
- Live batch 0 retained `attempts=1`; input/ranked/summary hashes and timestamps were unchanged.
- Live batch-0 ledger is now `cursor=100`, `completed_pages=1`, `ACK=1`, `committed=97`, `pending=null`.
- Strict progress is `next_row=100`, one completed batch (`97 REJECTED`, `3 known skips`), and batch 1 is active.

## Scientific best results

- Best trusted Stage 2 near-miss remains 13 tied `[[254,2,d<=39]]` codes. A replayed weight-39 logical witness gives the strict upper bound
  `FOM <= 2*39^2/254 = 1521/127 ~= 11.9763779528`.
  This is not an exact distance and is not a `>12` strict win.
- Best historical exact-distance reference remains `[[288,50,8]]`, with exact
  `FOM = 50*8^2/288 = 100/9 ~= 11.1111111111`.
  It is historical, not a new result from this rank-0 rerun.

## Monitoring commands

```bash
RUN=qcode-twisted-torus-ansatz-v3-science-strategy-v4-stage2-inclusive-rank0-rerun-v1
REPO=/root/qcode-structural-screen-speedup/qcode-discovery
PY=/root/science-mango-qcode-coset-two-block/qcode-discovery/.venv/bin/python

$PY -B -m humanize.pipeline_cli status --repo-dir "$REPO" --run-id "$RUN"
$PY -B -m humanize.strict_discovery_cli status --repo-dir "$REPO" --run-id "$RUN"
tail -n 100 "$REPO/results/humanize/pipelines/$RUN/pipeline.log"
tail -n 100 "$REPO/results/humanize/pipelines/$RUN/sidecars/stage2-strict-discovery-v1/worker.log"
```

Before any strict restart, re-run the canonical live-source overlap check and capacity gate. Do not manually edit/ACK a ledger, delete process/lock files, rebuild the portfolio, or reset a sealed cursor.

## Next actions

1. Let main Stage 2 and strict discovery continue; monitor sealed cursor/batch progress and wins.
2. If strict produces unresolved high-value candidates, enqueue only those into the separate deep multi-solver queue after evidence binding validation.
3. Preserve UNKNOWN as unresolved and retain only solver-proven bounds/witnesses; do not treat timeout as rejection or proof.
4. Push the production hotfix branch to the explicitly approved remote. The local production branch is one commit ahead until that external destination is authorized.
