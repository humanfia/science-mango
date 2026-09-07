# Kimi r25 portable checkpoint

Captured 2026-09-07 UTC from the stopped r25 workspace. This checkpoint is
only for continuing the Kimi experiment; never expose it to the fresh GPT
answer-blind run.

## State

- Formalization review: 28/28 passed.
- Proof review: 26 solved, 2 retry, 0 exhausted.
- Retry targets: T1-B2 and T2-A1, both with 3 of 4 reviewed attempts consumed.
- T1-C1 and T1-C2 were solved during r25.
- T2-A1 was administratively reopened for migration; its history is retained.
- There was no final r25 receipt. The old controller and broker had exited.

## Inventory

- `controller-blind/`: exact 28-row question-only JSONL and blind manifest.
- `workspace-overlay/`: 28 current Lean targets, blueprint chapters, and the 28
  question-only source reports referenced by the proof-gate contracts.
- `archon-state/`: authoritative gate JSON, progress notes, one iteration anchor,
  and selected T1-B2 salvage files.
- `CHECKSUMS.sha256`: SHA-256 for every other file in this directory.

No credential, official solution/marking file, controller grader, runtime,
cache, broker transcript, private home, or complete model log is included.

The `b2_*.lean` files are reference scratch only. In particular,
`b2_work.lean` has no `sorry` tokens but its last whole-file compile reported
41 errors. Do not replace the main T1-B2 target with it without repairing and
compiling it.

Known non-blocking provenance caveat: the inherited T2-C2 blueprint currently
hashes to `d22c...`, while its historical solved proof certificate records
`399d...`. This drift was already present in the stopped r25 workspace and is
outside the two retry targets. Runtime provenance validation remains fresh for
all 26 solved Lean targets; do not rewrite T2-C2 while continuing B2/A1.

## Restore

Follow the root [`README.md`](../../README.md): build and validate a fresh
problem-only seed, configure it for Kimi, then copy `workspace-overlay/.` to
the workspace root and `archon-state/.` to its `.archon/` directory. Start a
fresh `--from prover` campaign for two objectives. Do not try to resume an old
Claude session.

Before restoring, verify the package:

```bash
cd handoff/ipho-2026-kimi-r25
sha256sum -c CHECKSUMS.sha256
```
