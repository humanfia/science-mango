# IPhO 2026 Lean formalization run

This directory is a reproducible snapshot of the IPhO 2026 Archon run built
from [`../ipho_2026_source`](../ipho_2026_source).

It contains:

- 28 target files in `IPhO2026Problems/`;
- the corresponding physics-aware Lean blueprint;
- source-extraction and per-target grounding/prover reports;
- the final formalization/proof Review gate snapshots.

## Build

```bash
lake exe cache get
lake build
```

The checked-in snapshot builds with Lean 4.31.0, Mathlib v4.31.0, and PhysLean
at the revision recorded in `lake-manifest.json`.

## Result

See [`RESULTS.md`](RESULTS.md). At the saved checkpoint, 25 of 28 targets passed
proof Review. Two Lean placeholders remain, while one additional placeholder-
free target remains semantically unresolved.

Runtime state, model logs, caches, local MCP configuration, credentials, and
machine-specific session metadata are intentionally not committed.
