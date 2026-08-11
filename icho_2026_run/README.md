# IChO 2026 K3 clean-room rerun

This Lake project reruns the 32 theory-ready IChO 2026 subquestions from
papers T1--T9 with `kimi-k3[1m]` through the Claude Code harness. Practical
papers P1--P3 remain outside the target set.

The branch inherits the pinned Lean 4.31.0, Mathlib, Physlib, CRNT, and shared
chemistry infrastructure from `chemistry`. Before the rerun, all 32 prior
problem proofs, problem blueprints, source reports, Review certificates, and
runtime sessions were removed. The official source JSONL and source images are
the only problem-specific inputs.

## Clean-room boundary

Agents working in this project must not inspect Git history, another worktree,
the `chemistry` branch, or any previously published IChO proof dataset. They
may use only the current source question, marking-scheme answer, source images,
pinned upstream dependencies, and declarations present in this worktree.

## Status

The K3 rerun is being prepared. Success requires all 32 targets to pass direct
Lean compilation, source-aware formalization Review, proof Review, placeholder
scans, axiom sweeps, and the default Lake build.

## Build

```bash
lake exe cache get
lake build
```

The target queue is `references/icho_2026_theory_ready.jsonl`.
