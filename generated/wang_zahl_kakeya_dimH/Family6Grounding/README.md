# Family 6 grounding checkpoint

This directory contains the first small, independently buildable Family 6
grounding checkpoint. It records data-bearing plank/slab incidence semantics,
the machine grounding gate, and the direct fine-analytic angle-row reduction.

The current result is **fine-analytic-grounded**, not production-occurrence
aligned. In particular, it does not identify the analytic fine index with a
coarse occurrence bucket or infer a count through an arbitrary reindexing.

Two geometric inputs remain explicit and unproved here:

- `FaithfulCommonTangentFineAngleCoverage`, a coherence comparison across the
  possibly different existential certificate frames witnessing membership for
  one legacy slab body and scale;
- `FaithfulFineAngleOccupancyControl`, the scale-dependent packing estimate for
  canonical fine angle rows.

Thus this checkpoint is a conditional reduction, not a completed Family 6
proof. Build it with `lake build Family6Grounding`.
