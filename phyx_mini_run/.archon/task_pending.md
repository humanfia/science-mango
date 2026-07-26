# Pending Tasks

- **Eligible proof queue:** empty. Of 963 formalization-passed files, 933 are
  proof-Review solved, six earlier certified files are closed outside
  proof-gate tracking, and the remaining 24 are `proof_review_exhausted`.
  Iteration 042 therefore has eligibility shortfall 32.
- **Proof-Review-exhausted repair:** never redispatch `0071`, `0075`, `0088`,
  `0089`, `0096`, `0110`, `0115`, `0116`, `0118`, `0120`, `0127`, `0150`,
  `0158`, `0160`, `0169`, `0308`, `0428`, `0439`, `0544`, `0546`, `0869`,
  `0909`, `0967`, or `0971`. Nine of these retain 11 placeholders; fifteen
  have no placeholder but still failed elaboration/faithfulness Review.
  Structural repair plus explicit gate reset is required.
- **Grounding-evidence repair:** 35 current statements lack genuine
  post-formalization reports: `0078`, `0135`, `0165`, `0195`, `0197`, `0206`,
  `0325`, `0330`, `0331`, `0384`, `0388`, `0418`, `0435`, `0441`, `0455`,
  `0462`, `0463`, `0465`, `0466`, `0467`, `0472`, `0478`, `0483`, `0488`,
  `0498`, `0513`, `0514`, `0547`, `0596`, `0611`, `0627`, `0663`, `0776`,
  `0786`, and `0790`. Generic preflights do not satisfy the gate.
- **Stale grounding reports:** `0117` must document the symbolic all-distance
  destructive-interference equivalence, and `0629` the implicit Shockley/KVL
  equation with missing numerical input voltage and resistance.
- **Import blockers:** `0206` and `0472` also require a direct `Mathlib` import
  through an authorized Lean-writing structural route before re-review.
- **Isolated declaration cleanup:** 29 declaration-site-only nodes are
  confirmed unused and await an authorized Lean structural cleanup; do not
  invent graph edges.
- **Control files:** run-local `.archon/AGENTS.md` and
  `.archon/prompts/{plan,review}.md` remain absent; identical canonical copies
  are known, but restoration is outside the plan agent's write domain.
