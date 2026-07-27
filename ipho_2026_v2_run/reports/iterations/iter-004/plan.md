# Iteration 004 plan

## Decision made

- Repair exactly the two Proof Review-rejected theory contracts in `physics-formalize`.
- C.1 takes `Parameters.Valid`; this is the smallest physical premise that rules out the supplied negative-momentum counterexample while preserving all accepted downstream signatures.
- B.1 derives the radius equation from maximum-ray tangency, then exhibits \(\alpha=R,\beta=-R/2\); it no longer assumes coefficient identity. Reverse only if Formalization Review finds the existential answer contract disconnected from the derived equation.

## Evidence

- Official T1 solution derives the scalar law from momentum/energy conservation with \(p_\gamma=\hbar\omega/c\).
- Official T2 solution derives \(a=R\sin\theta_{\max}-(R/2)\sin(2\theta_{\max})\) from the tangent limiting ray.
- Proof Review: 20/22 theory targets accepted; only these two require redraft.
- Added blueprint entries and dependency edges for all six unmatched length helpers; removed both malformed bare-label prose occurrences.

## Deferrals

- All six E1 targets, including the `4_B_6` Physlib-import doctor finding, are user-skipped.
- `def:project:hello` remains isolated because it is a dependency-free bootstrap definition; wiring a false dependency would corrupt the graph.

## Tool substitutions

- `archon dag-query` is unavailable on `PATH`; used injected leandag state plus direct Lean/blueprint pin checks.

## Subagent skips

- None enabled; classic single-agent loop requested.
