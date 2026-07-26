# Prover result: `problem_phyx_mini_0095.lean`

## Status

Complete. The sole `sorry` was replaced by a sound proof without changing the
theorem signature or any preceding declaration.

## Proof summary

- Unfolded the two right-triangle relations and used
  `tan θ = sin θ / cos θ` on the acute angle branches.
- Combined those relations with `sin² θ + cos² θ = 1` and Snell's law to
  derive the exact squared-index identity
  `n² d² (H² + (d + s)²) = (d + s)² (H² + d²)`.
- Normalized by the positive run `d`, then used the supplied scale intervals
  `1.45 ≤ (d+s)/d ≤ 1.48` and `2.1 ≤ H/d ≤ 2.2`.
- Proved by exact rational polynomial bounds that
  `1.25 < n < 1.35`. This gives the requested `0.05` tolerance around `1.3`
  and proves that answer A is strictly closer than B, C, or D.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0095.lean`: exited 0 with
  no output.
- Lean LSP diagnostics: no errors; only style warnings about blank lines
  inside the long tactic proof.
- Source scan: no `sorry`, `admit`, `axiom`, `sorryAx`, or `native_decide`.
- `lean_verify` reports only the standard foundational axioms `propext`,
  `Classical.choice`, and `Quot.sound`, with no source-scan warnings.
- Sorry count: 1 → 0. Still open: none.

## Blueprint status

The target theorem is ready for `\leanok`. The blueprint was not edited
because this prover lane explicitly permits writes only to the assigned Lean
file and this result file; marker synchronization remains for an authorized
sync phase.

## Environment notes

- The requested run-local `.archon/AGENTS.md` is absent, as already recorded
  in `.archon/PROGRESS.md`.
- The advertised `archon dag-query` command was unavailable on `PATH`
  (`archon: command not found`). The proof is self-contained in the target's
  stated hypotheses.

## Redraft needed

None.
