# Prover result: `problem_phyx_mini_0300.lean`

## Status

Complete. All four `sorry` placeholders were replaced by sound proofs of the
frozen declarations. No placeholders remain and no redraft is needed.

## Proof summary

- `sine_phaseOffsetRadians_eq_one_third` specializes the sinusoidal
  displacement law at the graph origin. The figure supplies the `2 mm`
  displacement and `6 mm` amplitude, while the problem-data predicate supplies
  `x = t = 0`; linear arithmetic then gives `sin φ = 1/3`.
- `cosine_phaseOffsetRadians_negative` specializes the transverse-velocity
  law at the same point. The rising trace, positive angular frequency, and
  negative temporal phase sign force `cos φ < 0`.
- `phaseOffsetRadians_eq_pi_sub_arcsin_one_third` first excludes phases in
  `[π, 2π)` using the positive sine, then excludes `[0, π/2]` using the
  negative cosine. Thus `π - φ ∈ [-π/2, π/2]`, where
  `Real.arcsin_eq_of_sin_eq` identifies it with `arcsin (1/3)`.
- `problem_phyx_mini_0300` proves the rigorous enclosure
  `11/4 < φ < 57/20`, hence `|φ - 14/5| < 1/20`. The enclosure uses the
  imported `Real.sin_bound`, an algebraic five-angle identity, and monotonicity
  of sine on `[-π/2, π/2]`. A case split over the four displayed choices then
  proves that D is at least as close as every alternative.

The primary bitmap `phyx_data/test_image/300.png` was inspected directly. It
agrees with the formalized readouts: the trace is at the first positive
`2 mm` grid line at `t = 0`, is rising there, and reaches the `6 mm` scale.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0300.lean`: exit code 0
  with no output.
- Lean LSP diagnostics: no errors, warnings, or failed dependencies.
- Source scan: no `sorry`, `admit`, introduced `axiom`, `sorryAx`,
  `native_decide`, or metaprogramming escape hatch.
- Axiom audit of
  `PhyXMiniProblems.ProblemPhyXMini0300.problem_phyx_mini_0300` reports only
  the standard imported foundations `propext`, `Classical.choice`, and
  `Quot.sound`, with no source warnings.

## Blueprint status

The blueprint chapter exists. It was not edited because the explicit prover
write-permission rule limits this task to the assigned Lean file and this
result file. The following environments are proof-closed and ready for the
orchestrator's `\leanok` synchronization:

- `thm:physics:phyx_mini_0300:target`
- `lem:physics:phyx-mini-0300:phyxminiproblems-problemphyxmini0300-sine-phaseoffsetradians-eq-one-third`
- `lem:physics:phyx-mini-0300:phyxminiproblems-problemphyxmini0300-cosine-phaseoffsetradians-negative`
- `lem:physics:phyx-mini-0300:phyxminiproblems-problemphyxmini0300-phaseoffsetradians-eq-pi-sub-arcsin-one-third`

## Workflow notes

- The requested `.archon/AGENTS.md` is absent from this checkout. The supplied
  role instructions, `.archon/prover-modes/physics.md`, `.archon/PROGRESS.md`,
  the blueprint chapter, source report, grounding report, primary bitmap, and
  assigned Lean file were used instead.
- The advertised `archon` executable is not available on this lane's `PATH`,
  so the optional DAG node and ancestor queries could not run. The source
  report independently records `previous_parts: []`.
- The assigned Lean file contains no file-specific `/- USER: ... -/` comment.

## Redraft needed

None.

## Summary

- Sorry count: 4 → 0.
- Closed declarations: all four assigned lemmas/theorems.
- Still open: none.
