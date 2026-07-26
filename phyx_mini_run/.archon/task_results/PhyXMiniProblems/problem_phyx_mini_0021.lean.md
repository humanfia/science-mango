# Prover result: `PhyXMiniProblems/problem_phyx_mini_0021.lean`

## Outcome

- Closed `PhyXMiniProblems.ProblemPhyXMini0021.upper_stack_snell_invariant`.
- Closed `PhyXMiniProblems.ProblemPhyXMini0021.problem_phyx_mini_0021`.
- Preserved both declaration signatures and all physical-model definitions.
- No `sorry`, `admit`, new axioms, or proof escape hatches remain.
- No redraft is needed.

## Proof

The helper chains the two upper-interface Snell equalities.

For the main theorem, the proof derives the exact characterization

`θ ∈ IncidentAnglesProducingFinalTIR setup`

iff `θ` is a physical angle and

`5 / 8 < sin θ ∧ sin θ ≤ 3 / 4`.

The strict lower inequality is precisely final-interface total internal
reflection. The upper inequality is also physically necessary: a ray with a
larger conserved `n * sin θ` cannot traverse the `1.60`--`1.40`--`1.20`
upper stack. Conversely, inverse-sine choices for the two refracted angles
construct a valid upper-stack ray throughout this interval.

Sine monotonicity on the principal branch then proves that
`arcsin (5 / 8)` is a lower bound. For any purported larger lower bound, the
midpoint between `arcsin (5 / 8)` and the smaller of that bound and
`arcsin (3 / 4)` supplies a member of the incidence set below it, proving the
greatest-lower-bound property.

The nearest-tenth conclusion is certified without floating-point evaluation.
The proof first derives `3.141 < π < 3.142` from `Real.cos_bound` and six
double-angle steps. It then expands the two rounding endpoints around
`π / 6`, using `Real.sin_bound`, `Real.cos_bound`, and rational bounds
`1.732 ≤ √3 ≤ 1.733`. This proves that the degree readout lies strictly
between `38.65` and `38.75`, hence matches choice C (`38.7°`).

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0021.lean`: passed.
- Lean LSP diagnostics: no errors or warnings.
- Source scan: no `sorry`, `sorryAx`, `admit`, or introduced `axiom`.
- Axiom verification for both declarations reports only standard foundational
  dependencies: `propext`, `Classical.choice`, and `Quot.sound`.

## Blueprint status

The helper lemma and target theorem are ready for `\leanok`. The blueprint was
not edited because prover permissions make it read-only; the synchronization
or review lane should add the markers.

## Redraft needed

None.
