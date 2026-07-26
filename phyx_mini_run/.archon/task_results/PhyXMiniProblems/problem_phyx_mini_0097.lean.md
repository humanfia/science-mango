# Prover result: `problem_phyx_mini_0097.lean`

## Outcome

RESOLVED. The sole theorem,
`PhyXMiniProblems.ProblemPhyXMini0097.problem_phyx_mini_0097`, is proved with
no remaining `sorry`. Its declaration header and all supporting declarations
were left unchanged.

The proof:

- derives the internal incidence angle at `A` as `50°` from the right-angle
  prism geometry and the pictured `40°` in-glass entry angle;
- specializes Snell's law at the entry face and at `A`;
- uses the critical transmitted angle `90°` and positive refractive indices to
  eliminate the two indices and obtain
  `sin thetaA = sin 40° / sin 50°`;
- uses the physical branch `thetaA.toReal ∈ [0, π / 2]` and
  `Real.arcsin_sin` to conclude the stated principal-arcsine equality.

## Faithfulness audit

The proof uses the given geometry, both Snell-law hypotheses, the critical
transmission condition, refractive-index positivity, and the physical angle
branch. It does not use `recordedAnswerChoice`, introduce a target-bearing
assumption, or derive the result from inconsistency.

The exact conclusion is approximately `57°`, consistent with the current
source contract and its documentation that printed choice B (`60°`) is the
closest option while recorded choice A (`90°`) is retained only as metadata.

Source report:
`reports/phyx_mini/problem_phyx_mini_0097.source.json`.

## Verification

- `archon-lean-lsp` diagnostics: no errors or warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0097.lean`: exit code 0.
- Source scan: no suspicious proof escape patterns.
- Axiom audit for the target theorem: only `propext`, `Classical.choice`, and
  `Quot.sound`; no `sorryAx` or added axioms.
- Remaining `sorry` count in the assigned file: 0.

## Blueprint status

`thm:physics:phyx_mini_0097:target` is ready for the coordinator-managed
`\leanok` synchronization. The prover did not edit the blueprint chapter, in
accordance with prover write permissions.

## Redraft needed

None.
