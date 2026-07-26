# Prover result: `problem_phyx_mini_0489.lean`

## Status

- Closed both proof obligations:
  - `earthIrradiance_eq_stefanBoltzmann_times_radiusRatioSq`
  - `powerPerUnitArea_arrivingAtEarth_matches_answer_D`
- No `sorry`, `admit`, new axioms, or proof escape hatches remain.
- No declaration signature was changed.

## Proof summary

- Rewrote isotropic propagation using the spherical luminosity and
  Stefan--Boltzmann surface laws, canceled the nonzero Sun--Earth distance
  and positive factor involving `Real.pi`, and derived the inverse-square
  irradiance formula.
- Transported the figure's displayed distance to the setup distance, then
  substituted the stated temperature, solar radius, distance, and textbook
  Stefan--Boltzmann constant.
- Normalized the resulting exact irradiance and checked the tolerance and
  nearest-choice inequality for every `AnswerChoice`; choice `D = 1100 W/m²`
  is closest.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0489.lean` exited `0`.
- Lean LSP diagnostics are empty.
- Axiom/source verification found only the standard foundations `propext`,
  `Classical.choice`, and `Quot.sound`, with no suspicious source patterns.
- Both corresponding blueprint lemma/theorem proof environments are ready
  for `\leanok`; the blueprint was not edited because prover write
  permissions make it read-only and marker synchronization is
  coordinator-managed.

## Redraft needed

None.

## Environment note

The run-local `.archon/AGENTS.md` is absent, as recorded in
`.archon/PROGRESS.md`; the canonical archived role instructions and the
run-local physics prover mode were read instead.
