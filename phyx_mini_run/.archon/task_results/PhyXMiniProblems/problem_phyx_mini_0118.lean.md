# Prover result: `problem_phyx_mini_0118.lean`

## Status

Blocked by an underdetermined and in fact false universal numerical target.
The existing non-bare partial proof was preserved. It closes:

- the symbolic ray/interference calculation in `axialNodeDistance_formula`;
- the metre-to-centimetre conversion in
  `axialNodeDistance_matches_recordedAnswerA`;
- reduction of the final theorem to the unsupported numerical
  specialization.

One focused `sorry` remains at that final specialization. No declaration
signature was changed and no axiom or proof-laundering device was introduced.

## Concrete blocker

The hypotheses determine only

`d = (4 r² - (m λ)²) / (2 m λ)`.

They do not fix `r`, `λ`, `m`, or any equivalent numerical data. At the SI
readout level, for example, all supplied laws and positivity conditions admit

- `r = 1`, `d = 3/2`, reflection coordinate `x = 3/4`;
- incident and outgoing segment lengths `5/4`;
- direct length `3/2`, reflected length `5/2`;
- wavelength `λ = 1`, frequency `f = 1`, sound speed `c = 1`;
- constructive order `m = 1`, and tube length `2`.

Indeed,

- `x = d/2`;
- `(5/4)² = (3/4)² + 1²`;
- `5/2 - 3/2 = 1 = m λ`;
- `c = λ f`.

Such SI readouts are realized by Physlib's
`CarriesDimension.toDimensionful UnitChoices.SI`. This setup has
`d = 150 cm`, so it does not match answer A (`11.3 cm`). Consequently the
current theorem cannot be proved soundly from its premises.

## Redraft needed

- Original problem id: `phyx_mini_0118`
- Source report:
  `reports/phyx_mini/problem_phyx_mini_0118.source.json`
- Theorem:
  `PhyXMiniProblems.ProblemPhyXMini0118.axialNodeDistance_matches_recordedAnswerA`
- Problem: the theorem universally concludes the recorded numerical answer,
  but neither the source excerpt nor its hypotheses supply numerical radius,
  frequency, helium sound speed/wavelength, or constructive order.
- Smallest faithful change: replace the numerical answer conclusion by the
  symbolic conclusion already proved in `axialNodeDistance_formula`.
  If answer A must remain the target, first restore the omitted numerical
  apparatus/figure readouts as explicit source-data hypotheses; those values
  must specialize the symbolic formula to `11.3 cm` within the stated
  tolerance.

## Verification

- `archon-lean-lsp` diagnostics: no errors; one expected
  `declaration uses sorry` warning plus style-only linter messages.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0118.lean`: exit code 0,
  with the expected remaining `sorry` warning.
- The assigned file contains no `/- USER: ... -/` hint.
- The run-local `.archon/AGENTS.md` is absent, as noted in `PROGRESS.md`; the
  canonical archived `AGENTS.md`, current `PROGRESS.md`, injected physics mode,
  blueprint chapter, and grounding report were read.
- The blueprint was not edited: prover permissions make it read-only and
  `AGENTS.md` delegates `\leanok` synchronization to the automated sync phase.
