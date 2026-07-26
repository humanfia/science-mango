# Prover result: `problem_phyx_mini_0622.lean`

## Outcome

All three proof obligations are closed:

- `earthMeasuredHeightInMeters_eq_one`
- `earthMeasuredWidthInMeters_exact`
- `problem_phyx_mini_0622`

No `sorry`, `admit`, custom axiom, `native_decide`, or `sorryAx` remains.

## Proof summary

- The height lemma combines the figure's `1.00 m` annotation with the
  rest-height readout, then specializes the supplied Lorentz length law to the
  transverse height axis, where the readout is unchanged.
- The width lemma specializes the same law to the parallel width axis and
  rewrites the rest width and speed fraction to obtain
  `(3 / 2) / LorentzGroup.γ (9 / 10)`.
- The final theorem reduces this width exactly to `3 * Real.sqrt 19 / 20`.
  Squaring proves the certified bounds
  `43 / 10 < Real.sqrt 19 < 131 / 30`, from which the strict
  `0.005 m` tolerance around displayed choice C (`0.65 m`) follows.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0622.lean` exits with
  code 0 and no diagnostics.
- `lean_verify` reports only Lean's standard foundational axioms `propext`,
  `Classical.choice`, and `Quot.sound`, with no suspicious source patterns.
- A source scan confirms that no proof placeholder or escape hatch remains.

## Blueprint synchronization

The blueprint environments were not edited with `\leanok`, because the task's
explicit write-permission section authorizes edits only to the assigned Lean
file and this result file. An authorized blueprint synchronization step should
add markers for the two lemmas and the final theorem.

## Environment note

The requested `.archon/AGENTS.md` is absent in this run, as also recorded by
`.archon/PROGRESS.md`. The supplied prover instructions, progress record,
blueprint chapter, source report, and iteration plan were used instead.
