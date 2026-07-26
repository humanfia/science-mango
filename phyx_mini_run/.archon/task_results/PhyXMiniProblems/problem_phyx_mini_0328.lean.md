# Prover result: `problem_phyx_mini_0328.lean`

## Outcome

Complete. All three assigned proof obligations were closed without changing
any declaration header.

- `markedRidgeSeparation_is_halfWavelength` specializes the standing-wave law
  to the marked adjacent ridges and rewrites their endpoint difference as the
  marked separation.
- `standingWavelengthInGas_meters_eq` derives the exact Physlib conversion
  `centimetersValue length = 100 * metersValue length`, converts `9.20 cm` to
  `23/250 m`, and doubles it to obtain the wavelength `23/125 m`.
- `problem_phyx_mini_0328` specializes `v = λ f` to metres and seconds,
  computes `v = (23/125) * 4460 = 20516/25 m/s`, and exhausts the four answer
  choices to prove that only D lies within one half metre per second.

The assigned file now contains no `sorry`, `admit`, `axiom`, `sorryAx`,
`native_decide`, or other proof escape hatch.

## Verification

- Lean LSP diagnostics: no errors; only the frozen but mathematically
  redundant `h_physical` hypothesis in the wavelength lemma is reported as
  unused.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0328.lean`: exit code 0.
- Root `lake build`: completed successfully.
- The assigned path is not registered as an individual Lake module target, so
  direct file compilation supplied the file-level build check.
- Source and axiom verification found no suspicious patterns. The final
  theorem depends only on Lean's standard foundational axioms `propext`,
  `Classical.choice`, and `Quot.sound`.

## Blueprint readiness

The proof environments for
`markedRidgeSeparation_is_halfWavelength`,
`standingWavelengthInGas_meters_eq`, and `problem_phyx_mini_0328` are ready
for `\leanok`. The blueprint was not edited because the prover write boundary
reserves marker maintenance for deterministic synchronization.

The requested run-local `.archon/AGENTS.md` is absent; as directed by
`.archon/PROGRESS.md`, the canonical archive copy was read instead. No
`/- USER: ... -/` file-specific hint occurs in the assigned Lean file.

## Redraft needed

None.
