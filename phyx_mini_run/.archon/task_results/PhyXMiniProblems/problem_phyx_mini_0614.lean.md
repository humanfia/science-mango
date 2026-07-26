# Prover result: `problem_phyx_mini_0614.lean`

## Outcome

- Closed all three placeholders without changing any declaration signature:
  - `centralAcceptedEnergy_satisfies_wienPeakEquation`
  - `motorCurrent_squared_times_resistance_eq_narrowBandPower`
  - `motorCurrent_matches_answer_A`
- No `sorry`, `admit`, new axiom, `sorryAx`, or `native_decide` remains.
- No redraft is needed.

## Proof summary

- Derived the Wien peak equation honestly from the global spectral maximum and
  Planck spectrum. Since the available imports do not expose the calculus
  derivative API, the proof uses the imported first-order exponential
  remainder on a punctured neighborhood and compares perturbations from both
  sides.
- Derived the motor power balance by combining narrow-band capture, ideal
  conversion, electrical power, and Ohm's law.
- Reduced the final current to an exact current-squared expression. Proved
  `2.8214 < E₀/(k_B T) < 2.8215` using finite exponential-series bounds and
  proved `3.14 < π < 3.15` from the imported trigonometric bounds. These imply
  `90.9 A < I < 91.3 A`, hence the `0.2 A` tolerance and closest-choice result
  for answer A.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0614.lean`: exit 0 under
  the default heartbeat limit (only style-linter warnings).
- `lake build`: successful (4 jobs).
- `lean_verify` for
  `PhyXMiniProblems.ProblemPhyXMini0614.motorCurrent_matches_answer_A`:
  only standard axioms `propext`, `Classical.choice`, and `Quot.sound`;
  suspicious-source scan returned no warnings.
- Compared against the iteration-017 baseline: only the three proof bodies
  changed.

## Blueprint status

- The theorem and both derived-lemma proof environments are ready for
  deterministic `\leanok` synchronization.
- The blueprint was not edited because prover permissions make it read-only.

## Environment notes

- The requested run-local `.archon/AGENTS.md` was absent; the canonical archive
  role file identified by `PROGRESS.md` was read instead.
- The `archon` executable was not available on `PATH`, so the optional DAG
  query could not be run.
