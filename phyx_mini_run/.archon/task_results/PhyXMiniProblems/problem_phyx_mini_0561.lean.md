# Autoformalization result: `problem_phyx_mini_0561.lean`

## Assumption/target split

### Governing laws

- `FieldsRealizeScalarReadouts` connects Physlib's full electric, selector
  magnetic, and terrestrial magnetic vector fields to the scalar SI readouts
  in the plate and outside-drift regions. The positive normal is chosen so
  that the applied selector field points in the negative-normal direction;
  its force on a right-moving electron therefore opposes the upward electric
  force. The interface confines the applied selector fields to the plate
  region but assigns no numerical value to the signed Earth-field coefficient.
- `SatisfiesCrossedFieldVelocitySelection.selectorForceBalance` states the
  crossed-field Lorentz-force magnitude relation `E = u_x B` used to select
  the horizontal beam speed.
- `SatisfiesElectricDeflectionBetweenPlates` states uniform horizontal motion,
  `a_E = (|e|/m) E`, the exit vertical velocity, and the constant-acceleration
  plate-exit height `y_1`.
- `SatisfiesEarthFieldDriftKinematics` states uniform horizontal drift over
  `x_2`, the oriented magnetic acceleration
  `a_B = (|e|/m) u_x B_E`, the final vertical velocity, and the screen-angle
  relation. Its displacement law follows the primary image: `y_2` is total
  height above the initial beam line, so
  `y_2 = y_1 + u_y t_2 + (1/2) a_B t_2^2`.
- `SatisfiesThomsonNeglectCalculation` records the historical electric-only
  calculation
  `(|e|/m)_T = y_2 u_x^2 / (E x_1 (x_2 + x_1/2))`. It contains no Earth-field
  value, discrepancy value, or answer-choice assertion.
- `HasPhysicalParameters` supplies only positivity, nonempty experimental
  regions, and region disjointness needed to exclude degenerate branches.

### Previous-part results

- None. The source report has an empty `previous_parts` list, and the chapter
  declares no blueprint dependency. The requested `archon dag-query` check
  could not run because the `archon` executable is not available on this
  runtime's `PATH`.

### Figure/data readouts

- `MatchesProblemAndFigureReadouts` transcribes the stated applied magnetic
  field `5.5 * 10^-4 T`, electric field `1.5 * 10^4 V/m`, plate length
  `x_1 = 5 cm`, and displayed quotient `y_2 / x_2 = 8 / 110`.
- The primary raster shows `x_1` along the parallel plates; `x_2` from plate
  exit to screen; `y_1` from the initial beam line to the exit; `y_2` from the
  same initial beam line to the screen; rightward `u_x`; upward `u_y`; and the
  final angle `theta`. The predicate records these labels, directions, plate
  geometry, screen, and station ordering. It interprets `8/110` as the
  conventional centimetre pair `y_2 = 8 cm`, `x_2 = 110 cm`.
- `HasAcceptedElectronChargeToMassCalibration` records the accepted electron
  magnitude at textbook precision, `|e|/m = 1.76 * 10^11 C/kg`. This is
  external calibration data named by the question, not a statement about the
  requested terrestrial field.
- `AnswerChoice` and `displayedComponentInMicroteslas` transcribe all four
  displayed alternatives: A `-18`, B `-43`, C `-22`, and D `-31` microteslas.

### Current target conclusions

- `earthHorizontalComponent_exactFormula` derives the general outside-field
  correction in terms of the independent observables and the corrected mean
  drift slope `(y_2 - y_1) / x_2`.
- `thomsonNeglectChargeToMass_readout` derives Thomson's electric-only value
  `25600000000000 / 363 C/kg`, approximately `7.0523 * 10^10 C/kg`.
- `earthHorizontalComponent_microteslas` derives the exact value
  `-897375 / 29282 microteslas`, approximately `-30.646 microteslas`.
- `problem_phyx_mini_0561` concludes the historical readout, its strict
  discrepancy below the accepted readout, the exact inferred terrestrial
  component, and `IsClosestDisplayedChoice experiment .D`. Thus it selects
  the recorded `-31 microtesla` answer as the closest displayed value rather
  than asserting that the unrounded physical result is exactly `-31`.

## Goal-faithfulness audit

- `earthHorizontalComponent` is an independent signed dimensionful field of
  `ThomsonSecondExperiment`. It is not defined from the accepted ratio, the
  historical ratio, the answer choices, choice D, or either derived rational.
- No data, calibration, positivity, vector-field, velocity-selection,
  plate-kinematics, drift-kinematics, or neglect-calculation premise asserts a
  numerical value or sign for Earth's component.
- The drift law is a general Lorentz-acceleration and constant-acceleration
  relation. It does not contain the requested `-31` answer or the derived
  `-897375 / 29282` value.
- No premise mentions `IsClosestDisplayedChoice` or selects choice D.
  `displayedComponentInMicroteslas` is source metadata for all four choices;
  unfolding it cannot determine the independent Earth field.
- The accepted and Thomson-inferred charge-to-mass quantities are distinct
  fields. Only the accepted one has a calibration premise; the numerical
  Thomson readout and the comparison between them remain conclusions.
- The exact correction, numerical correction, historical numerical readout,
  discrepancy inequality, and closest-choice assertion are theorem or lemma
  conclusions with genuine `sorry` proof obligations. No local definition
  makes them true by unfolding.

## Declarations created and blueprint labels

- Dimension/readout layer: `speedDimension`, `accelerationDimension`,
  `electricFieldStrengthDimension`, `magneticFieldStrengthDimension`,
  `chargeToMassDimension`, eight dimensionful quantity types, and SI readouts
  for lengths, times, velocity and acceleration components, field strengths,
  and charge-to-mass magnitudes.
- Figure/model layer: `ParticleSpecies`, `PlateLabel`, `PlateArrangement`,
  `FigureAxis`, `TrajectoryStation`, `HorizontalBeamDirection`,
  `beamDirection`, `upwardDirection`, `earthHorizontalDirection`, and
  `ThomsonSecondExperiment`.
- Premise layer: `MatchesProblemAndFigureReadouts`,
  `HasAcceptedElectronChargeToMassCalibration`, `HasPhysicalParameters`,
  `FieldVanishesOutside`, `FieldsRealizeScalarReadouts`,
  `SatisfiesCrossedFieldVelocitySelection`,
  `SatisfiesElectricDeflectionBetweenPlates`,
  `SatisfiesEarthFieldDriftKinematics`, and
  `SatisfiesThomsonNeglectCalculation`.
- Target layer: `AnswerChoice`, `displayedComponentInMicroteslas`,
  `IsClosestDisplayedChoice`, `earthHorizontalComponent_exactFormula`,
  `thomsonNeglectChargeToMass_readout`,
  `earthHorizontalComponent_microteslas`, and `problem_phyx_mini_0561`.
- `PhyXMiniProblems.ProblemPhyXMini0561.problem_phyx_mini_0561` formalizes
  blueprint label `thm:physics:phyx_mini_0561:target`.

## LeanExplore queries/candidates actually used

Every query used `packages: ["Mathlib", "Physlib"]`.

- Query `Dimensionful WithDim physical dimension quantity` selected
  `Dimensionful` (id 394284) and `Dimension` (id 394292). Exact-name queries
  `WithDim` and `UnitChoices.SI` selected `WithDim` (id 394425) and
  `UnitChoices.SI` (id 394270).
- Query `ElectricField MagneticField` selected
  `Electromagnetism.ElectricField` (id 385559) and
  `Electromagnetism.MagneticField` (id 385560). The more-qualified query
  `Electromagnetism.ElectricField Electromagnetism.MagneticField` mostly
  returned electromagnetic-potential operations, so the exact shorter query
  was used to ground the field type abbreviations.
- Source, module, and docstring information was fetched for all six Physlib
  candidates above. It confirms that `WithDim` has an underlying `val`, that
  `Dimensionful` enforces unit-change behavior, that `UnitChoices.SI` uses
  metres, seconds, kilograms, coulombs, and kelvin, and that the field types are
  `Time -> Space d -> EuclideanSpace R (Fin d)` in
  `Physlib.Electromagnetism.Basic`.
- Query `EuclideanSpace.single coordinate basis vector` selected
  `EuclideanSpace.single` (id 133921). Its source, module, and docstring were
  fetched and confirm the standard coordinate basis-vector construction.
- Query `classical Lorentz force charged point particle velocity cross
  magnetic field` returned relativistic `Lorentz.Velocity`, free-particle,
  electromagnetic-potential, and stationary point-source candidates, but no
  applicable classical Lorentz-force trajectory law.
- Query `charge to mass ratio electron Thomson experiment` returned charge
  unit arithmetic, Standard Model charge labels, and electron-volt candidates,
  but no reusable electron charge-to-mass quantity or Thomson apparatus law.

## Physlib/Mathlib names grounded

- Physlib: `Dimension`, `Dimension.L𝓭`, `Dimension.T𝓭`, `Dimension.M𝓭`,
  `Dimension.C𝓭`, `Dimensionful`, `WithDim`, `UnitChoices`,
  `UnitChoices.SI`, `Electromagnetism.ElectricField`,
  `Electromagnetism.MagneticField`, `Time`, and `Space`.
- Mathlib: `NNReal`, `EuclideanSpace`, `EuclideanSpace.single`, `Fin`, `Set`,
  `Disjoint`, `Real.tan`, real absolute value, and finite inductive types.

## Local abstractions introduced

- Signed velocity, acceleration, and terrestrial field components use
  `Dimensionful (WithDim _ R)`. Lengths, time intervals, field magnitudes, and
  `|e|/m` use `Dimensionful (WithDim _ NNReal)`. These are dimension-bearing,
  unit-coherent physical quantities rather than transparent scalar aliases.
- `ThomsonSecondExperiment` retains the full field objects, plate and drift
  regions, independent scalar observables, both charge-to-mass quantities,
  figure distances, velocities, accelerations, transit times, and angle.
- `FieldsRealizeScalarReadouts` is a bridge from Physlib's field primitives to
  the signed SI components used by the school-physics equations. Its selector
  field sign is explicit and consistent with force cancellation for an
  electron; the unknown terrestrial coefficient remains independently signed.
- The four `Satisfies...` structures are local interfaces for the missing
  velocity-selector, Lorentz-acceleration, constant-acceleration, and Thomson
  neglect APIs. Each states a governing relation among independent physical
  observables and contains no current answer.

## Grounding gaps and redraft requests

- LeanExplore found no classical charged-particle Lorentz-force trajectory,
  velocity-selector, Thomson `e/m`, or deflection-plate API in Mathlib/Physlib.
  Faithful local law predicates were introduced instead of guessing names.
- The source prints only `y_2/x_2 = 8/110`; the numeric answer requires the
  conventional diagram interpretation `y_2 = 8 cm`, `x_2 = 110 cm`. This is
  explicit in the formalization and should be stated in a future blueprint
  proof narrative.
- The chapter names the currently accepted `e/m` value without printing it.
  The formalization uses the textbook-precision calibration
  `1.76 * 10^11 C/kg`. A blueprint redraft should state this calibration.
- The primary image shows `y_2` measured from the initial beam line, while
  `y_1` is the nonzero plate-exit height. Therefore the outside displacement
  is `y_2 - y_1`; a future informal proof should preserve this distinction.
- The blueprint contains no `\lean{...}` link or `\leanok` marker. Per the
  explicit write-permission restriction, the chapter was not edited. The plan
  or synchronization agent should link
  `PhyXMiniProblems.ProblemPhyXMini0561.problem_phyx_mini_0561` and add
  `\leanok` after reviewing the statement.
- The expected `.archon/AGENTS.md` role file is absent in this checkout, and
  the `archon` CLI advertised for DAG navigation is unavailable on `PATH`.
  The provided stage prompt, `.archon/PROGRESS.md`, and
  `.archon/prover-modes/physics-formalize.md` were used as the operative role
  instructions.

## Verification

- `archon-lean-lsp` diagnostics report exactly four expected `declaration uses
  sorry` warnings and no errors or failed dependencies.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0561.lean` exits 0 with
  exactly the same four expected warnings.
