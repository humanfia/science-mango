# Autoformalization result: `problem_phyx_mini_0549.lean` (iteration 003)

This is the genuine post-formalization report requested by the iteration-002
review gate. The gate failure was missing evidence, not a semantic rejection.
I re-read the current Lean file, physics blueprint, source report, and primary
image; repeated the Mathlib/Physlib searches below; and recompiled the exact
assigned file. The existing by-sorry formalization was already faithful, so no
Lean statement or signature was changed in iteration 003.

## Assumption/target split

### Governing laws

- `SatisfiesPhotoelectricEffectLaws.stoppingPotentialRelation` states, at each
  measured point A and B, that stopping the fastest photoelectrons gives
  `K_max = e |U_a|` in coherent SI scalar components.
- `SatisfiesPhotoelectricEffectLaws.einsteinEnergyBalance` states Einstein's
  photoelectric relation `h ν = φ + K_max` at A and B.
- `UsesPhyslibElementaryCharge.chargeCalibration` identifies the independent
  dimensionful electron-charge magnitude with Physlib's exact elementary
  charge when both are read in coulombs.
- `HasPhysicalPhotoelectricParameters` records the physical sign conditions:
  positive frequency, charge magnitude, and Planck constant; nonnegative
  stopping-potential magnitude, kinetic energy, and work function.

### Previous-part results

- None. The source report contains no previous parts, and no value or choice
  for Planck's constant is assumed.

### Figure/data readouts

- The primary image shows horizontal incident-light frequency coordinates in
  units of `10^14 Hz` and vertical stopping-potential magnitude coordinates in
  volts.
- The relevant labeled points are `O = (0,0)`, `A = (5,0)`, and `B = (10,2)`.
  Thus the measured rise from A to B is `2 V`, and the frequency run is
  `5 × 10^14 Hz`.
- A and B lie on the same rising straight plotted line. The horizontal and
  vertical dashed guides pass through B. The displayed acute `θ` is at A
  against the horizontal axis. The model's A--B endpoint pair denotes this
  relevant measured segment; the raster's fitted line continues slightly
  beyond B.
- `UsesSuppliedAxisCalibration` converts the dimensionless graph coordinates
  into the dimensionful frequency and potential measurements. It does not
  constrain the experimental Planck constant.

### Current target conclusions

- `inferredPlanckConstant_eq_elementaryCharge_mul_graphSlope` concludes
  `h = e · 2 / (5 · 10^14)` in joule-seconds.
- `problem_phyx_mini_0549` concludes the same slope formula and that D,
  displaying `6.4 × 10^-34 J·s`, is the unique printed choice within the
  declared half-last-digit rounding tolerance.

## Goal-faithfulness audit

The experimental Planck constant is an independent field of
`PhotoelectricExperiment` with the dimension of action. It is not defined from
the graph, the displayed choices, or `recordedDatasetAnswer`. No premise field
contains the target slope formula, the rounded value `6.4 × 10^-34`, a match
with D, or uniqueness of D. The slope must later be derived by applying the two
governing laws at A and B and subtracting to cancel the work function.

`MatchesDisplayedPlanckConstant` only defines rounding semantics for any
independently inferred constant. `IsUniqueMatchingDisplayedPlanckConstant`
states the substantive choice conclusion and occurs only in the theorem
conclusion. `recordedDatasetAnswer` is source metadata and is not used by any
hypothesis or by the theorem conclusion. No target is made true by unfolding a
local definition.

Source/law/answer audit:

- Source: the image, rather than the imprecise auxiliary caption, is used for
  B's position and the role of `θ`; B is at `(10,2)`, not on the vertical axis.
- Laws: the local law structure contains only the two standard photoelectric
  relations and no inferred numerical value.
- Answer: Physlib's exact `1.602176634 × 10^-19 C` gives approximately
  `6.408706536 × 10^-34 J·s`, so equality with printed D would be false;
  the explicit rounding predicate correctly captures the multiple-choice
  claim.

## Declarations and blueprint labels

The declarations present in the assigned file correspond to these blueprint
environments:

- `problem_phyx_mini_0549` — `thm:physics:phyx_mini_0549:target`.
- `inferredPlanckConstant_eq_elementaryCharge_mul_graphSlope` —
  `lem:physics:phyx-mini-0549:phyxminiproblems-problemphyxmini0549-inferredplanckconstant-eq-elementarycharge-mul-graphslope`.
- `electricPotentialDimension`, `actionDimension`, `FrequencyQuantity`,
  `StoppingPotentialMagnitude`, `ChargeMagnitudeQuantity`, and
  `PlanckConstantQuantity` — respectively the labels ending in
  `-electricpotentialdimension`, `-actiondimension`, `-frequencyquantity`,
  `-stoppingpotentialmagnitude`, `-chargemagnitudequantity`, and
  `-planckconstantquantity`, all with prefix
  `def:physics:phyx-mini-0549:phyxminiproblems-problemphyxmini0549`.
- `nonnegativeSIReadout`, `frequencyInHertz`, `stoppingPotentialInVolts`,
  `chargeMagnitudeInCoulombs`, `planckConstantInJouleSeconds`,
  `energyInJoules`, and `physlibElementaryChargeInCoulombs` — the definition
  labels with the same prefix and endings `-nonnegativesireadout`,
  `-frequencyinhertz`, `-stoppingpotentialinvolts`,
  `-chargemagnitudeincoulombs`, `-planckconstantinjouleseconds`,
  `-energyinjoules`, and `-physlibelementarychargeincoulombs`.
- `FigurePoint`, `MeasuredPoint`, `MeasuredPoint.toFigurePoint`, `FigureAxis`,
  `AxisQuantity`, `AxisUnit`, `StoppingPotentialFrequencyFigure`, and
  `PhotoelectricExperiment` — the definition labels with endings
  `-figurepoint`, `-measuredpoint`, `-measuredpoint-tofigurepoint`,
  `-figureaxis`, `-axisquantity`, `-axisunit`,
  `-stoppingpotentialfrequencyfigure`, and `-photoelectricexperiment`.
- `HasSuppliedFigurePresentation`, `HasSuppliedFigureReadouts`,
  `UsesSuppliedAxisCalibration`, `HasPhysicalPhotoelectricParameters`,
  `UsesPhyslibElementaryCharge`, and `SatisfiesPhotoelectricEffectLaws` — the
  definition labels with endings `-hassuppliedfigurepresentation`,
  `-hassuppliedfigurereadouts`, `-usessuppliedaxiscalibration`,
  `-hasphysicalphotoelectricparameters`, `-usesphyslibelementarycharge`, and
  `-satisfiesphotoelectriceffectlaws`.
- `AnswerChoice`, `displayedPlanckConstantInJouleSeconds`,
  `displayedAnswerToleranceInJouleSeconds`,
  `MatchesDisplayedPlanckConstant`,
  `IsUniqueMatchingDisplayedPlanckConstant`, and `recordedDatasetAnswer` — the
  definition labels with endings `-answerchoice`,
  `-displayedplanckconstantinjouleseconds`,
  `-displayedanswertoleranceinjouleseconds`,
  `-matchesdisplayedplanckconstant`,
  `-isuniquematchingdisplayedplanckconstant`, and
  `-recordeddatasetanswer`.

The blueprint was not edited because this task's final write permissions allow
only the assigned Lean file and this report. Consequently `\leanok` marker
synchronization remains for the owning blueprint workflow.

## LeanExplore queries and candidates actually used

Every query used `packages: ["Mathlib", "Physlib"]`. Fresh iteration-003
summary searches were:

- `photoelectric effect stopping potential Einstein energy balance Planck constant`
- `Dimensionful WithDim UnitChoices.SI DimEnergy physical units`
- `ChargeUnit.elementaryCharge coulombs`
- `frequency voltage action physical dimensions`
- `Constants.ℏ Planck constant`
- `WithDim`
- `DimEnergy`
- `ChargeUnit.coulombs`
- `UnitChoices.SI`
- `Dimensionful`
- `instCoeFunDimensionfulForallUnitChoices`
- `M𝓭 L𝓭 T𝓭 C𝓭 physical base dimensions`
- `Dimension.M𝓭`
- `Dimension.T𝓭`
- `ChargeUnit.div`

Module, docstring, and source data were fetched for the candidates actually
retained in the model: `Dimension` (394292), `Dimension.L𝓭` (394324),
`Dimension.T𝓭` (394330), `Dimension.M𝓭` (394336), `Dimension.C𝓭` (394337),
`WithDim` (394425), `UnitChoices.SI` (394270), `Dimensionful` (394284), the
`Dimensionful` function coercion (394285), `DimEnergy` (394468),
`ChargeUnit.elementaryCharge` (385585), and `ChargeUnit.coulombs` (385584).
The division implementation used to form the scalar coulomb readout was also
inspected through `ChargeUnit.instHDivNNReal` (385571) and
`ChargeUnit.div_eq_val` (385572); the supporting `ChargeUnit` (385567) and
`ChargeUnit.scale` (385578) definitions were fetched to verify the numerical
orientation of the ratio.
The photoelectric search returned only near misses such as `Constants.ℏ`, not
a stopping-potential or Einstein photoelectric law.

## Physlib/Mathlib names grounded

- Physlib `Dimension` and base dimensions `M𝓭`, `L𝓭`, `T𝓭`, and `C𝓭` ground
  the energy/charge potential dimension and the energy-times-time action
  dimension.
- Physlib `WithDim`, `Dimensionful`, its unit-choice function coercion, and
  `UnitChoices.SI` ground the dimensionful quantities and coherent-SI readout
  boundary. The source for `UnitChoices.SI` explicitly selects meters,
  seconds, kilograms, coulombs, and kelvin.
- Physlib `DimEnergy` is used for the metal work function and maximum kinetic
  energies.
- Physlib `ChargeUnit.elementaryCharge` and `ChargeUnit.coulombs` ground the
  exact elementary-charge readout; the source defines the former as
  `1.602176634e-19` times the coulomb unit, and the `HDiv` source confirms that
  `elementaryCharge / coulombs` returns that scalar rather than its reciprocal.
- Mathlib `NNReal` represents nonnegative physical magnitudes. `ℝ` is confined
  to explicit SI scalar components, graph coordinates/scales, the angle, and
  printed answer values.

## Local abstractions introduced

- Physlib has no ready-made frequency, stopping-potential magnitude,
  charge-magnitude, or ordinary-Planck-constant quantity types for this
  scenario. The file therefore uses `Dimensionful (WithDim d NNReal)` at the
  appropriate dimensions rather than scalar aliases.
- `StoppingPotentialFrequencyFigure` preserves raster labels, axis roles,
  units, raw coordinates, scales, dashed guides, and the angle separately
  from physical measurements.
- `PhotoelectricExperiment` keeps frequency, potential, charge, energy, work
  function, and the action-valued experimental Planck constant independent.
- The six premise structures separate presentation evidence, literal image
  data, coordinate calibration, sign conditions, known-charge calibration,
  and governing laws by provenance.
- The answer-choice and rounding predicates preserve the printed-answer role
  without turning the recorded answer into physics.

## Grounding gaps and redraft requests

- LeanExplore found no Mathlib/Physlib declarations for the photoelectric
  stopping-potential law or Einstein's photoelectric equation. Faithful local
  hypotheses are therefore required.
- `Constants.ℏ` is the reduced Planck constant, not the ordinary `h` requested
  by the problem, and its scalar API would not replace the experiment's
  independent action-valued quantity.
- No ready-made Physlib voltage, frequency, or action aliases surfaced.
- No blueprint redraft is needed. A future editorial pass could clarify that
  the A--B pair is the measured segment of a fitted line that extends beyond B
  in the raster, and could correct the auxiliary caption's descriptions of B
  and `θ`.

## Workflow and verification

- The requested `.archon/AGENTS.md` does not exist in this checkout. I used
  `.archon/prover-modes/physics-formalize.md`, which matches the role supplied
  in the task prompt.
- The `archon` executable was not available on this runtime's `PATH`, so the
  optional read-only DAG query could not be run.
- `archon-lean-lsp` diagnostics succeeded with only the expected `declaration
  uses sorry` warnings at lines 277 and 334.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0549.lean` exited 0 with
  only those same two expected warnings.
