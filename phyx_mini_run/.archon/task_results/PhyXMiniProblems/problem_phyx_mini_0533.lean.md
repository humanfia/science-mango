# Autoformalization result: `problem_phyx_mini_0533`

The chapter contains `% archon:physics`, so the `physics-formalize` discipline was used. The exact retry reason was the globalized-approximation blocker: the prior draft asserted the opaque-barrier approximation `P = exp (-2 κ L)` as an exact finite-parameter law. The redraft separates the exact physical transmission probability from the source's leading exponential estimate and gives the approximation an explicit remainder/error-bound contract.

## Assumption/target split

### Governing laws

- `SatisfiesBarrierDecayRelation`: in coherent SI readouts, `κ = sqrt (2 m (U - E)) / ℏ`.
- `SatisfiesExactRectangularBarrierTransmissionLaw`: for the finite rectangular barrier with `E < U`, the physical probability is
  `T = (1 + U^2 sinh^2 (κ L) / (4 E (U - E)))⁻¹`.
- `SatisfiesFiniteErrorOpaqueBarrierEstimate`: the separately stored leading estimate is `exp (-2 κ L)`; the physical probability is this estimate plus an explicit remainder, and the remainder's absolute value is bounded by a separately stored nonnegative bound. The approximation is therefore not asserted as an exact physical law.
- `SatisfiesRectangularPotentialProfile`: the potential is zero to the left and right and equals `U` in the barrier.
- `HasPhysicalTunnelingParameters`: positivity, `E < U`, positive width/mass/action/decay constant, the stated opaque-regime inequality, physical probability bounds, and nonnegativity of the approximation-error bound.
- `UsesStandardElectronReferenceData`: electron rest mass is calibrated in kilograms and the reduced Planck action is calibrated to Physlib's `Constants.ℏ` in joule-seconds.

### Previous-part results

- None. The source report has `previous_parts: []`.

### Figure/data readouts

- `MatchesProblemNumericalReadouts`: `E = 5 eV`, `U = 10 eV`, and `L = 0.2 nm`.
- `MatchesElectronBarrierScenario`: an electron moves in the positive-x direction toward a rectangular barrier.
- `MatchesSuppliedBarrierFigure`: the primary raster shows the position/energy axes, origin, orange rectangular profile, shaded interior, the `E`, `L`, and `U` labels, the `-e` charge mark, and the right-pointing incident arrow.
- `RectangularBarrierFigure` and the figure-label/direction/region enums retain the named geometry and labels without storing an answer.
- `displayedTunnelingProbability` records A = 0.0111, B = 0.0076, C = 0.0225, and D = 0.0103 as source metadata.

### Current target conclusions

`problem_phyx_mini_0533` concludes all of the following:

- the explicitly named leading semiclassical attenuation estimate is within `0.0001` of D;
- D is the uniquely nearest displayed value to that estimate;
- the exact finite-barrier tunneling probability is within `0.0001` of `0.0401`; and
- none of the four displayed values is within `0.0001` of the exact probability.

Numerically, the grounded constants give `κ L ≈ 2.29115`, `exp (-2 κ L) ≈ 0.0102313`, and exact rectangular-barrier transmission `T ≈ 0.0401006`. Thus the recorded D value is supported only as the bare exponential attenuation estimate, not as the exact finite rectangular-barrier transmission probability.

## Goal-faithfulness audit

- No premise mentions answer D, `0.0103`, the exact result `0.0401`, closeness to a choice, or nearest-choice selection.
- `tunnelingProbability` and `semiclassicalAttenuationEstimate` are independent setup fields. Neither is defined to be a displayed answer.
- The exact transmission law is a general relation in `E`, `U`, `κ`, and `L`; it does not contain the target numerical result.
- The opaque-barrier estimate is not equated to the physical probability. Their difference is an explicit stored remainder controlled by an independent error bound.
- The displayed-choice function is source metadata only. Substitution of the calibrated readouts and physical laws is still required to obtain every numerical conclusion.
- The target is not `True`, reflexive equality, or a definition manufactured to unfold to the recorded answer.

## Declarations and blueprint correspondence

The sole available blueprint declaration label is `thm:physics:phyx_mini_0533:target`. The main Lean declaration corresponding to it is:

- `PhyXMiniProblems.ProblemPhyXMini0533.problem_phyx_mini_0533`.

Supporting public declarations for which the blueprint writer may add entries after names stabilize are:

- Dimensionful types and projections: `LengthQuantity`, `MassQuantity`, `InverseLengthQuantity`, `actionDimension`, `ActionQuantity`, `lengthReadout`, `lengthInMeters`, `lengthInNanometers`, `energyInJoules`, `energyInElectronVolts`, `massInKilograms`, `actionInJouleSeconds`, and `inverseLengthInInverseMeters`.
- Physical/figure vocabulary: `ParticleSpecies`, `BarrierRegion`, `PotentialProfileShape`, `PlotAxisRole`, `FigureQuantityLabel`, `ParticleChargeLabel`, `HorizontalDirection`, `RectangularBarrierFigure`, and `ElectronBarrierSetup`.
- Assumption interfaces: `MatchesElectronBarrierScenario`, `MatchesProblemNumericalReadouts`, `MatchesSuppliedBarrierFigure`, `SatisfiesRectangularPotentialProfile`, `UsesStandardElectronReferenceData`, `HasPhysicalTunnelingParameters`, `SatisfiesBarrierDecayRelation`, `SatisfiesExactRectangularBarrierTransmissionLaw`, and `SatisfiesFiniteErrorOpaqueBarrierEstimate`.
- Answer metadata and comparison predicates: `AnswerChoice`, `displayedTunnelingProbability`, `MatchesDisplayedWithinOneTenThousandth`, and `IsUniqueNearestDisplayedProbability`.

The blueprint was not edited or marked `\leanok` because this task's explicit Write Permissions allow edits only to the assigned Lean file and this result file and expressly prohibit blueprint edits.

## LeanExplore queries and candidates actually used

All searches used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `rectangular potential barrier tunneling transmission coefficient quantum mechanics`: returned general `QuantumMechanics.SpaceDQuantumSystem.potentialCLM`, `potentialOperator`, and related potential-operator declarations. These are near misses and were not used because they do not provide a one-dimensional rectangular-barrier scattering/transmission law.
- Likely-name query `DimEnergy electronVolt Constants.ℏ LengthUnit nanometers`: found and grounded `DimEnergy`, `DimEnergy.electronVolt`, `Constants.ℏ`, `LengthUnit`, and `LengthUnit.nanometers`.
- Query `MassUnit kilograms Dimensionful WithDim physical mass`: found and grounded `Dimensionful`, `MassUnit`, and `MassUnit.kilograms`.
- Query `Dimensionful WithDim inverse length action physical units`: confirmed `Dimensionful`, `Dimension.L𝓭`, and the dimension infrastructure used for local inverse-length and action quantities.
- Query `Real.exp Real.sqrt absolute value` and exact-name query `Real.sqrt`: grounded `Real.exp`, `Real.sqrt`, and real absolute-value support.
- Query `Real.sinh exact rectangular barrier transmission`: grounded `Real.sinh`; no rectangular-barrier transmission declaration was returned.
- Query `Asymptotics.IsLittleO exponential asymptotic approximation`: found `Asymptotics.IsLittleO` lemmas such as `IsLittleO.of_bound`. They were inspected as an alternative remedy to the retry blocker but not used: the finite-parameter source question is modeled more directly by the explicit remainder/error-bound contract.

Source/module/docstring fetches were made for the candidates actually used: `Dimensionful`, `DimEnergy`, `DimEnergy.electronVolt`, `Constants.ℏ`, `LengthUnit.nanometers`, `MassUnit.kilograms`, `Real.exp`, `Real.sqrt`, and `Real.sinh`.

## Grounded Physlib/Mathlib names

- Physlib: `Dimensionful`, `WithDim`, `Dimension`, `Dimension.L𝓭`, `Dimension.M𝓭`, `Dimension.T𝓭`, `UnitChoices.SI`, `DimEnergy`, `DimEnergy.electronVolt`, `LengthUnit.meters`, `LengthUnit.nanometers`, `MassUnit.kilograms`, and `Constants.ℏ`.
- Mathlib: `NNReal`, `Real.sqrt`, `Real.exp`, `Real.sinh`, real absolute value notation, powers, and inverses.

## Local abstractions introduced

- `LengthQuantity`, `MassQuantity`, `InverseLengthQuantity`, and `ActionQuantity` specialize Physlib's unit-independent `Dimensionful (WithDim ...)` machinery. They preserve physical dimensions and are not scalar aliases.
- The figure enums and `RectangularBarrierFigure` preserve the discrete labels and geometry visible in image 533.
- `ElectronBarrierSetup` distinguishes the exact dimensionless tunneling probability, the leading semiclassical estimate, the approximation remainder, and its absolute error bound.
- The scenario/readout/figure/profile/law structures separate source facts, reference calibration, governing physics, and the current numerical target.
- A local exact rectangular-barrier law was necessary because LeanExplore found no matching Physlib scattering/transmission API.

## Grounding gaps and redraft requests

- No reusable Physlib declaration for a one-dimensional rectangular potential barrier, its evanescent decay constant, or its exact transmission coefficient was found.
- Physlib's `Constants.ℏ` is a positive scalar calibrated in J·s, not a dimensionful action object. The local `ActionQuantity` plus `actionInJouleSeconds` calibration bridges this gap explicitly.
- No ready-made dimensionful electron-rest-mass constant was found; the local mass quantity is calibrated to the standard SI readout.
- The source should be redrafted to say whether it asks for the crude leading exponential attenuation estimate or the exact rectangular-barrier transmission probability. With the stated data, D matches the former, while the latter is about `0.0401` and matches none of the choices.
- The blueprint proof should be fleshed out with interface matching for a finite rectangular barrier, derivation of the exact `sinh` formula, and an explicit explanation of why the recorded D value is only the bare exponential estimate.
- `.archon/AGENTS.md` was absent, so `.archon/prover-modes/physics-formalize.md` and the supplied role prompt governed the work. The `archon` executable was also absent from `PATH`, so the requested DAG queries could not be run.

## Verification

- `archon-lean-lsp` diagnostics: only `declaration uses sorry` at the target theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0533.lean`: exit code 0, with only the expected `sorry` warning.
