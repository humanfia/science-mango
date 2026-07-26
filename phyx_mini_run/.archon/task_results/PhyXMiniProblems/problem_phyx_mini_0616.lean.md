# Autoformalization result: `problem_phyx_mini_0616.lean`

## Assumption/target split

### Governing laws

- `MatchesPhyslibRectangularBarrier` calibrates Physlib's genuinely piecewise-constant `QuantumMechanics.RectangularBarrier` to the setup's kilogram, metre, and joule readouts. Physlib's object is `V₀` on `Set.Icc lower upper` and zero outside.
- `SatisfiesBarrierDecayRelation` states the under-barrier relation
  `κ = sqrt (2 m (U - E)) / ℏ` in coherent SI scalar readouts.
- `DefinesLeadingOpaqueBarrierTransmissionEstimate` states the textbook leading exponential estimate `T_lead = exp (-2 κ L)`. The setup field and conclusion deliberately call this an **estimate**. The declaration does not assert that this leading approximation is the exact rectangular-barrier transmission coefficient.
- `HasPhysicalTunnelingParameters` records positivity, `E < U`, the opaque regime, and generic probability-estimate bounds `0 ≤ T_lead ≤ 1`. It contains neither requested numerical endpoint.

### Previous-part results

- None. The source report has `previous_parts: []`, and no DAG dependency was available.

### Figure/data readouts

- `MatchesProblemNumericalReadouts`: both wire diameters are `1 mm`, free-electron density is `8.5 × 10^28 m⁻³`, gap length is `1 nm`, barrier height is `12 eV`, and incident electron energy is `5 eV`.
- `MatchesCopperOxideJunctionScenario`: electron, rectangular profile, two cylindrical copper wires, and oxide gap.
- `MatchesSuppliedCopperOxideFigure`: primary raster `616.png` shows `d`, `L`, `I_tunnel`, sources `V` and `V_B`, both positive-terminal marks, `V_B > V`, rightward current, the oxide between the wires, and a closed loop.
- `UsesStandardElectronReferenceData`: electron mass is calibrated to `9.1093837015e-31 kg`; the action quantity is calibrated to Physlib's `Constants.ℏ` joule-second readout.
- `MalformedSourceChoice` and `recordedMalformedSourceAnswer` retain the printed `5, 6, 7, 8 eV` choices and recorded A only as malformed dataset metadata. They do not participate in the theorem.

### Current target conclusions

- Auxiliary derived lemma `barrier_energy_deficit_electronvolts_eq_seven`: `U - E = 7 eV`.
- Numerical estimate lemma `leading_opaque_barrier_estimate_between_1_6e_12_and_1_8e_12`: `1.6 × 10⁻¹² < T_lead < 1.8 × 10⁻¹²`.
- Principal theorem `problem_phyx_mini_0616`: the same dimensionless estimate interval under the complete scenario, data, figure, calibration, parameter, decay, and estimate premises.

## Goal-faithfulness audit

The requested endpoints `16 / 10^13` and `18 / 10^13` occur only in the conclusions of the numerical lemma and principal theorem. They do not occur in the setup, scenario, readout, figure, reference-data, calibration, physical-parameter, decay-law, or estimate-law premises. The general estimate law contains independent `κ`, `L`, and `T_lead` fields and relates them by the standard symbolic formula; it does not contain the problem's specialized result.

The prior draft risked presenting `exp (-2 κ L)` as an exact law for the physical transmission coefficient. This redraft names the independent quantity `leadingOpaqueBarrierEstimate` and makes the law an exact definition of the output of that approximation scheme. Thus it does not globalize an opaque-barrier approximation. The final theorem answers the source's estimate question and does not misrepresent the unrelated energy-valued choices as probabilities. The `7 eV` fact remains an intermediate lemma rather than an answer selection.

## Declarations and blueprint correspondence

- Blueprint label `thm:physics:phyx_mini_0616:target` corresponds to `PhyXMiniProblems.ProblemPhyXMini0616.problem_phyx_mini_0616`.
- Blueprint label `lem:physics:phyx-mini-0616:phyxminiproblems-problemphyxmini0616-barrier-energy-deficit-electronvolts-eq-seven` corresponds to `PhyXMiniProblems.ProblemPhyXMini0616.barrier_energy_deficit_electronvolts_eq_seven`.
- Blueprint label `lem:physics:phyx-mini-0616:phyxminiproblems-problemphyxmini0616-leading-opaque-barrier-estimate-between-1-6e-12-and-1-8e-12` corresponds to `PhyXMiniProblems.ProblemPhyXMini0616.leading_opaque_barrier_estimate_between_1_6e_12_and_1_8e_12`.
- Dimension and quantity helpers: `LengthQuantity`, `MassQuantity`, `NumberDensityQuantity`, `actionDimension`, `ActionQuantity`, `InverseLengthQuantity`, `electricPotentialDimension`, `ElectricPotentialQuantity`, `electricCurrentDimension`, and `ElectricCurrentMagnitude`.
- Explicit scalar projections: `lengthReadout`, `lengthInMeters`, `lengthInMillimeters`, `lengthInNanometers`, `energyInJoules`, `energyInElectronVolts`, `massInKilograms`, `actionInJouleSeconds`, `inverseLengthInInverseMeters`, `numberDensityInPerCubicMeter`, `potentialInVolts`, and `currentInAmperes`.
- Physical/figure vocabulary: `WireSide`, `WireMaterial`, `WireShape`, `GapMaterial`, `ParticleSpecies`, `PotentialProfileShape`, `HorizontalDirection`, `VoltageSourceLabel`, `PotentialDifferenceRole`, `FigureQuantityLabel`, `CopperOxideJunctionFigure`, and `CopperOxideTunnelingSetup`.
- Premise interfaces: `MatchesCopperOxideJunctionScenario`, `MatchesProblemNumericalReadouts`, `MatchesSuppliedCopperOxideFigure`, `UsesStandardElectronReferenceData`, `MatchesPhyslibRectangularBarrier`, `HasPhysicalTunnelingParameters`, `SatisfiesBarrierDecayRelation`, and `DefinesLeadingOpaqueBarrierTransmissionEstimate`.
- Source-metadata helpers: `MalformedSourceChoice`, `MalformedSourceChoice.energyInElectronVolts`, and `recordedMalformedSourceAnswer`.

Each helper above has the matching generated `def:physics:phyx-mini-0616:...` entry in the chapter's declaration topology; the three proof-bearing declarations have the exact theorem/lemma labels listed above. These public helpers are required because the principal theorem's public signature must preserve physical dimensions, independent quantities, the primary-figure facts, numerical readouts, and the assumption/target split.

## LeanExplore queries and candidates actually used

All searches used package filters `['Mathlib', 'Physlib']`.

- Natural-language query `quantum mechanical transmission probability through a one-dimensional rectangular potential barrier` returned generic potential-operator declarations headed by `QuantumMechanics.SpaceDQuantumSystem.potentialCLM`; these are near misses because they provide neither rectangular scattering data nor a transmission coefficient.
- Likely-name query `QuantumMechanics.RectangularBarrier` did not retrieve the locally installed declaration from the LeanExplore index. The installed module and LSP hover subsequently confirmed the exact type and semantics.
- Query `dimensionful energy electronVolt` returned and grounded `DimEnergy.electronVolt` (id 394470), `Dimensionful` (id 394284), and `DimEnergy` (id 394468). Source/module lookups confirmed `Physlib.Units.Basic` and `Physlib.Units.WithDim.Energy` and the calibrated `1.602176634e-19 J` electron volt.
- Query `electron rest mass physical constant` returned `MassUnit` (id 385360) but no electron-rest-mass constant. Source/module lookup grounded `MassUnit`; LSP hover grounded `MassUnit.kilograms`.
- Query `reduced Planck constant Constants.ℏ` returned `Constants.ℏ` (id 390795), plus its positivity lemmas. Source/module lookup confirmed its positive real joule-second value in `Physlib.QuantumMechanics.PlanckConstant`.

The local Lean LSP search for `transmissionProbability` found only problem-local declarations in other project files, not Mathlib/Physlib infrastructure. Direct inspection of the installed `Physlib.QuantumMechanics.RectangularBarrier.Basic` module confirmed that it supplies the barrier object, its piecewise potential, and operators, but no reflection/transmission coefficient.

## Physlib/Mathlib names grounded

- Physlib units and dimensions: `Dimensionful`, `WithDim`, `Dimension`, `L𝓭`, `M𝓭`, `T𝓭`, `C𝓭`, `UnitChoices.SI`, `DimEnergy`, `DimEnergy.electronVolt`, `LengthUnit`, `LengthUnit.meters`, `LengthUnit.millimeters`, `LengthUnit.nanometers`, `MassUnit`, and `MassUnit.kilograms`.
- Physlib quantum infrastructure: `Constants.ℏ`, `QuantumMechanics.RectangularBarrier`, and its fields `m`, `lower`, `upper`, and `V₀`. LSP hover confirmed that the type's potential is `V₀` on `Icc lower upper` and zero outside.
- Mathlib analytic functions: `Real.sqrt` and `Real.exp`.

## Local abstractions introduced

- Dimensionful aliases instantiate Physlib's `Dimensionful (WithDim ... ...)` rather than collapsing length, mass, density, action, inverse length, potential, or current to bare reals. Reals appear only in named unit readouts and in the dimensionless estimate.
- Small inductive types preserve particle, material, shape, direction, voltage-role, and image-label distinctions.
- `CopperOxideJunctionFigure` records literal primary-image evidence separately from prose data and physics laws.
- `CopperOxideTunnelingSetup` keeps all physical quantities independent, including the decay constant and leading estimate.
- The local decay and leading-estimate interfaces fill the absent scattering/transmission API while preserving the actual symbolic laws. Their absence from Physlib is therefore a grounding gap, not a formalization blocker.

## Source/law/answer audit

- The primary image was inspected directly rather than relying only on its caption.
- Wire diameter and free-electron density are part of the stated junction setup but are irrelevant to the single-electron probability estimate; they are retained as readouts without being forced into the decay law.
- The source asks for a dimensionless probability estimate, while every printed option and recorded answer has energy units. The formalization therefore does not select A--D.
- Using the stated leading exponential convention gives approximately `1.685 × 10⁻¹²`, represented by the interval `(1.6 × 10⁻¹², 1.8 × 10⁻¹²)`. The declaration explicitly identifies this as a leading opaque-barrier estimate, not the exact finite rectangular-barrier coefficient.

## Grounding gaps and redraft requests

- **No blocking infrastructure gap.** Mathlib/Physlib currently exposes no reusable rectangular-barrier transmission-probability declaration. `DefinesLeadingOpaqueBarrierTransmissionEstimate` is the faithful local governing-law interface that completely fills this gap for the stated estimate.
- **No blocking constant gap.** No dimensionful electron-rest-mass constant was found; the independent dimensionful mass is faithfully calibrated by its kilogram readout.
- The source should be redrafted with dimensionless probability choices (or no choices). The existing `5--8 eV` options and recorded answer A are dimensionally incompatible with the question.
- `.archon/AGENTS.md` is absent at the requested path. The complete injected task instructions and `.archon/prover-modes/physics-formalize.md` supplied the role discipline.
- The advertised `archon` executable is not on `PATH`, so the optional DAG query could not be run.
- The blueprint theorem was not marked `\leanok` because the explicit write permissions forbid editing blueprint chapters. A coordinator with blueprint write permission should add the marker.

## Verification

`lake env lean PhyXMiniProblems/problem_phyx_mini_0616.lean` exited successfully. The only diagnostics are the three expected `declaration uses sorry` warnings for the two auxiliary lemmas and the principal theorem.
