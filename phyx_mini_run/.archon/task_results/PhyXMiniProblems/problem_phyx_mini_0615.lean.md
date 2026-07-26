# Autoformalization result: `problem_phyx_mini_0615.lean`

This is the genuine post-formalization evidence for Archon iteration 003. The
review-gate reason is evidence-only, so the already faithful Lean statement was
preserved and re-audited against the source report, primary bitmap, blueprint,
LeanExplore results, Lean LSP, and the real Lake environment.

## Assumption/target split

### Governing laws

- `UsesStandardReducedPlanckConstant` calibrates the dimensionful action by
  the joule-second readout `Constants.ℏ`.
- `MatchesPhyslibRectangularBarrier` calibrates the Physlib scalar barrier's
  mass, face separation, and height using coherent-SI readouts of the typed
  physical quantities.
- `HasPhysicalTunnelingParameters` states the model domain: positive mass,
  width, barrier energy, incident energy, energy deficit, action and wave
  number; `0 < E < U₀`; and the generic probability bound `T ∈ [0, 1]`.
- `ObeysTextbookRectangularBarrierTunneling.attenuationWaveNumberLaw` states
  `ℏ² κ² = 2 m (U₀ - E)` in coherent-SI scalar readouts.
- `ObeysTextbookRectangularBarrierTunneling.exactBarrierTransmissionLaw`
  states the exact finite rectangular-barrier coefficient
  `T = (1 + U₀² sinh²(κ L) / (4 E (U₀ - E)))⁻¹`. This is an exact stationary
  scattering law, not a globally asserted opaque-barrier approximation.

### Previous-part results

- None. The source report has `previous_parts: []`.

### Figure/data readouts

- `MatchesAlphaNucleusScenario` records an alpha particle initially trapped in
  a nucleus and encountering a one-dimensional rectangular barrier.
- `MatchesSuppliedBarrierFigure` records axes `r` and `U(r)`, printed labels
  `O`, `U₀`, and `E`, the rectangular curve, the `2.0 fm` width, and the
  bitmap's printed `1.0 MeV` gap.
- `MatchesProblemReadouts` records the prose data `m = 6.64e-27 kg`,
  `L = 2.0 fm`, `U₀ = 30.0 MeV`, and `U₀ - E = 10.0 MeV`.
- The primary bitmap was inspected directly. Its `1.0 MeV` annotation
  conflicts with the prose's `10.0 MeV` deficit, so the two remain independent
  source facts. The prose deficit controls the model used for the answer.

### Current target conclusions

- `energyInMegaElectronVolts setup.incidentKineticEnergy = 20`.
- `RoundsToThreeDecimalPlaces setup.tunnelingProbability 0.014`.
- `IsUniqueMatchingTunnelingChoice setup .A`.

## Goal-faithfulness audit

No current target conclusion is a hypothesis or a field of a scenario,
readout, calibration, physical-domain, or governing-law structure. In
particular, the exact transmission law contains neither `0.014` nor choice
`.A`; it constrains an independently stored `tunnelingProbability` using the
independent dimensionful inputs. The unit-interval premise is only the generic
range of a probability.

The choice table contains the source's displayed values, and
`recordedDatasetAnswer := .A` records dataset metadata, but neither is a
hypothesis of the theorem. The theorem does not mention
`recordedDatasetAnswer`. `RoundsToThreeDecimalPlaces` is a genuine half-open
interval of width `0.001`, while `IsUniqueMatchingTunnelingChoice` requires a
match and quantifies over every other choice; neither makes the conclusion
true by unfolding.

As an external numerical audit of the stated physical law, the prose data and
`ℏ = 1.054571817e-34 J s` give `κL = 2.76635600562` and
`T = 0.013976890501`, which lies in the interval rounding to `0.014`.

## Declarations and blueprint labels

All Lean names below have namespace
`PhyXMiniProblems.ProblemPhyXMini0615`. The label prefix for definitions is
`def:physics:phyx-mini-0615:phyxminiproblems-problemphyxmini0615-`.

| Lean declaration | Blueprint label suffix |
|---|---|
| `LengthQuantity` | `lengthquantity` |
| `MassQuantity` | `massquantity` |
| `EnergyQuantity` | `energyquantity` |
| `actionDimension` | `actiondimension` |
| `ActionQuantity` | `actionquantity` |
| `WaveNumberQuantity` | `wavenumberquantity` |
| `lengthReadout` | `lengthreadout` |
| `lengthInMeters` | `lengthinmeters` |
| `lengthInFemtometers` | `lengthinfemtometers` |
| `massInKilograms` | `massinkilograms` |
| `energyInJoules` | `energyinjoules` |
| `energyInElectronVolts` | `energyinelectronvolts` |
| `energyInMegaElectronVolts` | `energyinmegaelectronvolts` |
| `actionInJouleSeconds` | `actioninjouleseconds` |
| `waveNumberInInverseMeters` | `wavenumberininversemeters` |
| `ParticleSpecies` | `particlespecies` |
| `NuclearPotentialModel` | `nuclearpotentialmodel` |
| `PlotAxis` | `plotaxis` |
| `PlotAxisQuantity` | `plotaxisquantity` |
| `PotentialCurveShape` | `potentialcurveshape` |
| `FigureAnnotation` | `figureannotation` |
| `RectangularBarrierFigure` | `rectangularbarrierfigure` |
| `AlphaRectangularBarrierSetup` | `alpharectangularbarriersetup` |
| `MatchesAlphaNucleusScenario` | `matchesalphanucleusscenario` |
| `MatchesSuppliedBarrierFigure` | `matchessuppliedbarrierfigure` |
| `MatchesProblemReadouts` | `matchesproblemreadouts` |
| `UsesStandardReducedPlanckConstant` | `usesstandardreducedplanckconstant` |
| `MatchesPhyslibRectangularBarrier` | `matchesphyslibrectangularbarrier` |
| `HasPhysicalTunnelingParameters` | `hasphysicaltunnelingparameters` |
| `ObeysTextbookRectangularBarrierTunneling` | `obeystextbookrectangularbarriertunneling` |
| `AnswerChoice` | `answerchoice` |
| `displayedTunnelingProbability` | `displayedtunnelingprobability` |
| `recordedDatasetAnswer` | `recordeddatasetanswer` |
| `RoundsToThreeDecimalPlaces` | `roundstothreedecimalplaces` |
| `MatchesDisplayedTunnelingProbability` | `matchesdisplayedtunnelingprobability` |
| `IsUniqueMatchingTunnelingChoice` | `isuniquematchingtunnelingchoice` |

The proof-stage declarations correspond to these full labels:

- `incident_kinetic_energy_megaelectronvolts_eq`:
  `lem:physics:phyx-mini-0615:phyxminiproblems-problemphyxmini0615-incident-kinetic-energy-megaelectronvolts-eq`.
- `tunneling_probability_rounds_to_0_014`:
  `lem:physics:phyx-mini-0615:phyxminiproblems-problemphyxmini0615-tunneling-probability-rounds-to-0-014`.
- `problem_phyx_mini_0615`:
  `thm:physics:phyx_mini_0615:target`.

## LeanExplore queries and candidates actually used

Every search passed `packages: ["Mathlib", "Physlib"]`.

- `Dimensionful WithDim physical quantity units` returned `Dimensionful`
  (ID 394284), which is used for typed length, mass, action, and wave-number
  quantities.
- `DimEnergy joule electronVolt` returned `DimEnergy` (394468),
  `DimEnergy.joule` (394469), and `DimEnergy.electronVolt` (394470), all used
  by the energy type and readouts.
- `Constants.ℏ reduced Planck constant` returned `Constants.ℏ` (390795), used
  by the reference-action calibration.
- `Real.sinh hyperbolic sine` returned `Real.sinh` (128823), used in the exact
  transmission coefficient.
- `QuantumMechanics.RectangularBarrier rectangular potential barrier` did not
  return that type; its results were unrelated potential-operator APIs.
- `rectangular barrier tunneling transmission coefficient` returned no
  compatible barrier transmission declaration.

Module and source lookups were fetched only for the candidates adopted above:
`Dimensionful` is in `Physlib.Units.Basic`; the three energy declarations are
in `Physlib.Units.WithDim.Energy`; `Constants.ℏ` is in
`Physlib.QuantumMechanics.PlanckConstant`; and `Real.sinh` is in
`Mathlib.Analysis.Complex.Trigonometric`.

An LSP hover grounded the imported
`QuantumMechanics.RectangularBarrier : Type` from
`Physlib.QuantumMechanics.RectangularBarrier.Basic`: it is a positive-mass
one-dimensional particle whose potential is `V₀` on `Set.Icc lower upper` and
zero outside. LSP local name search did not index it, but hover elaboration in
the assigned file succeeded without diagnostics.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension`, `L𝓭`, `M𝓭`, `T𝓭`,
  `DimEnergy`, `DimEnergy.joule`, `DimEnergy.electronVolt`, `LengthUnit`,
  `MassUnit`, `UnitChoices`, `Constants.ℏ`, and
  `QuantumMechanics.RectangularBarrier`.
- Mathlib: `NNReal`, `Set.Icc`, real powers and inversion, and `Real.sinh`.

## Local abstractions introduced

- `LengthQuantity`, `MassQuantity`, `ActionQuantity`, and
  `WaveNumberQuantity` specialize Physlib's `Dimensionful (WithDim ...)`.
  They are not scalar aliases and preserve unit transformation and physical
  dimensions. `EnergyQuantity` directly uses Physlib's `DimEnergy`.
- Unit-labelled readout functions distinguish physical quantities from the
  real numbers used for numeric data and the dimensionless probability.
- The scenario enums, figure record, and setup preserve particle role, axes,
  graph labels, potential shape, geometry, and both conflicting source
  readouts.
- The local law structure preserves the physical meaning of attenuation and
  exact stationary scattering while keeping `κ` and `T` independent fields.
  It is needed because no compatible Physlib transmission-coefficient API was
  found.
- The answer/rounding predicates encode the displayed multiple-choice layer
  separately from the physical laws.

## Grounding gaps and redraft requests

- Mathlib/Physlib has no located exact rectangular-barrier transmission API;
  the textbook coefficient therefore remains a faithful local law interface.
- The source prose and primary bitmap conflict on the energy gap (`10.0 MeV`
  versus `1.0 MeV`). The Lean model preserves both and explicitly selects the
  prose datum for the physical computation; the source should eventually be
  corrected or annotate the discrepancy.
- The blueprint exists and has declaration topology, but its proof paragraphs
  are generic rather than an informal derivation. A plan-agent redraft should
  record `E = 30 - 10 = 20 MeV`, `κ = sqrt(2m(U₀-E))/ℏ`, substitution into
  the exact `sinh` coefficient, and rounding to `0.014`.
- `.archon/AGENTS.md` is absent. The injected role prompt,
  `.archon/PROGRESS.md`, and `.archon/prover-modes/physics-formalize.md` were
  used instead. The assigned Lean file contains no `/- USER: ... -/` hints.
- The advertised `archon` executable is not on `PATH`, so the optional DAG
  query could not run.
- The blueprint was not edited to add `\leanok`, because the explicit write
  permissions restrict edits to the assigned Lean file and this result file.
  A blueprint-authorized coordinator should add the marks after review.

## Verification

- `archon-lean-lsp` reports no errors or failed dependencies and exactly three
  expected `declaration uses sorry` warnings, at the two lemmas and theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0615.lean` exits 0 with
  exactly those same three warnings.

