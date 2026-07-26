# Autoformalization result: `problem_phyx_mini_0849.lean`

## Outcome

Created a compiling physics formalization with `by sorry` bodies for the
intermediate numerical bound and the blueprint target. Both Lean LSP
diagnostics and
`lake env lean PhyXMiniProblems/problem_phyx_mini_0849.lean` report no errors
and only the two expected `declaration uses sorry` warnings.

The primary bitmap was inspected. It places point 1 immediately outside the
center of the top surface, point 2 in the gray conducting material, and point
3 in the centered white cavity. The physical interpretation is therefore
`E₁ ≈ 900 N/C`, `E₂ = 0`, and `E₃ = 0`.

## Assumption/target split

### Governing laws

- `SatisfiesConductingBoxElectrostatics.surfaceChargeFromExcessElectrons`
  states the sign-sensitive conversion `sigma = -n e`.
- `SatisfiesConductingBoxElectrostatics.exteriorSurfaceBoundaryCondition`
  states the generic conductor boundary law
  `E = (sigma / epsilon_0) n_out` for any point assigned the top-adjacent
  exterior role.
- `SatisfiesConductingBoxElectrostatics.fieldVanishesInConductingMaterial`
  states the electrostatic-equilibrium conductor law for any point in the
  conducting region.
- `SatisfiesConductingBoxElectrostatics.fieldVanishesInChargeFreeCavity`
  states electrostatic shielding for any point in an enclosed charge-free
  cavity.
- `SatisfiesConductingBoxElectrostatics.dimensionfulFieldAgreesWithPhyslib`
  connects the dimensionful field readout to
  `Electromagnetism.ElectricField 3`.

### Previous-part results

- None; the source report has an empty `previous_parts` list.

### Figure/data readouts

- `MatchesSuppliedConductingBoxFigure` records the outer conducting
  rectangle, contained inner cavity, all three dots, point 1 outside the top
  center, point 2 in conductor material, and point 3 in the empty cavity.
- `MatchesConductingBoxScenario` records a negatively charged hollow
  conductor in vacuum, electrostatic equilibrium, a charge-free cavity, and
  sampling at the top-surface center.
- `MatchesReportedSurfaceDensityData` records
  `5.0 * 10^10 electrons/m^2`.
- `UsesStandardElectrostaticConstants` calibrates the elementary-charge
  magnitude against `ChargeUnit.elementaryCharge` and vacuum permittivity
  against `Electromagnetism.FreeSpace.ε₀` with its standard SI value.
- `HasPhysicalConductingBoxParameters` records positivity and that the top
  outward normal has unit length.
- The displayed choice numbers are `800`, `1000`, `200`, and `900`; dataset
  metadata records D.

### Current target conclusions

- `point1_field_strength_rounding_bounds`: point 1 has field strength in the
  interval `[850, 950] N/C`.
- `problem_phyx_mini_0849`: point 1 rounds to `900 N/C` at resolution
  `100 N/C`, point 2 and point 3 have zero field strength, and recorded answer
  D is the unique displayed match.

## Goal-faithfulness audit

`ConductingBoxSetup.fieldVectorAt` is an independent dimensionful physical
field and is not defined from any requested value. The law structure has no
`850`, `900`, `950`, answer label D, or special equation mentioning point 1,
point 2, or point 3. Its vanishing and boundary clauses quantify over every
point with the relevant physical region role; the figure premises separately
identify which numbered points have those roles. Thus the zero conclusions
are applications of general conductor/shielding laws, not duplicated target
hypotheses.

The density and fundamental constants are input calibrations, not
reverse-engineered field values. `recordedDatasetAnswer := .D` and the answer
table preserve source metadata but are never theorem premises. The generic
rounding/matching predicates do not force any choice, and the physical field
remains independent of them. All current numerical and point-specific results
occur only in the two declaration conclusions.

## Declarations and blueprint labels

- Dimensionful quantities/readouts:
  `SurfaceElectronNumberDensityQuantity`, `ChargeMagnitudeQuantity`,
  `SignedSurfaceChargeDensityQuantity`, `VacuumPermittivityQuantity`,
  `ElectricFieldVectorQuantity`, their four dimensions, and coherent-SI
  readout functions.
- Figure vocabulary: `FigurePoint`, `FigureRegion`,
  `SurfaceSampleLocation`, `ExcessChargeSign`, `ElectrostaticModel`, and
  `ConductingBoxFigure`.
- Physical setup and assumptions: `ConductingBoxSetup`,
  `MatchesConductingBoxScenario`, `MatchesReportedSurfaceDensityData`,
  `MatchesSuppliedConductingBoxFigure`, `UsesStandardElectrostaticConstants`,
  `HasPhysicalConductingBoxParameters`, and
  `SatisfiesConductingBoxElectrostatics`.
- Answer vocabulary: `AnswerChoice`,
  `displayedExteriorFieldStrengthInNewtonsPerCoulomb`,
  `RoundsToNearestResolution`, `AnswerMatchesExteriorField`, and
  `IsUniqueMatchingAnswer`.
- Intermediate declaration: `point1_field_strength_rounding_bounds`.
- Main declaration: `problem_phyx_mini_0849`, corresponding to
  `thm:physics:phyx_mini_0849:target`.

The blueprint chapter exists. It was not edited to add `\leanok` because the
task's final write-permission section restricts edits to the assigned Lean
file and this result file. The target declaration is ready for blueprint
marker synchronization by an authorized agent.

## LeanExplore queries and candidates actually used

All queries used `packages: ["Mathlib", "Physlib"]`:

- `electric field as a spacetime-dependent vector field`
- `Electromagnetism.ElectricField`
- `elementary electric charge in coulombs ChargeUnit.elementaryCharge`
- `vacuum permittivity Electromagnetism.FreeSpace epsilon_0`
- `Electromagnetism.FreeSpace structure vacuum permittivity ε₀`
- `Dimensionful WithDim physical quantity units`
- `electric field inside a conductor at electrostatic equilibrium is zero`
- `electrostatic shielding electric field vanishes in a charge-free cavity`
- `surface charge density boundary condition electric field sigma divided by epsilon zero`

Source/module/docstring details were fetched for the candidates used directly:

- `Electromagnetism.ElectricField` (ID 385559), an abbreviation
  `Time → Space d → EuclideanSpace ℝ (Fin d)` from
  `Physlib.Electromagnetism.Basic`.
- `ChargeUnit.elementaryCharge` (ID 385585), the standard
  `1.602176634e-19`-coulomb charge unit from
  `Physlib.Electromagnetism.Charge.ChargeUnit`.
- `Electromagnetism.FreeSpace` (ID 385663), containing positive real
  permittivity `ε₀` and permeability `μ₀`, from
  `Physlib.Electromagnetism.Dynamics.Basic`.
- `Dimensionful` (ID 394284), the unit-choice-coherent physical-quantity type
  from `Physlib.Units.Basic`.

## PhysLean/Mathlib names grounded

- `Electromagnetism.ElectricField`, `Electromagnetism.FreeSpace`,
  `ChargeUnit.elementaryCharge`, and `ChargeUnit.coulombs` ground the field,
  vacuum constants, and elementary-charge calibration.
- `Dimensionful`, `WithDim`, `Dimension`, `Dimension.M𝓭`, `Dimension.L𝓭`,
  `Dimension.T𝓭`, `Dimension.C𝓭`, and `UnitChoices.SI` ground the
  unit-independent quantities and coherent-SI projections.
- `EuclideanSpace ℝ (Fin 3)`, `Time`, and `Space 3` ground the field-vector and
  spacetime types. Their exact use was additionally validated by successful
  Lean elaboration.

## Local abstractions introduced

- Named dimensions for surface number density, surface charge density,
  vacuum permittivity, and electric field preserve the exact dimensional
  roles absent as ready-made named quantity types.
- Dimensionful wrappers distinguish electron count per area, charge
  magnitude, signed charge per area, permittivity, and vector electric field;
  no basic physical primitive is a transparent scalar alias.
- `ConductingBoxFigure`, `FigureRegion`, and the scenario/readout structures
  preserve the primary image's outer conductor, inner cavity, and point
  locations independently from the laws and conclusions.
- `SatisfiesConductingBoxElectrostatics` is the smallest local interface for
  the conductor boundary condition, equilibrium interior law, and cavity
  shielding law not found in PhysLean.
- `RoundsToNearestResolution` and `IsUniqueMatchingAnswer` represent the
  displayed-answer precision without defining the physical field from the
  desired answer.

## Grounding gaps

LeanExplore found general field, charge-density, and electromagnetic-potential
declarations, but no matching PhysLean theorem for a conductor's
`sigma/epsilon_0` boundary field, field vanishing inside conducting material,
or electrostatic shielding of a charge-free cavity. Plane-wave and
distributional-potential results returned by the searches were physical near
misses. The faithful local law interface was therefore necessary.

The `archon dag-query` command could not be run because `archon` is not on
`PATH` in this workspace session. No dependency-graph ancestor was used.
The requested `.archon/AGENTS.md` is also absent in the current project; the
injected prover-role instructions and `.archon/prover-modes/physics-formalize.md`
were followed.

## Redraft requests

- The source prints all answer values with `N m^2/C`, which is electric-flux
  dimension, although the question asks for electric-field strength. The Lean
  model interprets the numeric values as `N/C`; the source/blueprint should be
  corrected or explicitly explain this normalization.
- The source records only `D: 900` while asking for all of `E₁` through `E₃`.
  The formalization uses the standard conductor interpretation
  `(approximately 900, 0, 0) N/C`; a future blueprint redraft should state
  that triplet explicitly.
