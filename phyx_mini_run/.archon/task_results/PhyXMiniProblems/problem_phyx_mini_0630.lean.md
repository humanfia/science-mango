## Prover result — Archon iteration 018

Status: complete.

### Declaration proved

- `PhyXMiniProblems.ProblemPhyXMini0630.p_side_depletion_depth_is_275_nanometers`

The proof uses the `Dimensionful` scaling invariant to express the
centimetre readouts of both depletion depths as the same positive multiple of
their nanometre readouts.  Rewriting equilibrium charge neutrality with the
supplied densities and `a_n = 55 nm` gives the scaled equation for
`a_p = 275 nm`; positivity of the common unit scale permits cancellation.
Constructor analysis then proves that choice A matches and is the unique
matching displayed answer.

### Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0630.lean` exits
  successfully.
- The assigned Lean file contains no `sorry`, `admit`, `sorryAx`, introduced
  `axiom`, `native_decide`, or unsafe escape.
- Archon Lean verification reports only the standard foundational axioms
  `propext`, `Classical.choice`, and `Quot.sound`, with no source-scan warning.
- The compiler emits only unused-variable lints for the frozen hypotheses
  `hFigure` and `hPhysical`; the numerical conclusion needs only `hData` and
  the equilibrium law in `hLaws`.

### Redraft needed

None.

### Blueprint handoff

The target blueprint environment should be marked `\leanok`.  This prover did
not edit the chapter because the task's explicit write-permission section
allows edits only to the assigned Lean file and this task-result file and
specifically forbids blueprint edits.

### Environment notes

- `.archon/AGENTS.md` is absent in this checkout; the explicit prover prompt
  and `.archon/PROGRESS.md` supplied the applicable role.
- The advertised `archon` executable is not available on `PATH`, so the
  optional read-only DAG query could not be run.

## Assumption/target split

### Governing laws

- `SatisfiesDepletionRegionPhysics.noMobileCarriersInDepletion` records the
  depletion approximation for both electrons and holes.
- `constantNegativeChargeOnPDepletion` and
  `constantPositiveChargeOnNDepletion` state the fixed-ion laws
  `rho_p = -e N_A` and `rho_n = e N_D` throughout their respective depleted
  slabs.  They use charge-density readouts rather than equating dimensionally
  different charge and number densities.
- `noNetChargeOutsideDepletion` records the stated vanishing charge outside
  the interval from `-a_p` to `a_n`.
- `electricFieldPointsTowardPSide` and `stabilizingElectricFieldDeveloped`
  encode the stated field `E_vec = -E i_hat`: its x-component is nonpositive
  throughout the depletion region and strictly negative somewhere.
- `equilibriumChargeNeutralityPerUnitArea` is the general junction-equilibrium
  law `N_A a_p = N_D a_n`.  It relates the independently modeled p- and n-side
  depths and does not assign a numerical value to `a_p`.

### Previous-part results

- None.  The source report has an empty `previous_parts` list.

### Figure/data readouts

- `MatchesProblemData` records silicon on both sides, p-type boron doping on
  the left, n-type arsenic doping on the right, and an x-axis directed from p
  toward n.
- The supplied readouts are `N_A = 10^16 cm^-3`,
  `N_D = 5 * 10^16 cm^-3`, and `a_n = 55 nm`.
- The physical landmark coordinates are `-a_p`, `0`, and `a_n`, and the total
  physical depletion width satisfies `W = a_p + a_n`.
- `MatchesPrimaryFigure` transcribes the image labels `p`, `n`, `-a_p`, `0`,
  `a_n`, and `W`; negative p-side ions; positive n-side ions; the two terminal
  leads; and the qualitative left-to-right ordering.  Its image coordinates
  are explicitly schematic and unscaled.
- `HasPhysicalParameters` supplies only positivity/nondegeneracy conditions.

### Current target conclusions

- `lengthInNanometers setup.pSideDepletionDepth = 275`.
- Choice A matches this independently modeled depth, and it is the unique
  matching displayed choice.

## Goal-faithfulness audit

`PNJunctionSetup.pSideDepletionDepth` is an independent dimensionful physical
field.  It is not defined from `275`, from answer choice A, or from any solved
ratio.  Neither `MatchesProblemData`, `MatchesPrimaryFigure`,
`HasPhysicalParameters`, nor `SatisfiesDepletionRegionPhysics` contains the
conclusion `a_p = 275 nm` or an equivalent numerical assignment.

The only premise involving `a_p` substantively is the general charge-neutrality
law `N_A a_p = N_D a_n`, which is the physical equilibrium law used to solve
the question.  The fixed-ion laws independently describe the charge profile
and include the elementary-charge factor required for dimensional correctness.
The answer-choice table merely transcribes all four printed options; it does
not identify which one is correct in a hypothesis.  `MatchesAnswerChoice`
compares a choice with the setup's independent p-side depth and is used only in
the theorem conclusion.

Lengths, number densities, charge densities, charge magnitude, axial position,
and the electric-field component remain Physlib `Dimensionful (WithDim ...)`
quantities.  Reals are restricted to calibrated unit readouts, qualitative
image coordinates, and printed option values.

## Declarations created and blueprint labels

- Dimension layer: `inverseVolumeDimension`, `chargeDensityDimension`,
  `energyDimension`, `electricFieldDimension`, `LengthQuantity`,
  `SignedAxialPositionQuantity`, `NumberDensityQuantity`,
  `ChargeMagnitudeQuantity`, `ChargeDensityQuantity`, and
  `AxialElectricFieldQuantity`.
- Calibrated readouts: `lengthReadout`, `signedPositionReadout`,
  `numberDensityReadout`, `chargeDensityReadout`,
  `chargeMagnitudeInCoulombs`, `axialElectricFieldInVoltsPerMeter`, and the
  nanometre/centimetre specializations.
- Physical and figure vocabulary: `SemiconductorSide`, `ConductivityType`,
  `SemiconductorMaterial`, `DopantSpecies`, `MobileCarrier`,
  `FixedChargeSign`, `AxialDirection`, `JunctionLandmark`, and
  `PNJunctionFigure`.
- Physical setup and regions: `PNJunctionSetup`, `InPSideDepletion`,
  `InNSideDepletion`, `InDepletionRegion`, and `OutsideDepletionRegion`.
- Premise interfaces: `MatchesProblemData`, `MatchesPrimaryFigure`,
  `HasPhysicalParameters`, and `SatisfiesDepletionRegionPhysics`.
- Choice layer: `AnswerChoice`, `AnswerChoice.depthInNanometers`, and
  `MatchesAnswerChoice`.
- Blueprint label `thm:physics:phyx_mini_0630:target` corresponds to
  `PhyXMiniProblems.ProblemPhyXMini0630.p_side_depletion_depth_is_275_nanometers`.

## LeanExplore queries and candidates used

Every query used `packages: ["Mathlib", "Physlib"]`:

- `physical quantity with dimensions length number density inverse volume charge density electric field`
- `p-n junction depletion region charge neutrality semiconductor donor acceptor density`
- `PhysicalQuantity Dimension Length inverse volume`
- `WithDim Dimensionful UnitChoices`
- `number density inverse cubic length physical units`
- `LengthUnit.nanometers UnitChoices.SI`
- `LengthUnit.centimeters`

Candidates inspected and used:

- `Dimensionful` (LeanExplore id 394284), from `Physlib.Units.Basic`, is the
  unit-independent subtype used for all physical quantities.
- `Dimension.L𝓭` (id 394324), from `Physlib.Units.Dimension`, grounds the
  length and inverse-volume dimensions.
- `LengthUnit` (id 393137), from
  `Physlib.SpaceAndTime.Space.LengthUnit`, grounds calibrated length-unit
  selection.
- `LengthUnit.nanometers` (id 393157) and `LengthUnit.centimeters`
  (id 393160) provide the exact units used by the problem.
- `UnitChoices.SI` (id 394270), from `Physlib.Units.Basic`, supplies metres,
  seconds, kilograms, coulombs, and kelvin before the length unit is replaced
  for a named readout.

Near-match candidates inspected but not used:

- `Electromagnetism.ChargeDensity` (id 385563) is the undimensioned alias
  `Time -> Space -> Real`; it does not carry charge-per-volume dimensions and
  fixes a spacetime profile shape unsuitable for the dimensionful 1D junction
  interface.
- `Electromagnetism.ElectricField` (id 385559) is an undimensioned spacetime
  function to a Euclidean vector.  The source asks only for the signed axial
  component and its physical units, so the local dimensionful component type
  is the closer model.

## Physlib/Mathlib names grounded

- Physlib: `Dimension`, `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `M𝓭`,
  `T𝓭`, `C𝓭`, `UnitChoices.SI`, `LengthUnit`,
  `LengthUnit.nanometers`, and `LengthUnit.centimeters`.
- Mathlib: `NNReal`, `Fintype`, and the ordered-field operations used on
  calibrated real readouts.
- LeanExplore source/module inspection and successful Archon Lean LSP
  elaboration confirm these names in the checked environment.

## Local abstractions introduced

- Number density, charge density, and electric-field dimensions are composed
  from Physlib's base dimensions.  The resulting quantity types are
  dimensionful Physlib types, not transparent scalar aliases or one-field
  wrappers.
- `PNJunctionSetup` keeps physical depths, profiles, species, axis orientation,
  and figure metadata distinct.  In particular, the schematic image
  coordinate is not confused with physical axial position.
- The local region predicates express the physical intervals `[-a_p, 0)` and
  `[0, a_n]` using calibrated position/depth readouts.
- `SatisfiesDepletionRegionPhysics` is local because no semiconductor
  depletion-region API or junction neutrality theorem was found.  It states
  the governing laws rather than the requested solved value.

## Grounding gaps and redraft requests

- No Mathlib/Physlib declaration specific to semiconductor p-n depletion
  regions, dopant number densities, or `N_A a_p = N_D a_n` was found.  The
  faithful local interfaces above fill this gap.
- The scenario's opening sentence swaps conventional labels by associating
  `N_D` with p-type silicon and `N_A` with n-type silicon, whereas the numerical
  question, dopant species, image charge signs, and standard semiconductor
  convention unambiguously give p-side boron acceptors `N_A` and n-side
  arsenic donors `N_D`.  The Lean model follows that unambiguous latter data;
  the blueprint prose should be corrected.
- The prose says a charge-density magnitude equals an atom density, which is
  dimensionally incomplete.  The Lean law uses the physically required factor
  `e`, namely `|rho| = e N`.
- `.archon/AGENTS.md` and the assigned Lean file were initially absent.  The
  complete `.archon/prover-modes/physics-formalize.md` instructions and the
  relevant `PROGRESS.md` entry supplied the applicable role; the missing Lean
  file therefore contained no `/- USER: ... -/` hint.
- The `archon` executable advertised for DAG navigation was not available on
  this runtime's `PATH`, so the target node could not be queried.
- The blueprint exists, but the explicit write-permission section permits
  edits only to the assigned Lean file and this result and forbids blueprint
  edits.  Therefore `\leanok` was not added; a blueprint-owning agent should
  add it after accepting the formalization.

## Verification

- Archon Lean LSP diagnostics report successful elaboration with exactly one
  expected warning: the target theorem uses `sorry`.
- There are no Lean errors or failed dependencies.
