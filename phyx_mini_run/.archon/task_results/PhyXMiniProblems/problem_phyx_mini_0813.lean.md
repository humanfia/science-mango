# Autoformalization result: `problem_phyx_mini_0813.lean`

## Assumption/target split

### Governing laws

- `SatisfiesFrictionlessHarmonicMotion` bridges the dimensionful glider mass
  and spring stiffness to the scalar SI parameters of Physlib's
  `ClassicalMechanics.HarmonicOscillator`.
- Its trajectory-coordinate and trajectory-velocity fields identify the
  Physlib one-dimensional coordinate with displacement from the relaxed-spring
  equilibrium and its time derivative with the signed physical x-velocity.
- Its `mechanicalEnergyConservation` field states equality of
  `ClassicalMechanics.HarmonicOscillator.energy` at release and at the queried
  state. This is the frictionless mechanical-energy law, not a solved velocity
  formula.
- `HasPhysicalParameters` records strict positivity of the SI mass and
  stiffness readouts.

### Previous-part results

- None. This is a standalone one-part problem.

### Figure/data readouts

- `MatchesProblemAndPrimaryFigure` records `m = 0.200 kg`, `k = 5.00 N/m`,
  equilibrium `x = 0`, release position `x₁ = 0.100 m`, release velocity
  `v₁x = 0`, and queried position `x = 0.080 m`.
- The source's phrase "moves back toward its equilibrium position" is recorded
  only as the qualitative sign condition `v_x < 0` at the queried positive-x
  state. It does not state the speed magnitude.
- It also records the frictionless horizontal air track, spring attachment,
  rightward positive x-axis, Point 1 at the left spring endpoint, the relaxed
  endpoint at `x = 0`, and the roles of all labels visible in `813.png`.

### Current target conclusions

- `queriedVelocitySquared_eq_nineHundredths` concludes
  `v_x^2 = 9/100 (m/s)^2`.
- `problem_phyx_mini_0813` concludes the signed velocity
  `v_x = -3/10 m/s` and that recorded answer choice B reports it.

## Goal-faithfulness audit

- `GliderSpringSetup.xVelocityAt .queriedPosition` is an independent
  dimensionful quantity. It is not defined using `-3/10`, an answer choice, or
  the energy equation.
- No premise or law field contains the exact target velocity or its squared
  magnitude. The only velocity constraint in the source-data structure is the
  stated direction `v_x < 0`, which selects the negative root after energy
  conservation determines the magnitude.
- `AnswerChoice.velocityInMetersPerSecond` faithfully transcribes answer-list
  metadata. `AnswerChoiceReportsQueriedVelocity` occurs only in the theorem
  conclusion, never as a premise, so unfolding the metadata cannot establish
  the theorem without deriving the physical velocity.
- The energy assumption is expressed through Physlib's general oscillator
  energy at two states and contains no answer-specific numerical value.
- No current target was placed in a `Laws`, `Valid...Physics`, `Satisfies...`,
  setup field, or helper definition.

## Declarations and blueprint correspondence

- Dimensionful roles and readouts: `MassQuantity`,
  `SignedPositionQuantity`, `SignedVelocityQuantity`,
  `SpringStiffnessQuantity`, and their coherent unit readouts.
- Figure/process model: `ProcessInstant`, `FigureFeature`, `FigureLabel`,
  `FigureLabelRole`, `HorizontalDirection`, `TrackCondition`,
  `GliderSpringFigure`, and `GliderSpringSetup`.
- Source and law interfaces: `MatchesProblemAndPrimaryFigure`,
  `HasPhysicalParameters`, and `SatisfiesFrictionlessHarmonicMotion`.
- Derived declaration: `queriedVelocitySquared_eq_nineHundredths`.
- Answer metadata: `AnswerChoice`,
  `AnswerChoice.velocityInMetersPerSecond`,
  `recordedDatasetAnswerChoice`, and
  `AnswerChoiceReportsQueriedVelocity`.
- `problem_phyx_mini_0813` corresponds to blueprint label
  `thm:physics:phyx_mini_0813:target` and is ready for the deterministic
  `\leanok` synchronization. The blueprint was not edited because prover write
  permission is limited to this Lean file and this result file.

## LeanExplore queries and candidates

All searches used the requested package filter `['Mathlib', 'Physlib']`.

- Natural-language query: "one-dimensional mass spring harmonic oscillator
  total mechanical energy conservation kinetic elastic potential energy".
  Relevant results inspected were
  `ClassicalMechanics.HarmonicOscillator.energy`, `.kineticEnergy`,
  `.potentialEnergy`, `.energy_eq`, and
  `.InitialConditions.trajectory_energy`.
- Likely-name query: "HarmonicOscillator potentialEnergy kineticEnergy spring
  constant mass". The actual structure
  `ClassicalMechanics.HarmonicOscillator` was selected and used.
- Units query: "Dimensionful UnitChoices SI mass length velocity energy".
  `Dimensionful` and `UnitChoices.SI` were selected and used for coherent,
  unit-independent physical quantities and SI readout boundaries.
- Source, module, and docstring data were fetched for the oscillator structure,
  its kinetic/potential/total-energy declarations, `energy_eq`,
  `InitialConditions.trajectory_energy`, `Dimensionful`, and
  `UnitChoices.SI` before choosing the interface.

## Physlib/Mathlib names grounded

- `ClassicalMechanics.HarmonicOscillator` from
  `Physlib.ClassicalMechanics.HarmonicOscillator.Basic`.
- `ClassicalMechanics.HarmonicOscillator.energy` from the same module; its
  source defines total energy as kinetic plus potential energy.
- `Dimensionful`, `UnitChoices.SI`, `WithDim`, `M𝓭`, `L𝓭`, and `T𝓭` from
  Physlib's unit infrastructure.
- `MassUnit.kilograms`, `LengthUnit.meters`, and `TimeUnit.seconds` for the
  coherent SI boundary.
- `Time`, `EuclideanSpace ℝ (Fin 1)`, and the scoped time-derivative notation
  `∂ₜ` used by the oscillator API.

## Local abstractions introduced

- The local process-state and figure vocabularies preserve the two relevant
  instants and all named/visible features of the supplied bitmap. No matching
  reusable library API exists for problem-specific raster labels or Point 1.
- The dimensionful quantity abbreviations specialize Physlib's general
  `Dimensionful (WithDim ... ...)` representation to the exact dimensional
  roles needed here; they are not transparent aliases to `ℝ` or one-field
  scalar wrappers.
- `MatchesProblemAndPrimaryFigure` separates empirical/source evidence from
  `SatisfiesFrictionlessHarmonicMotion`, which holds the governing dynamics.

## Grounding gaps

- Physlib provides the harmonic oscillator and its energy, but no generic API
  for the semantic contents of this problem's raster image, so the figure
  transcription is necessarily local.
- `ClassicalMechanics.HarmonicOscillator.InitialConditions.trajectory_energy`
  was inspected but not used: it applies specifically to Physlib's generated
  closed-form trajectory from an `InitialConditions` object. The problem gives
  two named states without their times, so a general trajectory plus the
  two-state energy-conservation law is the smaller faithful interface.
- No redraft is requested.

## Verification

- `archon-lean-lsp` diagnostics: success, with only the two expected
  declaration-uses-`sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0813.lean`: exit code 0,
  with only those same expected warnings.
