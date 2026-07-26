import Mathlib.Analysis.Real.Sqrt
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0694

open Dimension

/-!
# Launch speed of a cube driven by a compressed spring

A `100 g` cube is released from rest against a spring compressed by `20 cm`.
The spring stiffness is `20 N/m`, and the horizontal surface is frictionless.
The primary image additionally labels the mass as `0.10 kg`, shows the spring
mounted to a wall on the left of the cube, and marks the equilibrium position
as the origin of an `x` axis.

Mass, length, speed, spring stiffness, and energy are represented by
unit-independent Physlib quantities.  Real numbers occur only at explicit
unit-readout boundaries and in the answer-choice data.

Assumption/target split:

* `MatchesFrictionlessSpringLaunchScenario` records the release and launch
  states stated in the prose;
* `MatchesGivenProblemData` and `MatchesPrimarySpringCubeFigure` record the
  numerical and raster-visible data;
* `SatisfiesElasticPotentialEnergyLaw`,
  `SatisfiesTranslationalKineticEnergyLaw`, and
  `SatisfiesMechanicalEnergyConservation` are the governing laws; and
* the exact launch speed, its one-decimal report, and the selection of choice C
  occur only in the conclusion of `springCubeLaunchSpeed`.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/--
A nonnegative, unit-independent spring stiffness.  Since `N/m = kg/s²`, its
dimension is `mass * time⁻²`.
-/
abbrev SpringStiffnessQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical length in centimetres. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Read a physical mass in grams. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.grams mass

/-- Read a speed in coherent SI units, metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read a spring stiffness in coherent SI units, newtons per metre. -/
def springStiffnessInNewtonsPerMeter
    (stiffness : SpringStiffnessQuantity) : ℝ :=
  ((stiffness UnitChoices.SI).val : ℝ)

/-- Read an energy in coherent SI units, joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Launch states and primary-figure vocabulary -/

/-- The two instants used in the energy balance. -/
inductive LaunchInstant where
  | release
  | leavesSpring
  deriving DecidableEq, Fintype, Repr

/-- The qualitative state of the spring at a launch instant. -/
inductive SpringConfiguration where
  | compressed
  | equilibrium
  | extended
  deriving DecidableEq, Repr

/-- How the spring is supported in the pictured apparatus. -/
inductive SpringMount where
  | wallMounted
  | free
  deriving DecidableEq, Repr

/-- Frictional character of the horizontal contact surface. -/
inductive SurfaceInteraction where
  | frictionless
  | frictional
  deriving DecidableEq, Repr

/-- Horizontal directions used by the displacement and launch arrows. -/
inductive HorizontalDirection where
  | leftward
  | rightward
  deriving DecidableEq, Repr

/-- Literal coordinate-axis symbols that a mechanics figure may display. -/
inductive AxisSymbol where
  | x
  | other
  deriving DecidableEq, Repr

/-!
Raster-visible content of image `694.png`.  The two numerical fields are label
readouts, not definitions of the corresponding physical quantities.
-/
structure SpringCubeFigure where
  massLabelKilograms : ℝ
  displacementLabelCentimeters : ℝ
  equilibriumCoordinateMeters : ℝ
  horizontalAxisSymbol : AxisSymbol
  wallShown : Bool
  springShown : Bool
  cubeShown : Bool
  springDrawnLeftOfCube : Bool
  displacementArrowDirection : HorizontalDirection
  displacementArrowEndsAtEquilibrium : Bool
  equilibriumPositionLabelShown : Bool

/-!
Independent physical quantities and state functions for the spring--cube
system.  In particular, the launch speed is an unconstrained physical field;
it is not defined from an answer choice.
-/
structure SpringCubeLaunchSetup where
  cubeMass : MassQuantity
  pullbackDistance : LengthQuantity
  springStiffness : SpringStiffnessQuantity
  springCompressionAt : LaunchInstant → LengthQuantity
  cubeSpeedAt : LaunchInstant → DimSpeed
  springPotentialEnergyAt : LaunchInstant → DimEnergy
  cubeKineticEnergyAt : LaunchInstant → DimEnergy
  springConfigurationAt : LaunchInstant → SpringConfiguration
  springMount : SpringMount
  surfaceInteraction : SurfaceInteraction
  launchDirection : HorizontalDirection
  figure : SpringCubeFigure

/-! ## Scenario, source data, and figure evidence -/

/--
The release-from-rest and equilibrium-departure conditions described by the
problem.  No field fixes the value of the departure speed.
-/
structure MatchesFrictionlessSpringLaunchScenario
    (setup : SpringCubeLaunchSetup) : Prop where
  springIsWallMounted : setup.springMount = .wallMounted
  surfaceIsFrictionless : setup.surfaceInteraction = .frictionless
  springInitiallyCompressed :
    setup.springConfigurationAt .release = .compressed
  springAtEquilibriumOnDeparture :
    setup.springConfigurationAt .leavesSpring = .equilibrium
  releaseCompressionIsPullback :
    setup.springCompressionAt .release = setup.pullbackDistance
  zeroCompressionOnDeparture :
    lengthInMeters (setup.springCompressionAt .leavesSpring) = 0
  releasedFromRest :
    speedInMetersPerSecond (setup.cubeSpeedAt .release) = 0
  cubeLaunchesRightward : setup.launchDirection = .rightward

/-- Numerical data stated in the prose of the problem. -/
structure MatchesGivenProblemData (setup : SpringCubeLaunchSetup) : Prop where
  cubeMassIsOneHundredGrams : massInGrams setup.cubeMass = 100
  pullbackIsTwentyCentimeters :
    lengthInCentimeters setup.pullbackDistance = 20
  springStiffnessIsTwentyNewtonsPerMeter :
    springStiffnessInNewtonsPerMeter setup.springStiffness = 20

/--
Literal evidence transcribed from the primary bitmap, including the displayed
`0.10 kg`, `Δr = 20 cm`, rightward arrow, and equilibrium marker at `x = 0`.
-/
structure MatchesPrimarySpringCubeFigure
    (setup : SpringCubeLaunchSetup) : Prop where
  massLabelIsPointOneKilograms : setup.figure.massLabelKilograms = 0.10
  massLabelDescribesCube :
    massInKilograms setup.cubeMass = setup.figure.massLabelKilograms
  displacementLabelIsTwentyCentimeters :
    setup.figure.displacementLabelCentimeters = 20
  displacementLabelDescribesPullback :
    lengthInCentimeters setup.pullbackDistance =
      setup.figure.displacementLabelCentimeters
  equilibriumMarkedAtZero : setup.figure.equilibriumCoordinateMeters = 0
  axisIsX : setup.figure.horizontalAxisSymbol = .x
  wallIsShown : setup.figure.wallShown = true
  springIsShown : setup.figure.springShown = true
  cubeIsShown : setup.figure.cubeShown = true
  springIsLeftOfCube : setup.figure.springDrawnLeftOfCube = true
  arrowPointsRight : setup.figure.displacementArrowDirection = .rightward
  arrowEndsAtEquilibrium :
    setup.figure.displacementArrowEndsAtEquilibrium = true
  equilibriumLabelIsShown :
    setup.figure.equilibriumPositionLabelShown = true

/-- Positivity conditions selecting a nondegenerate physical launch. -/
structure HasPhysicalSpringCubeParameters
    (setup : SpringCubeLaunchSetup) : Prop where
  positiveCubeMass : 0 < massInKilograms setup.cubeMass
  positivePullbackDistance : 0 < lengthInMeters setup.pullbackDistance
  positiveSpringStiffness :
    0 < springStiffnessInNewtonsPerMeter setup.springStiffness

/-! ## Governing energy laws -/

/-- Hooke-spring potential energy `U = (1/2) k x²` at both launch instants. -/
structure SatisfiesElasticPotentialEnergyLaw
    (setup : SpringCubeLaunchSetup) : Prop where
  energyFormula : ∀ instant,
    energyInJoules (setup.springPotentialEnergyAt instant) =
      (1 / 2 : ℝ) *
        springStiffnessInNewtonsPerMeter setup.springStiffness *
          (lengthInMeters (setup.springCompressionAt instant)) ^ 2

/-- Translational kinetic energy `K = (1/2) m v²` at both launch instants. -/
structure SatisfiesTranslationalKineticEnergyLaw
    (setup : SpringCubeLaunchSetup) : Prop where
  energyFormula : ∀ instant,
    energyInJoules (setup.cubeKineticEnergyAt instant) =
      (1 / 2 : ℝ) * massInKilograms setup.cubeMass *
        (speedInMetersPerSecond (setup.cubeSpeedAt instant)) ^ 2

/-- Total mechanical energy of the spring--cube system at one instant. -/
def totalMechanicalEnergyInJoules
    (setup : SpringCubeLaunchSetup) (instant : LaunchInstant) : ℝ :=
  energyInJoules (setup.springPotentialEnergyAt instant) +
    energyInJoules (setup.cubeKineticEnergyAt instant)

/-- With no dissipative work, total mechanical energy is conserved. -/
def SatisfiesMechanicalEnergyConservation
    (setup : SpringCubeLaunchSetup) : Prop :=
  totalMechanicalEnergyInJoules setup .release =
    totalMechanicalEnergyInJoules setup .leavesSpring

/-! ## Answer choices and target -/

/-- The four answer labels printed by the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The speed in metres per second printed next to an answer label. -/
def answerChoiceSpeedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 2.5
  | .B => 3.1
  | .C => 2.8
  | .D => 3.4

/-- Agreement with a speed displayed to the nearest tenth of a metre per second. -/
def AgreesWithOneDecimalSpeedReadout
    (speed : DimSpeed) (displayedMetersPerSecond : ℝ) : Prop :=
  |speedInMetersPerSecond speed - displayedMetersPerSecond| < (1 / 20 : ℝ)

/-- An answer choice reports the launch speed to the displayed precision. -/
def AnswerChoiceReportsLaunchSpeed
    (setup : SpringCubeLaunchSetup) (choice : AnswerChoice) : Prop :=
  AgreesWithOneDecimalSpeedReadout
    (setup.cubeSpeedAt .leavesSpring)
    (answerChoiceSpeedInMetersPerSecond choice)

/--
The energy laws give the exact departure speed `√8 m/s`, which is reported as
`2.8 m/s` to one decimal place; among the four displayed options, precisely
choice C reports that speed.
-/
theorem springCubeLaunchSpeed
    (setup : SpringCubeLaunchSetup)
    (hScenario : MatchesFrictionlessSpringLaunchScenario setup)
    (hData : MatchesGivenProblemData setup)
    (hFigure : MatchesPrimarySpringCubeFigure setup)
    (hPhysical : HasPhysicalSpringCubeParameters setup)
    (hElastic : SatisfiesElasticPotentialEnergyLaw setup)
    (hKinetic : SatisfiesTranslationalKineticEnergyLaw setup)
    (hConservation : SatisfiesMechanicalEnergyConservation setup) :
    speedInMetersPerSecond (setup.cubeSpeedAt .leavesSpring) = Real.sqrt 8 ∧
      AgreesWithOneDecimalSpeedReadout
        (setup.cubeSpeedAt .leavesSpring) 2.8 ∧
      ∀ choice,
        AnswerChoiceReportsLaunchSpeed setup choice ↔ choice = .C := by
  let ucm : UnitChoices :=
    {UnitChoices.SI with length := LengthUnit.centimeters}
  let um : UnitChoices :=
    {UnitChoices.SI with length := LengthUnit.meters}
  have hLengthScale :
      ucm.dimScale um L𝓭 = (⟨1 / 100, by norm_num⟩ : NNReal) := by
    norm_num [ucm, um, UnitChoices.dimScale, LengthUnit.centimeters,
      LengthUnit.meters]
  have hLengthUnits :=
    congrArg (fun q : WithDim L𝓭 NNReal => (q.val : ℝ))
      (setup.pullbackDistance.2 ucm um)
  rw [show dim (WithDim L𝓭 NNReal) = L𝓭 by rfl, hLengthScale] at hLengthUnits
  dsimp [um, ucm] at hLengthUnits
  norm_num at hLengthUnits
  change lengthInMeters setup.pullbackDistance =
    (1 / 100 : ℝ) * lengthInCentimeters setup.pullbackDistance at hLengthUnits
  rw [hData.pullbackIsTwentyCentimeters] at hLengthUnits
  norm_num at hLengthUnits
  have hMass : massInKilograms setup.cubeMass = (1 / 10 : ℝ) := by
    calc
      massInKilograms setup.cubeMass =
          setup.figure.massLabelKilograms := hFigure.massLabelDescribesCube
      _ = 0.10 := hFigure.massLabelIsPointOneKilograms
      _ = 1 / 10 := by norm_num
  have hElasticRelease := hElastic.energyFormula .release
  have hElasticDeparture := hElastic.energyFormula .leavesSpring
  have hKineticRelease := hKinetic.energyFormula .release
  have hKineticDeparture := hKinetic.energyFormula .leavesSpring
  rw [hScenario.releaseCompressionIsPullback,
    hData.springStiffnessIsTwentyNewtonsPerMeter, hLengthUnits] at hElasticRelease
  rw [hData.springStiffnessIsTwentyNewtonsPerMeter,
    hScenario.zeroCompressionOnDeparture] at hElasticDeparture
  rw [hMass, hScenario.releasedFromRest] at hKineticRelease
  rw [hMass] at hKineticDeparture
  norm_num at hElasticRelease hElasticDeparture hKineticRelease
  unfold SatisfiesMechanicalEnergyConservation
    totalMechanicalEnergyInJoules at hConservation
  have hSpeedSquared :
      (speedInMetersPerSecond (setup.cubeSpeedAt .leavesSpring)) ^ 2 = 8 := by
    nlinarith
  have hSpeedNonnegative :
      0 ≤ speedInMetersPerSecond (setup.cubeSpeedAt .leavesSpring) := by
    unfold speedInMetersPerSecond
    positivity
  have hSqrtSquared : (Real.sqrt (8 : ℝ)) ^ 2 = 8 := by
    norm_num
  have hExact :
      speedInMetersPerSecond (setup.cubeSpeedAt .leavesSpring) =
        Real.sqrt 8 := by
    nlinarith [Real.sqrt_nonneg (8 : ℝ)]
  have hSqrtLower : (14 / 5 : ℝ) < Real.sqrt 8 := by
    nlinarith [Real.sqrt_nonneg (8 : ℝ)]
  have hSqrtUpper : Real.sqrt 8 < (57 / 20 : ℝ) := by
    nlinarith [Real.sqrt_nonneg (8 : ℝ)]
  have hAgreement :
      AgreesWithOneDecimalSpeedReadout
        (setup.cubeSpeedAt .leavesSpring) 2.8 := by
    unfold AgreesWithOneDecimalSpeedReadout
    rw [hExact, abs_of_nonneg (by norm_num at hSqrtLower ⊢; linarith)]
    norm_num at hSqrtUpper ⊢
    linarith
  refine ⟨hExact, hAgreement, ?_⟩
  intro choice
  cases choice with
  | A =>
      constructor
      · intro h
        exfalso
        unfold AnswerChoiceReportsLaunchSpeed
          AgreesWithOneDecimalSpeedReadout at h
        simp only [answerChoiceSpeedInMetersPerSecond] at h
        rw [hExact, abs_of_nonneg (by norm_num at hSqrtLower ⊢; linarith)] at h
        norm_num at h
        linarith
      · intro h
        cases h
  | B =>
      constructor
      · intro h
        exfalso
        unfold AnswerChoiceReportsLaunchSpeed
          AgreesWithOneDecimalSpeedReadout at h
        simp only [answerChoiceSpeedInMetersPerSecond] at h
        rw [hExact, abs_of_nonpos (by norm_num at hSqrtUpper ⊢; linarith)] at h
        norm_num at h
        linarith
      · intro h
        cases h
  | C =>
      constructor
      · intro _
        rfl
      · intro _
        exact hAgreement
  | D =>
      constructor
      · intro h
        exfalso
        unfold AnswerChoiceReportsLaunchSpeed
          AgreesWithOneDecimalSpeedReadout at h
        simp only [answerChoiceSpeedInMetersPerSecond] at h
        rw [hExact, abs_of_nonpos (by norm_num at hSqrtUpper ⊢; linarith)] at h
        norm_num at h
        linarith
      · intro h
        cases h

end PhyXMiniProblems.ProblemPhyXMini0694
