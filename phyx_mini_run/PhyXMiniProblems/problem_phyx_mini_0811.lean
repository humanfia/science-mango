import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0811

open Dimension

/-!
# Speed at the bottom of a frictionless quarter-circle skateboard ramp

Throckmorton and his skateboard are treated as one particle of total mass
`25.0 kg`.  Starting from rest at Point 1, they follow the dashed trajectory
along a frictionless quarter-circle of radius `R = 3.00 m` to Point 2.  The
figure chooses the bottom datum `y = 0`, labels `y₁ = R`, `v₁ = 0`, and
`y₂ = 0`, and draws the unknown bottom velocity `v₂` horizontally rightward.

Mass, length, speed, acceleration, work, and energy are represented by
unit-independent Physlib quantities.  Real numbers occur only as coherent-SI
readouts and as exact representations of displayed numerical values.

Assumption/target split:

* governing laws: translational kinetic energy, gravitational potential
  energy relative to the displayed datum, zero work by the frictionless ramp
  contact, and the endpoint mechanical-energy balance;
* previous-part results: none;
* figure/data readouts: the Point 1 and Point 2 labels, center `O`, dashed
  quarter-circle path, rightward tangent velocity arrow, `R = 3.00 m`,
  `y₁ = R`, `y₂ = 0`, `v₁ = 0`, total mass `25.0 kg`, and calibrated
  terrestrial gravity `g = 9.8 m/s²`;
* current target conclusions: `v₂² = 58.8`,
  `v₂ = sqrt(58.8) m/s`, agreement with `7.67 m/s` to the displayed
  hundredth, and unique selection of answer choice B.

No target value for `v₂` is a setup field or a premise below.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- Linear acceleration has physical dimension `L T⁻²`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length or height. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative gravitational-acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A signed work or energy quantity. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a physical mass in coherent-SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a speed magnitude in coherent-SI metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read an acceleration magnitude in coherent-SI metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read work or energy in coherent-SI joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Endpoint, geometry, and primary-image vocabulary -/

/-- The two labeled endpoints used in the energy comparison. -/
inductive RampPoint where
  | point1
  | point2
  deriving DecidableEq, Fintype, Repr

/-- The body idealization stated in the problem. -/
inductive BodyModel where
  | pointParticle
  | extendedRigidBody
  deriving DecidableEq, Repr

/-- The geometric class of the pictured ramp segment. -/
inductive RampGeometry where
  | quarterCircle
  | otherCurve
  deriving DecidableEq, Repr

/-- Tangential interaction between the skateboard and the ramp. -/
inductive SurfaceInteraction where
  | frictionless
  | frictional
  deriving DecidableEq, Repr

/-- Horizontal directions used by the bottom velocity arrow. -/
inductive HorizontalDirection where
  | rightward
  | leftward
  deriving DecidableEq, Repr

/-- Physical or graphical objects visibly present in image `811.png`. -/
inductive FigureObject where
  | ramp
  | skateboarderAtPoint1
  | skateboarderAlongPath
  | skateboarderAtPoint2
  | centerOfCurvatureO
  | dashedTrajectory
  | bottomVelocityArrow
  | bottomHeightDatum
  deriving DecidableEq, Fintype, Repr

/-- Literal semantic labels printed in the primary image. -/
inductive FigureLabel where
  | point1
  | point2
  | centerO
  | y1EqualsR
  | v1EqualsZero
  | y2EqualsZero
  | v2
  | radiusThreeMeters
  | bottomDatumYEqualsZero
  deriving DecidableEq, Fintype, Repr

/-!
Literal evidence transcribed from the supplied bitmap.  Its real fields are
printed labels, not definitions of the physical trajectory or unknown speed.
-/
structure SkateboardRampFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  dashedTrajectoryStartsAt : RampPoint
  dashedTrajectoryEndsAt : RampPoint
  radiusIndicatorStartsAtCenterO : Bool
  radiusIndicatorEndsOnRamp : Bool
  point1IsAbovePoint2 : Bool
  bottomVelocityArrowAt : RampPoint
  bottomVelocityArrowDirection : HorizontalDirection
  bottomVelocityArrowIsTangentToRamp : Bool
  point1HeightLabelUsesRadiusR : Bool
  point2HeightLabelMeters : ℝ
  point1SpeedLabelMetersPerSecond : ℝ
  radiusLabelMeters : ℝ
  bottomDatumLabelMeters : ℝ

/-! ## Independent physical setup -/

/-!
The bottom speed is an independent observable field.  In particular, it is
not defined from an answer choice or from the desired energy formula.
-/
structure SkateboardRampSetup where
  figure : SkateboardRampFigure
  bodyModel : BodyModel
  rampGeometry : RampGeometry
  surfaceInteraction : SurfaceInteraction
  motionStartsAt : RampPoint
  motionEndsAt : RampPoint
  totalMass : MassQuantity
  rampRadius : LengthQuantity
  heightAboveBottomDatum : RampPoint → LengthQuantity
  speed : RampPoint → SpeedQuantity
  gravitationalAccelerationMagnitude : AccelerationQuantity
  translationalKineticEnergy : RampPoint → EnergyQuantity
  gravitationalPotentialEnergy : RampPoint → EnergyQuantity
  rampContactWorkFromPoint1ToPoint2 : EnergyQuantity

/-! ## Scenario, numerical data, and primary-image evidence -/

/-- The prose model: a particle descends a frictionless quarter-circle. -/
structure MatchesSkateboardRampScenario
    (setup : SkateboardRampSetup) : Prop where
  particleApproximation : setup.bodyModel = .pointParticle
  pathIsQuarterCircle : setup.rampGeometry = .quarterCircle
  rampIsFrictionless : setup.surfaceInteraction = .frictionless
  startsAtPoint1 : setup.motionStartsAt = .point1
  endsAtPoint2 : setup.motionEndsAt = .point2
  releasedFromRest :
    speedInMetersPerSecond (setup.speed .point1) = 0

/-!
Numerical problem data and the standard near-Earth gravitational calibration.
The gravity value is a model input, not a conclusion about the bottom speed.
-/
structure MatchesGivenProblemData
    (setup : SkateboardRampSetup) : Prop where
  totalMassIsTwentyFiveKilograms :
    massInKilograms setup.totalMass = 25
  rampRadiusIsThreeMeters :
    lengthInMeters setup.rampRadius = 3
  terrestrialGravityIsNinePointEight :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude = 49 / 5

/-!
Facts read from the primary image: the dashed path joins Point 1 to Point 2,
the radius is drawn from `O`, and the unknown `v₂` arrow is tangent and points
right.  The endpoint labels are connected to the independent physical fields,
but no numerical value is assigned to the Point 2 speed.
-/
structure MatchesPrimarySkateboardRampFigure
    (setup : SkateboardRampSetup) : Prop where
  everyObjectIsShown :
    ∀ object, setup.figure.showsObject object = true
  everyLabelIsShown :
    ∀ label, setup.figure.showsLabel label = true
  pathStartsAtPoint1 :
    setup.figure.dashedTrajectoryStartsAt = .point1
  pathEndsAtPoint2 :
    setup.figure.dashedTrajectoryEndsAt = .point2
  radiusStartsAtO :
    setup.figure.radiusIndicatorStartsAtCenterO = true
  radiusEndsOnRamp :
    setup.figure.radiusIndicatorEndsOnRamp = true
  point1AbovePoint2 : setup.figure.point1IsAbovePoint2 = true
  velocityArrowAtBottom : setup.figure.bottomVelocityArrowAt = .point2
  velocityArrowPointsRight :
    setup.figure.bottomVelocityArrowDirection = .rightward
  velocityArrowTangentToRamp :
    setup.figure.bottomVelocityArrowIsTangentToRamp = true
  figureSaysY1EqualsR :
    setup.figure.point1HeightLabelUsesRadiusR = true
  radiusLabelIsThreeMeters : setup.figure.radiusLabelMeters = 3
  point2HeightLabelIsZero : setup.figure.point2HeightLabelMeters = 0
  point1SpeedLabelIsZero :
    setup.figure.point1SpeedLabelMetersPerSecond = 0
  bottomDatumLabelIsZero : setup.figure.bottomDatumLabelMeters = 0
  physicalRadiusMatchesLabel :
    lengthInMeters setup.rampRadius = setup.figure.radiusLabelMeters
  point1HeightMatchesRadius :
    lengthInMeters (setup.heightAboveBottomDatum .point1) =
      lengthInMeters setup.rampRadius
  point2HeightMatchesLabel :
    lengthInMeters (setup.heightAboveBottomDatum .point2) =
      setup.figure.point2HeightLabelMeters
  point1SpeedMatchesLabel :
    speedInMetersPerSecond (setup.speed .point1) =
      setup.figure.point1SpeedLabelMetersPerSecond

/-- Positivity and nondegeneracy conditions selecting the physical branch. -/
structure HasPhysicalSkateboardRampParameters
    (setup : SkateboardRampSetup) : Prop where
  positiveMass : 0 < massInKilograms setup.totalMass
  positiveRadius : 0 < lengthInMeters setup.rampRadius
  positiveGravity :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude
  kineticEnergyNonnegative :
    ∀ point, 0 ≤ energyInJoules (setup.translationalKineticEnergy point)
  potentialEnergyNonnegative :
    ∀ point, 0 ≤ energyInJoules (setup.gravitationalPotentialEnergy point)

/-! ## Governing work and energy laws -/

/-- Total translational mechanical energy at a labeled endpoint. -/
def totalMechanicalEnergyInJoules
    (setup : SkateboardRampSetup) (point : RampPoint) : ℝ :=
  energyInJoules (setup.translationalKineticEnergy point) +
    energyInJoules (setup.gravitationalPotentialEnergy point)

/-!
The point-particle kinetic and gravitational potential energy formulae,
together with endpoint work-energy balance.  The contact-work term is retained
explicitly so that its vanishing is tied to the frictionless ramp rather than
hidden in the desired speed equation.
-/
structure SatisfiesSkateboardRampEnergyLaws
    (setup : SkateboardRampSetup) : Prop where
  translationalKineticEnergyLaw :
    ∀ point,
      energyInJoules (setup.translationalKineticEnergy point) =
        (1 / 2 : ℝ) * massInKilograms setup.totalMass *
          speedInMetersPerSecond (setup.speed point) ^ 2
  gravitationalPotentialEnergyLaw :
    ∀ point,
      energyInJoules (setup.gravitationalPotentialEnergy point) =
        massInKilograms setup.totalMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAccelerationMagnitude *
          lengthInMeters (setup.heightAboveBottomDatum point)
  frictionlessRampContactDoesNoWork :
    energyInJoules setup.rampContactWorkFromPoint1ToPoint2 = 0
  endpointMechanicalEnergyBalance :
    totalMechanicalEnergyInJoules setup .point2 =
      totalMechanicalEnergyInJoules setup .point1 +
        energyInJoules setup.rampContactWorkFromPoint1ToPoint2

/-! ## Derived relation and displayed answer -/

/-- The four speed choices displayed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metres-per-second value printed beside each answer label. -/
def displayedSpeedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 271 / 50
  | .B => 767 / 100
  | .C => 249 / 50
  | .D => 451 / 50

/-- The answer label stored in the source dataset; metadata, not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- Agreement with a speed displayed to the nearest hundredth of a metre per second. -/
def AgreesWithHundredthSpeedReadout
    (speed : SpeedQuantity) (displayedMetersPerSecond : ℝ) : Prop :=
  |speedInMetersPerSecond speed - displayedMetersPerSecond| < (1 / 200 : ℝ)

/-- A displayed choice reports the independently modeled bottom speed. -/
def AnswerChoiceReportsBottomSpeed
    (setup : SkateboardRampSetup) (choice : AnswerChoice) : Prop :=
  AgreesWithHundredthSpeedReadout
    (setup.speed .point2) (displayedSpeedInMetersPerSecond choice)

/-!
Energy conservation across the vertical drop `R` gives the exact squared
bottom speed `2 g R = 294/5 (m/s)²`.  This is a derived conclusion, not a law
field or figure readout.
-/
lemma bottomSpeedSquared
    (setup : SkateboardRampSetup)
    (_scenario : MatchesSkateboardRampScenario setup)
    (_data : MatchesGivenProblemData setup)
    (_figure : MatchesPrimarySkateboardRampFigure setup)
    (_physical : HasPhysicalSkateboardRampParameters setup)
    (_energyLaws : SatisfiesSkateboardRampEnergyLaws setup) :
    speedInMetersPerSecond (setup.speed .point2) ^ 2 = 294 / 5 := by
  have hheight1 :
      lengthInMeters (setup.heightAboveBottomDatum .point1) = 3 :=
    _figure.point1HeightMatchesRadius.trans _data.rampRadiusIsThreeMeters
  have hheight2 :
      lengthInMeters (setup.heightAboveBottomDatum .point2) = 0 := by
    rw [_figure.point2HeightMatchesLabel, _figure.point2HeightLabelIsZero]
  have hbalance := _energyLaws.endpointMechanicalEnergyBalance
  simp only [totalMechanicalEnergyInJoules,
    _energyLaws.translationalKineticEnergyLaw,
    _energyLaws.gravitationalPotentialEnergyLaw,
    _energyLaws.frictionlessRampContactDoesNoWork,
    _data.totalMassIsTwentyFiveKilograms,
    _data.terrestrialGravityIsNinePointEight,
    _scenario.releasedFromRest, hheight1, hheight2] at hbalance
  norm_num at hbalance ⊢
  linarith

/-!
The nonnegative bottom speed is `sqrt(58.8) m/s`, which rounds to `7.67 m/s`;
among the displayed choices, precisely choice B reports that value.

This theorem formalizes blueprint label
`thm:physics:phyx_mini_0811:target`.
-/
theorem skateboarderBottomSpeed
    (setup : SkateboardRampSetup)
    (_scenario : MatchesSkateboardRampScenario setup)
    (_data : MatchesGivenProblemData setup)
    (_figure : MatchesPrimarySkateboardRampFigure setup)
    (_physical : HasPhysicalSkateboardRampParameters setup)
    (_energyLaws : SatisfiesSkateboardRampEnergyLaws setup) :
    speedInMetersPerSecond (setup.speed .point2) = Real.sqrt (294 / 5) ∧
      AgreesWithHundredthSpeedReadout (setup.speed .point2) (767 / 100) ∧
      ∀ choice,
        AnswerChoiceReportsBottomSpeed setup choice ↔ choice = .B := by
  have hsq :=
    bottomSpeedSquared setup _scenario _data _figure _physical _energyLaws
  have hnonneg :
      0 ≤ speedInMetersPerSecond (setup.speed .point2) := by
    unfold speedInMetersPerSecond
    positivity
  have hrad : (0 : ℝ) ≤ 294 / 5 := by
    norm_num
  have hsqrt_nonneg : 0 ≤ Real.sqrt (294 / 5) :=
    Real.sqrt_nonneg _
  have hsqrt_sq :
      Real.sqrt (294 / 5) ^ 2 = (294 / 5 : ℝ) := by
    simpa using Real.sq_sqrt hrad
  have hspeed :
      speedInMetersPerSecond (setup.speed .point2) =
        Real.sqrt (294 / 5) := by
    nlinarith
  have hsqrt_lower :
      (1533 / 200 : ℝ) < Real.sqrt (294 / 5) := by
    nlinarith
  have hsqrt_upper :
      Real.sqrt (294 / 5) < (1535 / 200 : ℝ) := by
    nlinarith
  have hagree :
      AgreesWithHundredthSpeedReadout (setup.speed .point2) (767 / 100) := by
    rw [AgreesWithHundredthSpeedReadout, hspeed, abs_lt]
    constructor <;> nlinarith
  refine ⟨hspeed, hagree, ?_⟩
  intro choice
  constructor
  · intro h
    fin_cases choice
    · exfalso
      rw [AnswerChoiceReportsBottomSpeed, AgreesWithHundredthSpeedReadout,
        displayedSpeedInMetersPerSecond, hspeed, abs_lt] at h
      linarith
    · rfl
    · exfalso
      rw [AnswerChoiceReportsBottomSpeed, AgreesWithHundredthSpeedReadout,
        displayedSpeedInMetersPerSecond, hspeed, abs_lt] at h
      linarith
    · exfalso
      rw [AnswerChoiceReportsBottomSpeed, AgreesWithHundredthSpeedReadout,
        displayedSpeedInMetersPerSecond, hspeed, abs_lt] at h
      linarith
  · intro h
    subst choice
    exact hagree

end PhyXMiniProblems.ProblemPhyXMini0811
