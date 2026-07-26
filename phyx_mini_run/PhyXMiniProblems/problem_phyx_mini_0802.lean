import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0802

open Dimension

/-!
# Cable tension while a descending elevator stops

An elevator-and-load assembly has mass `800 kg`, initially moves downward at
`10.0 m/s`, and stops after travelling `25.0 m` with constant acceleration.
The primary figure chooses upward as the positive `Y` direction and labels the
upward cable force `T`, the downward weight `w = mg`, and the upward
acceleration component `a_y`.

Physical quantities below are unit-independent Physlib `Dimensionful`
quantities.  Real numbers occur only as coherent-unit readouts, figure data,
or displayed answer values.

Assumption/target split:

* governing laws: constant-acceleration stopping kinematics, `w = mg`, and
  Newton's second law along the upward-positive vertical axis;
* previous-part results: none;
* figure/data readouts: mass `800 kg`, initial speed `10 m/s`, stopping distance
  `25 m`, final velocity zero, standard gravity `9.8 m/s^2`, and the directions
  of the `Y`, `T`, `w`, motion, and `a_y` arrows;
* current target conclusions: `a_y = 2 m/s^2`, `w = 7840 N`, and especially
  cable tension `T = 9440 N`, which is displayed answer B.
-/

/-! ## Dimensionful mechanical quantities and coherent readouts -/

/-- The physical dimension of velocity, `L T^-1`. -/
def velocityDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- The physical dimension of acceleration, `L T^-2`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of force, `M L T^-2`. -/
def forceDimension : Dimension := M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length, used for the distance travelled. -/
abbrev LengthMagnitudeQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed component of displacement along the pictured `Y` axis. -/
abbrev VerticalDisplacementQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical speed. -/
abbrev SpeedMagnitudeQuantity : Type :=
  Dimensionful (WithDim velocityDimension NNReal)

/-- A signed component of velocity along the pictured `Y` axis. -/
abbrev VerticalVelocityQuantity : Type :=
  Dimensionful (WithDim velocityDimension ℝ)

/-- A signed component of acceleration along the pictured `Y` axis. -/
abbrev VerticalAccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension ℝ)

/-- A nonnegative magnitude of gravitational acceleration. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative force magnitude, used for both tension and weight. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- Read a nonnegative dimensionful quantity in coherent units. -/
def nonnegativeReadout {d : Dimension}
    (units : UnitChoices) (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Read a signed dimensionful quantity in coherent units. -/
def signedReadout {d : Dimension}
    (units : UnitChoices) (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity units).val

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI mass

/-- Metre readout of a nonnegative distance. -/
def distanceInMeters (distance : LengthMagnitudeQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI distance

/-- Metre readout of a signed vertical displacement. -/
def displacementYInMeters (displacement : VerticalDisplacementQuantity) : ℝ :=
  signedReadout UnitChoices.SI displacement

/-- Metres-per-second readout of a speed magnitude. -/
def speedInMetersPerSecond (speed : SpeedMagnitudeQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI speed

/-- Metres-per-second readout of a signed vertical velocity component. -/
def velocityYInMetersPerSecond (velocity : VerticalVelocityQuantity) : ℝ :=
  signedReadout UnitChoices.SI velocity

/-- Metres-per-second-squared readout of signed vertical acceleration. -/
def accelerationYInMetersPerSecondSquared
    (acceleration : VerticalAccelerationQuantity) : ℝ :=
  signedReadout UnitChoices.SI acceleration

/-- Metres-per-second-squared readout of an acceleration magnitude. -/
def accelerationMagnitudeInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI acceleration

/-- Newton readout of a force magnitude. -/
def forceInNewtons (force : ForceMagnitudeQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI force

/-! ## Independent setup and primary-figure labels -/

/-- Qualitative vertical directions used by the primary figure. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Whether the magnitude of the elevator's velocity is increasing or decreasing. -/
inductive SpeedTrend where
  | increasing
  | decreasing
  deriving DecidableEq, Repr

/-- The object whose combined mass is specified in the problem. -/
inductive MechanicalSystemKind where
  | elevatorAndLoad
  deriving DecidableEq, Repr

/-- The acceleration regime stated in the problem. -/
inductive AccelerationRegime where
  | constant
  deriving DecidableEq, Repr

/-!
Literal categorical information retained from the primary raster.  The
question's unknown tension magnitude does not occur as a numerical figure
field.
-/
structure ElevatorFigure where
  showsElevatorShaft : Bool
  showsElevatorDoors : Bool
  showsControlPanel : Bool
  showsSupportingCable : Bool
  showsHorizontalAxisX : Bool
  showsVerticalAxisY : Bool
  positiveYAxisDirection : VerticalDirection
  motionArrowDirection : VerticalDirection
  motionSpeedTrend : SpeedTrend
  showsTensionLabelT : Bool
  tensionArrowDirection : VerticalDirection
  showsWeightLabelWEqualsMg : Bool
  weightArrowDirection : VerticalDirection
  showsAccelerationLabelAy : Bool
  accelerationArrowDirection : VerticalDirection

/-!
Independent physical quantities for the stopping interval.  In particular,
`cableTension` is not defined from an answer choice or from `9440`.
-/
structure ElevatorBrakingSetup where
  systemKind : MechanicalSystemKind
  accelerationRegime : AccelerationRegime
  mass : MassQuantity
  initialSpeed : SpeedMagnitudeQuantity
  initialVelocityY : VerticalVelocityQuantity
  finalVelocityY : VerticalVelocityQuantity
  stoppingDistance : LengthMagnitudeQuantity
  verticalDisplacementY : VerticalDisplacementQuantity
  verticalAccelerationY : VerticalAccelerationQuantity
  gravityMagnitude : AccelerationMagnitudeQuantity
  cableTension : ForceMagnitudeQuantity
  weightMagnitude : ForceMagnitudeQuantity
  figure : ElevatorFigure

/-! ## Problem data, figure evidence, and governing laws -/

/-!
The prose data expressed as SI readouts.  Upward is positive, so the initial
velocity and stopping displacement are the negatives of their stated
magnitudes.  The standard near-Earth value `g = 9.8 m/s^2` is the convention
used by the recorded answer choices.
-/
structure MatchesProblemDescription (setup : ElevatorBrakingSetup) : Prop where
  systemIsElevatorAndLoad : setup.systemKind = .elevatorAndLoad
  accelerationIsConstant : setup.accelerationRegime = .constant
  combinedMassKilograms : massInKilograms setup.mass = 800
  initialSpeedMetersPerSecond :
    speedInMetersPerSecond setup.initialSpeed = 10
  initialVelocityPointsDown :
    velocityYInMetersPerSecond setup.initialVelocityY =
      -speedInMetersPerSecond setup.initialSpeed
  broughtToRest : velocityYInMetersPerSecond setup.finalVelocityY = 0
  stoppingDistanceMeters : distanceInMeters setup.stoppingDistance = 25
  displacementPointsDown :
    displacementYInMeters setup.verticalDisplacementY =
      -distanceInMeters setup.stoppingDistance
  standardGravityMetersPerSecondSquared :
    accelerationMagnitudeInMetersPerSecondSquared setup.gravityMagnitude =
      49 / 5

/-!
Primary-image evidence.  The label `w = mg` is recorded here only as a
graphical fact; the corresponding physical law is stated independently in
`SatisfiesVerticalDynamics`.
-/
structure MatchesPrimaryFigure (setup : ElevatorBrakingSetup) : Prop where
  elevatorShaftShown : setup.figure.showsElevatorShaft = true
  elevatorDoorsShown : setup.figure.showsElevatorDoors = true
  controlPanelShown : setup.figure.showsControlPanel = true
  supportingCableShown : setup.figure.showsSupportingCable = true
  horizontalAxisXShown : setup.figure.showsHorizontalAxisX = true
  verticalAxisYShown : setup.figure.showsVerticalAxisY = true
  yAxisPointsUpward : setup.figure.positiveYAxisDirection = .upward
  motionArrowPointsDown : setup.figure.motionArrowDirection = .downward
  motionSpeedIsDecreasing : setup.figure.motionSpeedTrend = .decreasing
  tensionLabelShown : setup.figure.showsTensionLabelT = true
  tensionArrowPointsUp : setup.figure.tensionArrowDirection = .upward
  weightRelationShown : setup.figure.showsWeightLabelWEqualsMg = true
  weightArrowPointsDown : setup.figure.weightArrowDirection = .downward
  accelerationLabelShown : setup.figure.showsAccelerationLabelAy = true
  accelerationArrowPointsUp : setup.figure.accelerationArrowDirection = .upward

/-!
The constant-acceleration relation `v_f^2 = v_i^2 + 2 a_y Δy`, stated in
every coherent unit system.  It contains no numerical value for the unknown
acceleration or tension.
-/
structure SatisfiesConstantAccelerationKinematics
    (setup : ElevatorBrakingSetup) : Prop where
  stoppingRelation :
    ∀ units,
      signedReadout units setup.finalVelocityY ^ 2 =
        signedReadout units setup.initialVelocityY ^ 2 +
          2 * signedReadout units setup.verticalAccelerationY *
            signedReadout units setup.verticalDisplacementY

/-!
The downward weight has magnitude `mg`, while the upward-positive force
balance is `T - w = m a_y`.  These general dynamics laws contain neither the
requested tension nor any answer-choice value.
-/
structure SatisfiesVerticalDynamics (setup : ElevatorBrakingSetup) : Prop where
  weightMagnitudeLaw :
    ∀ units,
      nonnegativeReadout units setup.weightMagnitude =
        nonnegativeReadout units setup.mass *
          nonnegativeReadout units setup.gravityMagnitude
  newtonsSecondLawAlongY :
    ∀ units,
      nonnegativeReadout units setup.cableTension -
          nonnegativeReadout units setup.weightMagnitude =
        nonnegativeReadout units setup.mass *
          signedReadout units setup.verticalAccelerationY

/-! ## Derived stopping quantities and displayed answer -/

/-- The stopping data and constant-acceleration law imply `a_y = 2 m/s^2`. -/
lemma brakingAccelerationY_eq_two
    (setup : ElevatorBrakingSetup)
    (hProblem : MatchesProblemDescription setup)
    (hKinematics : SatisfiesConstantAccelerationKinematics setup) :
    accelerationYInMetersPerSecondSquared setup.verticalAccelerationY = 2 := by
  have hf : signedReadout UnitChoices.SI setup.finalVelocityY = 0 := by
    simpa [velocityYInMetersPerSecond] using hProblem.broughtToRest
  have hi : signedReadout UnitChoices.SI setup.initialVelocityY = -10 := by
    calc
      signedReadout UnitChoices.SI setup.initialVelocityY =
          -speedInMetersPerSecond setup.initialSpeed :=
        hProblem.initialVelocityPointsDown
      _ = -10 := by rw [hProblem.initialSpeedMetersPerSecond]
  have hdy : signedReadout UnitChoices.SI setup.verticalDisplacementY = -25 := by
    calc
      signedReadout UnitChoices.SI setup.verticalDisplacementY =
          -distanceInMeters setup.stoppingDistance :=
        hProblem.displacementPointsDown
      _ = -25 := by rw [hProblem.stoppingDistanceMeters]
  have h := hKinematics.stoppingRelation UnitChoices.SI
  rw [hf, hi, hdy] at h
  change signedReadout UnitChoices.SI setup.verticalAccelerationY = 2
  norm_num at h
  linarith

/-- The stated mass and standard gravity give a weight magnitude of `7840 N`. -/
lemma elevatorWeight_eq_7840
    (setup : ElevatorBrakingSetup)
    (hProblem : MatchesProblemDescription setup)
    (hDynamics : SatisfiesVerticalDynamics setup) :
    forceInNewtons setup.weightMagnitude = 7840 := by
  change nonnegativeReadout UnitChoices.SI setup.weightMagnitude = 7840
  calc
    nonnegativeReadout UnitChoices.SI setup.weightMagnitude =
        nonnegativeReadout UnitChoices.SI setup.mass *
          nonnegativeReadout UnitChoices.SI setup.gravityMagnitude :=
      hDynamics.weightMagnitudeLaw UnitChoices.SI
    _ = 800 * (49 / 5) := by
      rw [← massInKilograms, ← accelerationMagnitudeInMetersPerSecondSquared,
        hProblem.combinedMassKilograms,
        hProblem.standardGravityMetersPerSecondSquared]
    _ = 7840 := by norm_num

/-- Labels of the four answers printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Cable-tension value printed beside each answer label, in newtons. -/
def AnswerChoice.tensionInNewtons : AnswerChoice → ℝ
  | .A => 8760
  | .B => 9440
  | .C => 9380
  | .D => 8540

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .B

/-- A displayed answer agrees exactly with the modeled cable-tension readout. -/
def MatchesAnswerChoice
    (setup : ElevatorBrakingSetup) (choice : AnswerChoice) : Prop :=
  forceInNewtons setup.cableTension = choice.tensionInNewtons

/-!
The upward force balance during braking gives cable tension `9440 N`, hence
the displayed answer is the recorded choice B.

This formalizes blueprint label `thm:physics:phyx_mini_0802:target`.
-/
theorem elevatorCableTension_is_answerB
    (setup : ElevatorBrakingSetup)
    (hProblem : MatchesProblemDescription setup)
    (hFigure : MatchesPrimaryFigure setup)
    (hKinematics : SatisfiesConstantAccelerationKinematics setup)
    (hDynamics : SatisfiesVerticalDynamics setup) :
    forceInNewtons setup.cableTension = 9440 ∧
      MatchesAnswerChoice setup recordedAnswerChoice := by
  have ha := brakingAccelerationY_eq_two setup hProblem hKinematics
  have hw := elevatorWeight_eq_7840 setup hProblem hDynamics
  have hm : nonnegativeReadout UnitChoices.SI setup.mass = 800 := by
    exact hProblem.combinedMassKilograms
  have hNewton := hDynamics.newtonsSecondLawAlongY UnitChoices.SI
  have hT : forceInNewtons setup.cableTension = 9440 := by
    change nonnegativeReadout UnitChoices.SI setup.cableTension = 9440
    change signedReadout UnitChoices.SI setup.verticalAccelerationY = 2 at ha
    change nonnegativeReadout UnitChoices.SI setup.weightMagnitude = 7840 at hw
    rw [hm, ha, hw] at hNewton
    norm_num at hNewton ⊢
    linarith
  constructor
  · exact hT
  · simpa [MatchesAnswerChoice, recordedAnswerChoice,
      AnswerChoice.tensionInNewtons] using hT

end PhyXMiniProblems.ProblemPhyXMini0802
