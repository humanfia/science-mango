import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0810

open Dimension

/-!
# Maximum height of a vertically thrown baseball

A `0.145 kg` baseball is thrown straight upward with initial vertical velocity
`20.0 m/s`.  The primary figure labels the release event by `y₁ = 0` and
`v₁ = 20.0 m/s`, and labels the highest point by `y₂` and `v₂ = 0`.
Air resistance is neglected.

Mass, position, velocity, and acceleration are represented by unit-independent
Physlib dimensionful quantities.  Real numbers occur only as coherent-unit
readouts and displayed multiple-choice values.

Assumption/target split:

* governing laws: the vertical acceleration is `-g`, and the two endpoint
  states obey the constant-acceleration velocity--position equation;
* previous-part results: none;
* figure/data readouts: `m = 0.145 kg`, `y₁ = 0`, `v₁ = 20.0 m/s`,
  `v₂ = 0`, the upward launch arrow, and standard terrestrial
  `g = 9.8 m/s²`;
* current target conclusions: the exact height gain `1000 / 49 m` and its
  agreement, to the displayed tenth of a metre, with answer choice B,
  `20.4 m`.
-/

/-! ## Dimensionful vertical-kinematics quantities -/

/-- The physical dimension of signed vertical velocity, `L T⁻¹`. -/
def verticalVelocityDimension : Dimension :=
  L𝓭 * T𝓭⁻¹

/-- The physical dimension of signed vertical acceleration, `L T⁻²`. -/
def verticalAccelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A signed vertical position relative to the coordinate origin in the figure. -/
abbrev VerticalPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A signed component of vertical velocity. -/
abbrev VerticalVelocityQuantity : Type :=
  Dimensionful (WithDim verticalVelocityDimension ℝ)

/-- A signed component of vertical acceleration. -/
abbrev VerticalAccelerationQuantity : Type :=
  Dimensionful (WithDim verticalAccelerationDimension ℝ)

/-- A nonnegative magnitude of gravitational acceleration. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim verticalAccelerationDimension NNReal)

/-- Read a physical mass in an arbitrary coherent unit system. -/
def massReadout (units : UnitChoices) (mass : MassQuantity) : ℝ :=
  ((mass units).val : ℝ)

/-- Read a signed vertical position in an arbitrary coherent unit system. -/
def positionReadout
    (units : UnitChoices) (position : VerticalPositionQuantity) : ℝ :=
  (position units).val

/-- Read a signed vertical velocity in an arbitrary coherent unit system. -/
def velocityReadout
    (units : UnitChoices) (velocity : VerticalVelocityQuantity) : ℝ :=
  (velocity units).val

/-- Read a signed vertical acceleration in an arbitrary coherent unit system. -/
def accelerationReadout
    (units : UnitChoices) (acceleration : VerticalAccelerationQuantity) : ℝ :=
  (acceleration units).val

/-- Read a nonnegative acceleration magnitude in coherent units. -/
def accelerationMagnitudeReadout
    (units : UnitChoices) (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration units).val : ℝ)

/-! ## Figure labels and independent physical setup -/

/-- The two endpoint states explicitly drawn in the primary figure. -/
inductive MotionEvent where
  | release
  | highestPoint
  deriving DecidableEq, Fintype, Repr

/-- Vertical directions used for the coordinate convention and launch arrow. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- The physical object identified by the problem statement. -/
inductive ThrownObjectKind where
  | baseball
  deriving DecidableEq, Repr

/-- The idealized dynamics selected by the phrase "ignoring air resistance." -/
inductive VerticalMotionModel where
  | uniformGravityNegligibleAirResistance
  deriving DecidableEq, Repr

/-- The five symbolic quantity labels visible in image `810.png`. -/
inductive FigureQuantityLabel where
  | massM
  | initialPositionY1
  | peakPositionY2
  | initialVelocityV1
  | peakVelocityV2
  deriving DecidableEq, Fintype, Repr

/-!
Literal content retained from the primary raster.  The numerical fields are
displayed SI readouts; `y₂` is retained only as a visible symbolic label and is
not assigned a numerical value in the figure data.
-/
structure BaseballVerticalThrowFigure where
  showsHand : Bool
  showsBaseballAt : MotionEvent → Bool
  showsQuantityLabel : FigureQuantityLabel → Bool
  showsLaunchArrow : Bool
  launchArrowDirection : VerticalDirection
  displayedMassKilograms : ℝ
  displayedVelocityMetersPerSecond : MotionEvent → ℝ
  displayedInitialPositionMeters : ℝ

/-!
Independent physical quantities of the throw.  In particular, the position at
`highestPoint` is an unconstrained observable here; it is neither defined from
the recorded answer nor from a closed-form height formula.
-/
structure BaseballVerticalThrowSetup where
  objectKind : ThrownObjectKind
  motionModel : VerticalMotionModel
  positiveCoordinateDirection : VerticalDirection
  launchDirection : VerticalDirection
  baseballMass : MassQuantity
  verticalPositionAt : MotionEvent → VerticalPositionQuantity
  verticalVelocityAt : MotionEvent → VerticalVelocityQuantity
  verticalAcceleration : VerticalAccelerationQuantity
  gravityMagnitude : AccelerationMagnitudeQuantity
  figure : BaseballVerticalThrowFigure

/-- Coherent-SI kilogram readout of the baseball mass. -/
def massInKilograms (setup : BaseballVerticalThrowSetup) : ℝ :=
  massReadout UnitChoices.SI setup.baseballMass

/-- Coherent-SI metre readout of the position at a labeled event. -/
def positionInMeters
    (setup : BaseballVerticalThrowSetup) (event : MotionEvent) : ℝ :=
  positionReadout UnitChoices.SI (setup.verticalPositionAt event)

/-- Coherent-SI metre-per-second readout at a labeled event. -/
def velocityInMetersPerSecond
    (setup : BaseballVerticalThrowSetup) (event : MotionEvent) : ℝ :=
  velocityReadout UnitChoices.SI (setup.verticalVelocityAt event)

/-- Coherent-SI metre-per-second-squared readout of signed acceleration. -/
def verticalAccelerationInMetersPerSecondSquared
    (setup : BaseballVerticalThrowSetup) : ℝ :=
  accelerationReadout UnitChoices.SI setup.verticalAcceleration

/-- Coherent-SI metre-per-second-squared readout of the magnitude `g`. -/
def gravityMagnitudeInMetersPerSecondSquared
    (setup : BaseballVerticalThrowSetup) : ℝ :=
  accelerationMagnitudeReadout UnitChoices.SI setup.gravityMagnitude

/-- The requested height is the peak position minus the release position. -/
def heightGainInMeters (setup : BaseballVerticalThrowSetup) : ℝ :=
  positionInMeters setup .highestPoint - positionInMeters setup .release

/-! ## Scenario, primary-image readouts, and governing laws -/

/-- The prose assumptions: a baseball is thrown upward in ideal uniform gravity. -/
structure MatchesProblemDescription
    (setup : BaseballVerticalThrowSetup) : Prop where
  objectIsBaseball : setup.objectKind = .baseball
  idealVerticalMotionModel :
    setup.motionModel = .uniformGravityNegligibleAirResistance
  positiveDirectionIsUpward : setup.positiveCoordinateDirection = .upward
  launchIsStraightUp : setup.launchDirection = .upward

/-!
Exact transcription of the primary bitmap.  The physical readouts are tied to
the displayed numbers, while the unknown label `y₂` receives no numerical
premise.
-/
structure MatchesPrimaryFigure
    (setup : BaseballVerticalThrowSetup) : Prop where
  handShown : setup.figure.showsHand = true
  bothBaseballsShown : ∀ event, setup.figure.showsBaseballAt event = true
  everyQuantityLabelShown :
    ∀ label, setup.figure.showsQuantityLabel label = true
  launchArrowShown : setup.figure.showsLaunchArrow = true
  launchArrowPointsUp : setup.figure.launchArrowDirection = .upward
  displayedMassValue : setup.figure.displayedMassKilograms = 29 / 200
  displayedInitialVelocityValue :
    setup.figure.displayedVelocityMetersPerSecond .release = 20
  displayedPeakVelocityValue :
    setup.figure.displayedVelocityMetersPerSecond .highestPoint = 0
  displayedInitialPositionValue :
    setup.figure.displayedInitialPositionMeters = 0
  massLabelMatchesPhysicalMass :
    massInKilograms setup = setup.figure.displayedMassKilograms
  initialVelocityLabelMatchesPhysicalVelocity :
    velocityInMetersPerSecond setup .release =
      setup.figure.displayedVelocityMetersPerSecond .release
  peakVelocityLabelMatchesPhysicalVelocity :
    velocityInMetersPerSecond setup .highestPoint =
      setup.figure.displayedVelocityMetersPerSecond .highestPoint
  initialPositionLabelMatchesPhysicalPosition :
    positionInMeters setup .release =
      setup.figure.displayedInitialPositionMeters

/-- The conventional near-Earth value used by the multiple-choice calculation. -/
structure UsesStandardEarthGravity
    (setup : BaseballVerticalThrowSetup) : Prop where
  gravityMagnitudeSI :
    gravityMagnitudeInMetersPerSecondSquared setup = 49 / 5

/-!
Positivity conditions select the physical upward-throw branch without fixing
the requested numerical height.
-/
structure HasPhysicalThrowParameters
    (setup : BaseballVerticalThrowSetup) : Prop where
  massPositive : 0 < massInKilograms setup
  gravityPositive : 0 < gravityMagnitudeInMetersPerSecondSquared setup
  releaseVelocityUpward : 0 < velocityInMetersPerSecond setup .release

/-!
The constant-gravity kinematic laws, stated for every coherent unit choice.
They relate the independent endpoint observables and contain neither
`1000 / 49`, the rounded value `20.4`, nor any answer-choice label.
-/
structure SatisfiesUniformGravityKinematics
    (setup : BaseballVerticalThrowSetup) : Prop where
  verticalAccelerationIsNegativeGravity :
    ∀ units,
      accelerationReadout units setup.verticalAcceleration =
        -accelerationMagnitudeReadout units setup.gravityMagnitude
  endpointVelocityPositionLaw :
    ∀ units,
      velocityReadout units
            (setup.verticalVelocityAt .highestPoint) ^ 2 =
        velocityReadout units (setup.verticalVelocityAt .release) ^ 2 +
          2 * accelerationReadout units setup.verticalAcceleration *
            (positionReadout units
                (setup.verticalPositionAt .highestPoint) -
              positionReadout units
                (setup.verticalPositionAt .release))

/-! ## Exact result and displayed answer choices -/

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Height in metres printed beside each answer choice. -/
def AnswerChoice.displayedHeightInMeters : AnswerChoice → ℝ
  | .A => 231 / 10
  | .B => 204 / 10
  | .C => 272 / 10
  | .D => 165 / 10

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .B

/-!
A tenth-metre display represents the ideal height when the discrepancy is
strictly less than half of the last displayed metre digit.
-/
def FitsDisplayedHeight
    (setup : BaseballVerticalThrowSetup) (choice : AnswerChoice) : Prop :=
  |heightGainInMeters setup - choice.displayedHeightInMeters| < 1 / 20

/-- Under the ideal model, the exact height gain is `20² / (2 * 9.8)`. -/
lemma heightGain_exact
    (setup : BaseballVerticalThrowSetup)
    (_problem : MatchesProblemDescription setup)
    (_figure : MatchesPrimaryFigure setup)
    (_gravity : UsesStandardEarthGravity setup)
    (_physical : HasPhysicalThrowParameters setup)
    (_kinematics : SatisfiesUniformGravityKinematics setup) :
    heightGainInMeters setup = 1000 / 49 := by
  have hInitialVelocity :
      velocityInMetersPerSecond setup .release = 20 := by
    calc
      velocityInMetersPerSecond setup .release =
          setup.figure.displayedVelocityMetersPerSecond .release :=
        _figure.initialVelocityLabelMatchesPhysicalVelocity
      _ = 20 := _figure.displayedInitialVelocityValue
  have hPeakVelocity :
      velocityInMetersPerSecond setup .highestPoint = 0 := by
    calc
      velocityInMetersPerSecond setup .highestPoint =
          setup.figure.displayedVelocityMetersPerSecond .highestPoint :=
        _figure.peakVelocityLabelMatchesPhysicalVelocity
      _ = 0 := _figure.displayedPeakVelocityValue
  have hAcceleration :
      verticalAccelerationInMetersPerSecondSquared setup =
        -(49 / 5 : ℝ) := by
    calc
      verticalAccelerationInMetersPerSecondSquared setup =
          -gravityMagnitudeInMetersPerSecondSquared setup :=
        _kinematics.verticalAccelerationIsNegativeGravity UnitChoices.SI
      _ = -(49 / 5 : ℝ) := by rw [_gravity.gravityMagnitudeSI]
  have hEndpoint :=
    _kinematics.endpointVelocityPositionLaw UnitChoices.SI
  change
    velocityInMetersPerSecond setup .highestPoint ^ 2 =
      velocityInMetersPerSecond setup .release ^ 2 +
        2 * verticalAccelerationInMetersPerSecondSquared setup *
          (positionInMeters setup .highestPoint -
            positionInMeters setup .release) at hEndpoint
  rw [hPeakVelocity, hInitialVelocity, hAcceleration] at hEndpoint
  unfold heightGainInMeters
  nlinarith [hEndpoint]

/-!
The ideal height is `1000 / 49 m`, which rounds to the displayed `20.4 m`,
answer choice B.

This formalizes blueprint label `thm:physics:phyx_mini_0810:target`.
-/
theorem maximumHeight_matches_answerB
    (setup : BaseballVerticalThrowSetup)
    (_problem : MatchesProblemDescription setup)
    (_figure : MatchesPrimaryFigure setup)
    (_gravity : UsesStandardEarthGravity setup)
    (_physical : HasPhysicalThrowParameters setup)
    (_kinematics : SatisfiesUniformGravityKinematics setup) :
    heightGainInMeters setup = 1000 / 49 ∧
      FitsDisplayedHeight setup .B := by
  have hExact :=
    heightGain_exact setup _problem _figure _gravity _physical _kinematics
  constructor
  · exact hExact
  · norm_num [FitsDisplayedHeight, hExact, AnswerChoice.displayedHeightInMeters,
      abs_of_nonneg]

end PhyXMiniProblems.ProblemPhyXMini0810
