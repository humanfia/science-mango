import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.SpaceAndTime.Time.TimeUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0688

open Dimension

/-!
# Tangential acceleration from a circular-motion vector diagram

At the pictured instant, a particle moves clockwise on a circle of radius
2.50 m.  The red velocity arrow is tangent to the path.  The purple total
acceleration arrow has magnitude 15.0 m/s² and makes an angle of 30.0 degrees
with the inward radial ray.

Lengths, speeds, and acceleration magnitudes below are unit-independent
Physlib quantities.  Real numbers occur only as unit readouts, a dimensionless
angle, and displayed answer values.  The radial and tangential acceleration
magnitudes are independent fields constrained by general circular-motion laws;
the requested tangential magnitude is not defined from the recorded answer.
-/

/-! ## Dimensionful quantities and coherent readouts -/

/-- The physical dimension of speed, L T⁻¹. -/
def speedDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- The physical dimension of acceleration, L T⁻². -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length magnitude. -/
abbrev LengthMagnitude : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical speed magnitude. -/
abbrev SpeedMagnitude : Type :=
  Dimensionful (WithDim speedDimension NNReal)

/-- A nonnegative, unit-independent physical acceleration magnitude. -/
abbrev AccelerationMagnitude : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthMagnitudeReadout
    (unit : LengthUnit) (length : LengthMagnitude) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a speed magnitude in coherent selected length and time units. -/
def speedMagnitudeReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedMagnitude) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read an acceleration magnitude in coherent selected units. -/
def accelerationMagnitudeReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationMagnitude) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  lengthMagnitudeReadout LengthUnit.meters length

/-- Metres-per-second readout of a speed magnitude. -/
def speedInMetersPerSecond (speed : SpeedMagnitude) : ℝ :=
  speedMagnitudeReadout LengthUnit.meters TimeUnit.seconds speed

/-- Metres-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitude) : ℝ :=
  accelerationMagnitudeReadout
    LengthUnit.meters TimeUnit.seconds acceleration

/-! ## Particle, vector, and primary-figure vocabulary -/

/-- Sense of motion around the circular path. -/
inductive RotationSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Fintype, Repr

/--
Named rays based at the pictured particle.  The total-acceleration ray lies
between the inward radial ray and the clockwise tangential ray in the image.
-/
inductive ParticleRay where
  | inwardRadial
  | clockwiseTangent
  | totalAcceleration
  deriving DecidableEq, Fintype, Repr

/-- The two vector arrows explicitly drawn in the supplied image. -/
inductive FigureVector where
  | velocityV
  | totalAccelerationA
  deriving DecidableEq, Fintype, Repr

/-- Literal or mathematical labels visible in the supplied image. -/
inductive FigureLabel where
  | velocityV
  | accelerationA
  | radius2Point50Meters
  | acceleration15Point0MetersPerSecondSquared
  | angle30Point0Degrees
  deriving DecidableEq, Fintype, Repr

/-- Geometric features visible in the circular-motion diagram. -/
inductive FigureFeature where
  | dashedCircularPath
  | markedCenter
  | particleOnPath
  | radiusSegment
  | angleArc
  deriving DecidableEq, Fintype, Repr

/--
A physical velocity vector at the instant, represented by its dimensionful
magnitude and its geometrically named direction ray.
-/
structure VelocityVectorAtParticle where
  magnitude : SpeedMagnitude
  direction : ParticleRay

/--
A physical acceleration vector at the instant, represented by its
dimensionful magnitude and its geometrically named direction ray.
-/
structure AccelerationVectorAtParticle where
  magnitude : AccelerationMagnitude
  direction : ParticleRay

/--
Primary-raster information from image 688.png.  Numerical marker fields are
scalar figure readouts; premises below relate them to independent physical
quantities in the setup.
-/
structure CircularAccelerationFigure where
  featureShown : FigureFeature → Bool
  vectorShown : FigureVector → Bool
  vectorRay : FigureVector → ParticleRay
  labelShown : FigureLabel → Bool
  angleFirstRay : ParticleRay
  angleSecondRay : ParticleRay
  totalAccelerationBetweenRadialAndClockwiseTangent : Bool
  radiusMarkerReadoutMeters : ℝ
  totalAccelerationMarkerReadoutMetersPerSecondSquared : ℝ
  radialAccelerationAngleMarkerReadoutDegrees : ℝ

/--
Physical state of the particle at the depicted instant.  The two component
magnitudes are observables constrained by the kinematic laws below; neither is
a local expansion of an answer choice.
-/
structure CircularMotionSnapshot where
  orbitRadius : LengthMagnitude
  velocity : VelocityVectorAtParticle
  totalAcceleration : AccelerationVectorAtParticle
  radialAccelerationMagnitude : AccelerationMagnitude
  tangentialAccelerationMagnitude : AccelerationMagnitude
  radialToTotalAccelerationAngleRadians : ℝ
  rotationSense : RotationSense
  figure : CircularAccelerationFigure

/-! ## Scenario, figure/data evidence, and governing laws -/

/-- The clockwise circular-motion facts stated in the problem and diagram. -/
structure MatchesClockwiseCircularMotionScenario
    (setup : CircularMotionSnapshot) : Prop where
  particleMovesClockwise : setup.rotationSense = .clockwise
  velocityIsClockwiseTangential :
    setup.velocity.direction = .clockwiseTangent
  totalAccelerationUsesPicturedRay :
    setup.totalAcceleration.direction = .totalAcceleration

/--
Incidence and spatial information read directly from the supplied image.  In
particular, the marked angle runs from the inward radius to the total
acceleration arrow, not from the tangent to that arrow.
-/
structure MatchesSuppliedCircularAccelerationFigure
    (setup : CircularMotionSnapshot) : Prop where
  everyFeatureShown :
    ∀ feature, setup.figure.featureShown feature = true
  everyVectorShown :
    ∀ vector, setup.figure.vectorShown vector = true
  everyLabelShown :
    ∀ label, setup.figure.labelShown label = true
  velocityArrowIsClockwiseTangent :
    setup.figure.vectorRay .velocityV = .clockwiseTangent
  totalAccelerationArrowUsesTotalRay :
    setup.figure.vectorRay .totalAccelerationA = .totalAcceleration
  angleStartsOnInwardRadius :
    setup.figure.angleFirstRay = .inwardRadial
  angleEndsOnTotalAcceleration :
    setup.figure.angleSecondRay = .totalAcceleration
  totalAccelerationIsBetweenRadialAndTangent :
    setup.figure.totalAccelerationBetweenRadialAndClockwiseTangent = true

/--
The three numerical readouts shown in the primary image, together with their
interpretation as physical radius, total-acceleration magnitude, and radian
angle.  No tangential-acceleration value appears here.
-/
structure MatchesPrimaryFigureReadouts
    (setup : CircularMotionSnapshot) : Prop where
  radiusMarkerReads2Point50Meters :
    setup.figure.radiusMarkerReadoutMeters = 2.50
  totalAccelerationMarkerReads15Point0MetersPerSecondSquared :
    setup.figure.totalAccelerationMarkerReadoutMetersPerSecondSquared = 15.0
  angleMarkerReads30Point0Degrees :
    setup.figure.radialAccelerationAngleMarkerReadoutDegrees = 30.0
  radiusMarkerRepresentsOrbitRadius :
    setup.figure.radiusMarkerReadoutMeters =
      lengthInMeters setup.orbitRadius
  accelerationMarkerRepresentsTotalMagnitude :
    setup.figure.totalAccelerationMarkerReadoutMetersPerSecondSquared =
      accelerationInMetersPerSecondSquared setup.totalAcceleration.magnitude
  degreeMarkerRepresentsRadianAngle :
    setup.radialToTotalAccelerationAngleRadians =
      setup.figure.radialAccelerationAngleMarkerReadoutDegrees *
        Real.pi / 180

/-- Positivity and acute-angle conditions selecting the pictured branch. -/
structure HasPhysicalCircularMotionParameters
    (setup : CircularMotionSnapshot) : Prop where
  orbitRadiusPositive : 0 < lengthInMeters setup.orbitRadius
  speedPositive : 0 < speedInMetersPerSecond setup.velocity.magnitude
  totalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.totalAcceleration.magnitude
  radialAccelerationNonnegative :
    0 ≤ accelerationInMetersPerSecondSquared
      setup.radialAccelerationMagnitude
  tangentialAccelerationNonnegative :
    0 ≤ accelerationInMetersPerSecondSquared
      setup.tangentialAccelerationMagnitude
  radialToTotalAngleAcute :
    0 < setup.radialToTotalAccelerationAngleRadians ∧
      setup.radialToTotalAccelerationAngleRadians < Real.pi / 2

/--
Instantaneous circular-motion kinematics.  The radial component is the
centripetal acceleration v²/r.  Resolving the total acceleration at angle phi
from the inward radius gives a_r = a cos(phi) and a_t = a sin(phi).
These are general laws and contain no numerical answer or answer label.
-/
structure SatisfiesCircularAccelerationDecomposition
    (setup : CircularMotionSnapshot) : Prop where
  radialComponentIsCentripetal :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      accelerationMagnitudeReadout lengthUnit timeUnit
          setup.radialAccelerationMagnitude =
        speedMagnitudeReadout lengthUnit timeUnit
              setup.velocity.magnitude ^ 2 /
          lengthMagnitudeReadout lengthUnit setup.orbitRadius
  radialComponentResolution :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      accelerationMagnitudeReadout lengthUnit timeUnit
          setup.radialAccelerationMagnitude =
        accelerationMagnitudeReadout lengthUnit timeUnit
            setup.totalAcceleration.magnitude *
          Real.cos setup.radialToTotalAccelerationAngleRadians
  tangentialComponentResolution :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      accelerationMagnitudeReadout lengthUnit timeUnit
          setup.tangentialAccelerationMagnitude =
        accelerationMagnitudeReadout lengthUnit timeUnit
            setup.totalAcceleration.magnitude *
          Real.sin setup.radialToTotalAccelerationAngleRadians

/-! ## Displayed answers and current target -/

/-- Labels of the four tangential-acceleration choices in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metres-per-second-squared value printed beside each answer label. -/
def displayedTangentialAccelerationInMetersPerSecondSquared :
    AnswerChoice → ℝ
  | .A => 2.50
  | .B => 10.00
  | .C => 7.50
  | .D => 5.00

/-- The answer label recorded by the source dataset, retained as metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A choice agrees exactly with the physical tangential-acceleration readout. -/
def MatchesDisplayedTangentialAcceleration
    (setup : CircularMotionSnapshot) (choice : AnswerChoice) : Prop :=
  accelerationInMetersPerSecondSquared
      setup.tangentialAccelerationMagnitude =
    displayedTangentialAccelerationInMetersPerSecondSquared choice

/-- A choice is the unique displayed value matching the physical result. -/
def IsUniqueMatchingTangentialAccelerationChoice
    (setup : CircularMotionSnapshot) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedTangentialAcceleration setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedTangentialAcceleration setup other → other = choice

/--
The 30-degree radial-to-total angle and the displayed total magnitude entail
a_t = 15 sin(pi/6) = 15/2 = 7.50 m/s², uniquely selecting choice C.

Blueprint: thm:physics:phyx_mini_0688:target.
-/
theorem tangentialAcceleration_is_7_point_50_metersPerSecondSquared
    (setup : CircularMotionSnapshot)
    (hScenario : MatchesClockwiseCircularMotionScenario setup)
    (hFigure : MatchesSuppliedCircularAccelerationFigure setup)
    (hReadouts : MatchesPrimaryFigureReadouts setup)
    (hPhysical : HasPhysicalCircularMotionParameters setup)
    (hKinematics : SatisfiesCircularAccelerationDecomposition setup) :
    accelerationInMetersPerSecondSquared
        setup.tangentialAccelerationMagnitude = (15 : ℝ) / 2 ∧
      MatchesDisplayedTangentialAcceleration setup .C ∧
      IsUniqueMatchingTangentialAccelerationChoice setup .C := by
  have hTotal :
      accelerationInMetersPerSecondSquared
          setup.totalAcceleration.magnitude = (15 : ℝ) := by
    have hMarker :=
      hReadouts.totalAccelerationMarkerReads15Point0MetersPerSecondSquared
    norm_num at hMarker
    rw [← hReadouts.accelerationMarkerRepresentsTotalMagnitude]
    exact hMarker
  have hDegree := hReadouts.angleMarkerReads30Point0Degrees
  norm_num at hDegree
  have hAngle :
      setup.radialToTotalAccelerationAngleRadians = Real.pi / 6 := by
    calc
      setup.radialToTotalAccelerationAngleRadians =
          30 * Real.pi / 180 := by
        rw [hReadouts.degreeMarkerRepresentsRadianAngle, hDegree]
      _ = Real.pi / 6 := by ring
  have hTangential :
      accelerationInMetersPerSecondSquared
          setup.tangentialAccelerationMagnitude = (15 : ℝ) / 2 := by
    have hResolution :=
      hKinematics.tangentialComponentResolution
        LengthUnit.meters TimeUnit.seconds
    change
      accelerationInMetersPerSecondSquared
            setup.tangentialAccelerationMagnitude =
        accelerationInMetersPerSecondSquared
              setup.totalAcceleration.magnitude *
          Real.sin setup.radialToTotalAccelerationAngleRadians
      at hResolution
    rw [hTotal, hAngle, Real.sin_pi_div_six] at hResolution
    norm_num at hResolution ⊢
    exact hResolution
  have hChoiceC : MatchesDisplayedTangentialAcceleration setup .C := by
    rw [MatchesDisplayedTangentialAcceleration,
      displayedTangentialAccelerationInMetersPerSecondSquared]
    norm_num at hTangential ⊢
    exact hTangential
  refine ⟨hTangential, hChoiceC, hChoiceC, ?_⟩
  intro other hOther
  cases other with
  | A =>
      exfalso
      norm_num [MatchesDisplayedTangentialAcceleration,
        displayedTangentialAccelerationInMetersPerSecondSquared] at hOther
      norm_num at hTangential
      linarith
  | B =>
      exfalso
      norm_num [MatchesDisplayedTangentialAcceleration,
        displayedTangentialAccelerationInMetersPerSecondSquared] at hOther
      norm_num at hTangential
      linarith
  | C => rfl
  | D =>
      exfalso
      norm_num [MatchesDisplayedTangentialAcceleration,
        displayedTangentialAccelerationInMetersPerSecondSquared] at hOther
      norm_num at hTangential
      linarith

end PhyXMiniProblems.ProblemPhyXMini0688
