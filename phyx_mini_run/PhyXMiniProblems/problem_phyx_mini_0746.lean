import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0746

open Dimension

/-!
# A skier landing on a downward slope

The primary image compares a prejump made before the break in the track with
a jump made at the edge of the `9.0°` downward slope.  This file formalizes the
edge jump asked about in the question, while retaining the qualitative
information from both panels of the figure.

Lengths, elapsed times, speeds, and gravitational acceleration are represented
by Physlib dimensionful quantities.  Real numbers occur only as coherent SI
readouts, dimensionless schematic coordinates and trigonometric values, and
the numerical values printed in the multiple-choice answers.

The landing drop is an independent physical quantity.  It is related to the
trajectory by general kinematic and geometric laws below, but no premise fixes
it to `1.11 m` or selects answer C.
-/

/-! ## Dimensionful quantities and SI readouts -/

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed horizontal or vertical displacement. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative elapsed physical time. -/
abbrev DurationQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative magnitude of gravitational acceleration. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Read a physical length in SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a signed displacement in SI metres. -/
def signedLengthInMeters (displacement : SignedLengthQuantity) : ℝ :=
  (displacement UnitChoices.SI).val

/-- Read an elapsed time in SI seconds. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  ((duration UnitChoices.SI).val : ℝ)

/-- Read a physical speed in SI metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read an acceleration in SI metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-! ## Physical and figure roles -/

/-- The two diagrams shown side by side in the supplied image. -/
inductive DiagramPanel where
  | prejump
  | edgeJump
  deriving DecidableEq, Fintype, Repr

/-- Schematic locations distinguished in each diagram. -/
inductive FigureAnchor where
  | launchPoint
  | slopeEdge
  | landingPoint
  deriving DecidableEq, Fintype, Repr

/-- The two visible portions of the ski course. -/
inductive CourseSection where
  | approximatelyFlatApproach
  | straightSteeperTrack
  deriving DecidableEq, Fintype, Repr

/-- The idealized model used for the skier while airborne. -/
inductive AirborneModel where
  | constantGravityNegligibleDrag
  deriving DecidableEq, Repr

/-- Where along the course the modeled jump begins. -/
inductive JumpLocation where
  | beforeSlopeEdge
  | atSlopeEdge
  deriving DecidableEq, Repr

/-!
Qualitative evidence transcribed from image `746.png`.  The coordinate
functions describe positions in the drawing only, so their values are
dimensionless and are not treated as measured physical lengths.
-/
structure SkierJumpFigure where
  horizontalPosition : DiagramPanel → FigureAnchor → ℝ
  verticalPosition : DiagramPanel → FigureAnchor → ℝ
  skierShownAtLaunch : DiagramPanel → Bool
  skierShownAtLanding : DiagramPanel → Bool
  curvedFlightPathShown : DiagramPanel → Bool
  courseSectionShown : DiagramPanel → CourseSection → Bool
  dashedLaunchLevelShown : DiagramPanel → Bool

/-!
Both panels show a launch and landing skier, a curved airborne path, a flat
approach, and a steeper straight track.  In the left panel the launch precedes
the edge and the prejump returns approximately to launch level at the top of
the slope.  In the right panel the launch is at the edge and the landing is
strictly down and to the right; only that panel shows the dashed launch level.
-/
structure MatchesPrimaryFigure (figure : SkierJumpFigure) : Prop where
  everyLaunchSkierShown :
    ∀ panel, figure.skierShownAtLaunch panel = true
  everyLandingSkierShown :
    ∀ panel, figure.skierShownAtLanding panel = true
  everyCurvedPathShown :
    ∀ panel, figure.curvedFlightPathShown panel = true
  everyCourseSectionShown :
    ∀ panel courseSection,
      figure.courseSectionShown panel courseSection = true
  prejumpLaunchesBeforeEdge :
    figure.horizontalPosition .prejump .launchPoint <
      figure.horizontalPosition .prejump .slopeEdge
  prejumpLandsAtTopOfSlope :
    figure.horizontalPosition .prejump .slopeEdge ≤
      figure.horizontalPosition .prejump .landingPoint
  prejumpReturnsToLaunchLevel :
    figure.verticalPosition .prejump .landingPoint =
      figure.verticalPosition .prejump .launchPoint
  edgeJumpLaunchesAtSlopeEdge :
    figure.horizontalPosition .edgeJump .launchPoint =
        figure.horizontalPosition .edgeJump .slopeEdge ∧
      figure.verticalPosition .edgeJump .launchPoint =
        figure.verticalPosition .edgeJump .slopeEdge
  edgeJumpLandsToRight :
    figure.horizontalPosition .edgeJump .launchPoint <
      figure.horizontalPosition .edgeJump .landingPoint
  edgeJumpLandsBelowLaunchLevel :
    figure.verticalPosition .edgeJump .landingPoint <
      figure.verticalPosition .edgeJump .launchPoint
  dashedLevelOnlyInEdgePanel :
    figure.dashedLaunchLevelShown .prejump = false ∧
      figure.dashedLaunchLevelShown .edgeJump = true

/-! ## Independent physical setup -/

/-!
Physical data for the right-hand, edge-jump experiment.  Coordinates are
signed physical displacements from the launch point, with horizontal positive
to the right and vertical positive upward.  The landing drop is stored as an
independent nonnegative length rather than being defined from an answer choice.
-/
structure SkierSlopeJumpSetup where
  figure : SkierJumpFigure
  model : AirborneModel
  jumpLocation : JumpLocation
  approachSection : CourseSection
  landingSection : CourseSection
  launchSpeed : DimSpeed
  launchAngle : Real.Angle
  slopeAngleBelowHorizontal : Real.Angle
  gravitationalAcceleration : AccelerationQuantity
  landingTime : DurationQuantity
  landingDrop : LengthQuantity
  horizontalDisplacement : DurationQuantity → SignedLengthQuantity
  verticalDisplacement : DurationQuantity → SignedLengthQuantity

/-- Convert a degree readout into a physical angle modulo `2π`. -/
noncomputable def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-!
The numerical and qualitative data stated in the problem.  The positive
`9°` angle denotes how far the straight landing track slopes below horizontal.
-/
structure MatchesProblemDescription (setup : SkierSlopeJumpSetup) : Prop where
  idealAirborneModel :
    setup.model = .constantGravityNegligibleDrag
  jumpBeginsAtSlopeEdge : setup.jumpLocation = .atSlopeEdge
  approachIsApproximatelyFlat :
    setup.approachSection = .approximatelyFlatApproach
  landingTrackIsStraightAndSteeper :
    setup.landingSection = .straightSteeperTrack
  launchSpeedMetersPerSecond :
    speedInMetersPerSecond setup.launchSpeed = 10
  launchAngleDegrees :
    setup.launchAngle = degrees (113 / 10)
  slopeAngleDegrees :
    setup.slopeAngleBelowHorizontal = degrees 9

/-- Standard near-Earth gravity used by the textbook projectile model. -/
structure UsesStandardNearEarthGravity
    (setup : SkierSlopeJumpSetup) : Prop where
  gravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration =
      49 / 5

/-!
The positive-time, down-slope branch depicted in the right-hand panel.  These
conditions rule out the trivial intersection at the launch point and choose
the physically relevant landing without assigning its numerical drop.
-/
structure HasPhysicalLandingBranch (setup : SkierSlopeJumpSetup) : Prop where
  landingTimePositive : 0 < durationInSeconds setup.landingTime
  launchSpeedPositive : 0 < speedInMetersPerSecond setup.launchSpeed
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  launchPointsRight : 0 < Real.Angle.cos setup.launchAngle
  launchPointsUp : 0 < Real.Angle.sin setup.launchAngle
  slopeDescendsToRight :
    0 < Real.Angle.tan setup.slopeAngleBelowHorizontal
  landingIsToRight :
    0 < signedLengthInMeters
      (setup.horizontalDisplacement setup.landingTime)
  landingIsBelowLaunch :
    signedLengthInMeters
      (setup.verticalDisplacement setup.landingTime) < 0
  landingDropPositive : 0 < lengthInMeters setup.landingDrop

/-!
The governing ideal-projectile and track-geometry relations in coherent SI
readouts:

* horizontal velocity is the constant component `v₀ cos θ₀`;
* vertical position is `v₀ sin θ₀ t - g t² / 2`;
* the straight track through the launch point has equation
  `y = -x tan α`; and
* the positive vertical drop is the negative landing height.

None of these laws contains `1.11` or an answer-choice assertion.
-/
structure SatisfiesIdealSlopeProjectileLaws
    (setup : SkierSlopeJumpSetup) : Prop where
  uniformHorizontalMotion : ∀ duration : DurationQuantity,
    signedLengthInMeters (setup.horizontalDisplacement duration) =
      speedInMetersPerSecond setup.launchSpeed *
        Real.Angle.cos setup.launchAngle * durationInSeconds duration
  verticalConstantGravityMotion : ∀ duration : DurationQuantity,
    signedLengthInMeters (setup.verticalDisplacement duration) =
      speedInMetersPerSecond setup.launchSpeed *
          Real.Angle.sin setup.launchAngle * durationInSeconds duration -
        (1 / 2 : ℝ) *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          durationInSeconds duration ^ 2
  landingLiesOnStraightSlope :
    signedLengthInMeters
        (setup.verticalDisplacement setup.landingTime) =
      -(signedLengthInMeters
          (setup.horizontalDisplacement setup.landingTime) *
        Real.Angle.tan setup.slopeAngleBelowHorizontal)
  dropIsVerticalSeparationFromLaunch :
    signedLengthInMeters
        (setup.verticalDisplacement setup.landingTime) =
      -lengthInMeters setup.landingDrop

/-! ## Derived closed form and displayed answers -/

/-!
The nonzero horizontal intersection of an ideal projectile with a straight
track descending by angle `α` from its launch point.
-/
noncomputable def predictedHorizontalLandingDistanceInMeters
    (setup : SkierSlopeJumpSetup) : ℝ :=
  2 * speedInMetersPerSecond setup.launchSpeed ^ 2 *
      Real.Angle.cos setup.launchAngle ^ 2 *
      (Real.Angle.tan setup.launchAngle +
        Real.Angle.tan setup.slopeAngleBelowHorizontal) /
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration

/-- The corresponding predicted vertical distance below launch level. -/
noncomputable def predictedLandingDropInMeters
    (setup : SkierSlopeJumpSetup) : ℝ :=
  predictedHorizontalLandingDistanceInMeters setup *
    Real.Angle.tan setup.slopeAngleBelowHorizontal

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Distance in metres printed beside each displayed answer label. -/
def AnswerChoice.displayedDistanceInMeters : AnswerChoice → ℝ
  | .A => 92 / 100
  | .B => 1
  | .C => 111 / 100
  | .D => 123 / 100

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Agreement with a distance displayed to the nearest centimetre. -/
def MatchesDisplayedDistance
    (setup : SkierSlopeJumpSetup) (choice : AnswerChoice) : Prop :=
  |lengthInMeters setup.landingDrop - choice.displayedDistanceInMeters| ≤
    (1 / 200 : ℝ)

/-- The selected printed distance is strictly closer than every alternative. -/
def IsUniqueClosestDisplayedDistance
    (setup : SkierSlopeJumpSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |lengthInMeters setup.landingDrop - choice.displayedDistanceInMeters| <
      |lengthInMeters setup.landingDrop - other.displayedDistanceInMeters|

/-!
Eliminating the positive landing time from the projectile equations and the
slope equation gives the nonzero horizontal intersection above.
-/
lemma horizontalLandingDistance_eq_prediction
    (setup : SkierSlopeJumpSetup)
    (_description : MatchesProblemDescription setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_physical : HasPhysicalLandingBranch setup)
    (_laws : SatisfiesIdealSlopeProjectileLaws setup) :
    signedLengthInMeters
        (setup.horizontalDisplacement setup.landingTime) =
      predictedHorizontalLandingDistanceInMeters setup := by
  have hHorizontal :=
    _laws.uniformHorizontalMotion setup.landingTime
  have hVertical :=
    _laws.verticalConstantGravityMotion setup.landingTime
  have hSlope := _laws.landingLiesOnStraightSlope
  have hTimeFactor :
      durationInSeconds setup.landingTime *
          (speedInMetersPerSecond setup.launchSpeed *
              Real.Angle.sin setup.launchAngle +
            speedInMetersPerSecond setup.launchSpeed *
              Real.Angle.cos setup.launchAngle *
              Real.Angle.tan setup.slopeAngleBelowHorizontal -
            (1 / 2 : ℝ) *
              accelerationInMetersPerSecondSquared
                setup.gravitationalAcceleration *
              durationInSeconds setup.landingTime) =
        0 := by
    rw [hHorizontal] at hSlope
    nlinarith
  have hTimeNonzero :
      durationInSeconds setup.landingTime ≠ 0 :=
    ne_of_gt _physical.landingTimePositive
  have hPositiveTimeEquation :=
    (mul_eq_zero.mp hTimeFactor).resolve_left hTimeNonzero
  rw [predictedHorizontalLandingDistanceInMeters,
    Real.Angle.tan_eq_sin_div_cos]
  field_simp [ne_of_gt _physical.gravityPositive,
    ne_of_gt _physical.launchPointsRight]
  have hScaled := congrArg
    (fun value : ℝ =>
      2 * speedInMetersPerSecond setup.launchSpeed *
        Real.Angle.cos setup.launchAngle * value)
    hPositiveTimeEquation
  have hHorizontalScaled := congrArg
    (fun value : ℝ =>
      value *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration)
    hHorizontal
  nlinarith [hScaled, hHorizontalScaled]

/-!
Combining the horizontal intersection with the straight-track geometry gives
the physical vertical drop.  This is a conclusion, not a model premise.
-/
lemma landingDrop_eq_prediction
    (setup : SkierSlopeJumpSetup)
    (_description : MatchesProblemDescription setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_physical : HasPhysicalLandingBranch setup)
    (_laws : SatisfiesIdealSlopeProjectileLaws setup) :
    lengthInMeters setup.landingDrop =
      predictedLandingDropInMeters setup := by
  have hHorizontal :=
    horizontalLandingDistance_eq_prediction setup _description _gravity
      _physical _laws
  have hSlope := _laws.landingLiesOnStraightSlope
  have hDrop := _laws.dropIsVerticalSeparationFromLaunch
  rw [predictedLandingDropInMeters]
  calc
    lengthInMeters setup.landingDrop =
        signedLengthInMeters
            (setup.horizontalDisplacement setup.landingTime) *
          Real.Angle.tan setup.slopeAngleBelowHorizontal := by
      linarith
    _ = predictedHorizontalLandingDistanceInMeters setup *
          Real.Angle.tan setup.slopeAngleBelowHorizontal := by
      rw [hHorizontal]

/-!
For `v₀ = 10 m/s`, `θ₀ = 11.3°`, `α = 9.0°`, and `g = 9.8 m/s²`, the
closed form is approximately `1.11338 m`.  Thus the skier lands `1.11 m`
below launch level to the displayed precision, uniquely selecting choice C.

This formalizes blueprint label `thm:physics:phyx_mini_0746:target`.
-/
theorem problem_phyx_mini_0746
    (setup : SkierSlopeJumpSetup)
    (_figure : MatchesPrimaryFigure setup.figure)
    (_description : MatchesProblemDescription setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_physical : HasPhysicalLandingBranch setup)
    (_laws : SatisfiesIdealSlopeProjectileLaws setup) :
    lengthInMeters setup.landingDrop =
        predictedLandingDropInMeters setup ∧
      MatchesDisplayedDistance setup .C ∧
      IsUniqueClosestDisplayedDistance setup .C := by
  have hsqrt2Lower : (14142135 / 10000000 : ℝ) ≤ Real.sqrt 2 := by
    have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hnonneg := Real.sqrt_nonneg 2
    nlinarith
  have hsqrt2Upper : Real.sqrt 2 ≤ (14142136 / 10000000 : ℝ) := by
    have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hnonneg := Real.sqrt_nonneg 2
    nlinarith
  have hqLower :
      (1847759 / 1000000 : ℝ) ≤ Real.sqrt (2 + Real.sqrt 2) := by
    have hsquare := Real.sq_sqrt
      (by positivity : (0 : ℝ) ≤ 2 + Real.sqrt 2)
    have hnonneg := Real.sqrt_nonneg (2 + Real.sqrt 2)
    nlinarith
  have hqUpper :
      Real.sqrt (2 + Real.sqrt 2) ≤ (18477591 / 10000000 : ℝ) := by
    have hsquare := Real.sq_sqrt
      (by positivity : (0 : ℝ) ≤ 2 + Real.sqrt 2)
    have hnonneg := Real.sqrt_nonneg (2 + Real.sqrt 2)
    nlinarith
  have hs16Low :
      (19509 / 100000 : ℝ) ≤ Real.sin (Real.pi / 16) := by
    rw [Real.sin_pi_div_sixteen]
    have hsquare := Real.sq_sqrt
      (by
        nlinarith only [hqUpper] :
        (0 : ℝ) ≤ 2 - Real.sqrt (2 + Real.sqrt 2))
    have hnonneg :=
      Real.sqrt_nonneg (2 - Real.sqrt (2 + Real.sqrt 2))
    nlinarith
  have hs16High :
      Real.sin (Real.pi / 16) ≤ (19510 / 100000 : ℝ) := by
    rw [Real.sin_pi_div_sixteen]
    have hsquare := Real.sq_sqrt
      (by
        nlinarith only [hqUpper] :
        (0 : ℝ) ≤ 2 - Real.sqrt (2 + Real.sqrt 2))
    have hnonneg :=
      Real.sqrt_nonneg (2 - Real.sqrt (2 + Real.sqrt 2))
    nlinarith
  have hc16Low :
      (98078 / 100000 : ℝ) ≤ Real.cos (Real.pi / 16) := by
    rw [Real.cos_pi_div_sixteen]
    have hsquare := Real.sq_sqrt
      (by positivity : (0 : ℝ) ≤ 2 + Real.sqrt (2 + Real.sqrt 2))
    have hnonneg :=
      Real.sqrt_nonneg (2 + Real.sqrt (2 + Real.sqrt 2))
    nlinarith
  have hc16High :
      Real.cos (Real.pi / 16) ≤ (98079 / 100000 : ℝ) := by
    rw [Real.cos_pi_div_sixteen]
    have hsquare := Real.sq_sqrt
      (by positivity : (0 : ℝ) ≤ 2 + Real.sqrt (2 + Real.sqrt 2))
    have hnonneg :=
      Real.sqrt_nonneg (2 + Real.sqrt (2 + Real.sqrt 2))
    nlinarith
  have hsqrt5Lower : (2236067 / 1000000 : ℝ) ≤ Real.sqrt 5 := by
    have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    have hnonneg := Real.sqrt_nonneg 5
    nlinarith
  have hsqrt5Upper : Real.sqrt 5 ≤ (2236068 / 1000000 : ℝ) := by
    have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    have hnonneg := Real.sqrt_nonneg 5
    nlinarith
  have hcos10 :
      Real.cos (Real.pi / 10) =
        Real.sqrt ((1 + Real.cos (Real.pi / 5)) / 2) := by
    convert Real.cos_half (x := Real.pi / 5)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) using 1 <;>
      ring
  have hc10Low :
      (951056 / 1000000 : ℝ) ≤ Real.cos (Real.pi / 10) := by
    rw [hcos10, Real.cos_pi_div_five]
    have hsquare := Real.sq_sqrt
      (by
        positivity :
        (0 : ℝ) ≤ (1 + (1 + Real.sqrt 5) / 4) / 2)
    have hnonneg :=
      Real.sqrt_nonneg ((1 + (1 + Real.sqrt 5) / 4) / 2)
    nlinarith
  have hc10High :
      Real.cos (Real.pi / 10) ≤ (951057 / 1000000 : ℝ) := by
    rw [hcos10, Real.cos_pi_div_five]
    have hsquare := Real.sq_sqrt
      (by
        positivity :
        (0 : ℝ) ≤ (1 + (1 + Real.sqrt 5) / 4) / 2)
    have hnonneg :=
      Real.sqrt_nonneg ((1 + (1 + Real.sqrt 5) / 4) / 2)
    nlinarith
  have hcos20 :
      Real.cos (Real.pi / 20) =
        Real.sqrt ((1 + Real.cos (Real.pi / 10)) / 2) := by
    convert Real.cos_half (x := Real.pi / 10)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) using 1 <;>
      ring
  have hsin20 :
      Real.sin (Real.pi / 20) =
        Real.sqrt ((1 - Real.cos (Real.pi / 10)) / 2) := by
    convert Real.sin_half_eq_sqrt (x := Real.pi / 10)
      (by positivity) (by linarith [Real.pi_pos]) using 1 <;>
      ring
  have hsaLow :
      (15643 / 100000 : ℝ) ≤ Real.sin (Real.pi / 20) := by
    rw [hsin20]
    have hsquare := Real.sq_sqrt
      (by
        nlinarith only [hc10High] :
        (0 : ℝ) ≤ (1 - Real.cos (Real.pi / 10)) / 2)
    have hnonneg :=
      Real.sqrt_nonneg ((1 - Real.cos (Real.pi / 10)) / 2)
    nlinarith
  have hsaHigh :
      Real.sin (Real.pi / 20) ≤ (15644 / 100000 : ℝ) := by
    rw [hsin20]
    have hsquare := Real.sq_sqrt
      (by
        nlinarith only [hc10High] :
        (0 : ℝ) ≤ (1 - Real.cos (Real.pi / 10)) / 2)
    have hnonneg :=
      Real.sqrt_nonneg ((1 - Real.cos (Real.pi / 10)) / 2)
    nlinarith
  have hcaLow :
      (98768 / 100000 : ℝ) ≤ Real.cos (Real.pi / 20) := by
    rw [hcos20]
    have hsquare := Real.sq_sqrt
      (by
        nlinarith only [hc10Low] :
        (0 : ℝ) ≤ (1 + Real.cos (Real.pi / 10)) / 2)
    have hnonneg :=
      Real.sqrt_nonneg ((1 + Real.cos (Real.pi / 10)) / 2)
    nlinarith
  have hcaHigh :
      Real.cos (Real.pi / 20) ≤ (98769 / 100000 : ℝ) := by
    rw [hcos20]
    have hsquare := Real.sq_sqrt
      (by
        nlinarith only [hc10Low] :
        (0 : ℝ) ≤ (1 + Real.cos (Real.pi / 10)) / 2)
    have hnonneg :=
      Real.sqrt_nonneg ((1 + Real.cos (Real.pi / 10)) / 2)
    nlinarith
  have hLaunchSin :
      Real.Angle.sin (degrees (113 / 10)) =
        Real.sin (Real.pi / 16) * Real.cos (Real.pi / 3600) +
          Real.cos (Real.pi / 16) * Real.sin (Real.pi / 3600) := by
    rw [degrees, Real.Angle.sin_coe]
    convert Real.sin_add (Real.pi / 16) (Real.pi / 3600) using 1 <;>
      ring
  have hLaunchCos :
      Real.Angle.cos (degrees (113 / 10)) =
        Real.cos (Real.pi / 16) * Real.cos (Real.pi / 3600) -
          Real.sin (Real.pi / 16) * Real.sin (Real.pi / 3600) := by
    rw [degrees, Real.Angle.cos_coe]
    convert Real.cos_add (Real.pi / 16) (Real.pi / 3600) using 1 <;>
      ring
  have hSlopeSin :
      Real.Angle.sin (degrees 9) = Real.sin (Real.pi / 20) := by
    rw [degrees, Real.Angle.sin_coe]
    congr 1
    ring
  have hSlopeCos :
      Real.Angle.cos (degrees 9) = Real.cos (Real.pi / 20) := by
    rw [degrees, Real.Angle.cos_coe]
    congr 1
    ring
  have hDeltaNonneg : (0 : ℝ) ≤ Real.pi / 3600 := by positivity
  have hDeltaPos : (0 : ℝ) < Real.pi / 3600 := by positivity
  have hDeltaLe : Real.pi / 3600 ≤ (1 / 900 : ℝ) := by
    nlinarith only [Real.pi_le_four]
  have hDeltaLeOne : |Real.pi / 3600| ≤ (1 : ℝ) := by
    rw [abs_of_nonneg hDeltaNonneg]
    linarith
  have hSinDeltaBound := Real.sin_bound hDeltaLeOne
  rw [abs_of_nonneg hDeltaNonneg] at hSinDeltaBound
  have hSinDeltaNonneg : (0 : ℝ) ≤ Real.sin (Real.pi / 3600) :=
    (Real.sin_pos_of_pos_of_lt_pi hDeltaPos
      (by nlinarith only [Real.pi_pos])).le
  have hErrorLeCubic :
      (Real.pi / 3600) ^ 4 * (5 / 96 : ℝ) ≤
        (Real.pi / 3600) ^ 3 / 6 := by
    have hCoefficient :
        (Real.pi / 3600) * (5 / 96 : ℝ) ≤ 1 / 6 := by
      calc
        (Real.pi / 3600) * (5 / 96 : ℝ) ≤
            (1 / 900 : ℝ) * (5 / 96) :=
          mul_le_mul_of_nonneg_right hDeltaLe (by norm_num)
        _ ≤ 1 / 6 := by norm_num
    calc
      (Real.pi / 3600) ^ 4 * (5 / 96 : ℝ) =
          (Real.pi / 3600) ^ 3 *
            ((Real.pi / 3600) * (5 / 96)) := by ring
      _ ≤ (Real.pi / 3600) ^ 3 * (1 / 6) := by
        exact mul_le_mul_of_nonneg_left hCoefficient
          (pow_nonneg hDeltaNonneg 3)
      _ = (Real.pi / 3600) ^ 3 / 6 := by ring
  have hSinDeltaUpper :
      Real.sin (Real.pi / 3600) ≤ (1 / 900 : ℝ) := by
    have hUpper := (abs_le.mp hSinDeltaBound).2
    linarith only [hUpper, hErrorLeCubic, hDeltaLe]
  have hCosDeltaBound := Real.cos_bound hDeltaLeOne
  rw [abs_of_nonneg hDeltaNonneg] at hCosDeltaBound
  have hCosDeltaLower :
      (99999 / 100000 : ℝ) ≤ Real.cos (Real.pi / 3600) := by
    have hLower := (abs_le.mp hCosDeltaBound).1
    have hDeltaSq :=
      pow_le_pow_left₀ hDeltaNonneg hDeltaLe 2
    have hDeltaFourth :=
      pow_le_pow_left₀ hDeltaNonneg hDeltaLe 4
    nlinarith only [hLower, hDeltaSq, hDeltaFourth]
  have hCosDeltaUpper : Real.cos (Real.pi / 3600) ≤ 1 :=
    Real.cos_le_one _
  have hSin16Nonneg : (0 : ℝ) ≤ Real.sin (Real.pi / 16) := by
    nlinarith only [hs16Low]
  have hCos16Nonneg : (0 : ℝ) ≤ Real.cos (Real.pi / 16) := by
    nlinarith only [hc16Low]
  have hCosDeltaNonneg : (0 : ℝ) ≤ Real.cos (Real.pi / 3600) := by
    nlinarith only [hCosDeltaLower]
  have hLaunchSinLow :
      (19509 / 100000 : ℝ) ≤
        Real.Angle.sin (degrees (113 / 10)) := by
    have hMono :
        Real.sin (Real.pi / 16) ≤
          Real.sin (Real.pi / 16 + Real.pi / 3600) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two
        (by nlinarith only [Real.pi_pos])
        (by nlinarith only [Real.pi_pos])
        (le_add_of_nonneg_right hDeltaNonneg)
    rw [Real.sin_add] at hMono
    nlinarith only [hs16Low, hMono, hLaunchSin]
  have hLaunchSinHigh :
      Real.Angle.sin (degrees (113 / 10)) ≤
        (19622 / 100000 : ℝ) := by
    have hFirstProduct :=
      mul_le_mul hs16High hCosDeltaUpper hCosDeltaNonneg
        (by norm_num)
    have hSecondProduct :=
      mul_le_mul hc16High hSinDeltaUpper hSinDeltaNonneg
        (by norm_num)
    nlinarith only [hFirstProduct, hSecondProduct, hLaunchSin]
  have hLaunchCosLow :
      (98055 / 100000 : ℝ) ≤
        Real.Angle.cos (degrees (113 / 10)) := by
    have hFirstProduct :=
      mul_le_mul hc16Low hCosDeltaLower (by norm_num) hCos16Nonneg
    have hSecondProduct :=
      mul_le_mul hs16High hSinDeltaUpper hSinDeltaNonneg
        (by norm_num)
    nlinarith only [hFirstProduct, hSecondProduct, hLaunchCos]
  have hLaunchCosHigh :
      Real.Angle.cos (degrees (113 / 10)) ≤
        (98079 / 100000 : ℝ) := by
    have hMono :
        Real.cos (Real.pi / 16 + Real.pi / 3600) ≤
          Real.cos (Real.pi / 16) :=
      Real.cos_le_cos_of_nonneg_of_le_pi
        (by positivity) (by nlinarith only [Real.pi_pos])
        (le_add_of_nonneg_right hDeltaNonneg)
    rw [Real.cos_add] at hMono
    nlinarith only [hc16High, hMono, hLaunchCos]
  have hSlopeTanLow :
      (15837 / 100000 : ℝ) ≤ Real.Angle.tan (degrees 9) := by
    rw [Real.Angle.tan_eq_sin_div_cos, hSlopeSin, hSlopeCos]
    apply (le_div_iff₀ (by nlinarith only [hcaLow])).2
    nlinarith only [hsaLow, hcaHigh]
  have hSlopeTanHigh :
      Real.Angle.tan (degrees 9) ≤ (15840 / 100000 : ℝ) := by
    rw [Real.Angle.tan_eq_sin_div_cos, hSlopeSin, hSlopeCos]
    apply (div_le_iff₀ (by nlinarith only [hcaLow])).2
    nlinarith only [hsaHigh, hcaLow]
  have hLaunchCosPositive :
      (0 : ℝ) < Real.Angle.cos (degrees (113 / 10)) := by
    nlinarith only [hLaunchCosLow]
  have hPredictionFormula :
      predictedLandingDropInMeters setup =
        (1000 / 49 : ℝ) *
          (Real.Angle.cos (degrees (113 / 10)) *
                Real.Angle.sin (degrees (113 / 10)) +
              Real.Angle.cos (degrees (113 / 10)) ^ 2 *
                Real.Angle.tan (degrees 9)) *
            Real.Angle.tan (degrees 9) := by
    rw [predictedLandingDropInMeters,
      predictedHorizontalLandingDistanceInMeters,
      _description.launchSpeedMetersPerSecond,
      _description.launchAngleDegrees,
      _description.slopeAngleDegrees,
      _gravity.gravityMetersPerSecondSquared,
      Real.Angle.tan_eq_sin_div_cos]
    field_simp [ne_of_gt hLaunchCosPositive]
    ring
  have hLaunchSinNonneg :
      (0 : ℝ) ≤ Real.Angle.sin (degrees (113 / 10)) := by
    nlinarith only [hLaunchSinLow]
  have hLaunchCosNonneg :
      (0 : ℝ) ≤ Real.Angle.cos (degrees (113 / 10)) := by
    nlinarith only [hLaunchCosLow]
  have hSlopeTanNonneg :
      (0 : ℝ) ≤ Real.Angle.tan (degrees 9) := by
    nlinarith only [hSlopeTanLow]
  have hPredictionLow :
      (221 / 200 : ℝ) ≤ predictedLandingDropInMeters setup := by
    rw [hPredictionFormula]
    calc
      (221 / 200 : ℝ) ≤
          (1000 / 49 : ℝ) *
            ((98055 / 100000 : ℝ) * (19509 / 100000 : ℝ) +
              (98055 / 100000 : ℝ) ^ 2 *
                (15837 / 100000 : ℝ)) *
            (15837 / 100000 : ℝ) := by norm_num
      _ ≤ (1000 / 49 : ℝ) *
            (Real.Angle.cos (degrees (113 / 10)) *
                  Real.Angle.sin (degrees (113 / 10)) +
                Real.Angle.cos (degrees (113 / 10)) ^ 2 *
                  Real.Angle.tan (degrees 9)) *
              Real.Angle.tan (degrees 9) := by
        gcongr
  have hPredictionHigh :
      predictedLandingDropInMeters setup ≤ (223 / 200 : ℝ) := by
    rw [hPredictionFormula]
    calc
      (1000 / 49 : ℝ) *
            (Real.Angle.cos (degrees (113 / 10)) *
                  Real.Angle.sin (degrees (113 / 10)) +
                Real.Angle.cos (degrees (113 / 10)) ^ 2 *
                  Real.Angle.tan (degrees 9)) *
              Real.Angle.tan (degrees 9) ≤
          (1000 / 49 : ℝ) *
            ((98079 / 100000 : ℝ) * (19622 / 100000 : ℝ) +
              (98079 / 100000 : ℝ) ^ 2 *
                (15840 / 100000 : ℝ)) *
            (15840 / 100000 : ℝ) := by
        gcongr
      _ ≤ (223 / 200 : ℝ) := by norm_num
  have hDropPrediction :
      lengthInMeters setup.landingDrop =
        predictedLandingDropInMeters setup :=
    landingDrop_eq_prediction setup _description _gravity _physical _laws
  have hPredictionApprox :
      |predictedLandingDropInMeters setup - (111 / 100 : ℝ)| ≤
        (1 / 200 : ℝ) := by
    rw [abs_le]
    constructor <;>
      nlinarith only [hPredictionLow, hPredictionHigh]
  refine ⟨hDropPrediction, ?_, ?_⟩
  · rw [MatchesDisplayedDistance,
      AnswerChoice.displayedDistanceInMeters, hDropPrediction]
    exact hPredictionApprox
  · rw [IsUniqueClosestDisplayedDistance]
    intro other hOther
    cases other with
    | A =>
        rw [AnswerChoice.displayedDistanceInMeters,
          AnswerChoice.displayedDistanceInMeters, hDropPrediction]
        rw [abs_of_nonneg
          (by
            nlinarith only [hPredictionLow] :
            (0 : ℝ) ≤ predictedLandingDropInMeters setup - 92 / 100)]
        exact lt_of_le_of_lt hPredictionApprox
          (by nlinarith only [hPredictionLow])
    | B =>
        rw [AnswerChoice.displayedDistanceInMeters,
          AnswerChoice.displayedDistanceInMeters, hDropPrediction]
        rw [abs_of_nonneg
          (by
            nlinarith only [hPredictionLow] :
            (0 : ℝ) ≤ predictedLandingDropInMeters setup - 1)]
        exact lt_of_le_of_lt hPredictionApprox
          (by nlinarith only [hPredictionLow])
    | C =>
        exact (hOther rfl).elim
    | D =>
        rw [AnswerChoice.displayedDistanceInMeters,
          AnswerChoice.displayedDistanceInMeters, hDropPrediction]
        rw [abs_of_nonpos
          (by
            nlinarith only [hPredictionHigh] :
            predictedLandingDropInMeters setup - 123 / 100 ≤ 0)]
        exact lt_of_le_of_lt hPredictionApprox
          (by nlinarith only [hPredictionHigh])

end PhyXMiniProblems.ProblemPhyXMini0746
