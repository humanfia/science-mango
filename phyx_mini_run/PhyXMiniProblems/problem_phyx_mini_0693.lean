import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0693

open Dimension

/-!
# Flight-time ratio for a one-bounce baseball throw

The primary image compares two idealized throws over the same horizontal
distance `D`.  The green no-bounce trajectory is launched at `45°`.  The blue
one-bounce trajectory consists of two level-ground projectile arcs, both at
the same acute angle `θ`; the speed at the start of the second arc is one half
of the speed at the start of the first arc.

Lengths, durations, speeds, and gravitational acceleration are represented by
Physlib dimensionful quantities.  Real numbers occur only as coherent SI
readouts, schematic image coordinates, physical angles in radians, and the
dimensionless ratio requested by the problem.
-/

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration. -/
abbrev DurationQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative magnitude of gravitational acceleration. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Second readout of a physical duration. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  nonnegativeSIReadout duration

/-- Metre-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Metre-per-second-squared readout of gravitational acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  nonnegativeSIReadout acceleration

/-! ## Physical roles and primary-image vocabulary -/

/-- The complete direct flight and the two arcs of the one-bounce flight. -/
inductive ThrowSegment where
  | directNoBounce
  | beforeBounce
  | afterBounce
  deriving DecidableEq, Fintype, Repr

/-- Ground points distinguished by the diagram and prose. -/
inductive GroundPoint where
  | outfielder
  | bouncePoint
  | catcher
  deriving DecidableEq, Fintype, Repr

/-- Colors used to distinguish the trajectories in the supplied image. -/
inductive TrajectoryColor where
  | blue
  | green
  deriving DecidableEq, Repr

/-- The two angle labels printed in the image. -/
inductive FigureAngleLabel where
  | theta
  | fortyFiveDegrees
  deriving DecidableEq, Fintype, Repr

/-!
Schematic evidence read from the primary image.  The coordinates are drawing
coordinates rather than measured physical distances; the physical baseline
length is stored separately as `distanceD` below.
-/
structure BaseballThrowFigure where
  horizontalCoordinate : GroundPoint → ℝ
  trajectoryColor : ThrowSegment → TrajectoryColor
  showsDashedTrajectory : ThrowSegment → Bool
  showsInitialVelocityArrow : ThrowSegment → Bool
  showsAngleLabelAt : GroundPoint → FigureAngleLabel → Bool
  showsHorizontalGroundLine : Bool
  showsDistanceLabelD : Bool

/-!
Independent physical quantities for the direct throw and both one-bounce
segments.  In particular, no duration or time ratio is defined from an answer
choice.  Relations among these quantities are supplied by scenario and
governing-law premises below.
-/
structure BaseballOneBounceSetup where
  figure : BaseballThrowFigure
  /-- Full outfielder-to-catcher distance, labelled `D`. -/
  distanceD : LengthQuantity
  /-- Horizontal range of each depicted projectile arc. -/
  horizontalRange : ThrowSegment → LengthQuantity
  /-- Initial speed of each depicted projectile arc. -/
  launchSpeed : ThrowSegment → DimSpeed
  /-- Speed immediately before the ball reaches the sole bounce point. -/
  incomingSpeedAtBounce : DimSpeed
  /-- Launch angle of each arc, measured from the horizontal ground. -/
  launchAngle : ThrowSegment → Real.Angle
  /-- Flight duration of each arc. -/
  flightDuration : ThrowSegment → DurationQuantity
  /-- Magnitude of the uniform downward gravitational acceleration. -/
  gravity : AccelerationQuantity
  /-- Number of ground impacts before the ball reaches the catcher. -/
  oneBounceThrowGroundImpacts : ℕ
  /-- The idealization that every arc starts and ends at the same elevation. -/
  everyArcHasEqualLaunchAndLandingHeight : Bool

/-! ## Figure readout, scenario data, and governing laws -/

/-- Qualitative and spatial facts visible in the supplied raster image. -/
structure MatchesPrimaryBaseballFigure
    (setup : BaseballOneBounceSetup) : Prop where
  outfielderBeforeBouncePoint :
    setup.figure.horizontalCoordinate .outfielder <
      setup.figure.horizontalCoordinate .bouncePoint
  bouncePointBeforeCatcher :
    setup.figure.horizontalCoordinate .bouncePoint <
      setup.figure.horizontalCoordinate .catcher
  oneBounceSegmentsAreBlue :
    setup.figure.trajectoryColor .beforeBounce = .blue ∧
      setup.figure.trajectoryColor .afterBounce = .blue
  noBounceTrajectoryIsGreen :
    setup.figure.trajectoryColor .directNoBounce = .green
  everyTrajectoryIsDashed :
    ∀ segment, setup.figure.showsDashedTrajectory segment = true
  everyLaunchArrowIsShown :
    ∀ segment, setup.figure.showsInitialVelocityArrow segment = true
  thetaShownAtOutfielder :
    setup.figure.showsAngleLabelAt .outfielder .theta = true
  thetaShownAtBouncePoint :
    setup.figure.showsAngleLabelAt .bouncePoint .theta = true
  fortyFiveDegreesShownAtOutfielder :
    setup.figure.showsAngleLabelAt
      .outfielder .fortyFiveDegrees = true
  horizontalGroundShown : setup.figure.showsHorizontalGroundLine = true
  distanceDShown : setup.figure.showsDistanceLabelD = true

/-!
Problem-statement data and the comparison convention implicit in the figure.
The no-bounce throw and the first leg of the one-bounce throw start with the
same speed.  The second blue leg leaves the bounce with half the incoming
impact speed and at the same angle `θ` as the first blue leg.  The direct green
throw is at `45°`.  The ideal-motion laws below separately relate the incoming
impact speed to the first launch speed.

The range equations state only that both routes connect the same endpoints;
they do not prescribe the requested time ratio.
-/
structure MatchesBaseballThrowScenario
    (setup : BaseballOneBounceSetup) : Prop where
  exactlyOneBounce : setup.oneBounceThrowGroundImpacts = 1
  equalEndpointElevations :
    setup.everyArcHasEqualLaunchAndLandingHeight = true
  directThrowUsesFortyFiveDegrees :
    setup.launchAngle .directNoBounce =
      ((Real.pi / 4 : ℝ) : Real.Angle)
  blueSegmentsUseSameAngle :
    setup.launchAngle .afterBounce = setup.launchAngle .beforeBounce
  blueAngleIsBelowFortyFiveDegrees :
    0 < (setup.launchAngle .beforeBounce).toReal ∧
      (setup.launchAngle .beforeBounce).toReal < Real.pi / 4
  equalInitialComparisonSpeeds :
    setup.launchSpeed .beforeBounce = setup.launchSpeed .directNoBounce
  reboundSpeedIsOneHalfOfIncomingSpeed :
    speedInMetersPerSecond (setup.launchSpeed .afterBounce) =
      (1 / 2 : ℝ) *
        speedInMetersPerSecond setup.incomingSpeedAtBounce
  directRouteSpansD :
    lengthInMeters (setup.horizontalRange .directNoBounce) =
      lengthInMeters setup.distanceD
  oneBounceRangesSpanD :
    lengthInMeters (setup.horizontalRange .beforeBounce) +
        lengthInMeters (setup.horizontalRange .afterBounce) =
      lengthInMeters setup.distanceD

/-- Positivity and nondegeneracy conditions for the physical setup. -/
structure HasPhysicalBaseballThrowParameters
    (setup : BaseballOneBounceSetup) : Prop where
  distancePositive : 0 < lengthInMeters setup.distanceD
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravity
  everySpeedPositive :
    ∀ segment, 0 < speedInMetersPerSecond (setup.launchSpeed segment)
  incomingSpeedAtBouncePositive :
    0 < speedInMetersPerSecond setup.incomingSpeedAtBounce
  everyRangePositive :
    ∀ segment, 0 < lengthInMeters (setup.horizontalRange segment)
  everyDurationPositive :
    ∀ segment, 0 < durationInSeconds (setup.flightDuration segment)

/-!
Standard ideal-projectile relations for an arc whose launch and landing
heights are equal, with no aerodynamic drag and uniform downward gravity:

* speed magnitude on returning to the launch height equals launch speed;
* horizontal range is `v² sin (2 α) / g`;
* flight time is `2 v sin α / g`.

They are stated as general relations for all three arcs and contain neither
the requested time ratio nor any answer-choice value.
-/
structure SatisfiesIdealLevelGroundProjectileLaws
    (setup : BaseballOneBounceSetup) : Prop where
  /-- With no drag, an arc returning to its launch height has the same speed
  magnitude on landing as on launch. -/
  incomingSpeedAtBounceEqualsFirstLaunchSpeed :
    speedInMetersPerSecond setup.incomingSpeedAtBounce =
      speedInMetersPerSecond (setup.launchSpeed .beforeBounce)
  levelGroundRangeLaw : ∀ segment,
    lengthInMeters (setup.horizontalRange segment) =
      speedInMetersPerSecond (setup.launchSpeed segment) ^ 2 *
          Real.Angle.sin (2 • setup.launchAngle segment) /
        accelerationInMetersPerSecondSquared setup.gravity
  levelGroundFlightTimeLaw : ∀ segment,
    durationInSeconds (setup.flightDuration segment) =
      2 * speedInMetersPerSecond (setup.launchSpeed segment) *
          Real.Angle.sin (setup.launchAngle segment) /
        accelerationInMetersPerSecondSquared setup.gravity

/-! ## Requested dimensionless ratio and displayed answers -/

/-- Total time in seconds for the two blue legs of the one-bounce throw. -/
def oneBounceFlightTimeInSeconds
    (setup : BaseballOneBounceSetup) : ℝ :=
  durationInSeconds (setup.flightDuration .beforeBounce) +
    durationInSeconds (setup.flightDuration .afterBounce)

/-- Flight time in seconds for the green direct throw. -/
def noBounceFlightTimeInSeconds
    (setup : BaseballOneBounceSetup) : ℝ :=
  durationInSeconds (setup.flightDuration .directNoBounce)

/-- The dimensionless ratio requested in the question. -/
def oneBounceToNoBounceTimeRatio
    (setup : BaseballOneBounceSetup) : ℝ :=
  oneBounceFlightTimeInSeconds setup /
    noBounceFlightTimeInSeconds setup

/-- Labels of the four numerical answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless time ratio printed beside each answer label. -/
def AnswerChoice.displayedRatio : AnswerChoice → ℝ
  | .A => 870 / 1000
  | .B => 647 / 1000
  | .C => 949 / 1000
  | .D => 511 / 1000

/-- Answer label recorded by the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Agreement with an answer displayed to three decimal places. -/
def MatchesDisplayedThreeDecimalRatio
    (setup : BaseballOneBounceSetup) (choice : AnswerChoice) : Prop :=
  |oneBounceToNoBounceTimeRatio setup - choice.displayedRatio| <
    (1 / 2000 : ℝ)

/-- The selected displayed value is strictly closer than every alternative. -/
def IsUniqueClosestDisplayedRatio
    (setup : BaseballOneBounceSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |oneBounceToNoBounceTimeRatio setup - choice.displayedRatio| <
      |oneBounceToNoBounceTimeRatio setup - other.displayedRatio|

/-!
Equal total ranges and the half-speed rebound force the lower blue launch
angle to satisfy `sin θ = 1 / sqrt 5`.  This is a derived statement, not a
premise of the physical model.
-/
lemma bounceLaunchAngleSine_exact
    (setup : BaseballOneBounceSetup)
    (_scenario : MatchesBaseballThrowScenario setup)
    (_physical : HasPhysicalBaseballThrowParameters setup)
    (_laws : SatisfiesIdealLevelGroundProjectileLaws setup) :
    Real.Angle.sin (setup.launchAngle .beforeBounce) =
      1 / Real.sqrt 5 := by
  have hspeed_after :
      speedInMetersPerSecond (setup.launchSpeed .afterBounce) =
        (1 / 2 : ℝ) *
          speedInMetersPerSecond (setup.launchSpeed .beforeBounce) := by
    rw [_scenario.reboundSpeedIsOneHalfOfIncomingSpeed,
      _laws.incomingSpeedAtBounceEqualsFirstLaunchSpeed]
  have hspeed_before_direct :
      speedInMetersPerSecond (setup.launchSpeed .beforeBounce) =
        speedInMetersPerSecond (setup.launchSpeed .directNoBounce) :=
    congrArg speedInMetersPerSecond _scenario.equalInitialComparisonSpeeds
  have hranges :
      lengthInMeters (setup.horizontalRange .beforeBounce) +
          lengthInMeters (setup.horizontalRange .afterBounce) =
        lengthInMeters (setup.horizontalRange .directNoBounce) := by
    rw [_scenario.oneBounceRangesSpanD, _scenario.directRouteSpansD]
  rw [_laws.levelGroundRangeLaw .beforeBounce,
    _laws.levelGroundRangeLaw .afterBounce,
    _laws.levelGroundRangeLaw .directNoBounce] at hranges
  have hsin45 :
      Real.Angle.sin (2 • (((Real.pi / 4 : ℝ)) : Real.Angle)) = 1 := by
    rw [Real.Angle.sin_two_nsmul, Real.Angle.sin_coe,
      Real.Angle.cos_coe, Real.sin_pi_div_four, Real.cos_pi_div_four]
    have h2 : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    norm_num [nsmul_eq_mul]
    nlinarith
  rw [_scenario.blueSegmentsUseSameAngle, hspeed_after,
    hspeed_before_direct, _scenario.directThrowUsesFortyFiveDegrees,
    hsin45] at hranges
  have hdouble :
      Real.Angle.sin (2 • setup.launchAngle .beforeBounce) = 4 / 5 := by
    have hv :
        0 < speedInMetersPerSecond (setup.launchSpeed .directNoBounce) :=
      _physical.everySpeedPositive .directNoBounce
    have hg :
        0 < accelerationInMetersPerSecondSquared setup.gravity :=
      _physical.gravityPositive
    field_simp [ne_of_gt hg] at hranges
    have hv2 :
        0 <
          speedInMetersPerSecond (setup.launchSpeed .directNoBounce) ^ 2 :=
      sq_pos_of_pos hv
    nlinarith
  have hθ := _scenario.blueAngleIsBelowFortyFiveDegrees
  have hsin_pos :
      0 < Real.Angle.sin (setup.launchAngle .beforeBounce) := by
    rw [← Real.Angle.sin_toReal]
    exact Real.sin_pos_of_pos_of_lt_pi hθ.1
      (by nlinarith [hθ.2, Real.pi_pos])
  have hcos_pos :
      0 < Real.Angle.cos (setup.launchAngle .beforeBounce) := by
    rw [← Real.Angle.cos_toReal]
    exact Real.cos_pos_of_mem_Ioo
      (by constructor <;> nlinarith [hθ.1, hθ.2, Real.pi_pos])
  have hsin_lt_cos :
      Real.Angle.sin (setup.launchAngle .beforeBounce) <
        Real.Angle.cos (setup.launchAngle .beforeBounce) := by
    rw [← Real.Angle.sin_toReal, ← Real.Angle.cos_toReal,
      ← Real.sin_pi_div_two_sub]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (by nlinarith [hθ.1, Real.pi_pos])
      (by nlinarith [hθ.1])
      (by nlinarith [hθ.2])
  rw [Real.Angle.sin_two_nsmul] at hdouble
  norm_num [nsmul_eq_mul] at hdouble
  have hcircle :=
    Real.Angle.cos_sq_add_sin_sq (setup.launchAngle .beforeBounce)
  have hsin_sq_lt_cos_sq :
      Real.Angle.sin (setup.launchAngle .beforeBounce) ^ 2 <
        Real.Angle.cos (setup.launchAngle .beforeBounce) ^ 2 :=
    (sq_lt_sq₀ hsin_pos.le hcos_pos.le).2 hsin_lt_cos
  have hsin_sq :
      Real.Angle.sin (setup.launchAngle .beforeBounce) ^ 2 = 1 / 5 := by
    nlinarith [sq_nonneg
      (Real.Angle.sin (setup.launchAngle .beforeBounce) -
        Real.Angle.cos (setup.launchAngle .beforeBounce)),
      sq_nonneg
      (Real.Angle.sin (setup.launchAngle .beforeBounce) +
        Real.Angle.cos (setup.launchAngle .beforeBounce))]
  have hsqrt_pos : 0 < Real.sqrt 5 :=
    Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  rw [eq_div_iff hsqrt_pos.ne']
  nlinarith [sq_nonneg
    (Real.Angle.sin (setup.launchAngle .beforeBounce) *
      Real.sqrt 5 - 1),
    sq_nonneg
    (Real.Angle.sin (setup.launchAngle .beforeBounce) *
      Real.sqrt 5 + 1)]

/-!
Adding the two blue flight times and comparing with the green `45°` flight
gives the exact dimensionless ratio `3 / sqrt 10`.
-/
lemma oneBounceToNoBounceTimeRatio_exact
    (setup : BaseballOneBounceSetup)
    (_scenario : MatchesBaseballThrowScenario setup)
    (_physical : HasPhysicalBaseballThrowParameters setup)
    (_laws : SatisfiesIdealLevelGroundProjectileLaws setup) :
    oneBounceToNoBounceTimeRatio setup = 3 / Real.sqrt 10 := by
  have hspeed_after :
      speedInMetersPerSecond (setup.launchSpeed .afterBounce) =
        (1 / 2 : ℝ) *
          speedInMetersPerSecond (setup.launchSpeed .beforeBounce) := by
    rw [_scenario.reboundSpeedIsOneHalfOfIncomingSpeed,
      _laws.incomingSpeedAtBounceEqualsFirstLaunchSpeed]
  have hspeed_before_direct :
      speedInMetersPerSecond (setup.launchSpeed .beforeBounce) =
        speedInMetersPerSecond (setup.launchSpeed .directNoBounce) :=
    congrArg speedInMetersPerSecond _scenario.equalInitialComparisonSpeeds
  have hsin :=
    bounceLaunchAngleSine_exact setup _scenario _physical _laws
  rw [oneBounceToNoBounceTimeRatio, oneBounceFlightTimeInSeconds,
    noBounceFlightTimeInSeconds,
    _laws.levelGroundFlightTimeLaw .beforeBounce,
    _laws.levelGroundFlightTimeLaw .afterBounce,
    _laws.levelGroundFlightTimeLaw .directNoBounce,
    _scenario.blueSegmentsUseSameAngle, hspeed_after,
    hspeed_before_direct, _scenario.directThrowUsesFortyFiveDegrees,
    hsin, Real.Angle.sin_coe, Real.sin_pi_div_four]
  have hv :
      0 < speedInMetersPerSecond (setup.launchSpeed .directNoBounce) :=
    _physical.everySpeedPositive .directNoBounce
  have hg :
      0 < accelerationInMetersPerSecondSquared setup.gravity :=
    _physical.gravityPositive
  have hsqrt2 : 0 < Real.sqrt 2 :=
    Real.sqrt_pos.2 (by norm_num)
  have hsqrt5 : 0 < Real.sqrt 5 :=
    Real.sqrt_pos.2 (by norm_num)
  have hsqrt10 : Real.sqrt 10 = Real.sqrt 5 * Real.sqrt 2 := by
    rw [show (10 : ℝ) = 5 * 2 by norm_num,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5)]
  rw [hsqrt10]
  field_simp [hv.ne', hg.ne', hsqrt2.ne', hsqrt5.ne']
  ring

/-!
The exact ratio is approximately `0.948683`, so its three-decimal display is
`0.949`, uniquely selecting answer C.

This formalizes blueprint label `thm:physics:phyx_mini_0693:target`.
-/
theorem problem_phyx_mini_0693
    (setup : BaseballOneBounceSetup)
    (_figure : MatchesPrimaryBaseballFigure setup)
    (_scenario : MatchesBaseballThrowScenario setup)
    (_physical : HasPhysicalBaseballThrowParameters setup)
    (_laws : SatisfiesIdealLevelGroundProjectileLaws setup) :
    oneBounceToNoBounceTimeRatio setup = 3 / Real.sqrt 10 ∧
      MatchesDisplayedThreeDecimalRatio setup .C ∧
      IsUniqueClosestDisplayedRatio setup .C := by
  have hexact :=
    oneBounceToNoBounceTimeRatio_exact setup _scenario _physical _laws
  have hsqrt_pos : 0 < Real.sqrt 10 :=
    Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : Real.sqrt 10 ^ 2 = (10 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hlower : (1897 / 2000 : ℝ) < 3 / Real.sqrt 10 := by
    rw [lt_div_iff₀ hsqrt_pos]
    nlinarith [sq_nonneg (1897 * Real.sqrt 10 - 6000)]
  have hupper : 3 / Real.sqrt 10 < (949 / 1000 : ℝ) := by
    rw [div_lt_iff₀ hsqrt_pos]
    nlinarith [sq_nonneg (949 * Real.sqrt 10 - 3000)]
  refine ⟨hexact, ?_, ?_⟩
  · unfold MatchesDisplayedThreeDecimalRatio
    rw [hexact]
    change |3 / Real.sqrt 10 - 949 / 1000| < (1 / 2000 : ℝ)
    rw [abs_lt]
    constructor <;> linarith
  · intro other hother
    rw [hexact]
    cases other with
    | A =>
        change
          |3 / Real.sqrt 10 - 949 / 1000| <
            |3 / Real.sqrt 10 - 870 / 1000|
        rw [abs_of_neg (by linarith), abs_of_pos (by linarith)]
        linarith
    | B =>
        change
          |3 / Real.sqrt 10 - 949 / 1000| <
            |3 / Real.sqrt 10 - 647 / 1000|
        rw [abs_of_neg (by linarith), abs_of_pos (by linarith)]
        linarith
    | C =>
        exact False.elim (hother rfl)
    | D =>
        change
          |3 / Real.sqrt 10 - 949 / 1000| <
            |3 / Real.sqrt 10 - 511 / 1000|
        rw [abs_of_neg (by linarith), abs_of_pos (by linarith)]
        linarith

end PhyXMiniProblems.ProblemPhyXMini0693
