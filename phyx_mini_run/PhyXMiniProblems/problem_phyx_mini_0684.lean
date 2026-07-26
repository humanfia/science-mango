import Mathlib
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0684

open Dimension

/-!
# One-twelfth scale model of a horizontal-channel waterfall

Water leaves a horizontal channel at the top of a wall, falls under gravity,
and lands in a lower pool.  A geometrically similar model is built at one
twelfth of every actual length.  Vertical free fall and uniform horizontal
motion determine the reduction in the channel-flow speed.

Lengths, durations, speed, and acceleration below are unit-independent
Physlib quantities.  Real numbers occur only as coherent-SI readouts,
dimensionless scale factors, schematic figure coordinates, and printed answer
values.  In particular, the model speed is an independent field and is not
defined to be the requested answer.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- Acceleration has physical dimension `L T⁻²`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical duration. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative, unit-independent acceleration magnitude. -/
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
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  nonnegativeSIReadout duration

/-- Metre-per-second readout of a speed magnitude. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  nonnegativeSIReadout speed

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  nonnegativeSIReadout acceleration

/-! ## Physical roles and primary-figure vocabulary -/

/-- Orientation of a channel at the point where its water leaves the lip. -/
inductive ChannelOrientation where
  | horizontal
  | other
  deriving DecidableEq, Repr

/-- Region into which the falling water is intended to land. -/
inductive ReceivingRegion where
  | lowerPool
  | other
  deriving DecidableEq, Repr

/-- Literal height label visible beside the double-headed arrow in the figure. -/
inductive FigureHeightLabel where
  | h
  deriving DecidableEq, Repr

/-!
The physical information transcribed from the supplied raster.  The figure
shows a horizontal upper channel, its lip at the top of a vertical wall, the
lower pool, the curved water path, and a vertical double-headed arrow labelled
`h`.  The labelled height is itself a dimensionful length.
-/
structure WaterfallFigure where
  labelledHeight : LengthQuantity
  heightArrowLabel : FigureHeightLabel
  showsHorizontalUpperChannel : Bool
  showsVerticalWall : Bool
  showsLowerPool : Bool
  showsCurvedWaterPath : Bool
  showsVerticalDoubleHeadedArrow : Bool

/-!
A physical realization of the waterfall.  Fall time and horizontal landing
range are independent quantities used by the kinematic laws; neither is fixed
by definition from the requested speed.
-/
structure WaterfallRealization where
  wallHeight : LengthQuantity
  channelFlowSpeed : SpeedQuantity
  fallTime : TimeQuantity
  horizontalLandingRange : LengthQuantity
  channelOrientation : ChannelOrientation
  receivingRegion : ReceivingRegion

/-!
The actual installation and its scale model experience the same local
gravitational acceleration.  `lengthScaleFactor` is dimensionless.
-/
structure WaterfallScaleSetup where
  figure : WaterfallFigure
  actual : WaterfallRealization
  model : WaterfallRealization
  gravitationalAcceleration : AccelerationQuantity
  lengthScaleFactor : ℝ

/-!
Primary-image evidence.  These fields transcribe objects and the label shown
in the raster and identify its labelled height with the actual wall height;
they impose no requested model-speed value.
-/
structure MatchesPrimaryFigure (setup : WaterfallScaleSetup) : Prop where
  labelledHeightIsActualWallHeight :
    setup.figure.labelledHeight = setup.actual.wallHeight
  arrowIsLabelledH : setup.figure.heightArrowLabel = .h
  horizontalUpperChannelShown :
    setup.figure.showsHorizontalUpperChannel = true
  verticalWallShown : setup.figure.showsVerticalWall = true
  lowerPoolShown : setup.figure.showsLowerPool = true
  curvedWaterPathShown : setup.figure.showsCurvedWaterPath = true
  verticalDoubleHeadedArrowShown :
    setup.figure.showsVerticalDoubleHeadedArrow = true

/-!
Numerical and qualitative data stated in the problem.  The actual channel
speed is `1.70 m/s`, the arrow height is `2.35 m`, and the model is described
as one-twelfth actual size.  No model-speed readout occurs here.
-/
structure MatchesProblemDescription (setup : WaterfallScaleSetup) : Prop where
  actualWallHeightMeters :
    lengthInMeters setup.actual.wallHeight = 2.35
  actualChannelSpeedMetersPerSecond :
    speedInMetersPerSecond setup.actual.channelFlowSpeed = 1.70
  actualChannelIsHorizontal :
    setup.actual.channelOrientation = .horizontal
  actualWaterLandsInLowerPool :
    setup.actual.receivingRegion = .lowerPool
  oneTwelfthLengthScale :
    setup.lengthScaleFactor = (1 / 12 : ℝ)

/-!
Positivity and nondegeneracy conditions for the two physical falls.  Although
the underlying Physlib quantities are nonnegative, strict positivity is
recorded where later cancellation and square-root reasoning require it.
-/
structure HasPhysicalParameters (setup : WaterfallScaleSetup) : Prop where
  actualWallHeightPositive :
    0 < lengthInMeters setup.actual.wallHeight
  modelWallHeightPositive :
    0 < lengthInMeters setup.model.wallHeight
  actualFallTimePositive :
    0 < timeInSeconds setup.actual.fallTime
  modelFallTimePositive :
    0 < timeInSeconds setup.model.fallTime
  actualHorizontalRangePositive :
    0 < lengthInMeters setup.actual.horizontalLandingRange
  modelHorizontalRangePositive :
    0 < lengthInMeters setup.model.horizontalLandingRange
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  lengthScaleFactorPositive : 0 < setup.lengthScaleFactor

/-! ## Governing kinematic and similarity laws -/

/-!
For each realization, water has zero initial vertical speed, undergoes
constant-gravity vertical free fall, and retains its horizontal channel speed.
The relations are written in coherent SI readouts so their scalar equations
are dimensionally homogeneous.  They contain no numerical model speed.
-/
structure SatisfiesHorizontalWaterfallKinematics
    (setup : WaterfallScaleSetup) : Prop where
  actualVerticalFreeFall :
    lengthInMeters setup.actual.wallHeight =
      (1 / 2 : ℝ) *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration *
        timeInSeconds setup.actual.fallTime ^ 2
  actualUniformHorizontalMotion :
    lengthInMeters setup.actual.horizontalLandingRange =
      speedInMetersPerSecond setup.actual.channelFlowSpeed *
        timeInSeconds setup.actual.fallTime
  modelVerticalFreeFall :
    lengthInMeters setup.model.wallHeight =
      (1 / 2 : ℝ) *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration *
        timeInSeconds setup.model.fallTime ^ 2
  modelUniformHorizontalMotion :
    lengthInMeters setup.model.horizontalLandingRange =
      speedInMetersPerSecond setup.model.channelFlowSpeed *
        timeInSeconds setup.model.fallTime

/-!
Standard geometric similarity scales every relevant length by the common
dimensionless factor and preserves the qualitative channel/pool geometry.
Scaling the landing range, rather than merely the wall height, records that
the entire water trajectory is to have the same shape in the model.
-/
structure SatisfiesStandardScaleGeometry
    (setup : WaterfallScaleSetup) : Prop where
  wallHeightScales :
    lengthInMeters setup.model.wallHeight =
      setup.lengthScaleFactor *
        lengthInMeters setup.actual.wallHeight
  horizontalLandingRangeScales :
    lengthInMeters setup.model.horizontalLandingRange =
      setup.lengthScaleFactor *
        lengthInMeters setup.actual.horizontalLandingRange
  channelOrientationPreserved :
    setup.model.channelOrientation = setup.actual.channelOrientation
  receivingRegionPreserved :
    setup.model.receivingRegion = setup.actual.receivingRegion

/-! ## Displayed choices and target -/

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Metre-per-second value printed beside each displayed answer choice. -/
def AnswerChoice.speedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 0.325
  | .B => 0.120
  | .C => 0.491
  | .D => 0.212

/-!
Rounding to the nearest `0.001` is represented by an error strictly less than
half of that unit.  The exact ideal-model speed is not exactly the decimal
`0.491`, so making this precision convention explicit avoids a false equality.
-/
def RoundsToThreeDecimalPlaces (value displayedValue : ℝ) : Prop :=
  |value - displayedValue| < (1 / 2000 : ℝ)

/-!
Eliminating the two positive fall times from the free-fall, horizontal-motion,
and geometric-similarity laws gives

`v_model = v_actual * sqrt(lengthScaleFactor)`.

At a length scale of `1/12` and an actual speed of `1.70 m/s`, this value is
approximately `0.49075 m/s`, which rounds to the `0.491 m/s` printed for
choice C.

Blueprint label: `thm:physics:phyx_mini_0684:target`.
-/
theorem problem_phyx_mini_0684
    (setup : WaterfallScaleSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_description : MatchesProblemDescription setup)
    (_physical : HasPhysicalParameters setup)
    (_kinematics : SatisfiesHorizontalWaterfallKinematics setup)
    (_scaleGeometry : SatisfiesStandardScaleGeometry setup) :
    speedInMetersPerSecond setup.model.channelFlowSpeed =
        speedInMetersPerSecond setup.actual.channelFlowSpeed *
          Real.sqrt setup.lengthScaleFactor ∧
      RoundsToThreeDecimalPlaces
        (speedInMetersPerSecond setup.model.channelFlowSpeed)
        (AnswerChoice.speedInMetersPerSecond .C) := by
  have htime_sq :
      timeInSeconds setup.model.fallTime ^ 2 =
        setup.lengthScaleFactor *
          timeInSeconds setup.actual.fallTime ^ 2 := by
    apply mul_left_cancel₀
      (show
        (1 / 2 : ℝ) *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration ≠ 0 by
        exact mul_ne_zero (by norm_num)
          (ne_of_gt _physical.gravitationalAccelerationPositive))
    calc
      ((1 / 2 : ℝ) *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration) *
          timeInSeconds setup.model.fallTime ^ 2 =
          lengthInMeters setup.model.wallHeight :=
        _kinematics.modelVerticalFreeFall.symm
      _ =
          setup.lengthScaleFactor *
            lengthInMeters setup.actual.wallHeight :=
        _scaleGeometry.wallHeightScales
      _ =
          setup.lengthScaleFactor *
            (((1 / 2 : ℝ) *
                accelerationInMetersPerSecondSquared
                  setup.gravitationalAcceleration) *
              timeInSeconds setup.actual.fallTime ^ 2) := by
        rw [_kinematics.actualVerticalFreeFall]
      _ =
          ((1 / 2 : ℝ) *
              accelerationInMetersPerSecondSquared
                setup.gravitationalAcceleration) *
            (setup.lengthScaleFactor *
              timeInSeconds setup.actual.fallTime ^ 2) := by
        ring
  have hsqrt_pos :
      0 < Real.sqrt setup.lengthScaleFactor :=
    Real.sqrt_pos.2 _physical.lengthScaleFactorPositive
  have hsqrt_sq :
      Real.sqrt setup.lengthScaleFactor ^ 2 =
        setup.lengthScaleFactor :=
    Real.sq_sqrt (le_of_lt _physical.lengthScaleFactorPositive)
  have htime_sq' :
      timeInSeconds setup.model.fallTime ^ 2 =
        (Real.sqrt setup.lengthScaleFactor *
          timeInSeconds setup.actual.fallTime) ^ 2 := by
    rw [mul_pow, hsqrt_sq]
    exact htime_sq
  have htime :
      timeInSeconds setup.model.fallTime =
        Real.sqrt setup.lengthScaleFactor *
          timeInSeconds setup.actual.fallTime := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp htime_sq' with h | h
    · exact h
    · nlinarith [
        mul_pos hsqrt_pos _physical.actualFallTimePositive,
        _physical.modelFallTimePositive]
  have hrange :
      speedInMetersPerSecond setup.model.channelFlowSpeed *
          timeInSeconds setup.model.fallTime =
        setup.lengthScaleFactor *
          (speedInMetersPerSecond setup.actual.channelFlowSpeed *
            timeInSeconds setup.actual.fallTime) := by
    calc
      speedInMetersPerSecond setup.model.channelFlowSpeed *
          timeInSeconds setup.model.fallTime =
          lengthInMeters setup.model.horizontalLandingRange :=
        _kinematics.modelUniformHorizontalMotion.symm
      _ =
          setup.lengthScaleFactor *
            lengthInMeters setup.actual.horizontalLandingRange :=
        _scaleGeometry.horizontalLandingRangeScales
      _ =
          setup.lengthScaleFactor *
            (speedInMetersPerSecond setup.actual.channelFlowSpeed *
              timeInSeconds setup.actual.fallTime) := by
        rw [_kinematics.actualUniformHorizontalMotion]
  have hcancel_time :
      speedInMetersPerSecond setup.model.channelFlowSpeed *
          Real.sqrt setup.lengthScaleFactor =
        setup.lengthScaleFactor *
          speedInMetersPerSecond setup.actual.channelFlowSpeed := by
    apply mul_right_cancel₀
      (ne_of_gt _physical.actualFallTimePositive)
    calc
      (speedInMetersPerSecond setup.model.channelFlowSpeed *
            Real.sqrt setup.lengthScaleFactor) *
          timeInSeconds setup.actual.fallTime =
          speedInMetersPerSecond setup.model.channelFlowSpeed *
            timeInSeconds setup.model.fallTime := by
        rw [htime]
        ring
      _ =
          setup.lengthScaleFactor *
            (speedInMetersPerSecond setup.actual.channelFlowSpeed *
              timeInSeconds setup.actual.fallTime) :=
        hrange
      _ =
          (setup.lengthScaleFactor *
              speedInMetersPerSecond setup.actual.channelFlowSpeed) *
            timeInSeconds setup.actual.fallTime := by
        ring
  have hspeed :
      speedInMetersPerSecond setup.model.channelFlowSpeed =
        speedInMetersPerSecond setup.actual.channelFlowSpeed *
          Real.sqrt setup.lengthScaleFactor := by
    apply mul_right_cancel₀ (ne_of_gt hsqrt_pos)
    calc
      speedInMetersPerSecond setup.model.channelFlowSpeed *
          Real.sqrt setup.lengthScaleFactor =
          setup.lengthScaleFactor *
            speedInMetersPerSecond setup.actual.channelFlowSpeed :=
        hcancel_time
      _ =
          Real.sqrt setup.lengthScaleFactor ^ 2 *
            speedInMetersPerSecond setup.actual.channelFlowSpeed := by
        rw [hsqrt_sq]
      _ =
          (speedInMetersPerSecond setup.actual.channelFlowSpeed *
              Real.sqrt setup.lengthScaleFactor) *
            Real.sqrt setup.lengthScaleFactor := by
        ring
  constructor
  · exact hspeed
  · unfold RoundsToThreeDecimalPlaces
    rw [hspeed, _description.actualChannelSpeedMetersPerSecond,
      _description.oneTwelfthLengthScale]
    change
      |(1.70 : ℝ) * Real.sqrt (1 / 12 : ℝ) - 0.491| <
        (1 / 2000 : ℝ)
    have hsqrt_nonneg :
        0 ≤ Real.sqrt (1 / 12 : ℝ) :=
      Real.sqrt_nonneg _
    have hsqrt_sq_numeric :
        Real.sqrt (1 / 12 : ℝ) ^ 2 = (1 / 12 : ℝ) := by
      rw [Real.sq_sqrt]
      norm_num
    have hlower_sq :
        (981 / 3400 : ℝ) ^ 2 < (1 / 12 : ℝ) := by
      norm_num
    have hupper_sq :
        (1 / 12 : ℝ) < (983 / 3400 : ℝ) ^ 2 := by
      norm_num
    have hlower :
        (981 / 3400 : ℝ) < Real.sqrt (1 / 12 : ℝ) := by
      nlinarith
    have hupper :
        Real.sqrt (1 / 12 : ℝ) < (983 / 3400 : ℝ) := by
      nlinarith
    rw [abs_lt]
    constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0684
