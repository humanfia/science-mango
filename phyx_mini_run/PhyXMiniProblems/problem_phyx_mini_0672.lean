import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0672

open Dimension

/-!
# Distance travelled from a velocity--time graph

An object starts at `x = 0 m` when `t = 0 s`.  The primary bitmap plots its
signed x-velocity in metres per second from `0 s` through `18 s`.  The curve is
piecewise linear through the points

`(0,-12)`, `(4,-12)`, `(9,18)`, `(13,18)`, and `(18,0)`.

This differs from the auxiliary prose caption, which reports different knots
and stops at `15 s`.  The declarations below use the primary bitmap, as the
chapter instructs.  Position, time, signed velocity, and total distance remain
dimensionful Physlib quantities.  Real numbers occur only as explicitly named
SI coordinate readouts and displayed answer values.

Assumption/target split:

* `MatchesProblemStatement` records the initial position and queried times;
* `MatchesSuppliedVelocityTimeFigure` records the axes, units, labels, and the
  velocity curve read directly from the bitmap;
* `SatisfiesOneDimensionalKinematics` states that velocity is the derivative of
  position and that distance over any ordered time interval is the integral of
  speed; and
* only `problem_phyx_mini_0672` concludes the requested `204 m` distance and
  selection of displayed answer C.
-/

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- A signed position on the x-axis, with physical dimension length. -/
abbrev SignedPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical time or duration. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A signed x-component of velocity, with dimension length per time. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A nonnegative total path length. -/
abbrev DistanceQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- Metre readout of a signed x-position. -/
def positionInMeters (position : SignedPositionQuantity) : ℝ :=
  (position UnitChoices.SI).val

/-- Second readout of a physical time. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  ((time UnitChoices.SI).val : ℝ)

/-- Metre-per-second readout of a signed x-velocity. -/
def velocityInMetersPerSecond (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity UnitChoices.SI).val

/-- Metre readout of a nonnegative total distance. -/
def distanceInMeters (distance : DistanceQuantity) : ℝ :=
  ((distance UnitChoices.SI).val : ℝ)

/-! ## Physical motion and primary-figure vocabulary -/

/-- Physical quantities assigned to the two graph axes. -/
inductive AxisQuantity where
  | time
  | xVelocity
  deriving DecidableEq, Repr

/-- Units printed beside the graph axes. -/
inductive AxisUnit where
  | seconds
  | metersPerSecond
  deriving DecidableEq, Repr

/-- Qualitative geometry of the thick plotted trace. -/
inductive VelocityCurveShape where
  | continuousPiecewiseLinear
  deriving DecidableEq, Repr

/-- Color of the velocity trace in the supplied raster. -/
inductive CurveColor where
  | brown
  deriving DecidableEq, Repr

/-!
Typed transcription of the velocity--time plot.  Its real argument is a time
coordinate read in seconds, while the plotted ordinate remains a dimensionful
signed velocity.
-/
structure VelocityTimeFigure where
  horizontalAxisQuantity : AxisQuantity
  verticalAxisQuantity : AxisQuantity
  horizontalAxisUnit : AxisUnit
  verticalAxisUnit : AxisUnit
  horizontalAxisLabel : String
  verticalAxisLabel : String
  displayedTimeTicksSeconds : List ℝ
  displayedVelocityTicksMetersPerSecond : List ℝ
  labeledTimeTickSpacingSeconds : ℝ
  labeledVelocityTickSpacingMetersPerSecond : ℝ
  curveShape : VelocityCurveShape
  curveColor : CurveColor
  velocityAtSeconds : ℝ → SignedVelocityQuantity

/-!
The one-dimensional motion and the independent total-distance observable.
`positionAtSeconds` is indexed by the numerical SI time coordinate needed for
calculus.  The two queried endpoints themselves remain physical times.
-/
structure OneDimensionalMotion where
  positionAtSeconds : ℝ → SignedPositionQuantity
  figure : VelocityTimeFigure
  queryStartTime : TimeQuantity
  queryEndTime : TimeQuantity
  totalDistanceTravelled : TimeQuantity → TimeQuantity → DistanceQuantity

/-! ## Exact primary-image readout -/

/-!
Velocity readout represented by the thick brown graph in image `672.png`.

The line is constant at `-12 m/s` through `4 s`, rises with slope
`6 m/s²` to `18 m/s` at `9 s`, stays there through `13 s`, and then falls
linearly to zero at `18 s`.
-/
def plottedVelocityMetersPerSecond (timeSeconds : ℝ) : ℝ :=
  if timeSeconds ≤ 4 then
    -12
  else if timeSeconds ≤ 9 then
    6 * timeSeconds - 36
  else if timeSeconds ≤ 13 then
    18
  else
    (18 / 5) * (18 - timeSeconds)

/-!
Axis metadata and quantitative curve data read from the primary bitmap.  The
velocity equality is restricted to the displayed interval, so this predicate
makes no assertion about an unplotted continuation of the motion.
-/
structure MatchesSuppliedVelocityTimeFigure
    (figure : VelocityTimeFigure) : Prop where
  horizontalAxisIsTime : figure.horizontalAxisQuantity = .time
  verticalAxisIsXVelocity : figure.verticalAxisQuantity = .xVelocity
  horizontalAxisUsesSeconds : figure.horizontalAxisUnit = .seconds
  verticalAxisUsesMetersPerSecond :
    figure.verticalAxisUnit = .metersPerSecond
  horizontalLabel : figure.horizontalAxisLabel = "t (s)"
  verticalLabel : figure.verticalAxisLabel = "vₓ (m/s)"
  displayedTimeTicks : figure.displayedTimeTicksSeconds = [0, 5, 10, 15]
  displayedVelocityTicks :
    figure.displayedVelocityTicksMetersPerSecond = [-10, 10, 20]
  labeledTimeSpacing : figure.labeledTimeTickSpacingSeconds = 5
  labeledVelocitySpacing :
    figure.labeledVelocityTickSpacingMetersPerSecond = 10
  displayedCurveShape : figure.curveShape = .continuousPiecewiseLinear
  displayedCurveColor : figure.curveColor = .brown
  velocityTraceMatchesImage : ∀ timeSeconds ∈ Set.Icc (0 : ℝ) 18,
    velocityInMetersPerSecond (figure.velocityAtSeconds timeSeconds) =
      plottedVelocityMetersPerSecond timeSeconds

/-!
The stated initial condition and requested physical time interval.  No total
distance or answer-choice value occurs in these data.
-/
structure MatchesProblemStatement (motion : OneDimensionalMotion) : Prop where
  initialPosition : positionInMeters (motion.positionAtSeconds 0) = 0
  queryStartsAtZeroSeconds : timeInSeconds motion.queryStartTime = 0
  queryEndsAtEighteenSeconds : timeInSeconds motion.queryEndTime = 18

/-! ## Governing kinematic laws -/

/-!
Standard one-dimensional kinematics in coherent SI coordinates.

The first field identifies the plotted signed velocity with the time derivative
of x-position.  The second states the general path-length law for every ordered
pair of physical times.  It does not prescribe the result for the interval in
the question or any answer-choice value.
-/
structure SatisfiesOneDimensionalKinematics
    (motion : OneDimensionalMotion) : Prop where
  velocityIsPositionDerivative : ∀ timeSeconds : ℝ,
    HasDerivAt
      (fun t => positionInMeters (motion.positionAtSeconds t))
      (velocityInMetersPerSecond
        (motion.figure.velocityAtSeconds timeSeconds))
      timeSeconds
  distanceIsIntegralOfSpeed : ∀ startTime endTime : TimeQuantity,
    timeInSeconds startTime ≤ timeInSeconds endTime →
      distanceInMeters (motion.totalDistanceTravelled startTime endTime) =
        ∫ timeSeconds in timeInSeconds startTime..timeInSeconds endTime,
          |velocityInMetersPerSecond
            (motion.figure.velocityAtSeconds timeSeconds)|

/-! ## Printed choices and formalization target -/

/-- Labels printed beside the four candidate distances. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Distance in metres printed beside each answer label. -/
def AnswerChoice.distanceInMeters : AnswerChoice → ℝ
  | .A => 272
  | .B => 136
  | .C => 204
  | .D => 182

/-- Answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- The queried physical distance agrees with a displayed answer. -/
def MatchesDisplayedDistance
    (motion : OneDimensionalMotion) (choice : AnswerChoice) : Prop :=
  distanceInMeters
      (motion.totalDistanceTravelled
        motion.queryStartTime motion.queryEndTime) =
    choice.distanceInMeters

/-- Exactly one displayed label agrees with the queried physical distance. -/
def IsUniqueMatchingDisplayedChoice
    (motion : OneDimensionalMotion) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedDistance motion choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedDistance motion other → other = choice

/-!
Blueprint label: `thm:physics:phyx_mini_0672:target`.

The four absolute areas under the primary velocity graph are `48 m`, `39 m`,
`72 m`, and `45 m`.  Thus the object travels `204 m` from `0 s` to `18 s`, and
the unique matching displayed answer is C.
-/
theorem problem_phyx_mini_0672
    (motion : OneDimensionalMotion)
    (hStatement : MatchesProblemStatement motion)
    (hFigure : MatchesSuppliedVelocityTimeFigure motion.figure)
    (hKinematics : SatisfiesOneDimensionalKinematics motion) :
    distanceInMeters
        (motion.totalDistanceTravelled
        motion.queryStartTime motion.queryEndTime) = 204 ∧
      MatchesDisplayedDistance motion recordedAnswerChoice ∧
      IsUniqueMatchingDisplayedChoice motion recordedAnswerChoice := by
  let speed : ℝ → ℝ := fun timeSeconds =>
    |plottedVelocityMetersPerSecond timeSeconds|
  have integral_id_formula (a b : ℝ) :
      (∫ x in a..b, x) = (b ^ 2 - a ^ 2) / 2 := by
    have hid :
        IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume a b :=
      continuous_id.intervalIntegrable a b
    have hconst :
        IntervalIntegrable (fun _ : ℝ => a + b) MeasureTheory.volume a b :=
      continuous_const.intervalIntegrable a b
    have hreflect :
        (∫ x in a..b, (a + b) - x) = ∫ x in a..b, x := by
      simpa only [id_eq, add_sub_cancel_right, add_sub_cancel_left] using
        (intervalIntegral.integral_comp_sub_left
          (fun x : ℝ => x) (a + b) (a := a) (b := b))
    rw [intervalIntegral.integral_sub hconst hid,
      intervalIntegral.integral_const] at hreflect
    norm_num at hreflect ⊢
    nlinarith
  have integral_affine_formula (a b m c : ℝ) :
      (∫ x in a..b, m * x + c) =
        m * ((b ^ 2 - a ^ 2) / 2) + c * (b - a) := by
    have hlinear :
        IntervalIntegrable (fun x : ℝ => m * x)
          MeasureTheory.volume a b :=
      (continuous_const.mul continuous_id).intervalIntegrable a b
    have hconstant :
        IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume a b :=
      continuous_const.intervalIntegrable a b
    rw [intervalIntegral.integral_add hlinear hconstant,
      intervalIntegral.integral_const_mul, integral_id_formula,
      intervalIntegral.integral_const]
    norm_num
    ring
  have combineIntervalIntegrable
      (f : ℝ → ℝ) (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c)
      (habInt : IntervalIntegrable f MeasureTheory.volume a b)
      (hbcInt : IntervalIntegrable f MeasureTheory.volume b c) :
      IntervalIntegrable f MeasureTheory.volume a c := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at habInt
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hbc] at hbcInt
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (hab.trans hbc),
      ← Set.Icc_union_Icc_eq_Icc hab hbc]
    exact habInt.union hbcInt
  have hSpeed0To4 :
      Set.EqOn speed (fun _ => (12 : ℝ)) (Set.uIcc 0 4) := by
    intro timeSeconds htime
    have htime' : timeSeconds ∈ Set.Icc (0 : ℝ) 4 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 4)] using htime
    simp only [speed, plottedVelocityMetersPerSecond, if_pos htime'.2]
    norm_num
  have hSpeed4To6 :
      Set.EqOn speed (fun timeSeconds => -6 * timeSeconds + 36)
        (Set.uIcc 4 6) := by
    intro timeSeconds htime
    have htime' : timeSeconds ∈ Set.Icc (4 : ℝ) 6 := by
      simpa [Set.uIcc_of_le (by norm_num : (4 : ℝ) ≤ 6)] using htime
    rcases htime' with ⟨hlower, hupper⟩
    by_cases hfour : timeSeconds ≤ 4
    · have : timeSeconds = 4 := le_antisymm hfour hlower
      subst timeSeconds
      norm_num [speed, plottedVelocityMetersPerSecond]
    · simp only [speed, plottedVelocityMetersPerSecond, if_neg hfour,
        if_pos (by linarith : timeSeconds ≤ 9),
        abs_of_nonpos (by linarith : 6 * timeSeconds - 36 ≤ 0)]
      ring
  have hSpeed6To9 :
      Set.EqOn speed (fun timeSeconds => 6 * timeSeconds + (-36))
        (Set.uIcc 6 9) := by
    intro timeSeconds htime
    have htime' : timeSeconds ∈ Set.Icc (6 : ℝ) 9 := by
      simpa [Set.uIcc_of_le (by norm_num : (6 : ℝ) ≤ 9)] using htime
    rcases htime' with ⟨hlower, hupper⟩
    simp only [speed, plottedVelocityMetersPerSecond,
      if_neg (by linarith : ¬ timeSeconds ≤ 4), if_pos hupper,
      abs_of_nonneg (by linarith : 0 ≤ 6 * timeSeconds - 36)]
    ring
  have hSpeed9To13 :
      Set.EqOn speed (fun _ => (18 : ℝ)) (Set.uIcc 9 13) := by
    intro timeSeconds htime
    have htime' : timeSeconds ∈ Set.Icc (9 : ℝ) 13 := by
      simpa [Set.uIcc_of_le (by norm_num : (9 : ℝ) ≤ 13)] using htime
    rcases htime' with ⟨hlower, hupper⟩
    by_cases hnine : timeSeconds ≤ 9
    · have : timeSeconds = 9 := le_antisymm hnine hlower
      subst timeSeconds
      norm_num [speed, plottedVelocityMetersPerSecond]
    · simp only [speed, plottedVelocityMetersPerSecond,
        if_neg (by linarith : ¬ timeSeconds ≤ 4), if_neg hnine,
        if_pos hupper]
      norm_num
  have hSpeed13To18 :
      Set.EqOn speed
        (fun timeSeconds => (-18 / 5) * timeSeconds + 324 / 5)
        (Set.uIcc 13 18) := by
    intro timeSeconds htime
    have htime' : timeSeconds ∈ Set.Icc (13 : ℝ) 18 := by
      simpa [Set.uIcc_of_le (by norm_num : (13 : ℝ) ≤ 18)] using htime
    rcases htime' with ⟨hlower, hupper⟩
    by_cases hthirteen : timeSeconds ≤ 13
    · have : timeSeconds = 13 := le_antisymm hthirteen hlower
      subst timeSeconds
      norm_num [speed, plottedVelocityMetersPerSecond]
    · simp only [speed, plottedVelocityMetersPerSecond,
        if_neg (by linarith : ¬ timeSeconds ≤ 4),
        if_neg (by linarith : ¬ timeSeconds ≤ 9), if_neg hthirteen]
      rw [abs_of_nonneg]
      · ring
      · exact mul_nonneg (by norm_num) (by linarith)
  have hIntegrable0To4 :
      IntervalIntegrable speed MeasureTheory.volume 0 4 :=
    (intervalIntegrable_congr fun _ htime =>
      hSpeed0To4 (Set.uIoc_subset_uIcc htime)).2
      (continuous_const.intervalIntegrable 0 4)
  have hIntegrable4To6 :
      IntervalIntegrable speed MeasureTheory.volume 4 6 :=
    (intervalIntegrable_congr fun _ htime =>
      hSpeed4To6 (Set.uIoc_subset_uIcc htime)).2
      (((continuous_const.mul continuous_id).add continuous_const)
        |>.intervalIntegrable 4 6)
  have hIntegrable6To9 :
      IntervalIntegrable speed MeasureTheory.volume 6 9 :=
    (intervalIntegrable_congr fun _ htime =>
      hSpeed6To9 (Set.uIoc_subset_uIcc htime)).2
      (((continuous_const.mul continuous_id).add continuous_const)
        |>.intervalIntegrable 6 9)
  have hIntegrable9To13 :
      IntervalIntegrable speed MeasureTheory.volume 9 13 :=
    (intervalIntegrable_congr fun _ htime =>
      hSpeed9To13 (Set.uIoc_subset_uIcc htime)).2
      (continuous_const.intervalIntegrable 9 13)
  have hIntegrable13To18 :
      IntervalIntegrable speed MeasureTheory.volume 13 18 :=
    (intervalIntegrable_congr fun _ htime =>
      hSpeed13To18 (Set.uIoc_subset_uIcc htime)).2
      (((continuous_const.mul continuous_id).add continuous_const)
        |>.intervalIntegrable 13 18)
  have hArea0To4 : (∫ timeSeconds in (0 : ℝ)..4, speed timeSeconds) = 48 := by
    rw [intervalIntegral.integral_congr hSpeed0To4,
      intervalIntegral.integral_const]
    norm_num
  have hArea4To6 : (∫ timeSeconds in (4 : ℝ)..6, speed timeSeconds) = 12 := by
    rw [intervalIntegral.integral_congr hSpeed4To6,
      integral_affine_formula]
    norm_num
  have hArea6To9 : (∫ timeSeconds in (6 : ℝ)..9, speed timeSeconds) = 27 := by
    rw [intervalIntegral.integral_congr hSpeed6To9,
      integral_affine_formula]
    norm_num
  have hArea9To13 :
      (∫ timeSeconds in (9 : ℝ)..13, speed timeSeconds) = 72 := by
    rw [intervalIntegral.integral_congr hSpeed9To13,
      intervalIntegral.integral_const]
    norm_num
  have hArea13To18 :
      (∫ timeSeconds in (13 : ℝ)..18, speed timeSeconds) = 45 := by
    rw [intervalIntegral.integral_congr hSpeed13To18,
      integral_affine_formula]
    norm_num
  have hIntegrable0To6 :
      IntervalIntegrable speed MeasureTheory.volume 0 6 :=
    combineIntervalIntegrable speed 0 4 6 (by norm_num) (by norm_num)
      hIntegrable0To4 hIntegrable4To6
  have hIntegrable0To9 :
      IntervalIntegrable speed MeasureTheory.volume 0 9 :=
    combineIntervalIntegrable speed 0 6 9 (by norm_num) (by norm_num)
      hIntegrable0To6 hIntegrable6To9
  have hIntegrable0To13 :
      IntervalIntegrable speed MeasureTheory.volume 0 13 :=
    combineIntervalIntegrable speed 0 9 13 (by norm_num) (by norm_num)
      hIntegrable0To9 hIntegrable9To13
  have hTotalArea : (∫ timeSeconds in (0 : ℝ)..18, speed timeSeconds) = 204 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
        hIntegrable0To13 hIntegrable13To18,
      ← intervalIntegral.integral_add_adjacent_intervals
        hIntegrable0To9 hIntegrable9To13,
      ← intervalIntegral.integral_add_adjacent_intervals
        hIntegrable0To6 hIntegrable6To9,
      ← intervalIntegral.integral_add_adjacent_intervals
        hIntegrable0To4 hIntegrable4To6,
      hArea0To4, hArea4To6, hArea6To9, hArea9To13, hArea13To18]
    norm_num
  have hOrdered :
      timeInSeconds motion.queryStartTime ≤
        timeInSeconds motion.queryEndTime := by
    rw [hStatement.queryStartsAtZeroSeconds,
      hStatement.queryEndsAtEighteenSeconds]
    norm_num
  have hDistanceAsArea :
      distanceInMeters
          (motion.totalDistanceTravelled
            motion.queryStartTime motion.queryEndTime) =
        ∫ timeSeconds in (0 : ℝ)..18, speed timeSeconds := by
    rw [hKinematics.distanceIsIntegralOfSpeed
        motion.queryStartTime motion.queryEndTime hOrdered,
      hStatement.queryStartsAtZeroSeconds,
      hStatement.queryEndsAtEighteenSeconds]
    apply intervalIntegral.integral_congr
    intro timeSeconds htime
    have htime' : timeSeconds ∈ Set.Icc (0 : ℝ) 18 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 18)] using htime
    simp only [speed]
    rw [hFigure.velocityTraceMatchesImage timeSeconds htime']
  have hDistance :
      distanceInMeters
          (motion.totalDistanceTravelled
            motion.queryStartTime motion.queryEndTime) = 204 :=
    hDistanceAsArea.trans hTotalArea
  refine ⟨hDistance, ?_, ?_⟩
  · simpa [MatchesDisplayedDistance, recordedAnswerChoice,
      AnswerChoice.distanceInMeters] using hDistance
  · refine ⟨?_, ?_⟩
    · simpa [MatchesDisplayedDistance, recordedAnswerChoice,
        AnswerChoice.distanceInMeters] using hDistance
    · intro other hother
      change distanceInMeters
          (motion.totalDistanceTravelled
            motion.queryStartTime motion.queryEndTime) =
        other.distanceInMeters at hother
      rw [hDistance] at hother
      cases other with
      | A => norm_num [AnswerChoice.distanceInMeters] at hother
      | B => norm_num [AnswerChoice.distanceInMeters] at hother
      | C => rfl
      | D => norm_num [AnswerChoice.distanceInMeters] at hother

end PhyXMiniProblems.ProblemPhyXMini0672
