import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Physlib.Units.WithDim.Speed

/-!
# Final position from a moped velocity--time graph

The primary image plots the signed axial velocity of a moped on a straight
road.  Its piecewise-linear curve passes through `(0 s, 0 m/s)`,
`(3 s, 8 m/s)`, `(5 s, 8 m/s)`, and `(9 s, -8 m/s)`.  These image readouts
differ from the auxiliary caption, whose breakpoints are therefore not used.

Physical time, position, and signed velocity remain unit-independent Physlib
quantities.  Real numbers are used only for calibrated seconds, metres, and
metres-per-second readouts, plot coordinates, and displayed answer values.

Assumption/target boundary:

* `MatchesPrimaryVelocityTimeFigure` records only facts visible in the image.
* `VelocityReadoutMatchesFigure` interprets its three line segments as the
  measured velocity readout.
* `SatisfiesPositionVelocityLaw` is the general kinematic law relating
  displacement to the integral of velocity.
* `StartsAtSpatialOrigin` states the initial-origin convention needed to turn
  the graph's displacement into an absolute final position.  The source does
  not state an independent initial position.
* There are no previous-part results.
* The requested `28 m` and answer C occur only in the displayed-answer table
  and theorem conclusions, never in a physical premise.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0671

open CarriesDimension Dimension

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A unit-independent physical time coordinate. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 ℝ)

/-- A signed physical position along the straight road. -/
abbrev PositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A signed physical velocity component along the road's `x`-axis. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Numerical coordinate of a physical time in a selected time unit. -/
def timeReadout (unit : TimeUnit) (time : TimeQuantity) : ℝ :=
  (time {UnitChoices.SI with time := unit}).val

/-- Numerical coordinate of a signed physical position in a selected length unit. -/
def positionReadout (unit : LengthUnit) (position : PositionQuantity) : ℝ :=
  (position {UnitChoices.SI with length := unit}).val

/-- Numerical signed-velocity component in selected length and time units. -/
def signedVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Construct a physical time coordinate from a readout in a selected unit. -/
def timeFromReadout (unit : TimeUnit) (value : ℝ) : TimeQuantity :=
  toDimensionful
    ({UnitChoices.SI with time := unit} : UnitChoices)
    (show WithDim T𝓭 ℝ from ⟨value⟩)

/-- SI-second time coordinate used by the graph. -/
def timeFromSeconds (value : ℝ) : TimeQuantity :=
  timeFromReadout TimeUnit.seconds value

/-- SI-metre readout of a signed physical position. -/
def positionInMeters (position : PositionQuantity) : ℝ :=
  positionReadout LengthUnit.meters position

/-- SI metres-per-second readout of a signed axial velocity. -/
def signedVelocityInMetersPerSecond
    (velocity : SignedVelocityQuantity) : ℝ :=
  signedVelocityReadout LengthUnit.meters TimeUnit.seconds velocity

/-! ## Scenario and primary-figure vocabulary -/

/-- Kind of driver stated in the scenario. -/
inductive DriverKind where
  | student
  | other
  deriving DecidableEq, Repr

/-- Kind of road vehicle stated in the scenario. -/
inductive VehicleKind where
  | moped
  | other
  deriving DecidableEq, Repr

/-- Geometry of the road on which the vehicle moves. -/
inductive RoadGeometry where
  | straight
  | other
  deriving DecidableEq, Repr

/-- The longitudinal spatial axis named by the velocity label `vₓ`. -/
inductive MotionAxis where
  | x
  deriving DecidableEq, Repr

/-- The two labelled axes in the supplied plot. -/
inductive FigureAxis where
  | time
  | axialVelocity
  deriving DecidableEq, Fintype, Repr

/-- Named vertices of the piecewise-linear curve, in chronological order. -/
inductive CurveVertex where
  | start
  | risingEnd
  | plateauEnd
  | curveEnd
  deriving DecidableEq, Fintype, Repr

/-- A scalar coordinate read directly from the velocity--time graph. -/
structure VelocityTimePoint where
  timeSeconds : ℝ
  velocityMetersPerSecond : ℝ

/-- Labels, ranges, vertices, and presentation facts visible in image `671.png`. -/
structure VelocityTimeFigure where
  axisLabel : FigureAxis → String
  curveVertex : CurveVertex → VelocityTimePoint
  horizontalAxisMinimumSeconds : ℝ
  horizontalAxisMaximumSeconds : ℝ
  verticalAxisMinimumMetersPerSecond : ℝ
  verticalAxisMaximumMetersPerSecond : ℝ
  curveIsPiecewiseLinear : Bool
  showsSquareGrid : Bool
  curveIsReddishBrown : Bool

/-!
The physical motion.  Position and velocity are independent dimensionful
observables; neither is defined from a solved formula or an answer choice.
-/
structure StraightRoadMopedSetup where
  driverKind : DriverKind
  vehicleKind : VehicleKind
  roadGeometry : RoadGeometry
  motionAxis : MotionAxis
  positionAt : TimeQuantity → PositionQuantity
  axialVelocityAt : TimeQuantity → SignedVelocityQuantity
  figure : VelocityTimeFigure

/-! ## Scenario, figure readouts, and graph interpretation -/

/-- Categorical facts explicitly stated in the physical scenario. -/
structure MatchesMopedScenario
    (setup : StraightRoadMopedSetup) : Prop where
  driverIsStudent : setup.driverKind = .student
  vehicleIsMoped : setup.vehicleKind = .moped
  roadIsStraight : setup.roadGeometry = .straight
  velocityIsAlongXAxis : setup.motionAxis = .x

/-!
Facts transcribed from the primary raster.  In particular, the graph's actual
breakpoints are `3 s` and `5 s`, and the drawn curve ends at `9 s`, although
the horizontal plot axis continues to `10 s`.
-/
structure MatchesPrimaryVelocityTimeFigure
    (setup : StraightRoadMopedSetup) : Prop where
  timeAxisText : setup.figure.axisLabel .time = "t (s)"
  velocityAxisText : setup.figure.axisLabel .axialVelocity = "vₓ (m/s)"
  horizontalAxisStartsAtZero :
    setup.figure.horizontalAxisMinimumSeconds = 0
  horizontalAxisEndsAtTen :
    setup.figure.horizontalAxisMaximumSeconds = 10
  verticalAxisStartsAtNegativeEight :
    setup.figure.verticalAxisMinimumMetersPerSecond = -8
  verticalAxisEndsAtEight :
    setup.figure.verticalAxisMaximumMetersPerSecond = 8
  startTime : (setup.figure.curveVertex .start).timeSeconds = 0
  startVelocity :
    (setup.figure.curveVertex .start).velocityMetersPerSecond = 0
  risingEndTime : (setup.figure.curveVertex .risingEnd).timeSeconds = 3
  risingEndVelocity :
    (setup.figure.curveVertex .risingEnd).velocityMetersPerSecond = 8
  plateauEndTime :
    (setup.figure.curveVertex .plateauEnd).timeSeconds = 5
  plateauEndVelocity :
    (setup.figure.curveVertex .plateauEnd).velocityMetersPerSecond = 8
  curveEndTime : (setup.figure.curveVertex .curveEnd).timeSeconds = 9
  curveEndVelocity :
    (setup.figure.curveVertex .curveEnd).velocityMetersPerSecond = -8
  lineSegmentsShown : setup.figure.curveIsPiecewiseLinear = true
  squareGridShown : setup.figure.showsSquareGrid = true
  reddishBrownCurve : setup.figure.curveIsReddishBrown = true

/-!
Interpretation of the three line segments as calibrated signed-velocity
measurements.  This contains the graph data but no displacement, position, or
answer-choice value.
-/
structure VelocityReadoutMatchesFigure
    (setup : StraightRoadMopedSetup) : Prop where
  risingSegment :
    ∀ tSeconds : ℝ, 0 ≤ tSeconds → tSeconds ≤ 3 →
      signedVelocityInMetersPerSecond
          (setup.axialVelocityAt (timeFromSeconds tSeconds)) =
        (8 / 3) * tSeconds
  constantSegment :
    ∀ tSeconds : ℝ, 3 ≤ tSeconds → tSeconds ≤ 5 →
      signedVelocityInMetersPerSecond
          (setup.axialVelocityAt (timeFromSeconds tSeconds)) = 8
  fallingSegment :
    ∀ tSeconds : ℝ, 5 ≤ tSeconds → tSeconds ≤ 9 →
      signedVelocityInMetersPerSecond
          (setup.axialVelocityAt (timeFromSeconds tSeconds)) =
        8 - 4 * (tSeconds - 5)

/-!
The implicit origin convention required for the question to have an absolute
position answer rather than only a displacement answer.
-/
structure StartsAtSpatialOrigin
    (setup : StraightRoadMopedSetup) : Prop where
  initialPositionMeters :
    positionInMeters (setup.positionAt (timeFromSeconds 0)) = 0

/-! ## Governing kinematic law -/

/-!
For every ordered pair of displayed time readouts, signed displacement equals
the interval integral of signed velocity.  This is a general physical law and
does not contain the requested final position.
-/
structure SatisfiesPositionVelocityLaw
    (setup : StraightRoadMopedSetup) : Prop where
  displacementIsVelocityIntegral :
    ∀ startSeconds endSeconds : ℝ, startSeconds ≤ endSeconds →
      positionInMeters (setup.positionAt (timeFromSeconds endSeconds)) -
          positionInMeters (setup.positionAt (timeFromSeconds startSeconds)) =
        ∫ tSeconds in startSeconds..endSeconds,
          signedVelocityInMetersPerSecond
            (setup.axialVelocityAt (timeFromSeconds tSeconds))

/-! ## Displayed choices and target conclusions -/

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Position in metres printed beside each displayed answer label. -/
def displayedFinalPositionInMeters : AnswerChoice → ℝ
  | .A => 16
  | .B => 14
  | .C => 28
  | .D => 32

/-- The answer label recorded by the source dataset; it is metadata, not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
The signed area under the graph through `9 s` is `28 m`: the initial triangle
contributes `12`, the plateau `16`, and the positive and negative triangles
under the final segment cancel.
-/
lemma displacement_at_nine_seconds
    (setup : StraightRoadMopedSetup)
    (hGraph : VelocityReadoutMatchesFigure setup)
    (hKinematics : SatisfiesPositionVelocityLaw setup) :
    positionInMeters (setup.positionAt (timeFromSeconds 9)) -
        positionInMeters (setup.positionAt (timeFromSeconds 0)) = 28 := by
  let velocityReadout : ℝ → ℝ :=
    fun tSeconds =>
      signedVelocityInMetersPerSecond
        (setup.axialVelocityAt (timeFromSeconds tSeconds))
  have hIntegralIdZeroThree :
      (∫ tSeconds in (0 : ℝ)..3, tSeconds) = 9 / 2 := by
    have hReflection :
        (∫ tSeconds in (0 : ℝ)..3, (3 : ℝ) - tSeconds) =
          ∫ tSeconds in (0 : ℝ)..3, tSeconds := by
      simpa using
        (intervalIntegral.integral_comp_sub_left
          (fun tSeconds : ℝ => tSeconds) (3 : ℝ)
          (a := (0 : ℝ)) (b := 3))
    have hIdIntegrable :
        IntervalIntegrable (fun tSeconds : ℝ => tSeconds)
          MeasureTheory.volume 0 3 :=
      continuous_id.intervalIntegrable 0 3
    rw [intervalIntegral.integral_sub intervalIntegrable_const hIdIntegrable]
      at hReflection
    norm_num at hReflection ⊢
    linarith
  have hIntegralIdFiveNine :
      (∫ tSeconds in (5 : ℝ)..9, tSeconds) = 28 := by
    have hReflection :
        (∫ tSeconds in (5 : ℝ)..9, (14 : ℝ) - tSeconds) =
          ∫ tSeconds in (5 : ℝ)..9, tSeconds := by
      have h :=
        (intervalIntegral.integral_comp_sub_left
          (fun tSeconds : ℝ => tSeconds) (14 : ℝ)
          (a := (5 : ℝ)) (b := 9))
      norm_num at h
      exact h
    have hIdIntegrable :
        IntervalIntegrable (fun tSeconds : ℝ => tSeconds)
          MeasureTheory.volume 5 9 :=
      continuous_id.intervalIntegrable 5 9
    rw [intervalIntegral.integral_sub intervalIntegrable_const hIdIntegrable]
      at hReflection
    norm_num at hReflection ⊢
    linarith
  have hRisingIntegral :
      (∫ tSeconds in (0 : ℝ)..3, velocityReadout tSeconds) = 12 := by
    calc
      (∫ tSeconds in (0 : ℝ)..3, velocityReadout tSeconds) =
          ∫ tSeconds in (0 : ℝ)..3, (8 / 3 : ℝ) * tSeconds := by
        apply intervalIntegral.integral_congr
        intro tSeconds ht
        norm_num [Set.uIcc_of_le] at ht
        exact hGraph.risingSegment tSeconds ht.1 ht.2
      _ = (8 / 3 : ℝ) *
          (∫ tSeconds in (0 : ℝ)..3, tSeconds) := by
        rw [intervalIntegral.integral_const_mul]
      _ = 12 := by rw [hIntegralIdZeroThree]; norm_num
  have hConstantIntegral :
      (∫ tSeconds in (3 : ℝ)..5, velocityReadout tSeconds) = 16 := by
    calc
      (∫ tSeconds in (3 : ℝ)..5, velocityReadout tSeconds) =
          ∫ _tSeconds in (3 : ℝ)..5, (8 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro tSeconds ht
        norm_num [Set.uIcc_of_le] at ht
        exact hGraph.constantSegment tSeconds ht.1 ht.2
      _ = 16 := by norm_num
  have hFallingIntegral :
      (∫ tSeconds in (5 : ℝ)..9, velocityReadout tSeconds) = 0 := by
    have hAffineIntegrable :
        IntervalIntegrable (fun tSeconds : ℝ => 4 * tSeconds)
          MeasureTheory.volume 5 9 := by
      exact (continuous_const.mul continuous_id).intervalIntegrable 5 9
    calc
      (∫ tSeconds in (5 : ℝ)..9, velocityReadout tSeconds) =
          ∫ tSeconds in (5 : ℝ)..9,
            (8 : ℝ) - 4 * (tSeconds - 5) := by
        apply intervalIntegral.integral_congr
        intro tSeconds ht
        norm_num [Set.uIcc_of_le] at ht
        exact hGraph.fallingSegment tSeconds ht.1 ht.2
      _ = ∫ tSeconds in (5 : ℝ)..9, (28 : ℝ) - 4 * tSeconds := by
        apply intervalIntegral.integral_congr
        intro tSeconds _ht
        ring
      _ = (∫ _tSeconds in (5 : ℝ)..9, (28 : ℝ)) -
          ∫ tSeconds in (5 : ℝ)..9, 4 * tSeconds := by
        rw [intervalIntegral.integral_sub intervalIntegrable_const
          hAffineIntegrable]
      _ = 0 := by
        rw [intervalIntegral.integral_const_mul, hIntegralIdFiveNine]
        norm_num
  have hDisplacementZeroThree :
      positionInMeters (setup.positionAt (timeFromSeconds 3)) -
          positionInMeters (setup.positionAt (timeFromSeconds 0)) = 12 := by
    calc
      positionInMeters (setup.positionAt (timeFromSeconds 3)) -
          positionInMeters (setup.positionAt (timeFromSeconds 0)) =
          ∫ tSeconds in (0 : ℝ)..3, velocityReadout tSeconds :=
        hKinematics.displacementIsVelocityIntegral 0 3 (by norm_num)
      _ = 12 := hRisingIntegral
  have hDisplacementThreeFive :
      positionInMeters (setup.positionAt (timeFromSeconds 5)) -
          positionInMeters (setup.positionAt (timeFromSeconds 3)) = 16 := by
    calc
      positionInMeters (setup.positionAt (timeFromSeconds 5)) -
          positionInMeters (setup.positionAt (timeFromSeconds 3)) =
          ∫ tSeconds in (3 : ℝ)..5, velocityReadout tSeconds :=
        hKinematics.displacementIsVelocityIntegral 3 5 (by norm_num)
      _ = 16 := hConstantIntegral
  have hDisplacementFiveNine :
      positionInMeters (setup.positionAt (timeFromSeconds 9)) -
          positionInMeters (setup.positionAt (timeFromSeconds 5)) = 0 := by
    calc
      positionInMeters (setup.positionAt (timeFromSeconds 9)) -
          positionInMeters (setup.positionAt (timeFromSeconds 5)) =
          ∫ tSeconds in (5 : ℝ)..9, velocityReadout tSeconds :=
        hKinematics.displacementIsVelocityIntegral 5 9 (by norm_num)
      _ = 0 := hFallingIntegral
  linarith

/-!
Blueprint label: `thm:physics:phyx_mini_0671:target`.

At `t = 9.00 s`, the moped is at position `28 m` relative to the stated
initial origin, so exactly displayed choice C agrees with the physical result.
-/
theorem problem_phyx_mini_0671
    (setup : StraightRoadMopedSetup)
    (hScenario : MatchesMopedScenario setup)
    (hFigure : MatchesPrimaryVelocityTimeFigure setup)
    (hGraph : VelocityReadoutMatchesFigure setup)
    (hInitial : StartsAtSpatialOrigin setup)
    (hKinematics : SatisfiesPositionVelocityLaw setup) :
    positionInMeters (setup.positionAt (timeFromSeconds 9)) = 28 ∧
      positionInMeters (setup.positionAt (timeFromSeconds 9)) =
        displayedFinalPositionInMeters .C ∧
      ∀ choice : AnswerChoice,
        positionInMeters (setup.positionAt (timeFromSeconds 9)) =
            displayedFinalPositionInMeters choice ↔
          choice = .C := by
  have hFinalPosition :
      positionInMeters (setup.positionAt (timeFromSeconds 9)) = 28 := by
    have hDisplacement :=
      displacement_at_nine_seconds setup hGraph hKinematics
    linarith [hInitial.initialPositionMeters]
  refine ⟨hFinalPosition, ?_, ?_⟩
  · simpa [displayedFinalPositionInMeters] using hFinalPosition
  · intro choice
    rw [hFinalPosition]
    cases choice <;> norm_num [displayedFinalPositionInMeters] <;> simp

end PhyXMiniProblems.ProblemPhyXMini0671
