import Mathlib.Analysis.InnerProductSpace.PiL2
import Physlib.Units.WithDim.Speed

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0737

open Dimension

/-!
# Least average-velocity magnitude along a squirrel's path

The primary figure shows a squirrel travelling on level ground through the
labelled points `A`, `B`, `C`, and `D`, in that order.  Its observation times
are `0`, `5`, `10`, and `15` minutes.  Cartesian position, time, planar
velocity, and scalar speed are represented by unit-independent Physlib
quantities.  Real numbers occur only as readouts in the units printed in the
problem and figure.

Assumption/target split:

* `MatchesSquirrelScenario` records that the moving animal is a squirrel on
  level ground and transcribes the four stated observation times.
* `MatchesPrimaryFigure` records the axis labels and units, grid calibration,
  path order and geometry, and the four Cartesian coordinate readouts visible
  in image `737.png`.
* `SatisfiesAverageVelocityLaw` states the governing kinematic definition:
  average velocity is displacement divided by elapsed time.
* `HasPhysicalAverageVelocityMagnitudes` states that each scalar speed is the
  Euclidean norm of the corresponding average-velocity vector.
* There are no previous-part results.
* The exact magnitude `1/120 m/s`, the fact that endpoint `C` is the unique
  least case, and its agreement with printed answer C occur only in the target
  theorem's conclusion.
-/

/-! ## Dimensionful quantities and coherent unit readouts -/

/-- Velocity has physical dimension length divided by time. -/
def velocityDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- A signed position vector in the level-ground plane. -/
abbrev PlanarPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 (EuclideanSpace ℝ (Fin 2)))

/-- A physical observation time measured from the stated time origin. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A signed planar average-velocity vector. -/
abbrev PlanarVelocityQuantity : Type :=
  Dimensionful
    (WithDim velocityDimension (EuclideanSpace ℝ (Fin 2)))

/-- Read a physical planar position in a selected length unit. -/
def positionReadout
    (lengthUnit : LengthUnit) (position : PlanarPositionQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  (position {UnitChoices.SI with length := lengthUnit}).val

/-- Read a physical time in a selected time unit. -/
def timeReadout (timeUnit : TimeUnit) (time : TimeQuantity) : ℝ :=
  ((time {UnitChoices.SI with time := timeUnit}).val : ℝ)

/-- Read a planar velocity in selected length and time units. -/
def velocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : PlanarVelocityQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read a nonnegative speed in selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : DimSpeed) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Coherent-SI position-vector readout, in metres. -/
def positionInMeters (position : PlanarPositionQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  positionReadout LengthUnit.meters position

/-- Minute readout of a physical observation time. -/
def timeInMinutes (time : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.minutes time

/-- Second readout of a physical observation time. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.seconds time

/-- Coherent-SI average-velocity readout, in metres per second. -/
def velocityInMetersPerSecond (velocity : PlanarVelocityQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  velocityReadout LengthUnit.meters TimeUnit.seconds velocity

/-- Metres-per-second readout of a nonnegative physical speed. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-! ## Figure vocabulary and physical setup -/

/-- Cartesian axes printed on the level-ground diagram. -/
inductive DiagramAxis where
  | x
  | y
  deriving DecidableEq, Fintype, Repr

/-- Coordinate index associated with a printed Cartesian axis. -/
def DiagramAxis.toFin : DiagramAxis → Fin 2
  | .x => 0
  | .y => 1

/-- The physical quantity named by an axis. -/
inductive AxisQuantity where
  | xPosition
  | yPosition
  deriving DecidableEq, Repr

/-- Units printed beside the two spatial axes. -/
inductive AxisUnit where
  | meters
  deriving DecidableEq, Repr

/-- The four labelled locations on the squirrel's path. -/
inductive SquirrelPoint where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The three destinations whose average velocities from `A` are compared. -/
inductive Destination where
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Forget that a destination is restricted to one of `B`, `C`, and `D`. -/
def Destination.toSquirrelPoint : Destination → SquirrelPoint
  | .B => .B
  | .C => .C
  | .D => .D

/-- Qualitative geometry of the trace drawn through the four points. -/
inductive PathGeometry where
  | smoothCurvedTrace
  deriving DecidableEq, Repr

/-- The type of ground surface named in the physical scenario. -/
inductive GroundSurface where
  | level
  deriving DecidableEq, Repr

/-- The moving animal named in the physical scenario. -/
inductive MovingAnimal where
  | squirrel
  deriving DecidableEq, Repr

/-- Literal coordinate-plot content of the primary image. -/
structure SquirrelPathFigure where
  axisQuantity : DiagramAxis → AxisQuantity
  axisUnit : DiagramAxis → AxisUnit
  axisMinimumMeters : DiagramAxis → ℝ
  axisMaximumMeters : DiagramAxis → ℝ
  gridSpacingMeters : ℝ
  pathGeometry : PathGeometry
  pathStartsAt : SquirrelPoint
  pointsVisitedInOrder : List SquirrelPoint
  pointPosition : SquirrelPoint → PlanarPositionQuantity

/-- Read one Cartesian coordinate of a labelled point in metres. -/
def pointCoordinateInMeters
    (figure : SquirrelPathFigure) (point : SquirrelPoint)
    (axis : DiagramAxis) : ℝ :=
  positionInMeters (figure.pointPosition point) axis.toFin

/-!
Independent physical data for the motion.  Average-velocity vectors and their
magnitudes are fields because they are observables constrained by the two
governing-law premises below; no requested numerical result is stored here.
-/
structure SquirrelMotionSetup where
  animal : MovingAnimal
  groundSurface : GroundSurface
  figure : SquirrelPathFigure
  observationTime : SquirrelPoint → TimeQuantity
  averageVelocityFromA : Destination → PlanarVelocityQuantity
  averageVelocityMagnitudeFromA : Destination → DimSpeed

/-! ## Scenario data, primary-figure evidence, and governing laws -/

/-- Prose data: animal, level ground, and the four observation times. -/
structure MatchesSquirrelScenario (setup : SquirrelMotionSetup) : Prop where
  animalIsSquirrel : setup.animal = .squirrel
  groundIsLevel : setup.groundSurface = .level
  timeAtAInMinutes : timeInMinutes (setup.observationTime .A) = 0
  timeAtBInMinutes : timeInMinutes (setup.observationTime .B) = 5
  timeAtCInMinutes : timeInMinutes (setup.observationTime .C) = 10
  timeAtDInMinutes : timeInMinutes (setup.observationTime .D) = 15

/-!
Exact transcription of image `737.png`.  Coordinate `0` is horizontal and
coordinate `1` is vertical.  The raster grid has five-metre cells; its marked
points are `A = (15,-15)`, `B = (30,-45)`, `C = (20,-15)`, and
`D = (45,45)`, all in metres.  These are displacement data, not velocity or
answer assumptions.
-/
structure MatchesPrimaryFigure (figure : SquirrelPathFigure) : Prop where
  xAxisQuantity : figure.axisQuantity .x = .xPosition
  yAxisQuantity : figure.axisQuantity .y = .yPosition
  xAxisUnit : figure.axisUnit .x = .meters
  yAxisUnit : figure.axisUnit .y = .meters
  xAxisMinimum : figure.axisMinimumMeters .x = 0
  xAxisMaximum : figure.axisMaximumMeters .x = 50
  yAxisMinimum : figure.axisMinimumMeters .y = -50
  yAxisMaximum : figure.axisMaximumMeters .y = 50
  gridSpacing : figure.gridSpacingMeters = 5
  traceIsSmoothAndCurved : figure.pathGeometry = .smoothCurvedTrace
  traceStartsAtA : figure.pathStartsAt = .A
  visitOrder : figure.pointsVisitedInOrder = [.A, .B, .C, .D]
  pointAX : pointCoordinateInMeters figure .A .x = 15
  pointAY : pointCoordinateInMeters figure .A .y = -15
  pointBX : pointCoordinateInMeters figure .B .x = 30
  pointBY : pointCoordinateInMeters figure .B .y = -45
  pointCX : pointCoordinateInMeters figure .C .x = 20
  pointCY : pointCoordinateInMeters figure .C .y = -15
  pointDX : pointCoordinateInMeters figure .D .x = 45
  pointDY : pointCoordinateInMeters figure .D .y = 45

/-- SI displacement vector from `A` to one of the three destinations. -/
def displacementFromAInMeters
    (setup : SquirrelMotionSetup) (destination : Destination) :
    EuclideanSpace ℝ (Fin 2) :=
  positionInMeters
      (setup.figure.pointPosition destination.toSquirrelPoint) -
    positionInMeters (setup.figure.pointPosition .A)

/-- Elapsed SI time from the observation at `A` to a destination. -/
def elapsedTimeFromAInSeconds
    (setup : SquirrelMotionSetup) (destination : Destination) : ℝ :=
  timeInSeconds (setup.observationTime destination.toSquirrelPoint) -
    timeInSeconds (setup.observationTime .A)

/-!
Average velocity is displacement divided by elapsed time.  Scalar inverse
followed by scalar multiplication expresses that quotient for a vector.  The
law is uniform over `B`, `C`, and `D` and contains no endpoint comparison or
answer value.
-/
structure SatisfiesAverageVelocityLaw
    (setup : SquirrelMotionSetup) : Prop where
  velocityIsDisplacementOverElapsedTime :
    ∀ destination,
      velocityInMetersPerSecond
          (setup.averageVelocityFromA destination) =
        (elapsedTimeFromAInSeconds setup destination)⁻¹ •
          displacementFromAInMeters setup destination

/-!
The magnitude of each average-velocity vector is its Euclidean norm.  This is
a general magnitude law and does not identify which destination is least.
-/
structure HasPhysicalAverageVelocityMagnitudes
    (setup : SquirrelMotionSetup) : Prop where
  magnitudeIsEuclideanNorm :
    ∀ destination,
      speedInMetersPerSecond
          (setup.averageVelocityMagnitudeFromA destination) =
        ‖velocityInMetersPerSecond
          (setup.averageVelocityFromA destination)‖

/-! ## Answer readouts and current target -/

/-- Labels of the four values printed as possible answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metres-per-second value printed beside each answer label. -/
def AnswerChoice.displayedMetersPerSecond : AnswerChoice → ℝ
  | .A => 56 / 10000
  | .B => 62 / 10000
  | .C => 83 / 10000
  | .D => 97 / 10000

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
Agreement with a decimal printed to four places.  The half-unit rounding
radius at that precision is `0.00005 = 1/20000` metres per second.
-/
def RoundsToFourDecimalPlaces (actual displayed : ℝ) : Prop :=
  displayed - 1 / 20000 ≤ actual ∧
    actual < displayed + 1 / 20000

/-- A physical speed rounds to the value printed beside an answer choice. -/
def MatchesAnswerChoice (speed : DimSpeed) (choice : AnswerChoice) : Prop :=
  RoundsToFourDecimalPlaces
    (speedInMetersPerSecond speed) choice.displayedMetersPerSecond

/-- A destination has strictly smaller average-velocity magnitude than both alternatives. -/
def IsUniqueLeastAverageVelocityMagnitude
    (setup : SquirrelMotionSetup) (candidate : Destination) : Prop :=
  ∀ other, other ≠ candidate →
    speedInMetersPerSecond
        (setup.averageVelocityMagnitudeFromA candidate) <
      speedInMetersPerSecond
        (setup.averageVelocityMagnitudeFromA other)

/-!
From `A` to `C` the displacement has magnitude `5 m` and the elapsed time is
`600 s`, so the magnitude is exactly `1/120 m/s`.  It is uniquely least among
the three requested average velocities and rounds to the printed
`0.0083 m/s`, answer C.

This formalizes `thm:physics:phyx_mini_0737:target`.
-/
theorem least_averageVelocityMagnitude_is_one_over_oneHundredTwenty
    (setup : SquirrelMotionSetup)
    (h_scenario : MatchesSquirrelScenario setup)
    (h_figure : MatchesPrimaryFigure setup.figure)
    (h_averageVelocity : SatisfiesAverageVelocityLaw setup)
    (h_magnitudes : HasPhysicalAverageVelocityMagnitudes setup) :
    speedInMetersPerSecond
        (setup.averageVelocityMagnitudeFromA .C) = (1 : ℝ) / 120 ∧
      IsUniqueLeastAverageVelocityMagnitude setup .C ∧
      MatchesAnswerChoice
        (setup.averageVelocityMagnitudeFromA .C) recordedDatasetAnswer := by
  have h_timeConversion (time : TimeQuantity) :
      timeInSeconds time = 60 * timeInMinutes time := by
    have h := time.2
      ({UnitChoices.SI with time := TimeUnit.minutes} : UnitChoices)
      UnitChoices.SI
    change ((time UnitChoices.SI).val : ℝ) =
      60 * ((time {UnitChoices.SI with time := TimeUnit.minutes}).val : ℝ)
    rw [h]
    simp only [WithDim.dim_apply]
    have h_scale : UnitChoices.dimScale
        ({UnitChoices.SI with time := TimeUnit.minutes} : UnitChoices)
        UnitChoices.SI T𝓭 = 60 := by
      simp [UnitChoices.dimScale, TimeUnit.minutes_div_seconds]
    rw [h_scale]
    rfl
  have h_timeA : timeInSeconds (setup.observationTime .A) = 0 := by
    rw [h_timeConversion, h_scenario.timeAtAInMinutes]
    norm_num
  have h_timeB : timeInSeconds (setup.observationTime .B) = 300 := by
    rw [h_timeConversion, h_scenario.timeAtBInMinutes]
    norm_num
  have h_timeC : timeInSeconds (setup.observationTime .C) = 600 := by
    rw [h_timeConversion, h_scenario.timeAtCInMinutes]
    norm_num
  have h_timeD : timeInSeconds (setup.observationTime .D) = 900 := by
    rw [h_timeConversion, h_scenario.timeAtDInMinutes]
    norm_num
  have h_AX :
      positionInMeters (setup.figure.pointPosition .A) 0 = 15 := by
    simpa [pointCoordinateInMeters, DiagramAxis.toFin] using h_figure.pointAX
  have h_AY :
      positionInMeters (setup.figure.pointPosition .A) 1 = -15 := by
    simpa [pointCoordinateInMeters, DiagramAxis.toFin] using h_figure.pointAY
  have h_BX :
      positionInMeters (setup.figure.pointPosition .B) 0 = 30 := by
    simpa [pointCoordinateInMeters, DiagramAxis.toFin] using h_figure.pointBX
  have h_CX :
      positionInMeters (setup.figure.pointPosition .C) 0 = 20 := by
    simpa [pointCoordinateInMeters, DiagramAxis.toFin] using h_figure.pointCX
  have h_CY :
      positionInMeters (setup.figure.pointPosition .C) 1 = -15 := by
    simpa [pointCoordinateInMeters, DiagramAxis.toFin] using h_figure.pointCY
  have h_DX :
      positionInMeters (setup.figure.pointPosition .D) 0 = 45 := by
    simpa [pointCoordinateInMeters, DiagramAxis.toFin] using h_figure.pointDX
  have h_speedC :
      speedInMetersPerSecond
          (setup.averageVelocityMagnitudeFromA .C) = (1 : ℝ) / 120 := by
    rw [h_magnitudes.magnitudeIsEuclideanNorm,
      h_averageVelocity.velocityIsDisplacementOverElapsedTime]
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp only [PiLp.smul_apply, Real.norm_eq_abs]
    simp [elapsedTimeFromAInSeconds, displacementFromAInMeters,
      Destination.toSquirrelPoint, h_timeC, h_timeA, h_CX, h_AX, h_CY, h_AY]
    norm_num
  have h_velocityBX :
      velocityInMetersPerSecond (setup.averageVelocityFromA .B) 0 =
        (1 : ℝ) / 20 := by
    have h := congrArg
      (fun v : EuclideanSpace ℝ (Fin 2) => v 0)
      (h_averageVelocity.velocityIsDisplacementOverElapsedTime .B)
    simp only [PiLp.smul_apply] at h
    norm_num [elapsedTimeFromAInSeconds, displacementFromAInMeters,
      Destination.toSquirrelPoint, h_timeB, h_timeA, h_BX, h_AX] at h ⊢
    exact h
  have h_normB_lower : (1 : ℝ) / 20 ≤
      ‖velocityInMetersPerSecond (setup.averageVelocityFromA .B)‖ := by
    calc
      (1 : ℝ) / 20 =
          ‖velocityInMetersPerSecond
            (setup.averageVelocityFromA .B) 0‖ := by
        rw [h_velocityBX]
        norm_num
      _ ≤ ‖velocityInMetersPerSecond
          (setup.averageVelocityFromA .B)‖ := PiLp.norm_apply_le _ _
  have h_velocityDX :
      velocityInMetersPerSecond (setup.averageVelocityFromA .D) 0 =
        (1 : ℝ) / 30 := by
    have h := congrArg
      (fun v : EuclideanSpace ℝ (Fin 2) => v 0)
      (h_averageVelocity.velocityIsDisplacementOverElapsedTime .D)
    simp only [PiLp.smul_apply] at h
    norm_num [elapsedTimeFromAInSeconds, displacementFromAInMeters,
      Destination.toSquirrelPoint, h_timeD, h_timeA, h_DX, h_AX] at h ⊢
    exact h
  have h_normD_lower : (1 : ℝ) / 30 ≤
      ‖velocityInMetersPerSecond (setup.averageVelocityFromA .D)‖ := by
    calc
      (1 : ℝ) / 30 =
          ‖velocityInMetersPerSecond
            (setup.averageVelocityFromA .D) 0‖ := by
        rw [h_velocityDX]
        norm_num
      _ ≤ ‖velocityInMetersPerSecond
          (setup.averageVelocityFromA .D)‖ := PiLp.norm_apply_le _ _
  refine ⟨h_speedC, ?_, ?_⟩
  · intro other h_ne
    cases other with
    | B =>
        calc
          speedInMetersPerSecond
              (setup.averageVelocityMagnitudeFromA .C) =
                (1 : ℝ) / 120 := h_speedC
          _ < (1 : ℝ) / 20 := by norm_num
          _ ≤ ‖velocityInMetersPerSecond
              (setup.averageVelocityFromA .B)‖ := h_normB_lower
          _ = speedInMetersPerSecond
              (setup.averageVelocityMagnitudeFromA .B) :=
            (h_magnitudes.magnitudeIsEuclideanNorm .B).symm
    | C => exact (h_ne rfl).elim
    | D =>
        calc
          speedInMetersPerSecond
              (setup.averageVelocityMagnitudeFromA .C) =
                (1 : ℝ) / 120 := h_speedC
          _ < (1 : ℝ) / 30 := by norm_num
          _ ≤ ‖velocityInMetersPerSecond
              (setup.averageVelocityFromA .D)‖ := h_normD_lower
          _ = speedInMetersPerSecond
              (setup.averageVelocityMagnitudeFromA .D) :=
            (h_magnitudes.magnitudeIsEuclideanNorm .D).symm
  · simp only [MatchesAnswerChoice]
    rw [h_speedC]
    norm_num [recordedDatasetAnswer, AnswerChoice.displayedMetersPerSecond,
      RoundsToFourDecimalPlaces]

end PhyXMiniProblems.ProblemPhyXMini0737
