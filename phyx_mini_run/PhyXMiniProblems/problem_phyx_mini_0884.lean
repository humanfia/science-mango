import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0884

open Dimension

/-!
# Collapse time of a pulled square wire loop

A closed square loop is made from `40 cm` of inextensible wire.  The loop has
resistance `0.10 Ω` and lies in a uniform perpendicular magnetic field of
magnitude `0.50 T`.  At `t = 0`, the left and right corners shown in the
primary raster move horizontally apart, each at `0.293 m/s`.

The resistance and magnetic field are retained as dimensionful physical setup
data even though the collapse time is fixed by geometry and kinematics rather
than by an electromagnetic induction law.  Lengths, times, speeds, resistance,
and magnetic-flux density are represented by unit-independent Physlib
quantities.  Real numbers occur only in explicitly named coherent-unit
readouts and in the displayed answer choices.

Assumption/target split:

* governing laws: the inextensible loop has four equal sides, the initial
  square's pulled diagonal obeys the Pythagorean relation, the two opposite
  corner speeds add to give the diagonal-separation speed, and the loop is a
  straight line exactly when the pulled diagonal has length two side lengths;
* previous-part results: none;
* figure/data readouts: `40 cm`, `0.10 Ω`, `0.50 T`, `t = 0`, four corners and
  four wire segments, blue dots for the perpendicular field, and two outward
  arrows each labelled `0.293 m/s`;
* current targets: the exact elapsed-time formula and the statement that the
  physical collapse time rounds to answer choice C, `0.1 s`.

Neither target is a field or premise of any setup, figure, or law structure.
-/

/-! ## Dimensionful physical quantities and coherent-unit readouts -/

/-- The physical dimension `L T⁻¹` of speed. -/
def speedDimension : Dimension :=
  L𝓭 * T𝓭⁻¹

/-- The physical dimension `M L² T⁻¹ C⁻²` of electrical resistance. -/
def electricalResistanceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- The physical dimension `M T⁻¹ C⁻¹` of magnetic flux density. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical time. -/
abbrev TimeMagnitude : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent physical speed. -/
abbrev SpeedMagnitude : Type :=
  Dimensionful (WithDim speedDimension NNReal)

/-- A nonnegative, unit-independent electrical resistance. -/
abbrev ResistanceMagnitude : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- Read a physical length in the coherent length unit selected by `units`. -/
def lengthReadout (units : UnitChoices) (length : LengthMagnitude) : ℝ :=
  ((length units).val : ℝ)

/-- Read a physical time in the coherent time unit selected by `units`. -/
def timeReadout (units : UnitChoices) (time : TimeMagnitude) : ℝ :=
  ((time units).val : ℝ)

/-- Read a physical speed in the coherent speed unit selected by `units`. -/
def speedReadout (units : UnitChoices) (speed : SpeedMagnitude) : ℝ :=
  ((speed units).val : ℝ)

/-- Read a resistance in the coherent resistance unit selected by `units`. -/
def resistanceReadout
    (units : UnitChoices) (resistance : ResistanceMagnitude) : ℝ :=
  ((resistance units).val : ℝ)

/-- Read magnetic flux density in the coherent unit selected by `units`. -/
def magneticFluxDensityReadout
    (units : UnitChoices) (field : MagneticFluxDensityMagnitude) : ℝ :=
  ((field units).val : ℝ)

/-- Coherent-SI metre readout of a physical length. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  lengthReadout UnitChoices.SI length

/-- Centimetre readout used for the stated total wire length. -/
def lengthInCentimeters (length : LengthMagnitude) : ℝ :=
  100 * lengthInMeters length

/-- Coherent-SI second readout of a physical time. -/
def timeInSeconds (time : TimeMagnitude) : ℝ :=
  timeReadout UnitChoices.SI time

/-- Coherent-SI metre-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : SpeedMagnitude) : ℝ :=
  speedReadout UnitChoices.SI speed

/-- Coherent-SI ohm readout of a physical resistance. -/
def resistanceInOhms (resistance : ResistanceMagnitude) : ℝ :=
  resistanceReadout UnitChoices.SI resistance

/-- Coherent-SI tesla readout of a magnetic-flux-density magnitude. -/
def magneticFluxDensityInTeslas (field : MagneticFluxDensityMagnitude) : ℝ :=
  magneticFluxDensityReadout UnitChoices.SI field

/-! ## Figure labels and independent physical setup -/

/-- The four vertices of the diamond-oriented square in image `884.png`. -/
inductive LoopCorner where
  | left
  | top
  | right
  | bottom
  deriving DecidableEq, Fintype, Repr

/-- The four pieces of wire joining successive visible corners. -/
inductive WireSegment where
  | upperLeft
  | upperRight
  | lowerRight
  | lowerLeft
  deriving DecidableEq, Fintype, Repr

/-- The two diagonally opposite corners to which the green arrows are attached. -/
inductive PulledCorner where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- Horizontal directions of the two velocity arrows in the figure. -/
inductive HorizontalDirection where
  | leftward
  | rightward
  deriving DecidableEq, Repr

/-- Direction represented by the conventional blue dot field markers. -/
inductive FieldPageDirection where
  | outOfPage
  | intoPage
  deriving DecidableEq, Repr

/-- Topology of the physical wire. -/
inductive LoopTopology where
  | closedSingleLoop
  deriving DecidableEq, Repr

/-- Initial shape asserted by the problem prose. -/
inductive InitialLoopShape where
  | square
  deriving DecidableEq, Repr

/-- Mechanical idealization used while the square deforms through rhombi. -/
inductive WireDeformationModel where
  | flexibleInextensible
  deriving DecidableEq, Repr

/-- Spatial relation between the magnetic field and the loop plane. -/
inductive FieldLoopOrientation where
  | perpendicularToLoopPlane
  deriving DecidableEq, Repr

/-- Uniformity idealization for the applied magnetic field. -/
inductive FieldUniformity where
  | uniform
  deriving DecidableEq, Repr

/-- The direction expected for each of the two outward velocity arrows. -/
def expectedArrowDirection : PulledCorner → HorizontalDirection
  | .left => .leftward
  | .right => .rightward

/-!
Literal information transcribed from the primary raster.  Displayed speeds are
scalar metre-per-second readouts; they are calibrated to independent physical
speed quantities below.
-/
structure CollapsingLoopFigure where
  cornerShown : LoopCorner → Bool
  wireSegmentShown : WireSegment → Bool
  blueFieldDotPatternShown : Bool
  blueDotsEncodeDirection : FieldPageDirection
  velocityArrowShown : PulledCorner → Bool
  velocityArrowDirection : PulledCorner → HorizontalDirection
  displayedCornerSpeedMetersPerSecond : PulledCorner → ℝ
  pulledDiagonalDrawnHorizontally : Bool

/-!
Independent physical data for the deforming loop.  In particular,
`collapseTime` and `pulledDiagonalLength` are observables, not definitions made
from `0.1 s` or from any answer choice.
-/
structure CollapsingSquareLoopSetup where
  topology : LoopTopology
  initialShape : InitialLoopShape
  deformationModel : WireDeformationModel
  fieldOrientation : FieldLoopOrientation
  fieldUniformity : FieldUniformity
  wireLength : LengthMagnitude
  sideLength : LengthMagnitude
  loopResistance : ResistanceMagnitude
  magneticFluxDensity : MagneticFluxDensityMagnitude
  cornerSpeed : PulledCorner → SpeedMagnitude
  startTime : TimeMagnitude
  collapseTime : TimeMagnitude
  pulledDiagonalLength : TimeMagnitude → LengthMagnitude
  figure : CollapsingLoopFigure

/-- Length of the pulled left-right diagonal at a physical time, in metres. -/
def pulledDiagonalInMeters
    (setup : CollapsingSquareLoopSetup) (time : TimeMagnitude) : ℝ :=
  lengthInMeters (setup.pulledDiagonalLength time)

/-- Side length of the inextensible rhombus, in metres. -/
def sideLengthInMeters (setup : CollapsingSquareLoopSetup) : ℝ :=
  lengthInMeters setup.sideLength

/-- Elapsed time from the onset of pulling to collapse, in seconds. -/
def collapseElapsedTimeInSeconds (setup : CollapsingSquareLoopSetup) : ℝ :=
  timeInSeconds setup.collapseTime - timeInSeconds setup.startTime

/-! ## Problem data, primary-image evidence, and governing laws -/

/-- Qualitative prose assumptions and the three non-figure numerical data. -/
structure MatchesCollapsingSquareLoopDescription
    (setup : CollapsingSquareLoopSetup) : Prop where
  wireFormsClosedLoop : setup.topology = .closedSingleLoop
  loopInitiallySquare : setup.initialShape = .square
  wireIsFlexibleAndInextensible :
    setup.deformationModel = .flexibleInextensible
  magneticFieldIsUniform : setup.fieldUniformity = .uniform
  magneticFieldIsPerpendicular :
    setup.fieldOrientation = .perpendicularToLoopPlane
  totalWireLengthIsFortyCentimeters :
    lengthInCentimeters setup.wireLength = 40
  loopResistanceIsOneTenthOhm :
    resistanceInOhms setup.loopResistance = 1 / 10
  fieldMagnitudeIsOneHalfTesla :
    magneticFluxDensityInTeslas setup.magneticFluxDensity = 1 / 2
  pullingStartsAtZeroSeconds : timeInSeconds setup.startTime = 0

/-!
The primary-image facts, including the two separately drawn speeds.  This
structure contains no collapse-time value and no answer-choice data.
-/
structure MatchesPrimaryCollapsingLoopFigure
    (setup : CollapsingSquareLoopSetup) : Prop where
  everyCornerIsShown : ∀ corner, setup.figure.cornerShown corner = true
  everyWireSegmentIsShown :
    ∀ segment, setup.figure.wireSegmentShown segment = true
  perpendicularFieldDotsAreShown :
    setup.figure.blueFieldDotPatternShown = true
  dotPatternPointsOutOfPage :
    setup.figure.blueDotsEncodeDirection = .outOfPage
  bothVelocityArrowsAreShown :
    ∀ corner, setup.figure.velocityArrowShown corner = true
  arrowsPointApart : ∀ corner,
    setup.figure.velocityArrowDirection corner = expectedArrowDirection corner
  eachDisplayedSpeedIsPointTwoNineThree : ∀ corner,
    setup.figure.displayedCornerSpeedMetersPerSecond corner = 293 / 1000
  displayedSpeedsCalibratePhysicalSpeeds : ∀ corner,
    speedInMetersPerSecond (setup.cornerSpeed corner) =
      setup.figure.displayedCornerSpeedMetersPerSecond corner
  pulledDiagonalIsHorizontal :
    setup.figure.pulledDiagonalDrawnHorizontally = true

/-! Positivity and chronological conditions selecting the physical branch. -/
structure HasPhysicalCollapsingLoopParameters
    (setup : CollapsingSquareLoopSetup) : Prop where
  wireLengthPositive : 0 < lengthInMeters setup.wireLength
  sideLengthPositive : 0 < sideLengthInMeters setup
  resistancePositive : 0 < resistanceInOhms setup.loopResistance
  fieldMagnitudePositive :
    0 < magneticFluxDensityInTeslas setup.magneticFluxDensity
  eachCornerSpeedPositive : ∀ corner,
    0 < speedInMetersPerSecond (setup.cornerSpeed corner)
  collapseDoesNotPrecedePulling :
    timeInSeconds setup.startTime ≤ timeInSeconds setup.collapseTime

/-!
Fixed-perimeter and initial-square geometry, stated in every coherent unit
system.  The first equation says the `40 cm` wire remains four equal sides;
the second is the Pythagorean relation for the initial square diagonal.
-/
structure SatisfiesInextensibleSquareGeometry
    (setup : CollapsingSquareLoopSetup) : Prop where
  perimeterIsFourEqualSides : ∀ units,
    lengthReadout units setup.wireLength =
      4 * lengthReadout units setup.sideLength
  initialSquareDiagonalPythagoreanLaw : ∀ units,
    lengthReadout units
          (setup.pulledDiagonalLength setup.startTime) ^ 2 =
      2 * lengthReadout units setup.sideLength ^ 2

/-!
The separation of the pulled corners grows at the sum of their two outward
speeds.  This is a general kinematic law on the interval from the start event
through the independently modeled collapse event; it contains no requested
time value.
-/
structure SatisfiesOppositeCornerSeparationKinematics
    (setup : CollapsingSquareLoopSetup) : Prop where
  pulledDiagonalGrowthLaw : ∀ (units : UnitChoices) (time : TimeMagnitude),
    timeReadout units setup.startTime ≤ timeReadout units time →
    timeReadout units time ≤ timeReadout units setup.collapseTime →
      lengthReadout units (setup.pulledDiagonalLength time) =
        lengthReadout units
            (setup.pulledDiagonalLength setup.startTime) +
          (speedReadout units (setup.cornerSpeed .left) +
            speedReadout units (setup.cornerSpeed .right)) *
            (timeReadout units time - timeReadout units setup.startTime)

/-!
For an inextensible four-sided loop pulled along one diagonal, the degenerate
straight-line configuration occurs when that diagonal equals two side
lengths.  This geometric event definition has no numerical time in it.
-/
def IsStraightLineConfiguration
    (setup : CollapsingSquareLoopSetup) (time : TimeMagnitude) : Prop :=
  ∀ units,
    lengthReadout units (setup.pulledDiagonalLength time) =
      2 * lengthReadout units setup.sideLength

/-! The modeled collapse time is the first straight-line event after pulling. -/
structure IsFirstStraightLineCollapse
    (setup : CollapsingSquareLoopSetup) : Prop where
  straightAtCollapse :
    IsStraightLineConfiguration setup setup.collapseTime
  noEarlierStraightConfiguration : ∀ time,
    timeInSeconds setup.startTime ≤ timeInSeconds time →
    timeInSeconds time < timeInSeconds setup.collapseTime →
      ¬ IsStraightLineConfiguration setup time

/-! ## Collapse-time formula and displayed answer -/

/-- Labels of the four answer choices supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Duration in seconds printed beside each displayed answer choice. -/
def AnswerChoice.displayedDurationInSeconds : AnswerChoice → ℝ
  | .A => 7 / 10
  | .B => 3 / 10
  | .C => 1 / 10
  | .D => 9 / 10

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Rounding to the nearest tenth of a second, matching the answer display. -/
def RoundsToNearestTenthSecond (time displayedTime : ℝ) : Prop :=
  displayedTime - 1 / 20 ≤ time ∧ time < displayedTime + 1 / 20

/-- A displayed choice agrees with the modeled physical collapse duration. -/
def AnswerMatchesCollapseTime
    (setup : CollapsingSquareLoopSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestTenthSecond
    (collapseElapsedTimeInSeconds setup) choice.displayedDurationInSeconds

/-!
The initial diagonal is `√2` side lengths, the collapsed diagonal is two side
lengths, and the diagonal opens at the sum of the two corner speeds.  Hence
the elapsed collapse time is the remaining diagonal distance divided by that
relative speed.  This is a conclusion, not a premise of the main theorem.
-/
lemma collapse_elapsed_time_formula
    (setup : CollapsingSquareLoopSetup)
    (_physical : HasPhysicalCollapsingLoopParameters setup)
    (_geometry : SatisfiesInextensibleSquareGeometry setup)
    (_kinematics : SatisfiesOppositeCornerSeparationKinematics setup)
    (_collapse : IsFirstStraightLineCollapse setup) :
    collapseElapsedTimeInSeconds setup =
      ((2 - Real.sqrt 2) * sideLengthInMeters setup) /
        (speedInMetersPerSecond (setup.cornerSpeed .left) +
          speedInMetersPerSecond (setup.cornerSpeed .right)) := by
  have hstart_le_collapse :
      timeReadout UnitChoices.SI setup.startTime ≤
        timeReadout UnitChoices.SI setup.collapseTime := by
    simpa [timeInSeconds] using _physical.collapseDoesNotPrecedePulling
  have hgrowth :
      lengthInMeters (setup.pulledDiagonalLength setup.collapseTime) =
        lengthInMeters (setup.pulledDiagonalLength setup.startTime) +
          (speedInMetersPerSecond (setup.cornerSpeed .left) +
            speedInMetersPerSecond (setup.cornerSpeed .right)) *
            collapseElapsedTimeInSeconds setup := by
    simpa [lengthInMeters, speedInMetersPerSecond,
      collapseElapsedTimeInSeconds, timeInSeconds] using
      (_kinematics.pulledDiagonalGrowthLaw UnitChoices.SI setup.collapseTime
        hstart_le_collapse le_rfl)
  have hstraight :
      lengthInMeters (setup.pulledDiagonalLength setup.collapseTime) =
        2 * sideLengthInMeters setup := by
    simpa [lengthInMeters, sideLengthInMeters] using
      (_collapse.straightAtCollapse UnitChoices.SI)
  have hpythagorean :
      lengthInMeters (setup.pulledDiagonalLength setup.startTime) ^ 2 =
        2 * sideLengthInMeters setup ^ 2 := by
    simpa [lengthInMeters, sideLengthInMeters] using
      (_geometry.initialSquareDiagonalPythagoreanLaw UnitChoices.SI)
  have hinitialDiagonal_nonnegative :
      0 ≤ lengthInMeters (setup.pulledDiagonalLength setup.startTime) := by
    unfold lengthInMeters lengthReadout
    positivity
  have hinitialDiagonal :
      lengthInMeters (setup.pulledDiagonalLength setup.startTime) =
        Real.sqrt 2 * sideLengthInMeters setup := by
    calc
      lengthInMeters (setup.pulledDiagonalLength setup.startTime) =
          Real.sqrt
            (lengthInMeters
              (setup.pulledDiagonalLength setup.startTime) ^ 2) :=
        (Real.sqrt_sq hinitialDiagonal_nonnegative).symm
      _ = Real.sqrt (2 * sideLengthInMeters setup ^ 2) := by
        rw [hpythagorean]
      _ = Real.sqrt 2 * Real.sqrt (sideLengthInMeters setup ^ 2) :=
        Real.sqrt_mul (x := (2 : ℝ)) (by norm_num)
          (sideLengthInMeters setup ^ 2)
      _ = Real.sqrt 2 * sideLengthInMeters setup := by
        rw [Real.sqrt_sq (le_of_lt _physical.sideLengthPositive)]
  have hrelativeSpeed_positive :
      0 <
        speedInMetersPerSecond (setup.cornerSpeed .left) +
          speedInMetersPerSecond (setup.cornerSpeed .right) :=
    add_pos (_physical.eachCornerSpeedPositive .left)
      (_physical.eachCornerSpeedPositive .right)
  apply (eq_div_iff (ne_of_gt hrelativeSpeed_positive)).2
  nlinarith

/-!
With side length `0.40 / 4 = 0.10 m` and total separation speed
`2 * 0.293 = 0.586 m/s`, the exact expression above is approximately
`0.09996 s`, which rounds to `0.1 s`, recorded answer C.

This declaration formalizes `thm:physics:phyx_mini_0884:target`.
-/
theorem problem_phyx_mini_0884
    (setup : CollapsingSquareLoopSetup)
    (_description : MatchesCollapsingSquareLoopDescription setup)
    (_figure : MatchesPrimaryCollapsingLoopFigure setup)
    (_physical : HasPhysicalCollapsingLoopParameters setup)
    (_geometry : SatisfiesInextensibleSquareGeometry setup)
    (_kinematics : SatisfiesOppositeCornerSeparationKinematics setup)
    (_collapse : IsFirstStraightLineCollapse setup) :
    RoundsToNearestTenthSecond
        (collapseElapsedTimeInSeconds setup) ((1 : ℝ) / 10) ∧
      AnswerMatchesCollapseTime setup recordedDatasetAnswer := by
  have hperimeter :
      lengthInMeters setup.wireLength = 4 * sideLengthInMeters setup := by
    simpa [lengthInMeters, sideLengthInMeters] using
      (_geometry.perimeterIsFourEqualSides UnitChoices.SI)
  have hwireLength :=
    _description.totalWireLengthIsFortyCentimeters
  have hsideLength : sideLengthInMeters setup = (1 : ℝ) / 10 := by
    rw [lengthInCentimeters] at hwireLength
    nlinarith
  have hleftSpeed :
      speedInMetersPerSecond (setup.cornerSpeed .left) = (293 : ℝ) / 1000 := by
    calc
      speedInMetersPerSecond (setup.cornerSpeed .left) =
          setup.figure.displayedCornerSpeedMetersPerSecond .left :=
        _figure.displayedSpeedsCalibratePhysicalSpeeds .left
      _ = (293 : ℝ) / 1000 :=
        _figure.eachDisplayedSpeedIsPointTwoNineThree .left
  have hrightSpeed :
      speedInMetersPerSecond (setup.cornerSpeed .right) = (293 : ℝ) / 1000 := by
    calc
      speedInMetersPerSecond (setup.cornerSpeed .right) =
          setup.figure.displayedCornerSpeedMetersPerSecond .right :=
        _figure.displayedSpeedsCalibratePhysicalSpeeds .right
      _ = (293 : ℝ) / 1000 :=
        _figure.eachDisplayedSpeedIsPointTwoNineThree .right
  have hformula :=
    collapse_elapsed_time_formula setup _physical _geometry _kinematics _collapse
  have hsqrt_two_squared : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_two_nonnegative : 0 ≤ Real.sqrt 2 :=
    Real.sqrt_nonneg 2
  have hsqrt_two_lower : (7 : ℝ) / 5 < Real.sqrt 2 := by
    nlinarith
  have hsqrt_two_upper : Real.sqrt 2 < (3 : ℝ) / 2 := by
    nlinarith
  have hrounds :
      RoundsToNearestTenthSecond
        (collapseElapsedTimeInSeconds setup) ((1 : ℝ) / 10) := by
    rw [hformula, hsideLength, hleftSpeed, hrightSpeed]
    unfold RoundsToNearestTenthSecond
    constructor <;> norm_num <;> nlinarith
  exact ⟨hrounds, by
    simpa [AnswerMatchesCollapseTime, recordedDatasetAnswer,
      AnswerChoice.displayedDurationInSeconds] using hrounds⟩

end PhyXMiniProblems.ProblemPhyXMini0884
