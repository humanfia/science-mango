import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Physlib.Units.WithDim.Speed

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

/-!
# Position vector of an airplane in uniform horizontal flight

An observer stands at the ground origin.  An airplane moves with constant
velocity parallel to the positive `x`-axis at a fixed altitude of `7600 m`.
The position vector from the observer is vertical at `t = 0 s`, and at
`t = 30 s` its Cartesian readout is `(8040, 7600) m`.  The problem asks for
the magnitude and orientation of that vector at `t = 45 s`.

Times, lengths, planar positions, and planar velocities below are
unit-independent Physlib quantities.  Real numbers occur only in named-unit
readouts, Cartesian coordinates, angles, and displayed answer values.  The
position and velocity carriers are Mathlib Euclidean spaces, so their norm is
the physical Euclidean magnitude after a coherent unit choice.

Assumption/target split:

* `MatchesFlyoverScenario` records the observer-centered ground frame and the
  horizontal flight axis.
* `MatchesProblemReadouts` records the stated `0 s`, `30 s`, and `45 s`
  instants, the altitude, and the two given position vectors `P₀` and `P₃₀`.
* `MatchesSuppliedFlyoverFigure` records only labels and qualitative geometry
  visible in the primary bitmap.  In particular, the `30` is the subscript in
  `P₃₀`; the image contains no quantitative angle mark.
* `SatisfiesUniformHorizontalFlight` is the governing law: uniform
  translation, velocity parallel to `x`, and constant altitude.
* There are no previous-part results.
* The `t = 45 s` components, magnitude, orientation, rounded numerical
  readouts, and selection of answer C occur only in lemma/theorem conclusions.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0679

open Dimension

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A signed planar position vector with physical dimension length. -/
abbrev PlanarPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 (EuclideanSpace ℝ (Fin 2)))

/-- A signed planar velocity vector with physical dimension length per time. -/
abbrev PlanarVelocityQuantity : Type :=
  Dimensionful
    (WithDim (L𝓭 * T𝓭⁻¹) (EuclideanSpace ℝ (Fin 2)))

/-- A physical time coordinate relative to the stated `t = 0` origin. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 ℝ)

/-- A nonnegative physical length, used for the fixed altitude. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- Cartesian axes of the observer-centered ground frame. -/
inductive DiagramAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Coordinate index corresponding to a diagram axis. -/
def DiagramAxis.toFin : DiagramAxis → Fin 2
  | .horizontal => 0
  | .vertical => 1

/-- Read a planar position vector in a selected length unit. -/
def positionVectorReadout
    (lengthUnit : LengthUnit) (position : PlanarPositionQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  (position {UnitChoices.SI with length := lengthUnit}).val

/-- Read one component of a planar position in a selected length unit. -/
def positionComponentReadout
    (lengthUnit : LengthUnit) (position : PlanarPositionQuantity)
    (axis : DiagramAxis) : ℝ :=
  positionVectorReadout lengthUnit position axis.toFin

/-- Read the Euclidean magnitude of a planar position in a selected unit. -/
def positionMagnitudeReadout
    (lengthUnit : LengthUnit) (position : PlanarPositionQuantity) : ℝ :=
  ‖positionVectorReadout lengthUnit position‖

/-- Read one component of a planar velocity in selected length/time units. -/
def velocityComponentReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : PlanarVelocityQuantity) (axis : DiagramAxis) : ℝ :=
  (velocity {UnitChoices.SI with
      length := lengthUnit, time := timeUnit}).val axis.toFin

/-- Read a physical time coordinate in a selected time unit. -/
def timeReadout (timeUnit : TimeUnit) (time : TimeQuantity) : ℝ :=
  (time {UnitChoices.SI with time := timeUnit}).val

/-- Read a physical length in a selected length unit. -/
def lengthReadout (lengthUnit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := lengthUnit}).val : ℝ)

/-- Metre readout of one position component. -/
def positionComponentInMeters
    (position : PlanarPositionQuantity) (axis : DiagramAxis) : ℝ :=
  positionComponentReadout LengthUnit.meters position axis

/-- Metre readout of a position-vector magnitude. -/
def positionMagnitudeInMeters (position : PlanarPositionQuantity) : ℝ :=
  positionMagnitudeReadout LengthUnit.meters position

/-- Metre-per-second readout of one velocity component. -/
def velocityComponentInMetersPerSecond
    (velocity : PlanarVelocityQuantity) (axis : DiagramAxis) : ℝ :=
  velocityComponentReadout
    LengthUnit.meters TimeUnit.seconds velocity axis

/-- Second readout of a physical time coordinate. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.seconds time

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-!
For a first-quadrant vector, its orientation above the positive `x`-axis is
the arctangent of vertical component divided by horizontal component.  This
is a general geometric readout; it contains no problem-specific coordinate.
-/
def orientationAbovePositiveXAxisRadians
    (position : PlanarPositionQuantity) : ℝ :=
  Real.arctan
    (positionComponentInMeters position .vertical /
      positionComponentInMeters position .horizontal)

/-- Convert a radian angle to its degree readout. -/
def radiansToDegrees (angleRadians : ℝ) : ℝ :=
  angleRadians * 180 / Real.pi

/-- Orientation above the positive `x`-axis, expressed in degrees. -/
def orientationAbovePositiveXAxisDegrees
    (position : PlanarPositionQuantity) : ℝ :=
  radiansToDegrees (orientationAbovePositiveXAxisRadians position)

/-! ## Observer frame, physical setup, and primary-figure vocabulary -/

/-- Qualitative specification of the observer-centered ground frame. -/
structure GroundObserverFrame where
  observerAtCoordinateOrigin : Bool
  positiveXAxisIsHorizontal : Bool
  positiveYAxisIsUpward : Bool
  observerStandsOnGround : Bool

/-- Vector labels printed in the supplied raster. -/
inductive FigureVectorLabel where
  | P0
  | P30
  deriving DecidableEq, Fintype, Repr

/-- Qualitative directions of the two arrows in the supplied raster. -/
inductive FigureVectorDirection where
  | verticalUp
  | upperRight
  deriving DecidableEq, Repr

/-- Presentation-level information transcribed from the primary bitmap. -/
structure AirplaneFlyoverFigure where
  printedVectorText : FigureVectorLabel → String
  vectorShown : FigureVectorLabel → Bool
  vectorTailAtObserver : FigureVectorLabel → Bool
  vectorHeadOnFlightPath : FigureVectorLabel → Bool
  vectorDirection : FigureVectorLabel → FigureVectorDirection
  observerShown : Bool
  observerShownOnGround : Bool
  airplaneShown : Bool
  airplaneShownAtHeadOfP30 : Bool
  dashedFlightPathShown : Bool
  dashedFlightPathHorizontal : Bool
  quantitativeLengthScaleShown : Bool
  quantitativeAngleMarkShown : Bool

/-!
Independent physical data of the flyover.  `positionFromObserver` is the
airplane's position vector with tail at the stationary observer.  Neither its
value at the query time nor any answer choice is fixed by this structure.
-/
structure AirplaneFlyoverSetup where
  frame : GroundObserverFrame
  flightAxis : DiagramAxis
  flightAltitude : LengthQuantity
  initialTime : TimeQuantity
  sampleTime : TimeQuantity
  queryTime : TimeQuantity
  positionFromObserver : TimeQuantity → PlanarPositionQuantity
  constantVelocity : PlanarVelocityQuantity
  figure : AirplaneFlyoverFigure

/-! ## Scenario, source data, figure evidence, and governing laws -/

/-- Qualitative facts stated about the observer and the coordinate frame. -/
structure MatchesFlyoverScenario (setup : AirplaneFlyoverSetup) : Prop where
  observerAtOrigin : setup.frame.observerAtCoordinateOrigin = true
  xAxisHorizontal : setup.frame.positiveXAxisIsHorizontal = true
  yAxisUpward : setup.frame.positiveYAxisIsUpward = true
  observerOnGround : setup.frame.observerStandsOnGround = true
  flightParallelToXAxis : setup.flightAxis = .horizontal

/-!
Numerical readouts stated in the problem.  The query-time position, magnitude,
orientation, and answer label do not occur here.
-/
structure MatchesProblemReadouts (setup : AirplaneFlyoverSetup) : Prop where
  initialTimeSeconds : timeInSeconds setup.initialTime = 0
  sampleTimeSeconds : timeInSeconds setup.sampleTime = 30
  queryTimeSeconds : timeInSeconds setup.queryTime = 45
  altitudeMeters : lengthInMeters setup.flightAltitude = 7600
  P0HorizontalMeters :
    positionComponentInMeters
        (setup.positionFromObserver setup.initialTime) .horizontal = 0
  P0VerticalMeters :
    positionComponentInMeters
        (setup.positionFromObserver setup.initialTime) .vertical = 7600
  P30HorizontalMeters :
    positionComponentInMeters
        (setup.positionFromObserver setup.sampleTime) .horizontal = 8040
  P30VerticalMeters :
    positionComponentInMeters
        (setup.positionFromObserver setup.sampleTime) .vertical = 7600

/-!
Raw qualitative evidence from image `679.png`.  No position at `45 s`, vector
magnitude, orientation, or answer choice is represented in this predicate.
-/
structure MatchesSuppliedFlyoverFigure
    (figure : AirplaneFlyoverFigure) : Prop where
  P0Text : figure.printedVectorText .P0 = "P₀"
  P30Text : figure.printedVectorText .P30 = "P₃₀"
  bothVectorsShown : ∀ label, figure.vectorShown label = true
  bothVectorsStartAtObserver :
    ∀ label, figure.vectorTailAtObserver label = true
  bothVectorsEndOnFlightPath :
    ∀ label, figure.vectorHeadOnFlightPath label = true
  P0Direction : figure.vectorDirection .P0 = .verticalUp
  P30Direction : figure.vectorDirection .P30 = .upperRight
  observerVisible : figure.observerShown = true
  observerOnGround : figure.observerShownOnGround = true
  airplaneVisible : figure.airplaneShown = true
  airplaneAtP30Head : figure.airplaneShownAtHeadOfP30 = true
  dashedPathVisible : figure.dashedFlightPathShown = true
  dashedPathHorizontal : figure.dashedFlightPathHorizontal = true
  noQuantitativeLengthScale : figure.quantitativeLengthScaleShown = false
  noQuantitativeAngleMark : figure.quantitativeAngleMarkShown = false

/-!
Uniform straight-line kinematics, stated in arbitrary compatible length and
time units.  The vertical component of velocity vanishes and every position
has the given altitude.  These laws are general in both times and contain no
special formula or numerical conclusion for `45 s`.
-/
structure SatisfiesUniformHorizontalFlight
    (setup : AirplaneFlyoverSetup) : Prop where
  uniformTranslation :
    ∀ (startTime endTime : TimeQuantity)
      (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
      (axis : DiagramAxis),
      positionComponentReadout lengthUnit
          (setup.positionFromObserver endTime) axis =
        positionComponentReadout lengthUnit
            (setup.positionFromObserver startTime) axis +
          velocityComponentReadout lengthUnit timeUnit
              setup.constantVelocity axis *
            (timeReadout timeUnit endTime -
              timeReadout timeUnit startTime)
  velocityParallelToXAxis :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      velocityComponentReadout lengthUnit timeUnit
          setup.constantVelocity .vertical = 0
  fixedAltitude :
    ∀ (time : TimeQuantity) (lengthUnit : LengthUnit),
      positionComponentReadout lengthUnit
          (setup.positionFromObserver time) .vertical =
        lengthReadout lengthUnit setup.flightAltitude

/-! ## Derived kinematics -/

/-- The two supplied position vectors determine a horizontal speed of `268 m/s`. -/
lemma horizontalVelocityInMetersPerSecond_eq_268
    (setup : AirplaneFlyoverSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFlight : SatisfiesUniformHorizontalFlight setup) :
    velocityComponentInMetersPerSecond
        setup.constantVelocity .horizontal = 268 := by
  have hTranslation :=
    hFlight.uniformTranslation setup.initialTime setup.sampleTime
      LengthUnit.meters TimeUnit.seconds .horizontal
  change
    positionComponentInMeters
        (setup.positionFromObserver setup.sampleTime) .horizontal =
      positionComponentInMeters
          (setup.positionFromObserver setup.initialTime) .horizontal +
        velocityComponentInMetersPerSecond
            setup.constantVelocity .horizontal *
          (timeInSeconds setup.sampleTime -
            timeInSeconds setup.initialTime) at hTranslation
  rw [hReadouts.P30HorizontalMeters, hReadouts.P0HorizontalMeters,
    hReadouts.sampleTimeSeconds, hReadouts.initialTimeSeconds] at hTranslation
  norm_num at hTranslation ⊢
  linarith

/-!
Uniform motion for another `15 s` places the airplane at horizontal coordinate
`12060 m`; fixed altitude leaves the vertical coordinate at `7600 m`.
-/
lemma queryPositionComponents
    (setup : AirplaneFlyoverSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFlight : SatisfiesUniformHorizontalFlight setup) :
    positionComponentInMeters
        (setup.positionFromObserver setup.queryTime) .horizontal = 12060 ∧
      positionComponentInMeters
        (setup.positionFromObserver setup.queryTime) .vertical = 7600 := by
  have hVelocity :=
    horizontalVelocityInMetersPerSecond_eq_268 setup hReadouts hFlight
  have hTranslation :=
    hFlight.uniformTranslation setup.sampleTime setup.queryTime
      LengthUnit.meters TimeUnit.seconds .horizontal
  change
    positionComponentInMeters
        (setup.positionFromObserver setup.queryTime) .horizontal =
      positionComponentInMeters
          (setup.positionFromObserver setup.sampleTime) .horizontal +
        velocityComponentInMetersPerSecond
            setup.constantVelocity .horizontal *
          (timeInSeconds setup.queryTime -
            timeInSeconds setup.sampleTime) at hTranslation
  rw [hReadouts.P30HorizontalMeters, hVelocity,
    hReadouts.queryTimeSeconds, hReadouts.sampleTimeSeconds] at hTranslation
  have hAltitude :=
    hFlight.fixedAltitude setup.queryTime LengthUnit.meters
  change
    positionComponentInMeters
        (setup.positionFromObserver setup.queryTime) .vertical =
      lengthInMeters setup.flightAltitude at hAltitude
  rw [hReadouts.altitudeMeters] at hAltitude
  constructor
  · norm_num at hTranslation ⊢
    linarith
  · exact hAltitude

/-! ## Displayed choices and target conclusions -/

/-- Labels of the four displayed magnitude choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metre values printed beside the four answer labels. -/
def displayedMagnitudeInMeters : AnswerChoice → ℝ
  | .A => 13400
  | .B => 29100
  | .C => 14300
  | .D => 18700

/-- Answer label recorded in the dataset metadata; this is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- An actual magnitude rounds to a displayed hundred-metre value. -/
def RoundsToNearestHundredMeters (actual displayed : ℝ) : Prop :=
  displayed - 50 ≤ actual ∧ actual < displayed + 50

/-- An angle readout rounds to a displayed tenth of a degree. -/
def RoundsToNearestTenthDegree (actual displayed : ℝ) : Prop :=
  displayed - 1 / 20 ≤ actual ∧ actual < displayed + 1 / 20

/-- A displayed magnitude is at least as close as every alternative. -/
def IsNearestDisplayedMagnitude
    (setup : AirplaneFlyoverSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |positionMagnitudeInMeters
          (setup.positionFromObserver setup.queryTime) -
        displayedMagnitudeInMeters choice| ≤
      |positionMagnitudeInMeters
          (setup.positionFromObserver setup.queryTime) -
        displayedMagnitudeInMeters other|

/-- A displayed magnitude is the unique nearest answer choice. -/
def IsUniqueNearestDisplayedMagnitude
    (setup : AirplaneFlyoverSetup) (choice : AnswerChoice) : Prop :=
  IsNearestDisplayedMagnitude setup choice ∧
    ∀ other : AnswerChoice,
      IsNearestDisplayedMagnitude setup other → other = choice

/-!
At `45 s`, the position vector is `(12060, 7600) m`.  Hence its exact
magnitude is `sqrt (12060² + 7600²) m`, approximately `1.43 * 10^4 m`, and
its orientation is `arctan (7600 / 12060)`, approximately `32.2°` above the
positive `x`-axis.  Choice C is the unique nearest displayed magnitude.

This formalizes blueprint label `thm:physics:phyx_mini_0679:target`.
-/
theorem problem_phyx_mini_0679
    (setup : AirplaneFlyoverSetup)
    (hScenario : MatchesFlyoverScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFigure : MatchesSuppliedFlyoverFigure setup.figure)
    (hFlight : SatisfiesUniformHorizontalFlight setup) :
    positionComponentInMeters
        (setup.positionFromObserver setup.queryTime) .horizontal = 12060 ∧
      positionComponentInMeters
        (setup.positionFromObserver setup.queryTime) .vertical = 7600 ∧
      positionMagnitudeInMeters
          (setup.positionFromObserver setup.queryTime) =
        Real.sqrt ((12060 : ℝ) ^ 2 + (7600 : ℝ) ^ 2) ∧
      orientationAbovePositiveXAxisRadians
          (setup.positionFromObserver setup.queryTime) =
        Real.arctan ((7600 : ℝ) / 12060) ∧
      RoundsToNearestHundredMeters
        (positionMagnitudeInMeters
          (setup.positionFromObserver setup.queryTime))
        (displayedMagnitudeInMeters recordedDatasetAnswer) ∧
      RoundsToNearestTenthDegree
        (orientationAbovePositiveXAxisDegrees
          (setup.positionFromObserver setup.queryTime))
        (161 / 5) ∧
      IsUniqueNearestDisplayedMagnitude setup recordedDatasetAnswer := by
  rcases queryPositionComponents setup hReadouts hFlight with
    ⟨hHorizontal, hVertical⟩
  have hHorizontalVector :
      positionVectorReadout LengthUnit.meters
          (setup.positionFromObserver setup.queryTime) 0 = 12060 := by
    simpa [positionComponentInMeters, positionComponentReadout,
      DiagramAxis.toFin] using hHorizontal
  have hVerticalVector :
      positionVectorReadout LengthUnit.meters
          (setup.positionFromObserver setup.queryTime) 1 = 7600 := by
    simpa [positionComponentInMeters, positionComponentReadout,
      DiagramAxis.toFin] using hVertical
  have hMagnitude :
      positionMagnitudeInMeters
          (setup.positionFromObserver setup.queryTime) =
        Real.sqrt ((12060 : ℝ) ^ 2 + (7600 : ℝ) ^ 2) := by
    unfold positionMagnitudeInMeters positionMagnitudeReadout
    rw [← Real.sqrt_sq (norm_nonneg _)]
    congr 1
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    rw [hHorizontalVector, hVerticalVector]
  have hOrientationRadians :
      orientationAbovePositiveXAxisRadians
          (setup.positionFromObserver setup.queryTime) =
        Real.arctan ((7600 : ℝ) / 12060) := by
    rw [orientationAbovePositiveXAxisRadians, hHorizontal, hVertical]

  have hRadicandNonnegative :
      0 ≤ (12060 : ℝ) ^ 2 + (7600 : ℝ) ^ 2 := by positivity
  have hSqrtSquare :=
    Real.sq_sqrt hRadicandNonnegative
  have hSqrtNonnegative :=
    Real.sqrt_nonneg ((12060 : ℝ) ^ 2 + (7600 : ℝ) ^ 2)
  have hMagnitudeLower :
      (14250 : ℝ) ≤
        Real.sqrt ((12060 : ℝ) ^ 2 + (7600 : ℝ) ^ 2) := by
    nlinarith
  have hMagnitudeUpper :
      Real.sqrt ((12060 : ℝ) ^ 2 + (7600 : ℝ) ^ 2) <
        (14350 : ℝ) := by
    nlinarith
  norm_num at hMagnitudeLower hMagnitudeUpper
  have hMagnitudeRounds :
      RoundsToNearestHundredMeters
        (positionMagnitudeInMeters
          (setup.positionFromObserver setup.queryTime))
        (displayedMagnitudeInMeters recordedDatasetAnswer) := by
    rw [RoundsToNearestHundredMeters, hMagnitude]
    constructor
    · norm_num [displayedMagnitudeInMeters, recordedDatasetAnswer]
      exact hMagnitudeLower
    · norm_num [displayedMagnitudeInMeters, recordedDatasetAnswer]
      exact hMagnitudeUpper

  have r_lt_arctan_of_poly {q r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
      (hq0 : 0 ≤ q)
      (hpoly :
        r - r ^ 3 / 6 + r ^ 4 * (5 / 96) <
          q * (1 - r ^ 2 / 2 - r ^ 4 * (5 / 96))) :
      r < Real.arctan q := by
    have habs : |r| ≤ 1 := by
      rw [abs_of_pos hr0]
      exact hr1.le
    have hs := Real.sin_bound habs
    have hc := Real.cos_bound habs
    rw [abs_of_pos hr0] at hs hc
    have hsinUpper :
        Real.sin r ≤ r - r ^ 3 / 6 + r ^ 4 * (5 / 96) := by
      linarith [abs_le.mp hs |>.2]
    have hcosLower :
        1 - r ^ 2 / 2 - r ^ 4 * (5 / 96) ≤ Real.cos r := by
      linarith [abs_le.mp hc |>.1]
    have hrpi : r < Real.pi / 2 :=
      hr1.trans_le Real.one_le_pi_div_two
    have hcosPositive : 0 < Real.cos r :=
      Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos], hrpi⟩
    have htan : Real.tan r < q := by
      rw [Real.tan_eq_sin_div_cos, div_lt_iff₀ hcosPositive]
      calc
        Real.sin r ≤ r - r ^ 3 / 6 + r ^ 4 * (5 / 96) := hsinUpper
        _ < q * (1 - r ^ 2 / 2 - r ^ 4 * (5 / 96)) := hpoly
        _ ≤ q * Real.cos r :=
          mul_le_mul_of_nonneg_left hcosLower hq0
    rw [← Real.arctan_tan (by linarith [Real.pi_pos]) hrpi]
    exact Real.arctan_strictMono htan
  have arctan_lt_r_of_poly {q r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
      (hq0 : 0 ≤ q)
      (hpoly :
        q * (1 - r ^ 2 / 2 + r ^ 4 * (5 / 96)) <
          r - r ^ 3 / 6 - r ^ 4 * (5 / 96)) :
      Real.arctan q < r := by
    have habs : |r| ≤ 1 := by
      rw [abs_of_pos hr0]
      exact hr1.le
    have hs := Real.sin_bound habs
    have hc := Real.cos_bound habs
    rw [abs_of_pos hr0] at hs hc
    have hsinLower :
        r - r ^ 3 / 6 - r ^ 4 * (5 / 96) ≤ Real.sin r := by
      linarith [abs_le.mp hs |>.1]
    have hcosUpper :
        Real.cos r ≤ 1 - r ^ 2 / 2 + r ^ 4 * (5 / 96) := by
      linarith [abs_le.mp hc |>.2]
    have hrpi : r < Real.pi / 2 :=
      hr1.trans_le Real.one_le_pi_div_two
    have hcosPositive : 0 < Real.cos r :=
      Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos], hrpi⟩
    have htan : q < Real.tan r := by
      rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcosPositive]
      calc
        q * Real.cos r ≤ q * (1 - r ^ 2 / 2 + r ^ 4 * (5 / 96)) :=
          mul_le_mul_of_nonneg_left hcosUpper hq0
        _ < r - r ^ 3 / 6 - r ^ 4 * (5 / 96) := hpoly
        _ ≤ Real.sin r := hsinLower
    rw [← Real.arctan_tan (by linarith [Real.pi_pos]) hrpi]
    exact Real.arctan_strictMono htan

  have hArctanFifthLower :
      (19729 / 100000 : ℝ) < Real.arctan (1 / 5 : ℝ) := by
    apply r_lt_arctan_of_poly <;> norm_num
  have hArctanFifthUpper :
      Real.arctan (1 / 5 : ℝ) < (79 / 400 : ℝ) := by
    apply arctan_lt_r_of_poly <;> norm_num
  have hArctan239Lower :
      (1 / 240 : ℝ) < Real.arctan (1 / 239 : ℝ) := by
    apply r_lt_arctan_of_poly <;> norm_num
  have hArctan239Upper :
      Real.arctan (1 / 239 : ℝ) < (1 / 239 : ℝ) := by
    apply arctan_lt_r_of_poly <;> norm_num
  have hMachin := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  norm_num [inv_eq_one_div] at hMachin
  have hPiLower : (3139 / 1000 : ℝ) < Real.pi := by
    nlinarith
  have hPiUpper : Real.pi < (393 / 125 : ℝ) := by
    nlinarith

  have hCorrectionLower :
      (2229 / 10000 : ℝ) < Real.arctan (223 / 983 : ℝ) := by
    apply r_lt_arctan_of_poly <;> norm_num
  have hCorrectionUpper :
      Real.arctan (223 / 983 : ℝ) < (28 / 125 : ℝ) := by
    apply arctan_lt_r_of_poly <;> norm_num
  have hArctanComplement :
      Real.arctan ((7600 : ℝ) / 12060) +
          Real.arctan (223 / 983 : ℝ) =
        Real.pi / 4 := by
    rw [Real.arctan_add]
    · norm_num [Real.arctan_one]
    · norm_num
  have hAngleRadiansLower :
      643 * Real.pi / 3600 ≤ Real.arctan ((7600 : ℝ) / 12060) := by
    nlinarith
  have hAngleRadiansUpper :
      Real.arctan ((7600 : ℝ) / 12060) < 645 * Real.pi / 3600 := by
    nlinarith
  have hAngleDegreesLower :
      (643 / 20 : ℝ) ≤
        Real.arctan ((7600 : ℝ) / 12060) * 180 / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith
  have hAngleDegreesUpper :
      Real.arctan ((7600 : ℝ) / 12060) * 180 / Real.pi <
        (129 / 4 : ℝ) := by
    rw [div_lt_iff₀ Real.pi_pos]
    nlinarith
  have hOrientationDegrees :
      orientationAbovePositiveXAxisDegrees
          (setup.positionFromObserver setup.queryTime) =
        Real.arctan ((7600 : ℝ) / 12060) * 180 / Real.pi := by
    rw [orientationAbovePositiveXAxisDegrees, radiansToDegrees,
      hOrientationRadians]
  have hOrientationRounds :
      RoundsToNearestTenthDegree
        (orientationAbovePositiveXAxisDegrees
          (setup.positionFromObserver setup.queryTime))
        (161 / 5) := by
    rw [RoundsToNearestTenthDegree, hOrientationDegrees]
    constructor
    · convert hAngleDegreesLower using 1 <;> norm_num
    · convert hAngleDegreesUpper using 1 <;> norm_num

  have hActualMagnitudeLower :
      (14250 : ℝ) ≤
        positionMagnitudeInMeters
          (setup.positionFromObserver setup.queryTime) := by
    rw [hMagnitude]
    norm_num
    exact hMagnitudeLower
  have hActualMagnitudeUpper :
      positionMagnitudeInMeters
          (setup.positionFromObserver setup.queryTime) <
        (14350 : ℝ) := by
    rw [hMagnitude]
    norm_num
    exact hMagnitudeUpper
  have hChoiceCDistance :
      |positionMagnitudeInMeters
          (setup.positionFromObserver setup.queryTime) - 14300| ≤ 50 := by
    rw [abs_le]
    constructor <;> linarith
  have hChoiceADistance :
      800 <
        |positionMagnitudeInMeters
          (setup.positionFromObserver setup.queryTime) - 13400| := by
    rw [abs_of_pos (by linarith)]
    linarith
  have hChoiceBDistance :
      14000 <
        |positionMagnitudeInMeters
          (setup.positionFromObserver setup.queryTime) - 29100| := by
    rw [abs_of_neg (by linarith)]
    linarith
  have hChoiceDDistance :
      4000 <
        |positionMagnitudeInMeters
          (setup.positionFromObserver setup.queryTime) - 18700| := by
    rw [abs_of_neg (by linarith)]
    linarith
  have hNearestC :
      IsNearestDisplayedMagnitude setup recordedDatasetAnswer := by
    rw [IsNearestDisplayedMagnitude]
    intro other
    cases other
    · change
        |positionMagnitudeInMeters
            (setup.positionFromObserver setup.queryTime) - 14300| ≤
          |positionMagnitudeInMeters
            (setup.positionFromObserver setup.queryTime) - 13400|
      linarith
    · change
        |positionMagnitudeInMeters
            (setup.positionFromObserver setup.queryTime) - 14300| ≤
          |positionMagnitudeInMeters
            (setup.positionFromObserver setup.queryTime) - 29100|
      linarith
    · exact le_rfl
    · change
        |positionMagnitudeInMeters
            (setup.positionFromObserver setup.queryTime) - 14300| ≤
          |positionMagnitudeInMeters
            (setup.positionFromObserver setup.queryTime) - 18700|
      linarith
  have hUniqueC :
      ∀ other : AnswerChoice,
        IsNearestDisplayedMagnitude setup other →
          other = recordedDatasetAnswer := by
    intro other hOther
    rw [IsNearestDisplayedMagnitude] at hOther
    cases other
    · exfalso
      have h := hOther recordedDatasetAnswer
      change
        |positionMagnitudeInMeters
            (setup.positionFromObserver setup.queryTime) - 13400| ≤
          |positionMagnitudeInMeters
            (setup.positionFromObserver setup.queryTime) - 14300| at h
      linarith
    · exfalso
      have h := hOther recordedDatasetAnswer
      change
        |positionMagnitudeInMeters
            (setup.positionFromObserver setup.queryTime) - 29100| ≤
          |positionMagnitudeInMeters
            (setup.positionFromObserver setup.queryTime) - 14300| at h
      linarith
    · rfl
    · exfalso
      have h := hOther recordedDatasetAnswer
      change
        |positionMagnitudeInMeters
            (setup.positionFromObserver setup.queryTime) - 18700| ≤
          |positionMagnitudeInMeters
            (setup.positionFromObserver setup.queryTime) - 14300| at h
      linarith
  exact
    ⟨hHorizontal, hVertical, hMagnitude, hOrientationRadians,
      hMagnitudeRounds, hOrientationRounds, hNearestC, hUniqueC⟩

end PhyXMiniProblems.ProblemPhyXMini0679
