import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0669

open Dimension

/-!
# Average velocity from a position--time graph

The particle moves along the `x` axis.  The primary raster is a calibrated
position--time plot whose visible vertices, in seconds and metres, are

`(0, 0), (2, 10), (4, 5), (5, 5), (7, -6), (8, 0)`.

The raster is used as primary evidence: in particular, its trough is at
`-6 m`, whereas the auxiliary prose caption describes that point
inconsistently.  Position and average velocity are unit-independent Physlib
quantities.  Real numbers occur only as scalar readouts in the units printed
on the axes and beside the answer choices.

Assumption/target boundary:

* `MatchesProblemStatement` records that the motion is one-dimensional along
  the `x` axis.
* `MatchesPrimaryFigure` records the axis labels, axis units and ranges, grid,
  polyline geometry, and all six visible vertices.
* `SatisfiesAverageVelocityLaw` is the governing kinematic law that average
  velocity equals displacement divided by elapsed time.
* There are no previous-part results.
* The value `0 m/s` and its agreement with answer choice C occur only in the
  conclusion of the target theorem, not in any setup or law premise.
-/

/-! ## Dimensionful physical quantities and coherent SI readouts -/

/-- A signed position coordinate along the particle's one-dimensional axis. -/
abbrev AxialPosition : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A signed one-dimensional velocity, with physical dimension `L T⁻¹`. -/
abbrev AxialVelocity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Metre readout of a signed axial position. -/
def positionInMeters (position : AxialPosition) : ℝ :=
  (position UnitChoices.SI).val

/-- Metres-per-second readout of a signed axial velocity. -/
def velocityInMetersPerSecond (velocity : AxialVelocity) : ℝ :=
  (velocity UnitChoices.SI).val

/-! ## Primary-figure vocabulary and calibrated data -/

/-- Physical quantity assigned to one of the plot axes. -/
inductive AxisQuantity where
  | time
  | xPosition
  deriving DecidableEq, Repr

/-- Unit printed beside a plot axis. -/
inductive AxisUnit where
  | seconds
  | meters
  deriving DecidableEq, Repr

/-- The spatial axis named in the physical scenario. -/
inductive SpatialAxis where
  | x
  deriving DecidableEq, Repr

/-- The geometry of the thick trace drawn in the primary raster. -/
inductive TraceGeometry where
  | continuousPiecewiseLinear
  deriving DecidableEq, Repr

/-- Names for the six visible vertices of the plotted motion. -/
inductive FigureVertex where
  | initialOrigin
  | positivePeak
  | plateauStart
  | plateauEnd
  | negativeTrough
  | finalOrigin
  deriving DecidableEq, Fintype, Repr

/-!
The calibrated position--time figure.  The trace argument is a real scalar
because it is the numerical coordinate read from the horizontal axis in
seconds; its value is still a dimensionful physical position.
-/
structure PositionTimeFigure where
  horizontalAxisQuantity : AxisQuantity
  verticalAxisQuantity : AxisQuantity
  horizontalAxisUnit : AxisUnit
  verticalAxisUnit : AxisUnit
  horizontalAxisMinimumSeconds : ℝ
  horizontalAxisMaximumSeconds : ℝ
  verticalAxisMinimumMeters : ℝ
  verticalAxisMaximumMeters : ℝ
  hasRectangularGrid : Bool
  traceGeometry : TraceGeometry
  vertexTimeSeconds : FigureVertex → ℝ
  positionTraceAtSeconds : ℝ → AxialPosition

/--
The trace is the straight line segment joining two named consecutive vertices.
This is figure evidence, not a dynamical law and not an answer assumption.
-/
def IsStraightTraceSegment
    (figure : PositionTimeFigure) (first second : FigureVertex) : Prop :=
  ∀ t : ℝ,
    figure.vertexTimeSeconds first ≤ t →
      t ≤ figure.vertexTimeSeconds second →
        positionInMeters (figure.positionTraceAtSeconds t) =
          positionInMeters
              (figure.positionTraceAtSeconds
                (figure.vertexTimeSeconds first)) +
            (t - figure.vertexTimeSeconds first) /
                (figure.vertexTimeSeconds second -
                  figure.vertexTimeSeconds first) *
              (positionInMeters
                  (figure.positionTraceAtSeconds
                    (figure.vertexTimeSeconds second)) -
                positionInMeters
                  (figure.positionTraceAtSeconds
                    (figure.vertexTimeSeconds first)))

/-!
Exact transcription of image 669.  The endpoint positions are calibrated
measurements from the graph.  They do not state the requested average velocity.
-/
def MatchesPrimaryFigure (figure : PositionTimeFigure) : Prop :=
  figure.horizontalAxisQuantity = .time ∧
    figure.verticalAxisQuantity = .xPosition ∧
    figure.horizontalAxisUnit = .seconds ∧
    figure.verticalAxisUnit = .meters ∧
    figure.horizontalAxisMinimumSeconds = 0 ∧
    figure.horizontalAxisMaximumSeconds = 8 ∧
    figure.verticalAxisMinimumMeters = -6 ∧
    figure.verticalAxisMaximumMeters = 10 ∧
    figure.hasRectangularGrid = true ∧
    figure.traceGeometry = .continuousPiecewiseLinear ∧
    figure.vertexTimeSeconds .initialOrigin = 0 ∧
    figure.vertexTimeSeconds .positivePeak = 2 ∧
    figure.vertexTimeSeconds .plateauStart = 4 ∧
    figure.vertexTimeSeconds .plateauEnd = 5 ∧
    figure.vertexTimeSeconds .negativeTrough = 7 ∧
    figure.vertexTimeSeconds .finalOrigin = 8 ∧
    positionInMeters (figure.positionTraceAtSeconds 0) = 0 ∧
    positionInMeters (figure.positionTraceAtSeconds 2) = 10 ∧
    positionInMeters (figure.positionTraceAtSeconds 4) = 5 ∧
    positionInMeters (figure.positionTraceAtSeconds 5) = 5 ∧
    positionInMeters (figure.positionTraceAtSeconds 7) = -6 ∧
    positionInMeters (figure.positionTraceAtSeconds 8) = 0 ∧
    IsStraightTraceSegment figure .initialOrigin .positivePeak ∧
    IsStraightTraceSegment figure .positivePeak .plateauStart ∧
    IsStraightTraceSegment figure .plateauStart .plateauEnd ∧
    IsStraightTraceSegment figure .plateauEnd .negativeTrough ∧
    IsStraightTraceSegment figure .negativeTrough .finalOrigin

/-! ## Particle setup and governing kinematics -/

/-!
The average velocity is an independent physical observable.  No numerical
value for it is stored in this structure.
-/
structure ParticleMotionSetup where
  spatialAxis : SpatialAxis
  figure : PositionTimeFigure
  averageVelocityOverDisplayedInterval : AxialVelocity

/-- The scenario specifies one-dimensional motion along the `x` axis. -/
def MatchesProblemStatement (setup : ParticleMotionSetup) : Prop :=
  setup.spatialAxis = .x

/-!
Average velocity over the displayed interval is displacement divided by its
elapsed time.  This is the governing kinematic law; it contains no displayed
answer value.
-/
structure SatisfiesAverageVelocityLaw
    (setup : ParticleMotionSetup) : Prop where
  displayedIntervalLaw :
    velocityInMetersPerSecond
        setup.averageVelocityOverDisplayedInterval =
      (positionInMeters
          (setup.figure.positionTraceAtSeconds
            setup.figure.horizontalAxisMaximumSeconds) -
        positionInMeters
          (setup.figure.positionTraceAtSeconds
            setup.figure.horizontalAxisMinimumSeconds)) /
        (setup.figure.horizontalAxisMaximumSeconds -
          setup.figure.horizontalAxisMinimumSeconds)

/-! ## Displayed answers and formalization target -/

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metres-per-second scalar displayed beside each answer label. -/
def AnswerChoice.metersPerSecond : AnswerChoice → ℝ
  | .A => 6
  | .B => 10
  | .C => 0
  | .D => 2

/-- A physical axial velocity agrees with the scalar printed for a choice. -/
def MatchesAnswerChoice
    (velocity : AxialVelocity) (choice : AnswerChoice) : Prop :=
  velocityInMetersPerSecond velocity = choice.metersPerSecond

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
The average velocity between `0 s` and `8 s` is `0 m/s`, so it agrees with
recorded answer choice C.

This formalizes `thm:physics:phyx_mini_0669:target`.
-/
theorem averageVelocityOverDisplayedInterval_is_zero
    (setup : ParticleMotionSetup)
    (h_problem : MatchesProblemStatement setup)
    (h_figure : MatchesPrimaryFigure setup.figure)
    (h_averageVelocity : SatisfiesAverageVelocityLaw setup) :
    velocityInMetersPerSecond
        setup.averageVelocityOverDisplayedInterval = 0 ∧
      MatchesAnswerChoice
        setup.averageVelocityOverDisplayedInterval recordedAnswerChoice := by
  obtain ⟨_, _, _, _, h_timeMin, h_timeMax, _, _, _, _, _, _, _, _, _, _,
    h_positionAtZero, _, _, _, _, h_positionAtEight, _, _, _, _, _⟩ := h_figure
  have h_velocityZero :
      velocityInMetersPerSecond
          setup.averageVelocityOverDisplayedInterval = 0 := by
    calc
      velocityInMetersPerSecond
            setup.averageVelocityOverDisplayedInterval =
          (positionInMeters
                (setup.figure.positionTraceAtSeconds
                  setup.figure.horizontalAxisMaximumSeconds) -
            positionInMeters
                (setup.figure.positionTraceAtSeconds
                  setup.figure.horizontalAxisMinimumSeconds)) /
            (setup.figure.horizontalAxisMaximumSeconds -
              setup.figure.horizontalAxisMinimumSeconds) :=
        h_averageVelocity.displayedIntervalLaw
      _ = 0 := by
        rw [h_timeMax, h_timeMin, h_positionAtEight, h_positionAtZero]
        norm_num
  refine ⟨h_velocityZero, ?_⟩
  simpa [MatchesAnswerChoice, recordedAnswerChoice,
    AnswerChoice.metersPerSecond] using h_velocityZero

end PhyXMiniProblems.ProblemPhyXMini0669
