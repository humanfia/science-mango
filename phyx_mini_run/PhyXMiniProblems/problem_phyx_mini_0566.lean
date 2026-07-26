import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Relativity.LorentzGroup.Boosts.Basic
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Speed

/-!
# Relativistic area of an equilateral triangle

Observer `O` measures an equilateral triangle `ABC` at rest in the
`xy`-plane.  Its area is `3 m²`, and its symmetry axis from `C` to the
midpoint of `AB` makes an angle of `15°` with the common `x ≡ x'`
direction.  Observer `O'` moves at `0.6 c` along that direction and
measures the triangle `A'B'C'`.

Areas, lengths, and speed are represented by Physlib's unit-independent
dimensionful quantities.  Real numbers occur only as explicitly named SI
readouts, planar coordinate readouts, times, radian angles, dimensionless
speed fractions, and displayed answer values.

The supplied dataset records answer B, `1.4 m²`.  The standard simultaneous
Lorentz-contraction model stated below instead implies `2.4 m²`: a boost
contracts one planar coordinate by `1 / γ` and leaves the transverse
coordinate unchanged, so every planar area is multiplied by `1 / γ = 0.8`.
The blueprint-labelled theorem states this physically derivable value.  The
recorded answer remains separate source metadata, and a second theorem states
its disagreement with the standard model, so the discrepancy is not hidden in
a premise or asserted as a false physical conclusion.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0566

open Dimension

/-! ## Dimensionful quantities and scalar readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical area. -/
abbrev AreaQuantity : Type := DimArea

/-- Read a physical length in coherent SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical area in coherent SI square metres. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Read a physical speed in coherent SI metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  (speed UnitChoices.SI).val

/-- Physlib's exact vacuum speed of light, read in metres per second. -/
def vacuumSpeedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-- Convert a numerical degree readout to a radian coordinate. -/
def degreesToRadians (degrees : ℝ) : ℝ :=
  degrees * Real.pi / 180

/-! ## Observers, triangle labels, and coordinate readouts -/

/-- The rest observer and the relatively moving observer in the problem. -/
inductive ObserverLabel where
  | O
  | OPrime
  deriving DecidableEq, Fintype, Repr

/-- A physical vertex, labelled without or with primes according to frame. -/
inductive TriangleVertex where
  | A
  | B
  | C
  deriving DecidableEq, Fintype, Repr

/-- The six vertex labels printed in the supplied figure. -/
inductive FigureVertexLabel where
  | A
  | B
  | C
  | APrime
  | BPrime
  | CPrime
  deriving DecidableEq, Fintype, Repr

/-- Coordinate-axis labels visible in the two panels of the figure. -/
inductive CoordinateAxisLabel where
  | x
  | y
  | xPrime
  | yPrime
  deriving DecidableEq, Fintype, Repr

/-- Direction of the relative-velocity arrow along the common horizontal axis. -/
inductive HorizontalDirection where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- Named qualitative features visible in the primary raster `566.png`. -/
inductive FigureFeature where
  | restTriangle
  | movingTriangle
  | restHorizontalAxis
  | restVerticalAxis
  | movingHorizontalAxis
  | movingVerticalAxis
  | commonHorizontalAxisMark
  | velocityArrow
  | symmetryAxisSegment
  | thetaAngleMark
  deriving DecidableEq, Fintype, Repr

/--
A signed Cartesian coordinate readout in metres.

This is deliberately a scalar readout of a point in a selected frame, not a
replacement for the physical lengths, areas, or speed in the setup.
-/
structure PlanarPointMeters where
  x : ℝ
  y : ℝ
  deriving DecidableEq

/-- Squared Euclidean separation of two coordinate readouts, in square metres. -/
def squaredDistanceMeters
    (p q : PlanarPointMeters) : ℝ :=
  (q.x - p.x) ^ 2 + (q.y - p.y) ^ 2

/-- Coordinate midpoint of two planar point readouts. -/
def midpointMeters
    (p q : PlanarPointMeters) : PlanarPointMeters where
  x := (p.x + q.x) / 2
  y := (p.y + q.y) / 2

/--
Unsigned triangle area obtained from three Cartesian coordinate readouts.
The determinant is the oriented double area, so the result is in square
metres.
-/
def coordinateTriangleAreaSquareMeters
    (a b c : PlanarPointMeters) : ℝ :=
  abs
      ((b.x - a.x) * (c.y - a.y) -
        (b.y - a.y) * (c.x - a.x)) /
    2

/-! ## Primary figure and independent physical setup -/

/--
Qualitative transcription of the supplied image.  The image carries symbolic
labels and directions; the numerical `3 m²`, `15°`, and `0.6 c` data
come from the prose and are linked separately below.
-/
structure RelativisticTriangleFigure where
  shows : FigureFeature → Bool
  restVertexLabel : TriangleVertex → FigureVertexLabel
  movingVertexLabel : TriangleVertex → FigureVertexLabel
  restHorizontalAxisLabel : CoordinateAxisLabel
  restVerticalAxisLabel : CoordinateAxisLabel
  movingHorizontalAxisLabel : CoordinateAxisLabel
  movingVerticalAxisLabel : CoordinateAxisLabel
  velocityArrowDirection : HorizontalDirection
  symmetryAxisStartsAt : TriangleVertex
  symmetryAxisOppositeSide : TriangleVertex × TriangleVertex

/--
The triangle and its independent observables in the two observer frames.

The measured area for `OPrime` is an independent physical quantity.  It is
not defined from a displayed answer or from a Lorentz-contraction formula.
The coordinate and sampling-time fields give the operational data from which
each observer's simultaneous area measurement can be related to that physical
area.
-/
structure RelativisticTriangleSetup where
  figure : RelativisticTriangleFigure
  triangleRestObserver : ObserverLabel
  movingObserver : ObserverLabel
  measuredArea : ObserverLabel → AreaQuantity
  relativeSpeed : DimSpeed
  relativeMotionDirection : HorizontalDirection
  symmetryAxisAngleRadians : ℝ
  restSymmetryAxisLength : LengthQuantity
  restSymmetryAxisEndpointMeters : PlanarPointMeters
  vertexCoordinateMeters :
    ObserverLabel → TriangleVertex → PlanarPointMeters
  vertexSamplingTimeSeconds :
    ObserverLabel → TriangleVertex → ℝ

/-- The dimensionless speed parameter `β = v/c`. -/
def speedFractionOfLight
    (setup : RelativisticTriangleSetup) : ℝ :=
  speedInMetersPerSecond setup.relativeSpeed /
    vacuumSpeedOfLightInMetersPerSecond

/-- Physlib's Lorentz factor for the relative speed. -/
def lorentzFactor
    (setup : RelativisticTriangleSetup) : ℝ :=
  LorentzGroup.γ (speedFractionOfLight setup)

/-- Coordinate area of the three labelled vertices in one observer frame. -/
def coordinateAreaSquareMeters
    (setup : RelativisticTriangleSetup)
    (observer : ObserverLabel) : ℝ :=
  coordinateTriangleAreaSquareMeters
    (setup.vertexCoordinateMeters observer .A)
    (setup.vertexCoordinateMeters observer .B)
    (setup.vertexCoordinateMeters observer .C)

/-! ## Figure/data readouts and ordinary triangle geometry -/

/-- Observer roles and the rightward relative motion stated in the prose. -/
structure MatchesRelativisticTriangleScenario
    (setup : RelativisticTriangleSetup) : Prop where
  triangleIsAtRestForO : setup.triangleRestObserver = .O
  movingObserverIsOPrime : setup.movingObserver = .OPrime
  relativeMotionIsPositiveHorizontal :
    setup.relativeMotionDirection = .positive

/--
Direct qualitative evidence from `phyx_data/test_image/566.png`: both
triangles, the primed and unprimed labels, both coordinate systems, the
`x ≡ x'` mark, the rightward velocity arrow, and the symmetry-axis angle
from `C`.
-/
structure MatchesSuppliedTriangleFigure
    (setup : RelativisticTriangleSetup) : Prop where
  everyNamedFeatureShown :
    ∀ feature, setup.figure.shows feature = true
  restLabelA : setup.figure.restVertexLabel .A = .A
  restLabelB : setup.figure.restVertexLabel .B = .B
  restLabelC : setup.figure.restVertexLabel .C = .C
  movingLabelA : setup.figure.movingVertexLabel .A = .APrime
  movingLabelB : setup.figure.movingVertexLabel .B = .BPrime
  movingLabelC : setup.figure.movingVertexLabel .C = .CPrime
  restHorizontalAxisIsX :
    setup.figure.restHorizontalAxisLabel = .x
  restVerticalAxisIsY :
    setup.figure.restVerticalAxisLabel = .y
  movingHorizontalAxisIsXPrime :
    setup.figure.movingHorizontalAxisLabel = .xPrime
  movingVerticalAxisIsYPrime :
    setup.figure.movingVerticalAxisLabel = .yPrime
  velocityArrowPointsPositive :
    setup.figure.velocityArrowDirection = .positive
  symmetryAxisStartsAtC :
    setup.figure.symmetryAxisStartsAt = .C
  symmetryAxisEndsOnAB :
    setup.figure.symmetryAxisOppositeSide = (.A, .B)
  restCAtAxisOrigin :
    setup.vertexCoordinateMeters .O .C = ⟨0, 0⟩
  movingCPrimeAtAxisOrigin :
    setup.vertexCoordinateMeters .OPrime .C = ⟨0, 0⟩

/--
The numerical readouts supplied by the problem statement.  No value for the
area measured by `OPrime` occurs here.
-/
structure MatchesProblemData
    (setup : RelativisticTriangleSetup) : Prop where
  restAreaIsThreeSquareMeters :
    areaInSquareMeters (setup.measuredArea .O) = 3
  speedIsPointSixC :
    speedFractionOfLight setup = (3 / 5 : ℝ)
  symmetryAxisIsFifteenDegrees :
    setup.symmetryAxisAngleRadians = degreesToRadians 15

/--
The rest-frame coordinate triangle is equilateral, and its symmetry axis runs
from `C` to the midpoint of `AB` with the stated sine/cosine projections.
These are ordinary Euclidean geometry constraints, not an area answer.
-/
structure SatisfiesRestEquilateralGeometry
    (setup : RelativisticTriangleSetup) : Prop where
  sideABEqualsSideBC :
    squaredDistanceMeters
        (setup.vertexCoordinateMeters .O .A)
        (setup.vertexCoordinateMeters .O .B) =
      squaredDistanceMeters
        (setup.vertexCoordinateMeters .O .B)
        (setup.vertexCoordinateMeters .O .C)
  sideBCEqualsSideCA :
    squaredDistanceMeters
        (setup.vertexCoordinateMeters .O .B)
        (setup.vertexCoordinateMeters .O .C) =
      squaredDistanceMeters
        (setup.vertexCoordinateMeters .O .C)
        (setup.vertexCoordinateMeters .O .A)
  symmetryAxisEndsAtABMidpoint :
    setup.restSymmetryAxisEndpointMeters =
      midpointMeters
        (setup.vertexCoordinateMeters .O .A)
        (setup.vertexCoordinateMeters .O .B)
  symmetryAxisLongitudinalProjection :
    setup.restSymmetryAxisEndpointMeters.x -
        (setup.vertexCoordinateMeters .O .C).x =
      lengthInMeters setup.restSymmetryAxisLength *
        Real.cos setup.symmetryAxisAngleRadians
  symmetryAxisTransverseProjection :
    setup.restSymmetryAxisEndpointMeters.y -
        (setup.vertexCoordinateMeters .O .C).y =
      lengthInMeters setup.restSymmetryAxisLength *
        Real.sin setup.symmetryAxisAngleRadians

/-- Positivity, angle range, and subluminal conditions for the physical branch. -/
structure HasPhysicalRelativisticParameters
    (setup : RelativisticTriangleSetup) : Prop where
  restAreaPositive :
    0 < areaInSquareMeters (setup.measuredArea .O)
  movingAreaPositive :
    0 < areaInSquareMeters (setup.measuredArea .OPrime)
  symmetryAxisLengthPositive :
    0 < lengthInMeters setup.restSymmetryAxisLength
  symmetryAxisAngleAcute :
    0 < setup.symmetryAxisAngleRadians ∧
      setup.symmetryAxisAngleRadians < Real.pi / 2
  speedFractionNonnegative :
    0 ≤ speedFractionOfLight setup
  speedFractionSubluminal :
    speedFractionOfLight setup < 1

/-! ## Operational area measurement and governing relativity -/

/--
Each observer samples the three vertices simultaneously in that observer's
frame, and the physical area readout agrees with the determinant area of those
simultaneous coordinates.
-/
structure SatisfiesSimultaneousCoordinateAreaMeasurement
    (setup : RelativisticTriangleSetup) : Prop where
  verticesSampledSimultaneously :
    ∀ (observer : ObserverLabel) (vertex : TriangleVertex),
      setup.vertexSamplingTimeSeconds observer vertex =
        setup.vertexSamplingTimeSeconds observer .C
  physicalAreaAgreesWithCoordinates :
    ∀ observer : ObserverLabel,
      areaInSquareMeters (setup.measuredArea observer) =
        coordinateAreaSquareMeters setup observer

/--
Special-relativistic spatial contraction on the simultaneous moving-frame
slice.  Relative to vertex `C`, the coordinate parallel to the boost is
divided by Physlib's `γ(β)`; the transverse coordinate is invariant.

This is a generic governing law.  It contains neither a numerical moving area
nor an answer-choice label.
-/
structure ObeysLorentzCoordinateContraction
    (setup : RelativisticTriangleSetup) : Prop where
  longitudinalCoordinateContracts :
    ∀ vertex : TriangleVertex,
      (setup.vertexCoordinateMeters .OPrime vertex).x -
          (setup.vertexCoordinateMeters .OPrime .C).x =
        ((setup.vertexCoordinateMeters .O vertex).x -
            (setup.vertexCoordinateMeters .O .C).x) /
          lorentzFactor setup
  transverseCoordinateInvariant :
    ∀ vertex : TriangleVertex,
      (setup.vertexCoordinateMeters .OPrime vertex).y -
          (setup.vertexCoordinateMeters .OPrime .C).y =
        (setup.vertexCoordinateMeters .O vertex).y -
          (setup.vertexCoordinateMeters .O .C).y

/-!
The determinant area law and coordinate contraction imply the generic
standard-model scaling `A' = A / γ(β)`.  This is a derived conclusion rather
than a field of either governing-law structure.
-/
lemma area_scales_by_inverse_lorentz_factor
    (setup : RelativisticTriangleSetup)
    (_measurement : SatisfiesSimultaneousCoordinateAreaMeasurement setup)
    (_contraction : ObeysLorentzCoordinateContraction setup) :
    areaInSquareMeters (setup.measuredArea .OPrime) =
      areaInSquareMeters (setup.measuredArea .O) /
        lorentzFactor setup := by
  rw [_measurement.physicalAreaAgreesWithCoordinates .OPrime,
    _measurement.physicalAreaAgreesWithCoordinates .O]
  unfold coordinateAreaSquareMeters coordinateTriangleAreaSquareMeters
  have hAx := _contraction.longitudinalCoordinateContracts .A
  have hBx := _contraction.longitudinalCoordinateContracts .B
  have hAy := _contraction.transverseCoordinateInvariant .A
  have hBy := _contraction.transverseCoordinateInvariant .B
  have hdet :
      ((setup.vertexCoordinateMeters .OPrime .B).x -
            (setup.vertexCoordinateMeters .OPrime .A).x) *
          ((setup.vertexCoordinateMeters .OPrime .C).y -
            (setup.vertexCoordinateMeters .OPrime .A).y) -
        ((setup.vertexCoordinateMeters .OPrime .B).y -
            (setup.vertexCoordinateMeters .OPrime .A).y) *
          ((setup.vertexCoordinateMeters .OPrime .C).x -
            (setup.vertexCoordinateMeters .OPrime .A).x) =
        (((setup.vertexCoordinateMeters .O .B).x -
              (setup.vertexCoordinateMeters .O .A).x) *
            ((setup.vertexCoordinateMeters .O .C).y -
              (setup.vertexCoordinateMeters .O .A).y) -
          ((setup.vertexCoordinateMeters .O .B).y -
              (setup.vertexCoordinateMeters .O .A).y) *
            ((setup.vertexCoordinateMeters .O .C).x -
              (setup.vertexCoordinateMeters .O .A).x)) /
          lorentzFactor setup := by
    rw [show
        (setup.vertexCoordinateMeters .OPrime .B).x -
              (setup.vertexCoordinateMeters .OPrime .A).x =
            ((setup.vertexCoordinateMeters .OPrime .B).x -
                (setup.vertexCoordinateMeters .OPrime .C).x) -
              ((setup.vertexCoordinateMeters .OPrime .A).x -
                (setup.vertexCoordinateMeters .OPrime .C).x) by ring,
      hBx, hAx,
      show
        (setup.vertexCoordinateMeters .OPrime .C).y -
              (setup.vertexCoordinateMeters .OPrime .A).y =
            -((setup.vertexCoordinateMeters .OPrime .A).y -
                (setup.vertexCoordinateMeters .OPrime .C).y) by ring,
      hAy,
      show
        (setup.vertexCoordinateMeters .OPrime .B).y -
              (setup.vertexCoordinateMeters .OPrime .A).y =
            ((setup.vertexCoordinateMeters .OPrime .B).y -
                (setup.vertexCoordinateMeters .OPrime .C).y) -
              ((setup.vertexCoordinateMeters .OPrime .A).y -
                (setup.vertexCoordinateMeters .OPrime .C).y) by ring,
      hBy, hAy,
      show
        (setup.vertexCoordinateMeters .OPrime .C).x -
              (setup.vertexCoordinateMeters .OPrime .A).x =
            -((setup.vertexCoordinateMeters .OPrime .A).x -
                (setup.vertexCoordinateMeters .OPrime .C).x) by ring,
      hAx]
    ring
  rw [hdet, abs_div]
  have hγ : 0 ≤ lorentzFactor setup := by
    unfold lorentzFactor LorentzGroup.γ
    positivity
  rw [abs_of_nonneg hγ]
  ring

/-!
For the stated `3 m²` rest area and `β = 3/5`, the standard simultaneous
Lorentz-contraction model gives `A' = 12/5 m² = 2.4 m²`.
-/
lemma standard_model_area_is_two_point_four
    (setup : RelativisticTriangleSetup)
    (_data : MatchesProblemData setup)
    (_measurement : SatisfiesSimultaneousCoordinateAreaMeasurement setup)
    (_contraction : ObeysLorentzCoordinateContraction setup) :
    areaInSquareMeters (setup.measuredArea .OPrime) = (12 / 5 : ℝ) := by
  rw [area_scales_by_inverse_lorentz_factor setup _measurement _contraction,
    _data.restAreaIsThreeSquareMeters]
  unfold lorentzFactor
  rw [_data.speedIsPointSixC]
  norm_num [LorentzGroup.γ]
  rw [show Real.sqrt 25 = 5 by
      exact (Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)).2 (by norm_num),
    show Real.sqrt 16 = 4 by
      exact (Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)).2 (by norm_num)]
  norm_num

/-! ## Multiple-choice source metadata -/

/-- Labels of the four square-metre-valued choices in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Area in square metres printed beside each answer label. -/
def displayedAreaSquareMeters : AnswerChoice → ℝ
  | .A => 3
  | .B => 7 / 5
  | .C => 33 / 10
  | .D => 16 / 5

/-- The answer label recorded in the supplied dataset. -/
def recordedDatasetAnswer : AnswerChoice := .B

/--
An answer choice agrees with the independently represented moving-frame area.
Unfolding this definition leaves a substantive equality to the measured area;
it does not make any choice correct by definition.
-/
def MatchesDisplayedAreaChoice
    (setup : RelativisticTriangleSetup)
    (choice : AnswerChoice) : Prop :=
  areaInSquareMeters (setup.measuredArea .OPrime) =
    displayedAreaSquareMeters choice

/-!
The physical answer to the question under the stated simultaneous
Lorentz-contraction model is `12/5 m² = 2.4 m²`.  This is the target associated
with `thm:physics:phyx_mini_0566:target`; the source's recorded answer is not a
premise of the theorem.
-/
theorem problem_phyx_mini_0566
    (setup : RelativisticTriangleSetup)
    (_scenario : MatchesRelativisticTriangleScenario setup)
    (_figure : MatchesSuppliedTriangleFigure setup)
    (_data : MatchesProblemData setup)
    (_physical : HasPhysicalRelativisticParameters setup)
    (_geometry : SatisfiesRestEquilateralGeometry setup)
    (_measurement : SatisfiesSimultaneousCoordinateAreaMeasurement setup)
    (_contraction : ObeysLorentzCoordinateContraction setup) :
    areaInSquareMeters (setup.measuredArea .OPrime) = (12 / 5 : ℝ) := by
  exact standard_model_area_is_two_point_four setup _data _measurement _contraction

/-!
The source metadata records choice B, whose displayed value is `7/5 m²`.
Under the same stated data and standard contraction law, that choice does not
match the independently represented moving-frame area.  This conclusion makes
the source discrepancy machine-visible without treating either the recorded
label or its displayed value as physical input data.
-/
theorem recorded_answer_disagrees_with_standard_model
    (setup : RelativisticTriangleSetup)
    (_data : MatchesProblemData setup)
    (_measurement : SatisfiesSimultaneousCoordinateAreaMeasurement setup)
    (_contraction : ObeysLorentzCoordinateContraction setup) :
    ¬ MatchesDisplayedAreaChoice setup recordedDatasetAnswer := by
  intro hchoice
  have hstandard :=
    standard_model_area_is_two_point_four setup _data _measurement _contraction
  unfold MatchesDisplayedAreaChoice recordedDatasetAnswer displayedAreaSquareMeters at hchoice
  linarith

end PhyXMiniProblems.ProblemPhyXMini0566
