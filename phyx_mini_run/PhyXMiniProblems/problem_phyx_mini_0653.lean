import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Filter.Extr
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Most likely position from a triangular probability-density graph

The supplied figure plots the one-dimensional position probability density
`P(x)` for a particle.  Its horizontal coordinate is measured in centimetres,
its density readout therefore has units of inverse centimetres, and the graph
is a symmetric triangle with base endpoints at `-4 cm` and `4 cm` and apex at
`0 cm`.  The (unspecified) positive apex density is labelled `a`.

Positions and probability densities below retain their physical dimensions
through Physlib.  Real numbers are used only for named-unit coordinate and
density readouts, dimensionless probabilities, and the displayed choices.

Assumption/target split:

* `MatchesSuppliedPositionDensityFigure` records labels, units, ticks, and the
  three plotted landmarks read from the primary image;
* `FigurePlotsTriangularPositionDensity` records the positive, piecewise-linear
  triangular curve shown in the image;
* `SatisfiesPositionProbabilityLaws` records normalization and the relation
  between density integrals and position-event probabilities; and
* the unique density maximizer `x = 0 cm` and the correctness of answer choice C
  occur only in the conclusions of the final lemma and theorem.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0653

open CarriesDimension Dimension

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A signed, unit-independent position on the one-dimensional axis. -/
abbrev PositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative position-probability density, carrying inverse-length dimension. -/
abbrev ProbabilityDensityQuantity : Type :=
  Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-- Numerical coordinate of a physical position in a selected length unit. -/
def positionReadout (unit : LengthUnit) (position : PositionQuantity) : ℝ :=
  (position ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- Numerical density in the reciprocal of the selected length unit. -/
def densityReadout
    (unit : LengthUnit) (density : ProbabilityDensityQuantity) : ℝ :=
  ((density ({ UnitChoices.SI with length := unit } : UnitChoices)).val : ℝ)

/-- Construct a physical position from its centimetre coordinate. -/
def positionFromCentimeters (value : ℝ) : PositionQuantity :=
  toDimensionful
    ({ UnitChoices.SI with length := LengthUnit.centimeters } : UnitChoices)
    (show WithDim L𝓭 ℝ from ⟨value⟩)

/-! ## Particle distribution and primary-figure vocabulary -/

/--
A particle's one-dimensional position distribution.  The density and the
dimensionless probability assigned to coordinate events are independent
observables; the physical laws below relate them.
-/
structure OneDimensionalPositionDistribution where
  probabilityDensityAt : PositionQuantity → ProbabilityDensityQuantity
  probabilityOfCentimeterCoordinateSet : Set ℝ → ℝ

/-- Probability-density readout at a coordinate whose numerical value is in centimetres. -/
def densityAtCentimeterCoordinate
    (distribution : OneDimensionalPositionDistribution)
    (xInCentimeters : ℝ) : ℝ :=
  densityReadout LengthUnit.centimeters
    (distribution.probabilityDensityAt
      (positionFromCentimeters xInCentimeters))

/-- The qualitative curve shape visible in the supplied plot. -/
inductive DensityCurveShape where
  | symmetricTriangle
  | other
  deriving DecidableEq, Repr

/-- Labels of the five horizontal tick marks visible in the supplied image. -/
inductive HorizontalTickLabel where
  | minusFour
  | minusTwo
  | zero
  | plusTwo
  | plusFour
  deriving DecidableEq, Fintype, Repr

/--
Axis labels, units, ticks, landmarks, and the apex-height label shown in image
`653.png`.  The physical apex density is not assigned a numerical value.
-/
structure PositionDensityFigure where
  horizontalAxisLabel : String
  verticalAxisLabel : String
  horizontalAxisUnit : LengthUnit
  densityReciprocalLengthUnit : LengthUnit
  displayedTickCoordinateCm : HorizontalTickLabel → ℝ
  leftIntercept : PositionQuantity
  apexPosition : PositionQuantity
  rightIntercept : PositionQuantity
  apexDensityA : ProbabilityDensityQuantity
  apexHeightLabel : String
  verticalApexGuideShown : Bool
  curveShape : DensityCurveShape

/-- The particle distribution together with the graph that presents it. -/
structure ParticlePositionExperiment where
  distribution : OneDimensionalPositionDistribution
  figure : PositionDensityFigure

/-! ## Figure/data readouts -/

/--
Text, centimetre calibration, tick labels, and plotted landmark positions read
from the primary image.  This records that the triangle's apex is drawn above
the origin, but does not assert that the origin is the most likely position.
-/
structure MatchesSuppliedPositionDensityFigure
    (figure : PositionDensityFigure) : Prop where
  horizontalLabel : figure.horizontalAxisLabel = "x (cm)"
  verticalLabel : figure.verticalAxisLabel = "P(x)"
  horizontalUnitIsCentimeters :
    figure.horizontalAxisUnit = LengthUnit.centimeters
  densityUnitIsInverseCentimeters :
    figure.densityReciprocalLengthUnit = LengthUnit.centimeters
  minusFourTick : figure.displayedTickCoordinateCm .minusFour = -4
  minusTwoTick : figure.displayedTickCoordinateCm .minusTwo = -2
  zeroTick : figure.displayedTickCoordinateCm .zero = 0
  plusTwoTick : figure.displayedTickCoordinateCm .plusTwo = 2
  plusFourTick : figure.displayedTickCoordinateCm .plusFour = 4
  leftInterceptInCentimeters :
    positionReadout LengthUnit.centimeters figure.leftIntercept = -4
  apexPositionInCentimeters :
    positionReadout LengthUnit.centimeters figure.apexPosition = 0
  rightInterceptInCentimeters :
    positionReadout LengthUnit.centimeters figure.rightIntercept = 4
  apexLabel : figure.apexHeightLabel = "a"
  verticalGuideAtApex : figure.verticalApexGuideShown = true
  plottedShape : figure.curveShape = .symmetricTriangle

/-! ## Figure geometry and governing probability laws -/

/--
The plotted curve is zero outside its base and is the linear interpolation
from the left intercept to the positive height `a`, then back to the right
intercept.  This is primary-figure evidence; it contains no most-likely
position or answer-choice conclusion.
-/
structure FigurePlotsTriangularPositionDensity
    (experiment : ParticlePositionExperiment) : Prop where
  apexDensityIsPositive :
    0 < densityReadout LengthUnit.centimeters
      experiment.figure.apexDensityA
  triangularInterpolation :
    let leftX :=
      positionReadout LengthUnit.centimeters experiment.figure.leftIntercept
    let apexX :=
      positionReadout LengthUnit.centimeters experiment.figure.apexPosition
    let rightX :=
      positionReadout LengthUnit.centimeters experiment.figure.rightIntercept
    let apexDensity :=
      densityReadout LengthUnit.centimeters experiment.figure.apexDensityA
    ∀ xInCentimeters : ℝ,
      densityAtCentimeterCoordinate experiment.distribution xInCentimeters =
        if xInCentimeters < leftX ∨ rightX < xInCentimeters then
          0
        else if xInCentimeters ≤ apexX then
          apexDensity * (xInCentimeters - leftX) / (apexX - leftX)
        else
          apexDensity * (rightX - xInCentimeters) / (rightX - apexX)

/--
Normalization and the governing relation between a position density and the
dimensionless probability of a measurable coordinate event.  Nonnegativity is
built into `ProbabilityDensityQuantity` through its `NNReal` value type.
-/
structure SatisfiesPositionProbabilityLaws
    (distribution : OneDimensionalPositionDistribution) : Prop where
  densityIntegrable :
    MeasureTheory.Integrable (densityAtCentimeterCoordinate distribution)
  normalizedPositionDensity :
    (∫ xInCentimeters : ℝ,
      densityAtCentimeterCoordinate distribution xInCentimeters) = 1
  probabilityOfMeasurableSet :
    ∀ coordinateSet : Set ℝ, MeasurableSet coordinateSet →
      distribution.probabilityOfCentimeterCoordinateSet coordinateSet =
        ∫ xInCentimeters in coordinateSet,
          densityAtCentimeterCoordinate distribution xInCentimeters
  probabilityBounds :
    ∀ coordinateSet : Set ℝ, MeasurableSet coordinateSet →
      0 ≤ distribution.probabilityOfCentimeterCoordinateSet coordinateSet ∧
        distribution.probabilityOfCentimeterCoordinateSet coordinateSet ≤ 1

/-! ## Most-likely relation, displayed choices, and current target -/

/--
A centimetre coordinate is most likely precisely when the displayed density
has a global maximum there.  `IsMaxOn` states the governing maximization
criterion without selecting a coordinate.
-/
def IsMostLikelyCoordinateCm
    (distribution : OneDimensionalPositionDistribution)
    (xInCentimeters : ℝ) : Prop :=
  IsMaxOn (densityAtCentimeterCoordinate distribution) Set.univ xInCentimeters

/-- The displayed density has exactly one most-likely centimetre coordinate. -/
def IsUniqueMostLikelyCoordinateCm
    (distribution : OneDimensionalPositionDistribution)
    (xInCentimeters : ℝ) : Prop :=
  IsMostLikelyCoordinateCm distribution xInCentimeters ∧
    ∀ yInCentimeters : ℝ,
      IsMostLikelyCoordinateCm distribution yInCentimeters →
        yInCentimeters = xInCentimeters

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Centimetre coordinate printed beside each answer label. -/
def displayedPositionCm : AnswerChoice → ℝ
  | .A => 1
  | .B => -1
  | .C => 0
  | .D => 2

/-- The answer label recorded in the supplied dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A displayed choice names the distribution's unique most-likely coordinate. -/
def IsCorrectAnswer
    (distribution : OneDimensionalPositionDistribution)
    (choice : AnswerChoice) : Prop :=
  IsUniqueMostLikelyCoordinateCm distribution (displayedPositionCm choice)

/-- The selected displayed choice is the only choice satisfying the physical criterion. -/
def IsUniqueCorrectAnswer
    (distribution : OneDimensionalPositionDistribution)
    (choice : AnswerChoice) : Prop :=
  IsCorrectAnswer distribution choice ∧
    ∀ otherChoice : AnswerChoice,
      IsCorrectAnswer distribution otherChoice → otherChoice = choice

/-!
The positive symmetric triangular profile has its unique global density
maximum at the figure's apex, whose primary-image coordinate is `0 cm`.
-/
lemma suppliedTriangle_uniqueMostLikelyCoordinate
    (experiment : ParticlePositionExperiment)
    (h_figure : MatchesSuppliedPositionDensityFigure experiment.figure)
    (h_triangle : FigurePlotsTriangularPositionDensity experiment) :
    IsUniqueMostLikelyCoordinateCm experiment.distribution 0 := by
  have h_density (x : ℝ) :
      densityAtCentimeterCoordinate experiment.distribution x =
        if x < -4 ∨ 4 < x then
          0
        else if x ≤ 0 then
          densityReadout LengthUnit.centimeters experiment.figure.apexDensityA *
              (x - (-4)) / (0 - (-4))
        else
          densityReadout LengthUnit.centimeters experiment.figure.apexDensityA *
              (4 - x) / (4 - 0) := by
    simpa only [h_figure.leftInterceptInCentimeters,
      h_figure.apexPositionInCentimeters,
      h_figure.rightInterceptInCentimeters] using
        h_triangle.triangularInterpolation x
  have h_apex_pos :
      0 < densityReadout LengthUnit.centimeters
        experiment.figure.apexDensityA :=
    h_triangle.apexDensityIsPositive
  unfold IsUniqueMostLikelyCoordinateCm IsMostLikelyCoordinateCm
  constructor
  · intro x hx
    change densityAtCentimeterCoordinate experiment.distribution x ≤
      densityAtCentimeterCoordinate experiment.distribution 0
    rw [h_density x, h_density 0]
    norm_num
    by_cases h_outside : x < -4 ∨ 4 < x
    · rw [if_pos h_outside]
      positivity
    · rw [if_neg h_outside]
      by_cases h_left : x ≤ 0
      · rw [if_pos h_left]
        rcases not_or.mp h_outside with ⟨h_left_base, h_right_base⟩
        have h_left_bound : -4 ≤ x := not_lt.mp h_left_base
        have h_right_bound : x ≤ 4 := not_lt.mp h_right_base
        nlinarith
      · rw [if_neg h_left]
        rcases not_or.mp h_outside with ⟨h_left_base, h_right_base⟩
        have h_left_bound : -4 ≤ x := not_lt.mp h_left_base
        have h_right_bound : x ≤ 4 := not_lt.mp h_right_base
        nlinarith
  · intro y h_y
    have hy_bound := h_y (Set.mem_univ (0 : ℝ))
    change densityAtCentimeterCoordinate experiment.distribution 0 ≤
      densityAtCentimeterCoordinate experiment.distribution y at hy_bound
    rw [h_density 0, h_density y] at hy_bound
    norm_num at hy_bound
    by_cases h_outside : y < -4 ∨ 4 < y
    · rw [if_pos h_outside] at hy_bound
      nlinarith
    · rw [if_neg h_outside] at hy_bound
      by_cases h_left : y ≤ 0
      · rw [if_pos h_left] at hy_bound
        nlinarith
      · rw [if_neg h_left] at hy_bound
        nlinarith

/-!
The unique most-likely position is `x = 0 cm`, so the uniquely correct
displayed answer is the dataset's recorded choice C.

This formalizes `thm:physics:phyx_mini_0653:target`.  Neither maximality at
zero nor answer C occurs in a figure or physical-law premise.
-/
theorem problem_phyx_mini_0653
    (experiment : ParticlePositionExperiment)
    (h_figure : MatchesSuppliedPositionDensityFigure experiment.figure)
    (h_triangle : FigurePlotsTriangularPositionDensity experiment)
    (h_probability :
      SatisfiesPositionProbabilityLaws experiment.distribution) :
    IsUniqueMostLikelyCoordinateCm experiment.distribution 0 ∧
      IsUniqueCorrectAnswer experiment.distribution .C := by
  have h_unique :=
    suppliedTriangle_uniqueMostLikelyCoordinate experiment h_figure h_triangle
  refine ⟨h_unique, ?_⟩
  unfold IsUniqueCorrectAnswer IsCorrectAnswer
  constructor
  · simpa [displayedPositionCm] using h_unique
  · intro otherChoice h_other
    have h_coordinate : displayedPositionCm otherChoice = 0 :=
      h_unique.2 _ h_other.1
    cases otherChoice with
    | A => norm_num [displayedPositionCm] at h_coordinate
    | B => norm_num [displayedPositionCm] at h_coordinate
    | C => rfl
    | D => norm_num [displayedPositionCm] at h_coordinate

end PhyXMiniProblems.ProblemPhyXMini0653
