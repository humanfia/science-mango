import Mathlib
import Physlib.QuantumMechanics.HilbertSpaces.OneDimension.Basic
import Physlib.SpaceAndTime.Space.LengthUnit

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0651

open MeasureTheory
open scoped Interval

/-!
# Position probability for a triangular wavefunction

The primary bitmap plots a one-dimensional wavefunction against a position
axis measured in nanometres.  Its red graph is zero outside `[0, 1]`, rises
linearly from `(0, 0)` to the point `(3/4, c)`, and falls linearly to `(1, 0)`.
In particular, the image places the peak at the third tick, `3/4 nm`; the
auxiliary caption's claim that the peak is at `1/2 nm` is not consistent with
the image or with the recorded numerical answer.

The real arguments below are calibrated position readouts in nanometres, and
the complex values are wavefunction-amplitude readouts in `nm⁻¹ᐟ²`.  Thus
`Complex.normSq` has unit `nm⁻¹`, while its integral against the nanometre
coordinate is a dimensionless probability.  Physlib's `MemHS` records that
the representative belongs to the one-dimensional quantum Hilbert space.

Assumption/target split:

* governing laws: square-integrability, normalization, and the Born rule;
* previous-part results: none;
* figure/data readouts: the axis labels and unit, endpoints `0` and `1 nm`,
  quarter ticks, the peak `(3/4 nm, c)`, the two straight segments, zero
  amplitude outside the confining interval, and query interval `[0, 1/4] nm`;
* current targets: `c² = 3`, interval probability `1/36`, its three-decimal
  display `0.028`, and unique selection of answer choice C.
-/

/-! ## Physical setup and calibrated readouts -/

/-- The Physlib length unit used for every scalar position readout below. -/
def positionAxisUnit : LengthUnit := LengthUnit.nanometers

/-- Labels and numerical geometry read from the supplied wavefunction plot. -/
structure TriangularWavefunctionFigure where
  horizontalAxisLabel : String
  horizontalAxisUnitLabel : String
  verticalAxisLabel : String
  peakAmplitudeLabel : String
  leftEndpointNm : ℝ
  firstQuarterTickNm : ℝ
  midpointTickNm : ℝ
  peakPositionNm : ℝ
  rightEndpointNm : ℝ
  profileIsDrawnZeroOutside : Bool

/--
The particle's one-dimensional position experiment.

`waveAmplitudePerSqrtNanometre` is a pointwise representative of the quantum
state, needed because the figure specifies point values.  The physical
square-integrability condition is imposed separately using Physlib's
`HilbertSpace.MemHS`.  `intervalProbability` is an independent observable
whose relation to the wavefunction is supplied by the general Born law.
-/
structure TriangularWavefunctionExperiment where
  waveAmplitudePerSqrtNanometre : ℝ → ℂ
  peakAmplitudePerSqrtNanometre : ℝ
  intervalProbability : ℝ → ℝ → ℝ
  figure : TriangularWavefunctionFigure

/-- The squared-modulus position density, numerically measured in `nm⁻¹`. -/
def probabilityDensityPerNanometre
    (experiment : TriangularWavefunctionExperiment) (xNm : ℝ) : ℝ :=
  Complex.normSq (experiment.waveAmplitudePerSqrtNanometre xNm)

/-- Numerical endpoints of the interval asked about in the problem. -/
structure PositionProbabilityQuestion where
  lowerEndpointNm : ℝ
  upperEndpointNm : ℝ

/-! ## Primary-figure and question readouts -/

/--
Direct transcription of the labels and tick locations in image `651.png`,
together with the two red straight-line segments and the stated confinement.
The amplitude `c` is positive because the plotted peak lies above the axis.
-/
structure MatchesSuppliedTriangularWavefunctionFigure
    (experiment : TriangularWavefunctionExperiment) : Prop where
  horizontalAxis : experiment.figure.horizontalAxisLabel = "x"
  horizontalUnit : experiment.figure.horizontalAxisUnitLabel = "nm"
  verticalAxis : experiment.figure.verticalAxisLabel = "ψ(x)"
  peakLabel : experiment.figure.peakAmplitudeLabel = "c"
  leftEndpoint : experiment.figure.leftEndpointNm = 0
  firstQuarterTick : experiment.figure.firstQuarterTickNm = (1 : ℝ) / 4
  midpointTick : experiment.figure.midpointTickNm = (1 : ℝ) / 2
  peakAtThirdQuarter : experiment.figure.peakPositionNm = (3 : ℝ) / 4
  rightEndpoint : experiment.figure.rightEndpointNm = 1
  zeroOutsideShown : experiment.figure.profileIsDrawnZeroOutside = true
  peakAmplitudePositive : 0 < experiment.peakAmplitudePerSqrtNanometre
  risingSegment :
    ∀ xNm ∈ Set.Icc experiment.figure.leftEndpointNm
        experiment.figure.peakPositionNm,
      experiment.waveAmplitudePerSqrtNanometre xNm =
        Complex.ofReal
          (experiment.peakAmplitudePerSqrtNanometre *
            (xNm - experiment.figure.leftEndpointNm) /
              (experiment.figure.peakPositionNm -
                experiment.figure.leftEndpointNm))
  fallingSegment :
    ∀ xNm ∈ Set.Icc experiment.figure.peakPositionNm
        experiment.figure.rightEndpointNm,
      experiment.waveAmplitudePerSqrtNanometre xNm =
        Complex.ofReal
          (experiment.peakAmplitudePerSqrtNanometre *
            (experiment.figure.rightEndpointNm - xNm) /
              (experiment.figure.rightEndpointNm -
                experiment.figure.peakPositionNm))
  zeroOutsideConfinement :
    ∀ xNm : ℝ,
      (xNm < experiment.figure.leftEndpointNm ∨
        experiment.figure.rightEndpointNm < xNm) →
      experiment.waveAmplitudePerSqrtNanometre xNm = 0

/-- The queried position interval is exactly `0 nm ≤ x ≤ 0.25 nm`. -/
structure MatchesStatedPositionQuestion
    (question : PositionProbabilityQuestion) : Prop where
  lowerEndpoint : question.lowerEndpointNm = 0
  upperEndpoint : question.upperEndpointNm = (1 : ℝ) / 4

/-! ## Governing quantum laws -/

/--
The standard normalized one-dimensional Born model in nanometre coordinates.
These are general laws and do not prescribe the probability of the currently
queried interval or any answer-choice value.
-/
structure SatisfiesNormalizedBornModel
    (experiment : TriangularWavefunctionExperiment) : Prop where
  wavefunction_memHS :
    QuantumMechanics.OneDimension.HilbertSpace.MemHS
      experiment.waveAmplitudePerSqrtNanometre
  totalProbabilityIsOne :
    (∫ xNm : ℝ, probabilityDensityPerNanometre experiment xNm) = 1
  bornRule :
    ∀ lowerNm upperNm : ℝ,
      lowerNm ≤ upperNm →
      experiment.intervalProbability lowerNm upperNm =
        ∫ xNm in lowerNm..upperNm,
          probabilityDensityPerNanometre experiment xNm

/-! ## Printed answer choices -/

/-- Labels of the four probability values printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The dimensionless probability printed beside each answer label. -/
def displayedProbability : AnswerChoice → ℝ
  | .A => 20 / 1000
  | .B => 24 / 1000
  | .C => 28 / 1000
  | .D => 32 / 1000

/--
A dimensionless probability has the indicated nearest-thousandth display.
The half-open interval implements the usual half-up convention.
-/
def RoundsToThousandth (probability : ℝ) (thousandths : ℤ) : Prop :=
  (thousandths : ℝ) / 1000 - 1 / 2000 ≤ probability ∧
    probability < (thousandths : ℝ) / 1000 + 1 / 2000

/-- A displayed choice is strictly closer than every other printed value. -/
def IsUniqueClosestDisplayedChoice
    (probability : ℝ) (selected : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    other ≠ selected →
      |probability - displayedProbability selected| <
        |probability - displayedProbability other|

/-! ## Derived normalization and probability targets -/

/--
Normalization of the asymmetric triangular wavefunction fixes the squared
peak readout to `3 nm⁻¹`.
-/
lemma peakAmplitude_sq_eq_three
    (experiment : TriangularWavefunctionExperiment)
    (hFigure : MatchesSuppliedTriangularWavefunctionFigure experiment)
    (hBorn : SatisfiesNormalizedBornModel experiment) :
    experiment.peakAmplitudePerSqrtNanometre ^ 2 = 3 := by
  let squaredAmplitude : ℝ → ℝ := fun xNm =>
    probabilityDensityPerNanometre experiment xNm
  have hSquaredAmplitudeIntegrable : Integrable squaredAmplitude := by
    simpa only [squaredAmplitude, probabilityDensityPerNanometre,
      Complex.normSq_eq_norm_sq] using
      (QuantumMechanics.OneDimension.HilbertSpace.memHS_iff.mp
        hBorn.wavefunction_memHS).2
  have hSupport : Function.support squaredAmplitude ⊆ Set.Ioc 0 1 := by
    intro xNm hx
    change squaredAmplitude xNm ≠ 0 at hx
    constructor
    · by_contra hxPositive
      have hxNonpositive : xNm ≤ 0 := le_of_not_gt hxPositive
      apply hx
      simp only [squaredAmplitude, probabilityDensityPerNanometre]
      by_cases hxZero : xNm = 0
      · subst xNm
        rw [hFigure.risingSegment 0]
        · norm_num [Complex.normSq_ofReal, hFigure.leftEndpoint,
            hFigure.peakAtThirdQuarter]
        · rw [hFigure.leftEndpoint, hFigure.peakAtThirdQuarter]
          norm_num
      · rw [hFigure.zeroOutsideConfinement xNm]
        · norm_num
        · left
          simpa [hFigure.leftEndpoint] using
            lt_of_le_of_ne hxNonpositive hxZero
    · by_contra hxAtMostOne
      apply hx
      simp only [squaredAmplitude, probabilityDensityPerNanometre]
      rw [hFigure.zeroOutsideConfinement xNm]
      · norm_num
      · right
        simpa [hFigure.rightEndpoint] using lt_of_not_ge hxAtMostOne
  have hTotal :
      (∫ xNm in (0 : ℝ)..1, squaredAmplitude xNm) = 1 := by
    rw [intervalIntegral.integral_eq_integral_of_support_subset hSupport]
    exact hBorn.totalProbabilityIsOne
  have hSplit :
      (∫ xNm in (0 : ℝ)..((3 : ℝ) / 4), squaredAmplitude xNm) +
        ∫ xNm in ((3 : ℝ) / 4)..1, squaredAmplitude xNm = 1 := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      hSquaredAmplitudeIntegrable.intervalIntegrable
      hSquaredAmplitudeIntegrable.intervalIntegrable]
    exact hTotal
  have hRisingIntegral :
      (∫ xNm in (0 : ℝ)..((3 : ℝ) / 4), squaredAmplitude xNm) =
        experiment.peakAmplitudePerSqrtNanometre ^ 2 / 4 := by
    calc
      (∫ xNm in (0 : ℝ)..((3 : ℝ) / 4), squaredAmplitude xNm) =
          ∫ xNm in (0 : ℝ)..((3 : ℝ) / 4),
            (experiment.peakAmplitudePerSqrtNanometre *
              xNm / ((3 : ℝ) / 4)) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro xNm hx
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 4)] at hx
        have hxFigure :
            xNm ∈ Set.Icc experiment.figure.leftEndpointNm
              experiment.figure.peakPositionNm := by
          simpa [hFigure.leftEndpoint, hFigure.peakAtThirdQuarter] using hx
        simp only [squaredAmplitude, probabilityDensityPerNanometre,
          hFigure.risingSegment xNm hxFigure, Complex.normSq_ofReal]
        rw [hFigure.leftEndpoint, hFigure.peakAtThirdQuarter]
        ring
      _ = experiment.peakAmplitudePerSqrtNanometre ^ 2 / 4 := by
        rw [show
          (fun xNm : ℝ =>
            (experiment.peakAmplitudePerSqrtNanometre *
              xNm / ((3 : ℝ) / 4)) ^ 2) =
          (fun xNm : ℝ =>
            (16 * experiment.peakAmplitudePerSqrtNanometre ^ 2 / 9) *
              xNm ^ 2) by
            funext xNm
            ring]
        rw [intervalIntegral.integral_const_mul, integral_pow]
        norm_num
        ring
  have hFallingIntegral :
      (∫ xNm in ((3 : ℝ) / 4)..(1 : ℝ), squaredAmplitude xNm) =
        experiment.peakAmplitudePerSqrtNanometre ^ 2 / 12 := by
    calc
      (∫ xNm in ((3 : ℝ) / 4)..(1 : ℝ), squaredAmplitude xNm) =
          ∫ xNm in ((3 : ℝ) / 4)..(1 : ℝ),
            (experiment.peakAmplitudePerSqrtNanometre *
              (1 - xNm) / (1 - ((3 : ℝ) / 4))) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro xNm hx
        rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) / 4 ≤ 1)] at hx
        have hxFigure :
            xNm ∈ Set.Icc experiment.figure.peakPositionNm
              experiment.figure.rightEndpointNm := by
          simpa [hFigure.peakAtThirdQuarter, hFigure.rightEndpoint] using hx
        simp only [squaredAmplitude, probabilityDensityPerNanometre,
          hFigure.fallingSegment xNm hxFigure, Complex.normSq_ofReal]
        rw [hFigure.peakAtThirdQuarter, hFigure.rightEndpoint]
        ring
      _ = experiment.peakAmplitudePerSqrtNanometre ^ 2 / 12 := by
        rw [show
          (fun xNm : ℝ =>
            (experiment.peakAmplitudePerSqrtNanometre *
              (1 - xNm) / (1 - ((3 : ℝ) / 4))) ^ 2) =
          (fun xNm : ℝ =>
            (16 * experiment.peakAmplitudePerSqrtNanometre ^ 2) *
              (xNm - 1) ^ 2) by
            funext xNm
            ring]
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_comp_sub_right
            (fun xNm : ℝ => xNm ^ 2) 1,
          integral_pow]
        norm_num
        ring
  rw [hRisingIntegral, hFallingIntegral] at hSplit
  linarith

/--
The Born probability over the first quarter of the box is exactly `1/36`.
This is a derived relation, not a premise of the physical model.
-/
lemma firstQuarterProbability_eq_one_div_thirtySix
    (experiment : TriangularWavefunctionExperiment)
    (question : PositionProbabilityQuestion)
    (hFigure : MatchesSuppliedTriangularWavefunctionFigure experiment)
    (hQuestion : MatchesStatedPositionQuestion question)
    (hBorn : SatisfiesNormalizedBornModel experiment) :
    experiment.intervalProbability
        question.lowerEndpointNm question.upperEndpointNm = (1 : ℝ) / 36 := by
  rw [hQuestion.lowerEndpoint, hQuestion.upperEndpoint,
    hBorn.bornRule 0 ((1 : ℝ) / 4) (by norm_num)]
  calc
    (∫ xNm in (0 : ℝ)..((1 : ℝ) / 4),
        probabilityDensityPerNanometre experiment xNm) =
        ∫ xNm in (0 : ℝ)..((1 : ℝ) / 4),
          (experiment.peakAmplitudePerSqrtNanometre *
            xNm / ((3 : ℝ) / 4)) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro xNm hx
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 4)] at hx
      have hxFigure :
          xNm ∈ Set.Icc experiment.figure.leftEndpointNm
            experiment.figure.peakPositionNm := by
        rw [hFigure.leftEndpoint, hFigure.peakAtThirdQuarter]
        exact ⟨hx.1, le_trans hx.2 (by norm_num)⟩
      simp only [probabilityDensityPerNanometre,
        hFigure.risingSegment xNm hxFigure, Complex.normSq_ofReal]
      rw [hFigure.leftEndpoint, hFigure.peakAtThirdQuarter]
      ring
    _ = experiment.peakAmplitudePerSqrtNanometre ^ 2 / 108 := by
      rw [show
        (fun xNm : ℝ =>
          (experiment.peakAmplitudePerSqrtNanometre *
            xNm / ((3 : ℝ) / 4)) ^ 2) =
        (fun xNm : ℝ =>
          (16 * experiment.peakAmplitudePerSqrtNanometre ^ 2 / 9) *
            xNm ^ 2) by
          funext xNm
          ring]
      rw [intervalIntegral.integral_const_mul, integral_pow]
      norm_num
      ring
    _ = 1 / 36 := by
      rw [peakAmplitude_sq_eq_three experiment hFigure hBorn]
      norm_num

/-!
Blueprint label: `thm:physics:phyx_mini_0651:target`.

For the wavefunction and interval shown in the primary image, the probability
is `1/36`.  It rounds to `0.028` at three decimal places, and among the four
printed values choice C is uniquely closest.
-/
theorem problem_phyx_mini_0651
    (experiment : TriangularWavefunctionExperiment)
    (question : PositionProbabilityQuestion)
    (hFigure : MatchesSuppliedTriangularWavefunctionFigure experiment)
    (hQuestion : MatchesStatedPositionQuestion question)
    (hBorn : SatisfiesNormalizedBornModel experiment) :
    experiment.intervalProbability
        question.lowerEndpointNm question.upperEndpointNm = (1 : ℝ) / 36 ∧
      RoundsToThousandth
        (experiment.intervalProbability
          question.lowerEndpointNm question.upperEndpointNm) 28 ∧
      IsUniqueClosestDisplayedChoice
        (experiment.intervalProbability
          question.lowerEndpointNm question.upperEndpointNm) .C := by
  have hProbability :=
    firstQuarterProbability_eq_one_div_thirtySix
      experiment question hFigure hQuestion hBorn
  refine ⟨hProbability, ?_, ?_⟩
  · rw [hProbability]
    norm_num [RoundsToThousandth]
  · rw [hProbability]
    intro otherChoice hOtherChoice
    cases otherChoice with
    | A => norm_num [displayedProbability, abs_of_nonneg, abs_of_nonpos]
    | B => norm_num [displayedProbability, abs_of_nonneg, abs_of_nonpos]
    | C => exact (hOtherChoice rfl).elim
    | D => norm_num [displayedProbability, abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0651
