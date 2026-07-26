import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Physlib.QuantumMechanics.HilbertSpaces.OneDimension.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

/-!
# Electron position probability read from a plotted wavefunction

The supplied plot uses numerical position coordinates measured in centimeters and
numerical probability-density values measured in inverse centimeters.  Thus an
interval integral of `probabilityDensityPerCentimeter` against the centimeter
coordinate is dimensionless.

The physical input and the requested result are deliberately separated:

* `SatisfiesBornAndCountingLaws` records the general Born rule and the general
  scaling of an expected count by the number of detections.
* `MatchesSuppliedProbabilityDensityFigure` records the two straight graph
  segments, their labeled endpoints, and the zero density outside the plotted
  support.
* `MatchesDetectionQuestion` records the number of detections and the queried
  interval.
* `queriedIntervalProbability_eq_nineHundredths` and
  `problem_phyx_mini_0505` state the derived probability and count.  Neither
  value is assumed by any of the input predicates.
-/

namespace PhyXMiniProblems.ProblemPhyXMini0505

open scoped Interval

/-- The physical length unit used for every position-axis scalar readout. -/
noncomputable def positionAxisUnit : LengthUnit := LengthUnit.centimeters

/-- The physical dimension carried by the graph's vertical-axis readouts. -/
def probabilityDensityDimension : Dimension := (Dimension.L𝓭)⁻¹

/--
The physical experiment, represented through calibrated scalar readouts.

The argument of `waveFunctionInCentimeterCoordinates` and
`probabilityDensityPerCentimeter` is the numerical coordinate in centimeters.
The complex wavefunction readout therefore has the implicit unit `cm⁻¹ᐟ²`, and
its squared modulus has unit `cm⁻¹`.  Interval probabilities are dimensionless.
An expected count is real-valued even though the number of detected electrons is
natural-valued.
-/
structure ElectronPositionExperiment where
  waveFunctionInCentimeterCoordinates : ℝ → ℂ
  probabilityDensityPerCentimeter : ℝ → ℝ
  intervalProbability : ℝ → ℝ → ℝ
  detectedElectronCount : ℕ
  expectedLandingCount : ℝ → ℝ → ℝ

/-- Numerical labels on the position-probability-density plot. -/
structure ProbabilityDensityFigureAxes where
  leftEndpointCm : ℝ
  centerNodeCm : ℝ
  rightEndpointCm : ℝ
  zeroDensityPerCm : ℝ
  endpointDensityPerCm : ℝ

/-- Numerical centimeter coordinates defining the interval asked about. -/
structure DetectionQuestionReadout where
  lowerEndpointCm : ℝ
  upperEndpointCm : ℝ

/--
The supplied figure has endpoints `(-1 cm, 1 cm⁻¹)` and `(1 cm, 1 cm⁻¹)`, a
node at `(0 cm, 0 cm⁻¹)`, straight segments between those points, and zero
density outside `[-1 cm, 1 cm]`.
-/
def MatchesSuppliedProbabilityDensityFigure
    (experiment : ElectronPositionExperiment)
    (axes : ProbabilityDensityFigureAxes) : Prop :=
  axes.leftEndpointCm = -1 ∧
  axes.centerNodeCm = 0 ∧
  axes.rightEndpointCm = 1 ∧
  axes.zeroDensityPerCm = 0 ∧
  axes.endpointDensityPerCm = 1 ∧
  (∀ x ∈ Set.Icc axes.leftEndpointCm axes.centerNodeCm,
    experiment.probabilityDensityPerCentimeter x =
      axes.endpointDensityPerCm *
        (axes.centerNodeCm - x) /
          (axes.centerNodeCm - axes.leftEndpointCm)) ∧
  (∀ x ∈ Set.Icc axes.centerNodeCm axes.rightEndpointCm,
    experiment.probabilityDensityPerCentimeter x =
      axes.endpointDensityPerCm *
        (x - axes.centerNodeCm) /
          (axes.rightEndpointCm - axes.centerNodeCm)) ∧
  (∀ x, x < axes.leftEndpointCm ∨ axes.rightEndpointCm < x →
    experiment.probabilityDensityPerCentimeter x =
      axes.zeroDensityPerCm)

/-- The prose data: `10⁴` detections and the interval `[-0.30, 0.30] cm`. -/
def MatchesDetectionQuestion
    (experiment : ElectronPositionExperiment)
    (question : DetectionQuestionReadout) : Prop :=
  experiment.detectedElectronCount = 10 ^ 4 ∧
  question.lowerEndpointCm = -(3 / 10 : ℝ) ∧
  question.upperEndpointCm = 3 / 10

/--
General physical laws used in the calculation.

The density is the squared modulus of a square-integrable, normalized
one-dimensional wavefunction.  The Born rule obtains interval probability by
integrating that density, and the expected landing count is total detections
times interval probability.
-/
structure SatisfiesBornAndCountingLaws
    (experiment : ElectronPositionExperiment) : Prop where
  waveFunction_memHS :
    QuantumMechanics.OneDimension.HilbertSpace.MemHS
      experiment.waveFunctionInCentimeterCoordinates
  density_eq_modulus_sq :
    ∀ x, experiment.probabilityDensityPerCentimeter x =
      Complex.normSq (experiment.waveFunctionInCentimeterCoordinates x)
  density_normalized :
    (∫ x, experiment.probabilityDensityPerCentimeter x) = 1
  bornRule :
    ∀ a b, a ≤ b →
      experiment.intervalProbability a b =
        ∫ x in a..b, experiment.probabilityDensityPerCentimeter x
  expectedCountLaw :
    ∀ a b, a ≤ b →
      experiment.expectedLandingCount a b =
        (experiment.detectedElectronCount : ℝ) *
          experiment.intervalProbability a b

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice
  | A | B | C | D
  deriving DecidableEq

/-- Expected-electron counts printed beside the displayed answer choices. -/
def displayedExpectedCount : AnswerChoice → ℕ
  | .A => 500
  | .B => 1000
  | .C => 900
  | .D => 1300

/-- The answer label recorded in the source dataset, retained as metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/--
The area under the plotted density over `[-0.30, 0.30] cm` is `0.09`.
-/
lemma queriedIntervalProbability_eq_nineHundredths
    (experiment : ElectronPositionExperiment)
    (axes : ProbabilityDensityFigureAxes)
    (question : DetectionQuestionReadout)
    (hLaws : SatisfiesBornAndCountingLaws experiment)
    (hFigure : MatchesSuppliedProbabilityDensityFigure experiment axes)
    (hQuestion : MatchesDetectionQuestion experiment question) :
    experiment.intervalProbability
      question.lowerEndpointCm question.upperEndpointCm = 9 / 100 := by
  rcases hFigure with
    ⟨hLeftEndpoint, hCenterNode, hRightEndpoint, _hZeroDensity,
      hEndpointDensity, hDensityLeft, hDensityRight, _hDensityOutside⟩
  rcases hQuestion with ⟨_hDetectedCount, hLowerEndpoint, hUpperEndpoint⟩
  have hBounds :
      question.lowerEndpointCm ≤ question.upperEndpointCm := by
    rw [hLowerEndpoint, hUpperEndpoint]
    norm_num
  rw [hLaws.bornRule _ _ hBounds]
  have hLeftFormula :
      ∀ x ∈ Set.Icc (-(3 / 10 : ℝ)) 0,
        experiment.probabilityDensityPerCentimeter x = -x := by
    intro x hx
    have hxFigure :
        x ∈ Set.Icc axes.leftEndpointCm axes.centerNodeCm := by
      rw [hLeftEndpoint, hCenterNode]
      constructor <;> linarith [hx.1, hx.2]
    rw [hDensityLeft x hxFigure, hEndpointDensity, hCenterNode,
      hLeftEndpoint]
    ring
  have hRightFormula :
      ∀ x ∈ Set.Icc 0 (3 / 10 : ℝ),
        experiment.probabilityDensityPerCentimeter x = x := by
    intro x hx
    have hxFigure :
        x ∈ Set.Icc axes.centerNodeCm axes.rightEndpointCm := by
      rw [hCenterNode, hRightEndpoint]
      constructor <;> linarith [hx.1, hx.2]
    rw [hDensityRight x hxFigure, hEndpointDensity, hCenterNode,
      hRightEndpoint]
    ring
  have hDensityLeftIntegrable :
      IntervalIntegrable experiment.probabilityDensityPerCentimeter
        MeasureTheory.volume (-(3 / 10 : ℝ)) 0 := by
    refine (intervalIntegrable_congr ?_).2
      ((continuous_id.neg).intervalIntegrable _ _)
    intro x hx
    apply hLeftFormula x
    simpa [Set.uIcc_of_le (by norm_num : (-(3 / 10 : ℝ)) ≤ 0)] using
      (Set.uIoc_subset_uIcc hx)
  have hDensityRightIntegrable :
      IntervalIntegrable experiment.probabilityDensityPerCentimeter
        MeasureTheory.volume 0 (3 / 10 : ℝ) := by
    refine (intervalIntegrable_congr ?_).2
      (continuous_id.intervalIntegrable _ _)
    intro x hx
    apply hRightFormula x
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 10)] using
      (Set.uIoc_subset_uIcc hx)
  rw [hLowerEndpoint, hUpperEndpoint,
    ← intervalIntegral.integral_add_adjacent_intervals
      hDensityLeftIntegrable hDensityRightIntegrable]
  have hLeftIntegral :
      (∫ x in (-(3 / 10 : ℝ))..0,
        experiment.probabilityDensityPerCentimeter x) =
          ∫ x in (-(3 / 10 : ℝ))..0, -x := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply hLeftFormula x
    simpa [Set.uIcc_of_le (by norm_num : (-(3 / 10 : ℝ)) ≤ 0)] using hx
  have hRightIntegral :
      (∫ x in (0 : ℝ)..(3 / 10),
        experiment.probabilityDensityPerCentimeter x) =
          ∫ x in (0 : ℝ)..(3 / 10), x := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply hRightFormula x
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 10)] using hx
  have hRightIdIntegral :
      (∫ x in (0 : ℝ)..(3 / 10), x) = 9 / 200 := by
    have hReflection :
        (∫ x in (0 : ℝ)..(3 / 10), (3 / 10 : ℝ) - x) =
          ∫ x in (0 : ℝ)..(3 / 10), x := by
      simpa using
        (intervalIntegral.integral_comp_sub_left
          (fun x : ℝ => x) (3 / 10 : ℝ)
          (a := (0 : ℝ)) (b := 3 / 10))
    have hIdIntegrable :
        IntervalIntegrable (fun x : ℝ => x)
          MeasureTheory.volume 0 (3 / 10) :=
      continuous_id.intervalIntegrable _ _
    rw [intervalIntegral.integral_sub intervalIntegrable_const hIdIntegrable]
      at hReflection
    norm_num at hReflection ⊢
    linarith
  have hLeftIdIntegral :
      (∫ x in (-(3 / 10 : ℝ))..0, x) = -(9 / 200) := by
    have hReflection :
        (∫ x in (0 : ℝ)..(3 / 10), -x) =
          ∫ x in (-(3 / 10 : ℝ))..0, x := by
      simpa using
        (intervalIntegral.integral_comp_neg
          (fun x : ℝ => x) (a := (0 : ℝ)) (b := 3 / 10))
    rw [intervalIntegral.integral_neg, hRightIdIntegral] at hReflection
    linarith
  rw [hLeftIntegral, hRightIntegral, intervalIntegral.integral_neg,
    hLeftIdIntegral, hRightIdIntegral]
  norm_num

/--
Of `10⁴` detected electrons, the expected number in
`[-0.30 cm, 0.30 cm]` is `900`; this uniquely matches displayed choice C.

This is the declaration corresponding to blueprint label
`thm:physics:phyx_mini_0505:target`.
-/
theorem problem_phyx_mini_0505
    (experiment : ElectronPositionExperiment)
    (axes : ProbabilityDensityFigureAxes)
    (question : DetectionQuestionReadout)
    (hLaws : SatisfiesBornAndCountingLaws experiment)
    (hFigure : MatchesSuppliedProbabilityDensityFigure experiment axes)
    (hQuestion : MatchesDetectionQuestion experiment question) :
    experiment.expectedLandingCount
        question.lowerEndpointCm question.upperEndpointCm = 900 ∧
      (∀ choice,
        experiment.expectedLandingCount
            question.lowerEndpointCm question.upperEndpointCm =
              (displayedExpectedCount choice : ℝ) ↔
          choice = .C) := by
  have hIntervalProbability :=
    queriedIntervalProbability_eq_nineHundredths
      experiment axes question hLaws hFigure hQuestion
  rcases hQuestion with ⟨hDetectedCount, hLowerEndpoint, hUpperEndpoint⟩
  have hBounds :
      question.lowerEndpointCm ≤ question.upperEndpointCm := by
    rw [hLowerEndpoint, hUpperEndpoint]
    norm_num
  have hExpectedCount :
      experiment.expectedLandingCount
        question.lowerEndpointCm question.upperEndpointCm = 900 := by
    rw [hLaws.expectedCountLaw _ _ hBounds, hIntervalProbability,
      hDetectedCount]
    norm_num
  refine ⟨hExpectedCount, ?_⟩
  intro choice
  cases choice <;> simp [displayedExpectedCount, hExpectedCount]

end PhyXMiniProblems.ProblemPhyXMini0505
