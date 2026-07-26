import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Order.Interval.Set.Defs
import Physlib.QuantumMechanics.HilbertSpaces.OneDimension.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0648

/-!
# Neutron position probability from a plotted wavefunction

The supplied primary image plots a one-dimensional neutron wavefunction.  Its
horizontal coordinate is the numerical value of position in millimetres, while
the complex amplitude readout has the corresponding inverse-square-root
millimetre role.  The dimensionless position probability is represented by a
normalized probability measure and is related to the amplitude only through a
separate Born-law premise.

The primary image, rather than its auxiliary caption, shows a negative constant
plateau on `(-4, 0)`, a positive constant plateau on `(0, 4)`, and zero outside
the plotted support.  Values at the three jump locations do not affect any
position probability and are intentionally left unspecified.
-/

/-! ## Physical state and primary-figure vocabulary -/

/-- The particle species named by the problem statement. -/
inductive QuantumParticleKind where
  | neutron
  deriving DecidableEq, Repr

/-- Qualitative shape of the wavefunction in the supplied primary image. -/
inductive WaveFunctionCurveShape where
  | twoConstantPlateausWithCentralSignChange
  deriving DecidableEq, Repr

/-!
Numerical and textual readouts from the plotted wavefunction.

Coordinates are real readouts in millimetres.  The amplitude scale is the real
number printed as `c`; as a wavefunction amplitude it has the implicit unit
`mm⁻¹ᐟ²`, rather than being an untyped physical scalar.
-/
structure NeutronWaveFunctionFigure where
  xAxisLabel : String
  xAxisUnitLabel : String
  yAxisLabel : String
  positiveAmplitudeLabel : String
  negativeAmplitudeLabel : String
  printedXTickMillimeters : List ℝ
  leftSupportEdgeMillimeters : ℝ
  centralJumpMillimeters : ℝ
  rightSupportEdgeMillimeters : ℝ
  amplitudeScalePerSqrtMillimeter : ℝ
  curveShape : WaveFunctionCurveShape
  antisymmetricAboutOrigin : Bool

/-!
A neutron position experiment with a coordinate representative of its quantum
state and an independently specified probability observable.  Normalization is
carried by `ProbabilityMeasure`; Born's rule is imposed separately below.
-/
structure NeutronPositionExperiment where
  particleKind : QuantumParticleKind
  waveAmplitudePerSqrtMillimeter : ℝ → ℂ
  positionProbability : MeasureTheory.ProbabilityMeasure ℝ
  figure : NeutronWaveFunctionFigure

/-! ## Governing quantum laws -/

/-!
One-dimensional state admissibility and the position-space Born rule.

Lebesgue volume is taken on the numerical millimetre coordinate.  Thus
`Complex.normSq` has reciprocal-millimetre density role, and `withDensity`
turns it into the dimensionless position-probability measure.
-/
structure SatisfiesOneDimensionalPositionQuantumLaws
    (experiment : NeutronPositionExperiment) : Prop where
  waveFunction_memHS :
    QuantumMechanics.OneDimension.HilbertSpace.MemHS
      experiment.waveAmplitudePerSqrtMillimeter
  bornPositionMeasure :
    experiment.positionProbability.toMeasure =
      (MeasureTheory.volume : MeasureTheory.Measure ℝ).withDensity
        (fun xMillimeters : ℝ ↦
          ENNReal.ofReal
            (Complex.normSq
              (experiment.waveAmplitudePerSqrtMillimeter xMillimeters)))

/-! ## Problem-statement and figure readouts -/

/-!
Literal labels, landmarks, and plateau values read from the primary image
`648.png`.  This predicate contains no probability of the requested interval
and no numerical answer-choice value.
-/
structure MatchesProblemStatementAndFigure
    (experiment : NeutronPositionExperiment) : Prop where
  particleIsNeutron : experiment.particleKind = .neutron
  horizontalAxisIsPosition : experiment.figure.xAxisLabel = "x"
  horizontalAxisUsesMillimeters : experiment.figure.xAxisUnitLabel = "mm"
  verticalAxisIsWavefunction : experiment.figure.yAxisLabel = "ψ(x)"
  positiveLevelIsLabelledC :
    experiment.figure.positiveAmplitudeLabel = "c"
  negativeLevelIsLabelledMinusC :
    experiment.figure.negativeAmplitudeLabel = "-c"
  displayedTicks :
    experiment.figure.printedXTickMillimeters = [-4, -2, 2, 4]
  leftSupportEdge : experiment.figure.leftSupportEdgeMillimeters = -4
  centralSignChange : experiment.figure.centralJumpMillimeters = 0
  rightSupportEdge : experiment.figure.rightSupportEdgeMillimeters = 4
  displayedCurveShape :
    experiment.figure.curveShape =
      .twoConstantPlateausWithCentralSignChange
  displayedAntisymmetry :
    experiment.figure.antisymmetricAboutOrigin = true
  amplitudeScaleIsPositive :
    0 < experiment.figure.amplitudeScalePerSqrtMillimeter
  negativePlateau : ∀ xMillimeters : ℝ,
    experiment.figure.leftSupportEdgeMillimeters < xMillimeters →
    xMillimeters < experiment.figure.centralJumpMillimeters →
      experiment.waveAmplitudePerSqrtMillimeter xMillimeters =
        ((-experiment.figure.amplitudeScalePerSqrtMillimeter : ℝ) : ℂ)
  positivePlateau : ∀ xMillimeters : ℝ,
    experiment.figure.centralJumpMillimeters < xMillimeters →
    xMillimeters < experiment.figure.rightSupportEdgeMillimeters →
      experiment.waveAmplitudePerSqrtMillimeter xMillimeters =
        ((experiment.figure.amplitudeScalePerSqrtMillimeter : ℝ) : ℂ)
  zeroOutsidePlottedSupport : ∀ xMillimeters : ℝ,
    (xMillimeters < experiment.figure.leftSupportEdgeMillimeters ∨
      experiment.figure.rightSupportEdgeMillimeters < xMillimeters) →
      experiment.waveAmplitudePerSqrtMillimeter xMillimeters = 0

/-! ## Requested event and answer choices -/

/-- A closed interval of numerical position readouts, measured in millimetres. -/
structure PositionIntervalReadout where
  lowerMillimeters : ℝ
  upperMillimeters : ℝ

/-- The measurable position event represented by an interval readout. -/
def PositionIntervalReadout.region
    (interval : PositionIntervalReadout) : Set ℝ :=
  Set.Icc interval.lowerMillimeters interval.upperMillimeters

/-- The dimensionless probability assigned to a position interval. -/
def intervalProbability
    (experiment : NeutronPositionExperiment)
    (interval : PositionIntervalReadout) : ℝ :=
  (experiment.positionProbability.toMeasure interval.region).toReal

/-- The interval from `x = -1 mm` through `x = 1 mm` asked for in the problem. -/
def requestedCentralInterval : PositionIntervalReadout where
  lowerMillimeters := -1
  upperMillimeters := 1

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The dimensionless probability printed beside each answer choice. -/
def AnswerChoice.probabilityValue : AnswerChoice → ℝ
  | .A => 3 / 4
  | .B => 45 / 100
  | .C => 1 / 4
  | .D => 1 / 10

/-- Dataset metadata records choice C; this constant is never a premise. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- A choice matches when its displayed value equals the modeled probability. -/
def MatchesAnswerChoice
    (experiment : NeutronPositionExperiment)
    (interval : PositionIntervalReadout)
    (choice : AnswerChoice) : Prop :=
  intervalProbability experiment interval = choice.probabilityValue

/-!
Blueprint label: `thm:physics:phyx_mini_0648:target`.

For the normalized two-plateau neutron state shown in the figure, the central
`2 mm` interval occupies one quarter of the constant-density `8 mm` support.
-/
theorem problem_phyx_mini_0648
    (experiment : NeutronPositionExperiment)
    (hLaws : SatisfiesOneDimensionalPositionQuantumLaws experiment)
    (hFigure : MatchesProblemStatementAndFigure experiment) :
    intervalProbability experiment requestedCentralInterval = (1 : ℝ) / 4 := by
  let ρ : ℝ → ENNReal := fun xMillimeters ↦
    ENNReal.ofReal
      (Complex.normSq
        (experiment.waveAmplitudePerSqrtMillimeter xMillimeters))
  let d : ENNReal :=
    ENNReal.ofReal
      (experiment.figure.amplitudeScalePerSqrtMillimeter *
        experiment.figure.amplitudeScalePerSqrtMillimeter)
  have hDensity :
      ρ =ᵐ[MeasureTheory.volume]
        (Set.Ioo (-4 : ℝ) 4).indicator (fun _ : ℝ ↦ d) := by
    have hNegFour :
        ∀ᵐ xMillimeters : ℝ ∂MeasureTheory.volume,
          xMillimeters ≠ (-4 : ℝ) := by
      simp [MeasureTheory.ae_iff]
    have hZero :
        ∀ᵐ xMillimeters : ℝ ∂MeasureTheory.volume,
          xMillimeters ≠ (0 : ℝ) := by
      simp [MeasureTheory.ae_iff]
    have hFour :
        ∀ᵐ xMillimeters : ℝ ∂MeasureTheory.volume,
          xMillimeters ≠ (4 : ℝ) := by
      simp [MeasureTheory.ae_iff]
    filter_upwards [hNegFour, hZero, hFour] with
      xMillimeters hxNegFour hxZero hxFour
    by_cases hxSupport : xMillimeters ∈ Set.Ioo (-4 : ℝ) 4
    · rw [Set.indicator_of_mem hxSupport]
      rcases lt_or_gt_of_ne hxZero with hxNegative | hxPositive
      · have hWave :
            experiment.waveAmplitudePerSqrtMillimeter xMillimeters =
              ((-experiment.figure.amplitudeScalePerSqrtMillimeter : ℝ) : ℂ) := by
          apply hFigure.negativePlateau xMillimeters
          · simpa [hFigure.leftSupportEdge] using hxSupport.1
          · simpa [hFigure.centralSignChange] using hxNegative
        simp [ρ, d, hWave, Complex.normSq_ofReal]
      · have hWave :
            experiment.waveAmplitudePerSqrtMillimeter xMillimeters =
              ((experiment.figure.amplitudeScalePerSqrtMillimeter : ℝ) : ℂ) := by
          apply hFigure.positivePlateau xMillimeters
          · simpa [hFigure.centralSignChange] using hxPositive
          · simpa [hFigure.rightSupportEdge] using hxSupport.2
        simp [ρ, d, hWave, Complex.normSq_ofReal]
    · have hxOutside :
          xMillimeters < (-4 : ℝ) ∨ (4 : ℝ) < xMillimeters := by
        simp only [Set.mem_Ioo] at hxSupport
        by_contra hNotOutside
        have hNotLeft : ¬xMillimeters < (-4 : ℝ) :=
          fun hxLeft ↦ hNotOutside (Or.inl hxLeft)
        have hNotRight : ¬(4 : ℝ) < xMillimeters :=
          fun hxRight ↦ hNotOutside (Or.inr hxRight)
        exact hxSupport
          ⟨lt_of_le_of_ne (le_of_not_gt hNotLeft) (Ne.symm hxNegFour),
            lt_of_le_of_ne (le_of_not_gt hNotRight) hxFour⟩
      have hWave :
          experiment.waveAmplitudePerSqrtMillimeter xMillimeters = 0 := by
        apply hFigure.zeroOutsidePlottedSupport xMillimeters
        simpa [hFigure.leftSupportEdge, hFigure.rightSupportEdge] using hxOutside
      simp [ρ, hWave, Set.indicator_of_notMem hxSupport]
  have hTotal : (∫⁻ xMillimeters : ℝ, ρ xMillimeters ∂MeasureTheory.volume) = 1 := by
    calc
      (∫⁻ xMillimeters : ℝ, ρ xMillimeters ∂MeasureTheory.volume) =
          (MeasureTheory.volume : MeasureTheory.Measure ℝ).withDensity ρ Set.univ := by
            simp [MeasureTheory.withDensity_apply]
      _ = experiment.positionProbability.toMeasure Set.univ := by
        rw [← hLaws.bornPositionMeasure]
      _ = 1 := MeasureTheory.IsProbabilityMeasure.measure_univ
  have hWholeIntegral :
      (∫⁻ xMillimeters : ℝ, ρ xMillimeters ∂MeasureTheory.volume) = d * 8 := by
    calc
      (∫⁻ xMillimeters : ℝ, ρ xMillimeters ∂MeasureTheory.volume) =
          ∫⁻ xMillimeters : ℝ,
            (Set.Ioo (-4 : ℝ) 4).indicator (fun _ : ℝ ↦ d) xMillimeters
              ∂MeasureTheory.volume :=
        MeasureTheory.lintegral_congr_ae hDensity
      _ = ∫⁻ _xMillimeters : ℝ in Set.Ioo (-4 : ℝ) 4, d
            ∂MeasureTheory.volume := by
        rw [MeasureTheory.lintegral_indicator measurableSet_Ioo]
      _ = d * MeasureTheory.volume (Set.Ioo (-4 : ℝ) 4) :=
        MeasureTheory.setLIntegral_const _ _
      _ = d * 8 := by
        norm_num [Real.volume_Ioo]
  have hNormalizedDensity : d * 8 = 1 :=
    hWholeIntegral.symm.trans hTotal
  have hCentralIntegral :
      (∫⁻ xMillimeters : ℝ in Set.Icc (-1 : ℝ) 1, ρ xMillimeters
        ∂MeasureTheory.volume) = d * 2 := by
    calc
      (∫⁻ xMillimeters : ℝ in Set.Icc (-1 : ℝ) 1, ρ xMillimeters
          ∂MeasureTheory.volume) =
          ∫⁻ xMillimeters : ℝ in Set.Icc (-1 : ℝ) 1,
            (Set.Ioo (-4 : ℝ) 4).indicator (fun _ : ℝ ↦ d) xMillimeters
              ∂MeasureTheory.volume := by
        apply MeasureTheory.setLIntegral_congr_fun_ae measurableSet_Icc
        filter_upwards [hDensity] with xMillimeters hxDensity
        intro _
        exact hxDensity
      _ = ∫⁻ _xMillimeters : ℝ in Set.Icc (-1 : ℝ) 1, d
            ∂MeasureTheory.volume := by
        apply MeasureTheory.setLIntegral_congr_fun measurableSet_Icc
        intro xMillimeters hxCentral
        rw [Set.indicator_of_mem]
        constructor <;> linarith [hxCentral.1, hxCentral.2]
      _ = d * MeasureTheory.volume (Set.Icc (-1 : ℝ) 1) :=
        MeasureTheory.setLIntegral_const _ _
      _ = d * 2 := by
        norm_num [Real.volume_Icc]
  change
    (experiment.positionProbability.toMeasure (Set.Icc (-1 : ℝ) 1)).toReal =
      (1 : ℝ) / 4
  rw [hLaws.bornPositionMeasure,
    MeasureTheory.withDensity_apply _ measurableSet_Icc]
  change
    (∫⁻ xMillimeters : ℝ in Set.Icc (-1 : ℝ) 1, ρ xMillimeters
      ∂MeasureTheory.volume).toReal = (1 : ℝ) / 4
  rw [hCentralIntegral, ENNReal.toReal_mul]
  norm_num
  have hNormalizedDensityReal : d.toReal * 8 = 1 := by
    rw [← ENNReal.toReal_ofNat 8, ← ENNReal.toReal_mul, hNormalizedDensity]
    norm_num
  linarith

/-- Consequently, the probability agrees with the value printed as choice C. -/
theorem recorded_choice_is_correct
    (experiment : NeutronPositionExperiment)
    (hLaws : SatisfiesOneDimensionalPositionQuantumLaws experiment)
    (hFigure : MatchesProblemStatementAndFigure experiment) :
    MatchesAnswerChoice experiment requestedCentralInterval .C := by
  simpa [MatchesAnswerChoice, AnswerChoice.probabilityValue] using
    problem_phyx_mini_0648 experiment hLaws hFigure

end PhyXMiniProblems.ProblemPhyXMini0648
