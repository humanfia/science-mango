import Mathlib
import Physlib.QuantumMechanics.HilbertSpaces.OneDimension.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0647

open MeasureTheory

/-!
# Electron position probability from a piecewise-constant wavefunction

The supplied image plots a one-dimensional electron wavefunction.  The horizontal
coordinate is the numerical position readout in nanometres, while
`waveAmplitudePerSqrtNanometer x` is the numerical complex amplitude readout in
inverse square-root nanometres.  Consequently, `Complex.normSq` has the role of a
probability density per nanometre and its density measure gives dimensionless
probabilities.

The image is primary evidence: its two outer plateaus have height `-c/2`, despite
the auxiliary prose caption saying `-c`.  The central plateau has height `c`.

Assumption/target split:

* governing laws: square-integrability and the position-space Born rule;
* previous-part results: none;
* figure/data readouts: an electron, axis labels and units, the four position and
  amplitude ticks, a positive amplitude scale `c`, and the displayed piecewise
  wavefunction profile;
* target conclusions: the probability on `[-1 nm, 1 nm]` is `4/5 = 0.80`, so the
  matching displayed answer is B.
-/

/-! ## Particle and figure vocabulary -/

/-- The particle species stated in the problem. -/
inductive QuantumParticleKind where
  | electron
  deriving DecidableEq, Repr

/-- Physical quantity named on the horizontal axis. -/
inductive HorizontalAxisQuantity where
  | position
  deriving DecidableEq, Repr

/-- Unit printed on the horizontal position axis. -/
inductive PositionAxisUnit where
  | nanometers
  deriving DecidableEq, Repr

/-- Physical quantity named by the vertical-axis label `ψ(x)`. -/
inductive VerticalAxisQuantity where
  | waveFunctionAmplitude
  deriving DecidableEq, Repr

/-- The four position ticks visible in the image. -/
inductive PositionTick where
  | negTwo
  | negOne
  | posOne
  | posTwo
  deriving DecidableEq, Fintype, Repr

/-- The four amplitude ticks visible on the vertical axis. -/
inductive AmplitudeTick where
  | negC
  | negHalfC
  | posHalfC
  | posC
  deriving DecidableEq, Fintype, Repr

/-- Qualitative shape of the red curve in the supplied image. -/
inductive WaveFunctionCurveShape where
  | piecewiseConstantWithJumps
  deriving DecidableEq, Repr

/-- Nanometre coordinate readout printed at each horizontal tick. -/
def expectedPositionTickNanometers : PositionTick → ℝ
  | .negTwo => -2
  | .negOne => -1
  | .posOne => 1
  | .posTwo => 2

/-- Each vertical tick as a dimensionless multiple of the positive scale `c`. -/
def expectedAmplitudeTickMultiplier : AmplitudeTick → ℝ
  | .negC => -1
  | .negHalfC => -(1 / 2)
  | .posHalfC => 1 / 2
  | .posC => 1

/-!
The labeled numerical data in the wavefunction plot.  `amplitudeScalePerSqrtNanometer`
is the real readout denoted by `c`; it is not a scalar replacement for the electron
state itself.
-/
structure PiecewiseWaveFunctionFigure where
  horizontalAxisQuantity : HorizontalAxisQuantity
  horizontalAxisUnit : PositionAxisUnit
  verticalAxisQuantity : VerticalAxisQuantity
  positionTickNanometers : PositionTick → ℝ
  amplitudeTickMultiplier : AmplitudeTick → ℝ
  amplitudeScalePerSqrtNanometer : ℝ
  curveShape : WaveFunctionCurveShape

/-!
The electron-position experiment.  The wavefunction is a complex-valued coordinate
representative, while `positionProbability` is an independent normalized measure
until Born's law is imposed below.
-/
structure ElectronPositionExperiment where
  particleKind : QuantumParticleKind
  waveAmplitudePerSqrtNanometer : ℝ → ℂ
  positionProbability : MeasureTheory.ProbabilityMeasure ℝ
  figure : PiecewiseWaveFunctionFigure

/-! ## Figure profile and queried region -/

/-!
The piecewise-constant amplitude shown in the primary image.  Values at the four
jump points use a fixed half-open convention; changing finitely many endpoint values
does not change any Born probability.
-/
def plottedWaveAmplitudePerSqrtNanometer
    (figure : PiecewiseWaveFunctionFigure) (xNanometers : ℝ) : ℂ :=
  if xNanometers < figure.positionTickNanometers .negTwo then
    0
  else if xNanometers < figure.positionTickNanometers .negOne then
    ((-(figure.amplitudeScalePerSqrtNanometer / 2) : ℝ) : ℂ)
  else if xNanometers ≤ figure.positionTickNanometers .posOne then
    ((figure.amplitudeScalePerSqrtNanometer : ℝ) : ℂ)
  else if xNanometers ≤ figure.positionTickNanometers .posTwo then
    ((-(figure.amplitudeScalePerSqrtNanometer / 2) : ℝ) : ℂ)
  else
    0

/-- The closed interval from the `-1` tick to the `1` tick, in nanometre readouts. -/
def queriedRegionNanometers
    (figure : PiecewiseWaveFunctionFigure) : Set ℝ :=
  Set.Icc
    (figure.positionTickNanometers .negOne)
    (figure.positionTickNanometers .posOne)

/-- Dimensionless probability that the electron position lies in the queried region. -/
def queriedPositionProbability (experiment : ElectronPositionExperiment) : ℝ :=
  (experiment.positionProbability.toMeasure
    (queriedRegionNanometers experiment.figure)).toReal

/-! ## Governing physics and primary-image readouts -/

/-!
The square-integrability requirement and Born's position-probability law.  Lebesgue
volume is taken on the numerical nanometre coordinate, so the squared amplitude is
embedded as a nonnegative density with `ENNReal.ofReal`.
-/
structure SatisfiesBornPositionPhysics
    (experiment : ElectronPositionExperiment) : Prop where
  waveAmplitudeIsSquareIntegrable :
    QuantumMechanics.OneDimension.HilbertSpace.MemHS
      experiment.waveAmplitudePerSqrtNanometer
  probabilityMeasureHasBornDensity :
    experiment.positionProbability.toMeasure =
      (MeasureTheory.volume : MeasureTheory.Measure ℝ).withDensity
        (fun xNanometers => ENNReal.ofReal
          (Complex.normSq
            (experiment.waveAmplitudePerSqrtNanometer xNanometers)))

/-!
Scenario facts and exact readouts from `647.png`.  These assumptions contain the
plotted state but no probability for the central interval and no answer-choice value.
-/
structure MatchesProblemStatementAndFigure
    (experiment : ElectronPositionExperiment) : Prop where
  particleIsElectron : experiment.particleKind = .electron
  horizontalAxisIsPosition :
    experiment.figure.horizontalAxisQuantity = .position
  horizontalAxisUsesNanometers :
    experiment.figure.horizontalAxisUnit = .nanometers
  verticalAxisIsWaveFunctionAmplitude :
    experiment.figure.verticalAxisQuantity = .waveFunctionAmplitude
  positionTicksMatchImage :
    experiment.figure.positionTickNanometers = expectedPositionTickNanometers
  amplitudeTicksMatchImage :
    experiment.figure.amplitudeTickMultiplier = expectedAmplitudeTickMultiplier
  amplitudeScaleIsPositive :
    0 < experiment.figure.amplitudeScalePerSqrtNanometer
  curveHasDisplayedShape :
    experiment.figure.curveShape = .piecewiseConstantWithJumps
  waveAmplitudeMatchesImage : ∀ xNanometers : ℝ,
    experiment.waveAmplitudePerSqrtNanometer xNanometers =
      plottedWaveAmplitudePerSqrtNanometer experiment.figure xNanometers

/-! ## Answer choices and formalization target -/

/-- The four answer labels printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless probability displayed beside each answer label. -/
def AnswerChoice.displayedProbability : AnswerChoice → ℝ
  | .A => 2 / 5
  | .B => 4 / 5
  | .C => 9 / 10
  | .D => 3 / 5

/-- A displayed choice matches the modeled probability exactly. -/
def MatchesAnswerChoice
    (experiment : ElectronPositionExperiment) (choice : AnswerChoice) : Prop :=
  queriedPositionProbability experiment = choice.displayedProbability

/-!
The normalized piecewise wavefunction assigns probability `4/5` to the interval
from `-1 nm` through `1 nm`.
-/
lemma central_interval_probability
    (experiment : ElectronPositionExperiment)
    (hPhysics : SatisfiesBornPositionPhysics experiment)
    (hFigure : MatchesProblemStatementAndFigure experiment) :
    queriedPositionProbability experiment = (4 : ℝ) / 5 := by
  let c : ℝ := experiment.figure.amplitudeScalePerSqrtNanometer
  have hc : 0 < c := hFigure.amplitudeScaleIsPositive
  have hDensity (x : ℝ) :
      ENNReal.ofReal
          (Complex.normSq
            (experiment.waveAmplitudePerSqrtNanometer x)) =
        (Set.Ico (-2 : ℝ) (-1)).indicator
            (fun _ : ℝ => ENNReal.ofReal (c ^ 2 / 4)) x +
          (Set.Icc (-1 : ℝ) 1).indicator
            (fun _ : ℝ => ENNReal.ofReal (c ^ 2)) x +
          (Set.Ioc (1 : ℝ) 2).indicator
            (fun _ : ℝ => ENNReal.ofReal (c ^ 2 / 4)) x := by
    rw [hFigure.waveAmplitudeMatchesImage x,
      plottedWaveAmplitudePerSqrtNanometer,
      hFigure.positionTicksMatchImage]
    simp only [expectedPositionTickNanometers]
    by_cases h₁ : x < -2
    · have hLeft : x ∉ Set.Ico (-2 : ℝ) (-1) := by
        simp only [Set.mem_Ico, not_and_or]
        exact Or.inl (not_le.mpr h₁)
      have hCenter : x ∉ Set.Icc (-1 : ℝ) 1 := by
        simp only [Set.mem_Icc, not_and_or]
        exact Or.inl (not_le.mpr (lt_trans h₁ (by norm_num)))
      have hRight : x ∉ Set.Ioc (1 : ℝ) 2 := by
        simp only [Set.mem_Ioc, not_and_or]
        exact Or.inl
          (not_lt.mpr (le_trans (le_of_lt h₁) (by norm_num)))
      simp [h₁, hLeft, hCenter, hRight]
    by_cases h₂ : x < -1
    · have hLeft : x ∈ Set.Ico (-2 : ℝ) (-1) :=
        ⟨le_of_not_gt h₁, h₂⟩
      have hCenter : x ∉ Set.Icc (-1 : ℝ) 1 := by
        simp [Set.mem_Icc, not_le.mpr h₂]
      have hRight : x ∉ Set.Ioc (1 : ℝ) 2 := by
        simp only [Set.mem_Ioc, not_and_or]
        exact Or.inl
          (not_lt.mpr (le_trans (le_of_lt h₂) (by norm_num)))
      simp [h₁, h₂, hLeft, hCenter, hRight, Complex.normSq_ofReal,
        c]
      ring_nf
    by_cases h₃ : x ≤ 1
    · have hLeft : x ∉ Set.Ico (-2 : ℝ) (-1) := by
        simp [Set.mem_Ico, h₂]
      have hCenter : x ∈ Set.Icc (-1 : ℝ) 1 :=
        ⟨le_of_not_gt h₂, h₃⟩
      have hRight : x ∉ Set.Ioc (1 : ℝ) 2 := by
        simp [Set.mem_Ioc, not_lt.mpr h₃]
      simp [h₁, h₂, h₃, hLeft, hCenter, hRight, Complex.normSq_ofReal,
        c, pow_two]
    by_cases h₄ : x ≤ 2
    · have hLeft : x ∉ Set.Ico (-2 : ℝ) (-1) := by
        simp [Set.mem_Ico, h₂]
      have hCenter : x ∉ Set.Icc (-1 : ℝ) 1 := by
        simp [Set.mem_Icc, h₃]
      have hRight : x ∈ Set.Ioc (1 : ℝ) 2 :=
        ⟨lt_of_not_ge h₃, h₄⟩
      simp [h₁, h₂, h₃, h₄, hLeft, hCenter, hRight,
        Complex.normSq_ofReal, c]
      ring_nf
    · have hLeft : x ∉ Set.Ico (-2 : ℝ) (-1) := by
        simp [Set.mem_Ico, h₂]
      have hCenter : x ∉ Set.Icc (-1 : ℝ) 1 := by
        simp [Set.mem_Icc, h₃]
      have hRight : x ∉ Set.Ioc (1 : ℝ) 2 := by
        simp [Set.mem_Ioc, h₄]
      simp [h₁, h₂, h₃, h₄, hLeft, hCenter, hRight]
  have hTotal :
      (∫⁻ x : ℝ, ENNReal.ofReal
        (Complex.normSq
          (experiment.waveAmplitudePerSqrtNanometer x))) = 1 := by
    calc
      (∫⁻ x : ℝ, ENNReal.ofReal
          (Complex.normSq
            (experiment.waveAmplitudePerSqrtNanometer x))) =
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).withDensity
            (fun x : ℝ => ENNReal.ofReal
              (Complex.normSq
                (experiment.waveAmplitudePerSqrtNanometer x)))) Set.univ := by
            rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ,
              Measure.restrict_univ]
      _ = experiment.positionProbability.toMeasure Set.univ := by
        rw [hPhysics.probabilityMeasureHasBornDensity]
      _ = 1 := by simp
  have hLeftMeasurable :
      Measurable
        ((Set.Ico (-2 : ℝ) (-1)).indicator
          (fun _ : ℝ => ENNReal.ofReal (c ^ 2 / 4))) :=
    measurable_const.indicator measurableSet_Ico
  have hCenterMeasurable :
      Measurable
        ((Set.Icc (-1 : ℝ) 1).indicator
          (fun _ : ℝ => ENNReal.ofReal (c ^ 2))) :=
    measurable_const.indicator measurableSet_Icc
  have hIntegralValue :
      (∫⁻ x : ℝ, ENNReal.ofReal
        (Complex.normSq
          (experiment.waveAmplitudePerSqrtNanometer x))) =
        ENNReal.ofReal (c ^ 2 / 4) +
          ENNReal.ofReal (c ^ 2) * 2 +
          ENNReal.ofReal (c ^ 2 / 4) := by
    calc
      (∫⁻ x : ℝ, ENNReal.ofReal
          (Complex.normSq
            (experiment.waveAmplitudePerSqrtNanometer x))) =
          ∫⁻ x : ℝ,
            (Set.Ico (-2 : ℝ) (-1)).indicator
                (fun _ : ℝ => ENNReal.ofReal (c ^ 2 / 4)) x +
              (Set.Icc (-1 : ℝ) 1).indicator
                (fun _ : ℝ => ENNReal.ofReal (c ^ 2)) x +
              (Set.Ioc (1 : ℝ) 2).indicator
                (fun _ : ℝ => ENNReal.ofReal (c ^ 2 / 4)) x := by
            exact MeasureTheory.lintegral_congr hDensity
      _ =
          (∫⁻ x : ℝ,
            (Set.Ico (-2 : ℝ) (-1)).indicator
                (fun _ : ℝ => ENNReal.ofReal (c ^ 2 / 4)) x) +
          (∫⁻ x : ℝ,
            (Set.Icc (-1 : ℝ) 1).indicator
                (fun _ : ℝ => ENNReal.ofReal (c ^ 2)) x) +
          (∫⁻ x : ℝ,
            (Set.Ioc (1 : ℝ) 2).indicator
                (fun _ : ℝ => ENNReal.ofReal (c ^ 2 / 4)) x) := by
            rw [MeasureTheory.lintegral_add_left
              (hLeftMeasurable.add hCenterMeasurable)]
            rw [MeasureTheory.lintegral_add_left hLeftMeasurable]
      _ = ENNReal.ofReal (c ^ 2 / 4) +
          ENNReal.ofReal (c ^ 2) * 2 +
          ENNReal.ofReal (c ^ 2 / 4) := by
            rw [MeasureTheory.lintegral_indicator_const measurableSet_Ico,
              MeasureTheory.lintegral_indicator_const measurableSet_Icc,
              MeasureTheory.lintegral_indicator_const measurableSet_Ioc]
            norm_num [Real.volume_Ico, Real.volume_Icc, Real.volume_Ioc]
  have hScaleEquation :
      c ^ 2 / 4 + c ^ 2 * 2 + c ^ 2 / 4 = 1 := by
    have hENNRealEquation :
        ENNReal.ofReal (c ^ 2 / 4) +
            ENNReal.ofReal (c ^ 2) * 2 +
            ENNReal.ofReal (c ^ 2 / 4) =
          1 := by
      calc
        ENNReal.ofReal (c ^ 2 / 4) +
              ENNReal.ofReal (c ^ 2) * 2 +
              ENNReal.ofReal (c ^ 2 / 4) =
            (∫⁻ x : ℝ, ENNReal.ofReal
              (Complex.normSq
                (experiment.waveAmplitudePerSqrtNanometer x))) :=
          hIntegralValue.symm
        _ = 1 := hTotal
    have hNonnegativeSquare : 0 ≤ c ^ 2 := sq_nonneg c
    have hNonnegativeQuarterSquare : 0 ≤ c ^ 2 / 4 :=
      div_nonneg hNonnegativeSquare (by norm_num)
    have hToReal := congrArg ENNReal.toReal hENNRealEquation
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hNonnegativeQuarterSquare,
      ENNReal.toReal_ofReal hNonnegativeSquare] at hToReal
    norm_num at hToReal
    exact hToReal
  have hScaleSquared : c ^ 2 = (2 : ℝ) / 5 := by
    linarith [hScaleEquation]
  have hCentralDensity (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
      ENNReal.ofReal
          (Complex.normSq
            (experiment.waveAmplitudePerSqrtNanometer x)) =
        ENNReal.ofReal (c ^ 2) := by
    rw [hDensity x]
    have hNotLeft : x ∉ Set.Ico (-2 : ℝ) (-1) := by
      intro hLeft
      exact (not_lt_of_ge hx.1) hLeft.2
    have hNotRight : x ∉ Set.Ioc (1 : ℝ) 2 := by
      intro hRight
      exact (not_lt_of_ge hx.2) hRight.1
    simp [hNotLeft, hx, hNotRight]
  have hCentralIntegral :
      (∫⁻ x : ℝ in Set.Icc (-1 : ℝ) 1,
        ENNReal.ofReal
          (Complex.normSq
            (experiment.waveAmplitudePerSqrtNanometer x))) =
        ENNReal.ofReal (c ^ 2) * 2 := by
    calc
      (∫⁻ x : ℝ in Set.Icc (-1 : ℝ) 1,
          ENNReal.ofReal
            (Complex.normSq
              (experiment.waveAmplitudePerSqrtNanometer x))) =
          ∫⁻ _x : ℝ in Set.Icc (-1 : ℝ) 1,
            ENNReal.ofReal (c ^ 2) := by
              exact MeasureTheory.setLIntegral_congr_fun
                measurableSet_Icc hCentralDensity
      _ = ENNReal.ofReal (c ^ 2) *
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)
            (Set.Icc (-1 : ℝ) 1) :=
        MeasureTheory.setLIntegral_const _ _
      _ = ENNReal.ofReal (c ^ 2) * 2 := by
        norm_num [Real.volume_Icc]
  unfold queriedPositionProbability queriedRegionNanometers
  rw [hFigure.positionTicksMatchImage]
  simp only [expectedPositionTickNanometers]
  rw [hPhysics.probabilityMeasureHasBornDensity,
    MeasureTheory.withDensity_apply _ measurableSet_Icc,
    hCentralIntegral, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg c), hScaleSquared]
  norm_num

/-!
The requested probability is `0.80`, which is answer B.

This declaration corresponds to blueprint label
`thm:physics:phyx_mini_0647:target`.
-/
theorem problem_phyx_mini_0647
    (experiment : ElectronPositionExperiment)
    (hPhysics : SatisfiesBornPositionPhysics experiment)
    (hFigure : MatchesProblemStatementAndFigure experiment) :
    queriedPositionProbability experiment = (4 : ℝ) / 5 ∧
      MatchesAnswerChoice experiment .B := by
  have hProbability :=
    central_interval_probability experiment hPhysics hFigure
  constructor
  · exact hProbability
  · simpa [MatchesAnswerChoice, AnswerChoice.displayedProbability] using
      hProbability

end PhyXMiniProblems.ProblemPhyXMini0647
