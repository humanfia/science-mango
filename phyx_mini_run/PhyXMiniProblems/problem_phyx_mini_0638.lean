import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.Complex.Basic
import Physlib.QuantumMechanics.HilbertSpaces.OneDimension.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

/-!
# Exponential position wavefunction and a tail-detection count

The position axis in the supplied figure is calibrated in nanometres.  Physical
positions and lengths are nevertheless represented by unit-independent Physlib
quantities.  A wave-amplitude readout has dimension `L⁻¹ᐟ²`, a probability-density
readout has dimension `L⁻¹`, and their integral against a position coordinate is
dimensionless.

The source states that one million particles are detected.  For the normalized
profile in the figure, the probability of `x ≥ 1 nm` is `exp (-2)`, so the expected
count is about `135335`, not the recorded answer-choice value `135`.  The exact
source data are retained below; the inconsistent recorded answer is metadata and
is not made into a physical premise.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0638

open CarriesDimension Dimension

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A signed physical position on the one-dimensional axis. -/
abbrev PositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical length, used for the exponential decay length `L`. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A position-wavefunction amplitude, with physical dimension `L⁻¹ᐟ²`. -/
abbrev WaveAmplitudeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 ^ ((-1 : ℚ) / 2)) ℂ)

/-- A one-dimensional position-probability density, of dimension `L⁻¹`. -/
abbrev ProbabilityDensityQuantity : Type :=
  Dimensionful (WithDim L𝓭⁻¹ ℝ)

/-- The physical unit used on the horizontal axes of both supplied plots. -/
noncomputable def nanometerUnit : LengthUnit := LengthUnit.nanometers

/-- Numerical coordinate of a physical position in a selected length unit. -/
def positionReadout (unit : LengthUnit) (position : PositionQuantity) : ℝ :=
  (position ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- Numerical value of a nonnegative physical length in a selected unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length ({ UnitChoices.SI with length := unit } : UnitChoices)).val : ℝ)

/-- Numerical wave-amplitude readout in inverse square-root selected units. -/
def waveAmplitudeReadout
    (unit : LengthUnit) (amplitude : WaveAmplitudeQuantity) : ℂ :=
  (amplitude ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- Numerical probability-density readout in inverse selected units. -/
def probabilityDensityReadout
    (unit : LengthUnit) (density : ProbabilityDensityQuantity) : ℝ :=
  (density ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- Construct a physical position from its coordinate in a selected unit. -/
def positionFromReadout
    (unit : LengthUnit) (value : ℝ) : PositionQuantity :=
  toDimensionful
    ({ UnitChoices.SI with length := unit } : UnitChoices)
    (show WithDim L𝓭 ℝ from ⟨value⟩)

/-- The physical origin used by the piecewise wavefunction. -/
noncomputable def originPosition : PositionQuantity :=
  positionFromReadout nanometerUnit 0

/-! ## Quantum state, detection experiment, and primary-figure vocabulary -/

/-- The qualitative curve shape shown in each panel of the supplied figure. -/
inductive FigureCurveShape where
  | zeroForNegativeThenExponentialDecay
  | other
  deriving DecidableEq, Repr

/--
The state exposes independent amplitude, density, and tail-probability observables.
Born's rule below relates them; none is defined from the requested answer.
-/
structure OneDimensionalPositionState where
  waveAmplitudeAt : PositionQuantity → WaveAmplitudeQuantity
  probabilityDensityAt : PositionQuantity → ProbabilityDensityQuantity
  positionProbabilityAtOrBeyond : PositionQuantity → ℝ

/-- Labels, numerical ticks, curve styles, and annotation visible in image `638.png`. -/
structure ExponentialTailFigure where
  positionAxisLabel : String
  waveAmplitudeAxisLabel : String
  probabilityDensityAxisLabel : String
  waveEquationAnnotation : String
  waveCurveShape : FigureCurveShape
  densityCurveShape : FigureCurveShape
  horizontalLowerNanometers : ℝ
  horizontalUpperNanometers : ℝ
  waveOriginPerSqrtNanometer : ℝ
  densityOriginPerNanometer : ℝ
  shadedTailStartsNanometers : ℝ
  tailAreaAnnotation : String

/--
The physical experiment.  The expected count is an independent observable and is
related to probability only by the general counting law stated below.
-/
structure ExponentialTailDetectionSetup where
  state : OneDimensionalPositionState
  decayLength : LengthQuantity
  normalizationAmplitude : WaveAmplitudeQuantity
  queryThreshold : PositionQuantity
  detectedParticleCount : ℕ
  expectedParticleCountAtOrBeyond : PositionQuantity → ℝ
  figure : ExponentialTailFigure

/-! ## Figure/data readouts -/

/--
Exact problem data: `L = 1 nm`, the query begins at `1 nm`, and the run contains
`10⁶` detected particles.
-/
structure MatchesProblemData
    (setup : ExponentialTailDetectionSetup) : Prop where
  decayLengthIsOneNanometer :
    lengthReadout nanometerUnit setup.decayLength = 1
  queryThresholdIsOneNanometer :
    positionReadout nanometerUnit setup.queryThreshold = 1
  detectedParticleCountIsOneMillion :
    setup.detectedParticleCount = 10 ^ 6

/--
Primary-image evidence.  The upper origin label `1.414` is a three-decimal
display, so it is connected to the physical amplitude by its rounding interval.
The plotted wave curve is positive and real at the origin.  The lower origin
label `2` is the exact density value shown by the graph.
-/
structure MatchesPrimaryFigure
    (setup : ExponentialTailDetectionSetup) : Prop where
  positionAxisText : setup.figure.positionAxisLabel = "x (nm)"
  waveAxisText :
    setup.figure.waveAmplitudeAxisLabel = "ψ(x) (nm⁻¹ᐟ²)"
  densityAxisText :
    setup.figure.probabilityDensityAxisLabel = "P(x) (nm⁻¹)"
  waveEquationText :
    setup.figure.waveEquationAnnotation =
      "ψ(x) = (1.414 nm⁻¹ᐟ²) exp(-x / (1.0 nm))"
  waveShape :
    setup.figure.waveCurveShape = .zeroForNegativeThenExponentialDecay
  densityShape :
    setup.figure.densityCurveShape = .zeroForNegativeThenExponentialDecay
  horizontalRangeStartsAtZero :
    setup.figure.horizontalLowerNanometers = 0
  horizontalRangeEndsAtTwo :
    setup.figure.horizontalUpperNanometers = 2
  waveOriginLabel :
    setup.figure.waveOriginPerSqrtNanometer = 1414 / 1000
  densityOriginLabel :
    setup.figure.densityOriginPerNanometer = 2
  waveOriginHasZeroPhase :
    (waveAmplitudeReadout nanometerUnit
      (setup.state.waveAmplitudeAt originPosition)).im = 0
  waveOriginIsPositive :
    0 < (waveAmplitudeReadout nanometerUnit
      (setup.state.waveAmplitudeAt originPosition)).re
  waveOriginMatchesDisplayedRounding :
    abs
        (‖waveAmplitudeReadout nanometerUnit
              (setup.state.waveAmplitudeAt originPosition)‖ -
          setup.figure.waveOriginPerSqrtNanometer) < 1 / 2000
  densityOriginMatchesDisplayedValue :
    probabilityDensityReadout nanometerUnit
        (setup.state.probabilityDensityAt originPosition) =
      setup.figure.densityOriginPerNanometer
  shadedTailStartsAtOneNanometer :
    setup.figure.shadedTailStartsNanometers = 1
  shadedTailStartsAtQueryThreshold :
    setup.figure.shadedTailStartsNanometers =
      positionReadout nanometerUnit setup.queryThreshold
  annotationText :
    setup.figure.tailAreaAnnotation =
      "The area under the curve is Prob(x ≥ 1 nm)."

/-! ## Governing quantum and counting laws -/

/--
The stated piecewise exponential profile, square-integrability, normalization,
Born position-density law, tail-event integral, and expected-count scaling.

All formulas are stated for arbitrary calibrated length units.  Consequently the
physical laws are not tied to the nanometre readout used by the particular figure.
No field contains `exp (-2)`, `135`, or the derived expected count.
-/
structure SatisfiesExponentialWaveBornAndCountingLaws
    (setup : ExponentialTailDetectionSetup) : Prop where
  decayLengthPositive :
    ∀ unit : LengthUnit, 0 < lengthReadout unit setup.decayLength
  waveFunction_memHS :
    ∀ unit : LengthUnit,
      QuantumMechanics.OneDimension.HilbertSpace.MemHS
        (fun x : ℝ ↦
          waveAmplitudeReadout unit
            (setup.state.waveAmplitudeAt (positionFromReadout unit x)))
  waveVanishesAtNegativeCoordinates :
    ∀ (unit : LengthUnit) (x : ℝ), x < 0 →
      waveAmplitudeReadout unit
          (setup.state.waveAmplitudeAt (positionFromReadout unit x)) = 0
  exponentialWaveProfile :
    ∀ (unit : LengthUnit) (x : ℝ), 0 ≤ x →
      waveAmplitudeReadout unit
          (setup.state.waveAmplitudeAt (positionFromReadout unit x)) =
        waveAmplitudeReadout unit setup.normalizationAmplitude *
          ((Real.exp (-x / lengthReadout unit setup.decayLength) : ℝ) : ℂ)
  bornProbabilityDensity :
    ∀ (unit : LengthUnit) (x : ℝ),
      probabilityDensityReadout unit
          (setup.state.probabilityDensityAt (positionFromReadout unit x)) =
        Complex.normSq
          (waveAmplitudeReadout unit
            (setup.state.waveAmplitudeAt (positionFromReadout unit x)))
  normalizedProbabilityDensity :
    ∀ unit : LengthUnit,
      (∫ x : ℝ,
        probabilityDensityReadout unit
          (setup.state.probabilityDensityAt
            (positionFromReadout unit x))) = 1
  tailBornRule :
    ∀ (unit : LengthUnit) (threshold : PositionQuantity),
      setup.state.positionProbabilityAtOrBeyond threshold =
        ∫ x in Set.Ici (positionReadout unit threshold),
          probabilityDensityReadout unit
            (setup.state.probabilityDensityAt
              (positionFromReadout unit x))
  tailProbabilityBounds :
    ∀ threshold : PositionQuantity,
      0 ≤ setup.state.positionProbabilityAtOrBeyond threshold ∧
        setup.state.positionProbabilityAtOrBeyond threshold ≤ 1
  expectedCountLaw :
    ∀ threshold : PositionQuantity,
      setup.expectedParticleCountAtOrBeyond threshold =
        (setup.detectedParticleCount : ℝ) *
          setup.state.positionProbabilityAtOrBeyond threshold

/-! ## Answer-choice metadata and derived targets -/

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A | B | C | D
  deriving DecidableEq, Fintype, Repr

/-- Particle counts printed beside the displayed answer choices. -/
def displayedExpectedCount : AnswerChoice → ℕ
  | .A => 125
  | .B => 135
  | .C => 145
  | .D => 155

/-- The dataset's recorded label, retained only as source metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- Usual half-up rounding of a real-valued expectation to a natural count. -/
def RoundsToNearestParticle (value : ℝ) (particleCount : ℕ) : Prop :=
  (particleCount : ℝ) - 1 / 2 ≤ value ∧
    value < (particleCount : ℝ) + 1 / 2

/--
For the normalized exponential state with `L = 1 nm`, Born's rule assigns the
dimensionless tail probability `exp (-2)` to the event `x ≥ 1 nm`.
-/
lemma oneNanometerTailProbability
    (setup : ExponentialTailDetectionSetup)
    (hData : MatchesProblemData setup)
    (hLaws : SatisfiesExponentialWaveBornAndCountingLaws setup) :
    setup.state.positionProbabilityAtOrBeyond setup.queryThreshold =
      Real.exp (-2) := by
  let amplitude : ℂ :=
    waveAmplitudeReadout nanometerUnit setup.normalizationAmplitude
  let density : ℝ → ℝ := fun x =>
    probabilityDensityReadout nanometerUnit
      (setup.state.probabilityDensityAt
        (positionFromReadout nanometerUnit x))
  have hDensity (x : ℝ) :
      density x =
        Set.indicator (Set.Ici (0 : ℝ))
          (fun y : ℝ =>
            Complex.normSq amplitude * Real.exp ((-2 : ℝ) * y)) x := by
    dsimp [density]
    rw [hLaws.bornProbabilityDensity nanometerUnit x]
    by_cases hx : 0 ≤ x
    · calc
        Complex.normSq
            (waveAmplitudeReadout nanometerUnit
              (setup.state.waveAmplitudeAt
                (positionFromReadout nanometerUnit x))) =
            Complex.normSq amplitude * Real.exp ((-2 : ℝ) * x) := by
          rw [hLaws.exponentialWaveProfile nanometerUnit x hx,
            hData.decayLengthIsOneNanometer]
          dsimp [amplitude]
          rw [Complex.normSq_mul, Complex.normSq_ofReal, ← Real.exp_add]
          congr 2
          ring_nf
        _ = Set.indicator (Set.Ici (0 : ℝ))
            (fun y : ℝ =>
              Complex.normSq amplitude * Real.exp ((-2 : ℝ) * y)) x := by
          symm
          exact Set.indicator_of_mem hx _
    · have hxlt : x < 0 := lt_of_not_ge hx
      rw [hLaws.waveVanishesAtNegativeCoordinates nanometerUnit x hxlt]
      simp [Set.indicator, hx]
  have hNorm := hLaws.normalizedProbabilityDensity nanometerUnit
  change (∫ x : ℝ, density x) = 1 at hNorm
  rw [show density =
        Set.indicator (Set.Ici (0 : ℝ))
          (fun y : ℝ =>
            Complex.normSq amplitude * Real.exp ((-2 : ℝ) * y)) from
      funext hDensity,
    MeasureTheory.integral_indicator measurableSet_Ici,
    MeasureTheory.integral_const_mul,
    MeasureTheory.integral_Ici_eq_integral_Ioi,
    integral_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0)] at hNorm
  norm_num at hNorm
  have hAmplitude : Complex.normSq amplitude = 2 := by
    linarith
  rw [hLaws.tailBornRule nanometerUnit setup.queryThreshold,
    hData.queryThresholdIsOneNanometer]
  change (∫ x : ℝ in Set.Ici 1, density x) = Real.exp (-2)
  calc
    (∫ x : ℝ in Set.Ici 1, density x) =
        ∫ x : ℝ in Set.Ici 1,
          Complex.normSq amplitude * Real.exp ((-2 : ℝ) * x) := by
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Ici (by
        intro x hx
        have hx0 : x ∈ Set.Ici (0 : ℝ) := by
          exact le_trans (by norm_num : (0 : ℝ) ≤ 1) hx
        rw [hDensity x, Set.indicator_of_mem hx0])
    _ = Complex.normSq amplitude *
        ∫ x : ℝ in Set.Ici 1, Real.exp ((-2 : ℝ) * x) := by
      rw [MeasureTheory.integral_const_mul]
    _ = Real.exp (-2) := by
      rw [hAmplitude, MeasureTheory.integral_Ici_eq_integral_Ioi,
        integral_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0)]
      ring_nf

/-!
Blueprint label: `thm:physics:phyx_mini_0638:target`.

Of the stated `10⁶` detected particles, the exact expected count in the region
`x ≥ 1 nm` is `10⁶ exp (-2)`, which rounds to `135335` particles.  This preserves
the million-particle premise even though none of the source's displayed choices
has that magnitude.
-/
theorem problem_phyx_mini_0638
    (setup : ExponentialTailDetectionSetup)
    (hData : MatchesProblemData setup)
    (hFigure : MatchesPrimaryFigure setup)
    (hLaws : SatisfiesExponentialWaveBornAndCountingLaws setup) :
    setup.state.positionProbabilityAtOrBeyond setup.queryThreshold =
        Real.exp (-2) ∧
      setup.expectedParticleCountAtOrBeyond setup.queryThreshold =
        (10 ^ 6 : ℝ) * Real.exp (-2) ∧
      RoundsToNearestParticle
        (setup.expectedParticleCountAtOrBeyond setup.queryThreshold) 135335 := by
  have hProbability :=
    oneNanometerTailProbability setup hData hLaws
  have hExpected :
      setup.expectedParticleCountAtOrBeyond setup.queryThreshold =
        (10 ^ 6 : ℝ) * Real.exp (-2) := by
    rw [hLaws.expectedCountLaw, hData.detectedParticleCountIsOneMillion,
      hProbability]
    norm_num
  refine ⟨hProbability, hExpected, ?_⟩
  rw [hExpected]
  have hExpOne :
      (3678794 / 10000000 : ℝ) < Real.exp (-1) ∧
        Real.exp (-1) < (3678795 / 10000000 : ℝ) := by
    have h := Real.exp_bound (x := (-1 : ℝ)) (n := 12)
      (by norm_num) (by norm_num)
    rw [abs_le] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    constructor <;> linarith
  have hExpPos : 0 < Real.exp (-1) := Real.exp_pos _
  have hLowerProduct :
      0 < (Real.exp (-1) - (3678794 / 10000000 : ℝ)) *
        (Real.exp (-1) + (3678794 / 10000000 : ℝ)) := by
    apply mul_pos <;> nlinarith [hExpOne.1, hExpPos]
  have hUpperProduct :
      0 < ((3678795 / 10000000 : ℝ) - Real.exp (-1)) *
        ((3678795 / 10000000 : ℝ) + Real.exp (-1)) := by
    apply mul_pos <;> nlinarith [hExpOne.2, hExpPos]
  have hExpSq :
      Real.exp (-2) = Real.exp (-1) * Real.exp (-1) := by
    rw [show (-2 : ℝ) = (-1) + (-1) by norm_num, Real.exp_add]
  unfold RoundsToNearestParticle
  rw [hExpSq]
  norm_num
  constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0638
