import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0303

open Dimension

/-!
# Angular frequency of two phase-shifted string waves

Two sinusoidal waves have the same amplitude and `120 Hz` cyclic frequency
and travel in the positive direction of an `x` axis along a cord under
tension.  One wave may be translated relative to the other.  The supplied
graph plots the signed resultant-amplitude coefficient `y'` against this shift
distance: it runs from `y'_s` at zero shift, through zero at `10 cm`, to
`-y'_s` at `20 cm`, where `y'_s = 6.0 mm`.

Physical lengths, tension, cyclic frequency, wave number, and angular
frequency are represented by Physlib's unit-independent `Dimensionful`
quantities.  Real numbers below occur only as coherent named-unit readouts,
dimensionless phases, scalar displacement-component readouts, and displayed
answer values.

Assumption/target boundary:

* the problem supplies the common `120 Hz` cyclic frequency, equal amplitude,
  common propagation direction, cord tension, and the form of the waves;
* the primary figure supplies its labels, units, scale, and the three
  calibrated shift/amplitude landmarks;
* the governing laws supply `omega = 2 pi f`, `k lambda = 2 pi`, the
  positive-`x` phase convention, and linear superposition;
* `omega = 240 pi rad/s` and agreement with the displayed `754 rad/s` choice
  are conclusions only.
-/

/-! ## Dimensionful physical quantities and coherent readouts -/

/-- A nonnegative physical length, used for amplitudes and shift distances. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed length component, used for the graph's signed coefficient `y'`. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative cyclic frequency, with inverse-time dimension. -/
abbrev FrequencyQuantity : Type := Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative angular frequency; radians are dimensionless. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative wave number; radians are dimensionless. -/
abbrev WaveNumberQuantity : Type :=
  Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-- Cord tension, with force dimension `M L T^-2`. -/
abbrev TensionQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a nonnegative physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length { UnitChoices.SI with length := unit }).val : ℝ)

/-- Read a signed physical length component in a selected length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (length : SignedLengthQuantity) : ℝ :=
  (length { UnitChoices.SI with length := unit }).val

/-- Read a cyclic frequency in hertz, i.e. cycles per SI second. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Read an angular frequency in radians per SI second. -/
def angularFrequencyInRadiansPerSecond
    (angularFrequency : AngularFrequencyQuantity) : ℝ :=
  ((angularFrequency UnitChoices.SI).val : ℝ)

/-- Read a wave number in radians per SI metre. -/
def waveNumberInRadiansPerMeter (waveNumber : WaveNumberQuantity) : ℝ :=
  ((waveNumber UnitChoices.SI).val : ℝ)

/-- Read the cord tension in SI newtons. -/
def tensionInNewtons (tension : TensionQuantity) : ℝ :=
  ((tension UnitChoices.SI).val : ℝ)

/-! ## Wave roles and primary-figure geometry -/

/-- The two equal-amplitude, equal-frequency waves described in the problem. -/
inductive WaveIndex where
  | first
  | second
  deriving DecidableEq, Repr

/-- Direction in which a wave propagates along the cord's `x` axis. -/
inductive PropagationDirection where
  | negativeX
  | positiveX
  deriving DecidableEq, Repr

/-- The coordinate axes explicitly labelled in the primary graph. -/
inductive GraphAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical roles of the two graph coordinates. -/
inductive AxisQuantity where
  | shiftDistance
  | signedResultantAmplitude_yPrime
  deriving DecidableEq, Repr

/-- Three directly readable landmarks of the plotted curve. -/
inductive GraphLandmark where
  | positiveScaleAtZeroShift
  | zeroCrossingAtTenCentimeters
  | negativeScaleAtTwentyCentimeters
  deriving DecidableEq, Repr

/-!
The graph's independent dimensionful data.  Its amplitude function returns a
signed coefficient because the plotted curve extends from `y'_s` to
`-y'_s`; it is not being used as a nonnegative amplitude magnitude.
-/
structure ShiftAmplitudeGraph where
  axisQuantity : GraphAxis → AxisQuantity
  horizontalLengthUnit : LengthUnit
  verticalLengthUnit : LengthUnit
  verticalScaleYsPrime : LengthQuantity
  shiftDistance : GraphLandmark → LengthQuantity
  resultantSignedAmplitude : LengthQuantity → SignedLengthQuantity
  tenCentimeterTickPrinted : Bool
  twentyCentimeterTickPrinted : Bool
  gridShown : Bool
  smoothCurveShown : Bool
  curveDecreasesAcrossDisplayedRange : Bool

/-!
Independent apparatus quantities and scalar field readouts.

The single fields `amplitudeYm`, `frequency`, `waveNumber`, and
`angularFrequency` encode that the two waves share those quantities.  Their
values are otherwise independent: in particular, `angularFrequency` is not
defined to be the requested answer.  The displacement functions return the
signed transverse component in metres at SI coordinates and time.
-/
structure TwoWaveInterferenceSetup where
  graph : ShiftAmplitudeGraph
  cordTension : TensionQuantity
  amplitudeYm : LengthQuantity
  frequency : FrequencyQuantity
  wavelength : LengthQuantity
  waveNumber : WaveNumberQuantity
  angularFrequency : AngularFrequencyQuantity
  propagationDirection : WaveIndex → PropagationDirection
  phaseOffsetRadians : WaveIndex → LengthQuantity → ℝ
  displacementInMeters : WaveIndex → LengthQuantity → ℝ → ℝ → ℝ
  resultantDisplacementInMeters : LengthQuantity → ℝ → ℝ → ℝ

/-!
Numerical and qualitative data stated in the prose together with calibrated
evidence from the primary bitmap.  The graph data constrain only shift
distances and signed resultant amplitudes; no angular-frequency or answer
value appears among the figure premises.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : TwoWaveInterferenceSetup) : Prop where
  commonFrequencyIs120Hertz :
    frequencyInHertz setup.frequency = 120
  bothWavesTravelAlongPositiveX :
    ∀ wave : WaveIndex, setup.propagationDirection wave = .positiveX
  horizontalAxisIsShiftDistance :
    setup.graph.axisQuantity .horizontal = .shiftDistance
  verticalAxisIsSignedResultantAmplitude :
    setup.graph.axisQuantity .vertical = .signedResultantAmplitude_yPrime
  horizontalUnitIsCentimeters :
    setup.graph.horizontalLengthUnit = LengthUnit.centimeters
  verticalUnitIsMillimeters :
    setup.graph.verticalLengthUnit = LengthUnit.millimeters
  scaleYsPrimeIsSixMillimeters :
    lengthReadout LengthUnit.millimeters setup.graph.verticalScaleYsPrime = 6
  zeroShiftDistance :
    lengthReadout LengthUnit.centimeters
      (setup.graph.shiftDistance .positiveScaleAtZeroShift) = 0
  tenCentimeterZeroCrossingDistance :
    lengthReadout LengthUnit.centimeters
      (setup.graph.shiftDistance .zeroCrossingAtTenCentimeters) = 10
  twentyCentimeterNegativeScaleDistance :
    lengthReadout LengthUnit.centimeters
      (setup.graph.shiftDistance .negativeScaleAtTwentyCentimeters) = 20
  amplitudeAtZeroShiftIsPositiveScale :
    signedLengthReadout LengthUnit.millimeters
        (setup.graph.resultantSignedAmplitude
          (setup.graph.shiftDistance .positiveScaleAtZeroShift)) =
      lengthReadout LengthUnit.millimeters setup.graph.verticalScaleYsPrime
  amplitudeAtTenCentimetersIsZero :
    signedLengthReadout LengthUnit.millimeters
        (setup.graph.resultantSignedAmplitude
          (setup.graph.shiftDistance .zeroCrossingAtTenCentimeters)) = 0
  amplitudeAtTwentyCentimetersIsNegativeScale :
    signedLengthReadout LengthUnit.millimeters
        (setup.graph.resultantSignedAmplitude
          (setup.graph.shiftDistance .negativeScaleAtTwentyCentimeters)) =
      -lengthReadout LengthUnit.millimeters setup.graph.verticalScaleYsPrime
  tenCentimeterTickIsPrinted : setup.graph.tenCentimeterTickPrinted = true
  twentyCentimeterTickIsPrinted :
    setup.graph.twentyCentimeterTickPrinted = true
  graphHasGrid : setup.graph.gridShown = true
  graphShowsSmoothCurve : setup.graph.smoothCurveShown = true
  graphCurveDecreases :
    setup.graph.curveDecreasesAcrossDisplayedRange = true

/-- Positivity assumptions selecting a nondegenerate cord and two-wave setup. -/
structure HasPhysicalWaveParameters
    (setup : TwoWaveInterferenceSetup) : Prop where
  cordTensionPositive : 0 < tensionInNewtons setup.cordTension
  amplitudePositive :
    0 < lengthReadout LengthUnit.meters setup.amplitudeYm
  frequencyPositive : 0 < frequencyInHertz setup.frequency
  wavelengthPositive :
    0 < lengthReadout LengthUnit.meters setup.wavelength
  waveNumberPositive :
    0 < waveNumberInRadiansPerMeter setup.waveNumber
  angularFrequencyPositive :
    0 < angularFrequencyInRadiansPerSecond setup.angularFrequency

/-!
The standard laws for equal-frequency sinusoidal waves on a linear cord:

* cyclic and angular frequency obey `omega = 2 pi f`;
* wave number and wavelength obey `k lambda = 2 pi`;
* positive-`x` propagation uses the temporal phase `-omega t`;
* translating the second wave by `s` contributes phase `-k s`;
* transverse displacements superpose linearly;
* the signed coefficient of the resultant is `2 y_m cos (k s / 2)`.

These are general relations.  They contain neither the numerical conclusion
`240 pi` nor any of the displayed radian-per-second answers.
-/
structure SatisfiesTwoWaveInterferenceLaws
    (setup : TwoWaveInterferenceSetup) : Prop where
  cyclicToAngularFrequency :
    angularFrequencyInRadiansPerSecond setup.angularFrequency =
      2 * Real.pi * frequencyInHertz setup.frequency
  waveNumberWavelengthRelation :
    waveNumberInRadiansPerMeter setup.waveNumber *
        lengthReadout LengthUnit.meters setup.wavelength =
      2 * Real.pi
  firstWaveHasZeroPhaseOffset :
    ∀ shift : LengthQuantity, setup.phaseOffsetRadians .first shift = 0
  secondWavePhaseComesFromTranslation :
    ∀ shift : LengthQuantity,
      setup.phaseOffsetRadians .second shift =
        -(waveNumberInRadiansPerMeter setup.waveNumber *
          lengthReadout LengthUnit.meters shift)
  positiveXSinusoidalWaveform :
    ∀ (wave : WaveIndex) (shift : LengthQuantity)
        (xMeters tSeconds : ℝ),
      setup.displacementInMeters wave shift xMeters tSeconds =
        lengthReadout LengthUnit.meters setup.amplitudeYm *
          Real.sin
            (waveNumberInRadiansPerMeter setup.waveNumber * xMeters -
              angularFrequencyInRadiansPerSecond setup.angularFrequency *
                tSeconds +
              setup.phaseOffsetRadians wave shift)
  linearSuperposition :
    ∀ (shift : LengthQuantity) (xMeters tSeconds : ℝ),
      setup.resultantDisplacementInMeters shift xMeters tSeconds =
        setup.displacementInMeters .first shift xMeters tSeconds +
          setup.displacementInMeters .second shift xMeters tSeconds
  resultantSignedAmplitudeCoefficient :
    ∀ shift : LengthQuantity,
      signedLengthReadout LengthUnit.meters
          (setup.graph.resultantSignedAmplitude shift) =
        2 * lengthReadout LengthUnit.meters setup.amplitudeYm *
          Real.cos
            (waveNumberInRadiansPerMeter setup.waveNumber *
              lengthReadout LengthUnit.meters shift / 2)

/-! ## Displayed choices and formalization target -/

/-- Labels printed beside the four candidate angular frequencies. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Radian-per-second value printed beside each answer label. -/
def AnswerChoice.radiansPerSecond : AnswerChoice → ℝ
  | .A => 742
  | .B => 746
  | .C => 750
  | .D => 754

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/--
Agreement with an answer displayed to the nearest whole radian per second.
The strict half-width also excludes a midpoint tie.
-/
def MatchesNearestWholeRadianPerSecond
    (angularFrequencyRadiansPerSecond : ℝ)
    (choice : AnswerChoice) : Prop :=
  |angularFrequencyRadiansPerSecond - choice.radiansPerSecond| < (1 : ℝ) / 2

/-!
At `f = 120 Hz`, the governing relation gives
`omega = 2 pi f = 240 pi rad/s`, approximately `753.98 rad/s`.  Thus the
nearest displayed whole-radian value is `754 rad/s`, answer D.

This formalizes blueprint label `thm:physics:phyx_mini_0303:target`.
-/
theorem problem_phyx_mini_0303
    (setup : TwoWaveInterferenceSetup)
    (_problemAndFigure : MatchesProblemAndPrimaryFigure setup)
    (_physical : HasPhysicalWaveParameters setup)
    (_laws : SatisfiesTwoWaveInterferenceLaws setup) :
    angularFrequencyInRadiansPerSecond setup.angularFrequency =
        240 * Real.pi ∧
      MatchesNearestWholeRadianPerSecond
        (angularFrequencyInRadiansPerSecond setup.angularFrequency)
        recordedAnswerChoice := by
  have hω :
      angularFrequencyInRadiansPerSecond setup.angularFrequency =
        240 * Real.pi := by
    rw [_laws.cyclicToAngularFrequency,
      _problemAndFigure.commonFrequencyIs120Hertz]
    ring
  refine ⟨hω, ?_⟩
  rw [hω]
  simp only [MatchesNearestWholeRadianPerSecond, recordedAnswerChoice,
    AnswerChoice.radiansPerSecond]
  have hpiBounds :
      (1507 : ℝ) / 480 < Real.pi ∧ Real.pi < (503 : ℝ) / 160 := by
    have hsinLt : ∀ {x : ℝ}, 0 < x → Real.sin x < x := by
      intro x hx
      rcases lt_or_ge 1 x with h' | h'
      · exact (Real.sin_le_one x).trans_lt h'
      have hxabs : |x| = x := abs_of_nonneg hx.le
      have hbound :=
        le_of_abs_le (Real.sin_bound (show |x| ≤ 1 by rwa [hxabs]))
      rw [sub_le_iff_le_add', hxabs] at hbound
      apply hbound.trans_lt
      rw [sub_add, sub_lt_self_iff, sub_pos, div_eq_mul_inv (x ^ 3)]
      refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos hx 3)
      apply pow_le_pow_of_le_one hx.le h'
      simp
    have hpiThree : (3 : ℝ) < Real.pi := by
      have h := hsinLt (x := Real.pi / 6) (by positivity)
      rw [Real.sin_pi_div_six] at h
      nlinarith
    have hsBounds :
        (0.09799 : ℝ) < Real.sin (Real.pi / 32) ∧
          Real.sin (Real.pi / 32) < (0.09804 : ℝ) := by
      rw [Real.sin_pi_div_thirty_two]
      have ha0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
      have ha2 : (Real.sqrt 2) ^ 2 = 2 := by norm_num
      have haLower : (1.41421 : ℝ) < Real.sqrt 2 := by
        nlinarith
      have haUpper : Real.sqrt 2 < (1.41422 : ℝ) := by
        nlinarith
      have hb0 : 0 ≤ Real.sqrt (2 + Real.sqrt 2) := Real.sqrt_nonneg _
      have hb2 :
          (Real.sqrt (2 + Real.sqrt 2)) ^ 2 = 2 + Real.sqrt 2 := by
        rw [Real.sq_sqrt]
        positivity
      have hbLower :
          (1.84775 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
        nlinarith
      have hbUpper :
          Real.sqrt (2 + Real.sqrt 2) < (1.84777 : ℝ) := by
        nlinarith
      have hc0 :
          0 ≤ Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) :=
        Real.sqrt_nonneg _
      have hc2 :
          (Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) ^ 2 =
            2 + Real.sqrt (2 + Real.sqrt 2) := by
        rw [Real.sq_sqrt]
        positivity
      have hcLower :
          (1.96156 : ℝ) <
            Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
        nlinarith
      have hcUpper :
          Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) <
            (1.96159 : ℝ) := by
        nlinarith
      have he0 :
          0 ≤
            Real.sqrt (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) :=
        Real.sqrt_nonneg _
      have hradicand :
          0 ≤
            (2 : ℝ) - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
        nlinarith
      have he2 :
          (Real.sqrt
              (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)))) ^ 2 =
            2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
        rw [Real.sq_sqrt hradicand]
      constructor <;> nlinarith
    have hxNonneg : 0 ≤ Real.pi / 32 := by positivity
    have hxLeOne : Real.pi / 32 ≤ (1 : ℝ) := by
      nlinarith [Real.pi_le_four]
    have hTaylor := Real.sin_bound (x := Real.pi / 32) (by
      rw [abs_of_nonneg hxNonneg]
      exact hxLeOne)
    rw [abs_of_nonneg hxNonneg] at hTaylor
    have hTaylorSides := abs_le.mp hTaylor
    have hTaylorLower :
        Real.pi / 32 - (Real.pi / 32) ^ 3 / 6 -
            (Real.pi / 32) ^ 4 * (5 / 96) ≤
          Real.sin (Real.pi / 32) := by
      linarith [hTaylorSides.1]
    have hTaylorUpper :
        Real.sin (Real.pi / 32) ≤
          Real.pi / 32 - (Real.pi / 32) ^ 3 / 6 +
            (Real.pi / 32) ^ 4 * (5 / 96) := by
      linarith [hTaylorSides.2]
    have hpiLower : (1507 : ℝ) / 480 < Real.pi := by
      by_contra h
      have hpiLe : Real.pi ≤ (1507 : ℝ) / 480 := le_of_not_gt h
      have hxLower : (3 : ℝ) / 32 ≤ Real.pi / 32 := by
        nlinarith
      have hxUpper : Real.pi / 32 ≤ (1507 : ℝ) / 15360 := by
        nlinarith
      have hxCubeLower :
          ((3 : ℝ) / 32) ^ 3 ≤ (Real.pi / 32) ^ 3 :=
        pow_le_pow_left₀ (by norm_num) hxLower 3
      have hxFourthUpper :
          (Real.pi / 32) ^ 4 ≤ ((1507 : ℝ) / 15360) ^ 4 :=
        pow_le_pow_left₀ hxNonneg hxUpper 4
      nlinarith [hsBounds.1, hTaylorUpper]
    have hpiCoarseUpper : Real.pi < (16 : ℝ) / 5 := by
      by_contra h
      have hpiGe : (16 : ℝ) / 5 ≤ Real.pi := le_of_not_gt h
      have hxLower : (1 : ℝ) / 10 ≤ Real.pi / 32 := by
        nlinarith
      have hxUpper : Real.pi / 32 ≤ (1 : ℝ) / 8 := by
        nlinarith [Real.pi_le_four]
      have hxCubeUpper :
          (Real.pi / 32) ^ 3 ≤ ((1 : ℝ) / 8) ^ 3 :=
        pow_le_pow_left₀ hxNonneg hxUpper 3
      have hxFourthUpper :
          (Real.pi / 32) ^ 4 ≤ ((1 : ℝ) / 8) ^ 4 :=
        pow_le_pow_left₀ hxNonneg hxUpper 4
      nlinarith [hsBounds.2, hTaylorLower]
    have hpiUpper : Real.pi < (503 : ℝ) / 160 := by
      by_contra h
      have hpiGe : (503 : ℝ) / 160 ≤ Real.pi := le_of_not_gt h
      have hxLower : (503 : ℝ) / 5120 ≤ Real.pi / 32 := by
        nlinarith
      have hxUpper : Real.pi / 32 ≤ (1 : ℝ) / 10 := by
        nlinarith
      have hxCubeUpper :
          (Real.pi / 32) ^ 3 ≤ ((1 : ℝ) / 10) ^ 3 :=
        pow_le_pow_left₀ hxNonneg hxUpper 3
      have hxFourthUpper :
          (Real.pi / 32) ^ 4 ≤ ((1 : ℝ) / 10) ^ 4 :=
        pow_le_pow_left₀ hxNonneg hxUpper 4
      nlinarith [hsBounds.2, hTaylorLower]
    exact ⟨hpiLower, hpiUpper⟩
  rw [abs_lt]
  constructor
  · nlinarith [hpiBounds.1]
  · nlinarith [hpiBounds.2]

end PhyXMiniProblems.ProblemPhyXMini0303
