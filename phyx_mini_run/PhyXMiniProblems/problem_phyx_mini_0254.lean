import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0254

open Dimension

/-!
# Phase constant from position and velocity graphs

Figures (a) and (b) show a common one-dimensional simple harmonic motion.
The vertical scales are `x_s = 5.0 cm` and `v_s = 5.0 cm/s`, and the stated
angular frequency is `1.20 rad/s`.  At the common time origin, the primary
image places the position curve two of the five scale divisions above zero
and the velocity curve four of the five scale divisions below zero.

Physical time, length, speed, and angular frequency are represented by
Physlib dimensionful quantities.  Real numbers are used only for coherent SI
or centimeter/second readouts and for the dimensionless phase in radians.
-/

/-! ## Dimensionful quantities and readouts -/

/-- A unit-independent physical time. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- A unit-independent signed position or displacement. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A unit-independent signed velocity component. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Angular frequency, with inverse-time dimension; radians are dimensionless. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- Read a physical time in seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  (time UnitChoices.SI).val

/-- Read a signed physical length in centimeters. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * (length UnitChoices.SI).val

/-- Read a signed physical speed in centimeters per second. -/
def speedInCentimetersPerSecond (speed : SpeedQuantity) : ℝ :=
  100 * (speed UnitChoices.SI).val

/-- Read an angular frequency in radians per second. -/
def angularFrequencyInRadiansPerSecond
    (angularFrequency : AngularFrequencyQuantity) : ℝ :=
  (angularFrequency UnitChoices.SI).val

/-! ## Figure labels and physical setup -/

/-- The two panels explicitly labeled in the supplied image. -/
inductive FigurePanel where
  | positionGraph_a
  | velocityGraph_b
  deriving DecidableEq, Repr

/-- Quantities printed on the horizontal and vertical graph axes. -/
inductive AxisQuantity where
  | time_t
  | position_x
  | velocity_v
  deriving DecidableEq, Repr

/-- The scale symbols printed next to the vertical axes. -/
inductive VerticalScaleLabel where
  | positionScale_xs
  | velocityScale_vs
  deriving DecidableEq, Repr

/-!
The labels, scales, common origin, and qualitative slope information read
from the two graph panels.  The scale values and curve values are independent
physical quantities; their numerical relations are recorded separately in
`MatchesSuppliedPhaseGraphs`.
-/
structure PhaseGraphFigure where
  horizontalAxisQuantity : FigurePanel → AxisQuantity
  verticalAxisQuantity : FigurePanel → AxisQuantity
  verticalScaleLabel : FigurePanel → VerticalScaleLabel
  positionScale_xs : LengthQuantity
  velocityScale_vs : SpeedQuantity
  commonTimeOrigin : TimeQuantity
  curveDecreasesToRightAtOrigin : FigurePanel → Bool

/-!
The oscillator quantities named in the problem.  In particular, the phase
constant is an independent dimensionless parameter, not a definition of the
requested numerical answer.
-/
structure HarmonicPhaseSetup where
  figure : PhaseGraphFigure
  positionFunction : TimeQuantity → LengthQuantity
  velocityFunction : TimeQuantity → SpeedQuantity
  amplitude_xm : LengthQuantity
  angularFrequency_omega : AngularFrequencyQuantity
  phaseConstant_phi : ℝ

/-! ## Problem data, primary-image readouts, and governing laws -/

/-- The stated angular frequency `1.20 rad/s`. -/
def MatchesStatedAngularFrequency (setup : HarmonicPhaseSetup) : Prop :=
  angularFrequencyInRadiansPerSecond setup.angularFrequency_omega = 6 / 5

/-!
Labels and quantitative readouts from the primary image.

The top and bottom scale labels are separated from zero by five equal graph
divisions.  At the common vertical axis the position curve is two divisions
above zero, whereas the velocity curve is four divisions below zero.  Thus
the origin values are respectively `2/5` of `x_s` and `-4/5` of `v_s`.
These are figure observations, not assumptions about the requested phase.
-/
structure MatchesSuppliedPhaseGraphs (setup : HarmonicPhaseSetup) : Prop where
  panelAHorizontalAxis :
    setup.figure.horizontalAxisQuantity .positionGraph_a = .time_t
  panelAVerticalAxis :
    setup.figure.verticalAxisQuantity .positionGraph_a = .position_x
  panelBHorizontalAxis :
    setup.figure.horizontalAxisQuantity .velocityGraph_b = .time_t
  panelBVerticalAxis :
    setup.figure.verticalAxisQuantity .velocityGraph_b = .velocity_v
  panelAScaleLabel :
    setup.figure.verticalScaleLabel .positionGraph_a = .positionScale_xs
  panelBScaleLabel :
    setup.figure.verticalScaleLabel .velocityGraph_b = .velocityScale_vs
  positionCurveDecreasing :
    setup.figure.curveDecreasesToRightAtOrigin .positionGraph_a = true
  velocityCurveDecreasing :
    setup.figure.curveDecreasesToRightAtOrigin .velocityGraph_b = true
  commonOriginIsZero :
    timeInSeconds setup.figure.commonTimeOrigin = 0
  positionScaleReadout :
    lengthInCentimeters setup.figure.positionScale_xs = 5
  velocityScaleReadout :
    speedInCentimetersPerSecond setup.figure.velocityScale_vs = 5
  positionAtOriginFromFigure :
    lengthInCentimeters
        (setup.positionFunction setup.figure.commonTimeOrigin) =
      (2 / 5) * lengthInCentimeters setup.figure.positionScale_xs
  velocityAtOriginFromFigure :
    speedInCentimetersPerSecond
        (setup.velocityFunction setup.figure.commonTimeOrigin) =
      -(4 / 5) *
        speedInCentimetersPerSecond setup.figure.velocityScale_vs

/-!
Positivity and the conventional positive representative for the phase.
Restricting `φ` to one positive turn selects a representative of the periodic
cosine phase but does not prescribe its value.
-/
structure HasPhysicalHarmonicParameters (setup : HarmonicPhaseSetup) : Prop where
  amplitudePositive :
    0 < lengthInCentimeters setup.amplitude_xm
  angularFrequencyPositive :
    0 < angularFrequencyInRadiansPerSecond setup.angularFrequency_omega
  phasePositive : 0 < setup.phaseConstant_phi
  phaseWithinOneTurn : setup.phaseConstant_phi < 2 * Real.pi

/-!
The governing simple-harmonic-motion laws in the sign convention stated in
the question:

`x(t) = x_m cos (ωt + φ)` and
`v(t) = -ω x_m sin (ωt + φ)`.

The second field states that the plotted velocity is the velocity
corresponding to the plotted position.  Neither field mentions an answer
choice or a numerical phase.
-/
structure SatisfiesPositivePhaseCosineSHM
    (setup : HarmonicPhaseSetup) : Prop where
  positionNormalForm :
    ∀ time : TimeQuantity,
      lengthInCentimeters (setup.positionFunction time) =
        lengthInCentimeters setup.amplitude_xm *
          Real.cos
            (angularFrequencyInRadiansPerSecond
                setup.angularFrequency_omega *
              timeInSeconds time + setup.phaseConstant_phi)
  correspondingVelocityNormalForm :
    ∀ time : TimeQuantity,
      speedInCentimetersPerSecond (setup.velocityFunction time) =
        -(angularFrequencyInRadiansPerSecond
            setup.angularFrequency_omega *
          lengthInCentimeters setup.amplitude_xm *
          Real.sin
            (angularFrequencyInRadiansPerSecond
                setup.angularFrequency_omega *
              timeInSeconds time + setup.phaseConstant_phi))

/-! ## Displayed answers and formalization target -/

/-- Labels of the four displayed phase-constant choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The phase in radians printed beside each answer label. -/
def answerChoiceInRadians : AnswerChoice → ℝ
  | .A => 65 / 100
  | .B => 86 / 100
  | .C => 103 / 100
  | .D => 121 / 100

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Agreement with a displayed phase to the nearest `0.01 rad`. -/
def MatchesAnswerToNearestHundredth
    (phase : ℝ) (choice : AnswerChoice) : Prop :=
  |phase - answerChoiceInRadians choice| < 1 / 200

/-!
At the common origin the graph gives `x(0) = 2 cm` and `v(0) = -4 cm/s`.
For `ω = 1.20 rad/s`, division of the velocity relation by the position
relation gives `tan φ = 5/3`.  The positive one-turn representative selected
by the graph signs is therefore `arctan (5/3)`, approximately `1.03 rad`.
Consequently the phase matches choice C and is no farther from C than from
any other displayed choice.

This formalizes `thm:physics:phyx_mini_0254:target`.
-/
theorem phaseConstantFromPositionAndVelocityGraphs
    (setup : HarmonicPhaseSetup)
    (hFrequency : MatchesStatedAngularFrequency setup)
    (hFigure : MatchesSuppliedPhaseGraphs setup)
    (hPhysical : HasPhysicalHarmonicParameters setup)
    (hLaws : SatisfiesPositivePhaseCosineSHM setup) :
    setup.phaseConstant_phi = Real.arctan (5 / 3) ∧
      MatchesAnswerToNearestHundredth
        setup.phaseConstant_phi recordedAnswerChoice ∧
      ∀ choice : AnswerChoice,
        |setup.phaseConstant_phi -
            answerChoiceInRadians recordedAnswerChoice| ≤
          |setup.phaseConstant_phi - answerChoiceInRadians choice| := by
  have hPosition :
      lengthInCentimeters
          (setup.positionFunction setup.figure.commonTimeOrigin) = 2 := by
    rw [hFigure.positionAtOriginFromFigure, hFigure.positionScaleReadout]
    norm_num
  have hVelocity :
      speedInCentimetersPerSecond
          (setup.velocityFunction setup.figure.commonTimeOrigin) = -4 := by
    rw [hFigure.velocityAtOriginFromFigure, hFigure.velocityScaleReadout]
    norm_num
  have hPositionLaw :=
    hLaws.positionNormalForm setup.figure.commonTimeOrigin
  have hVelocityLaw :=
    hLaws.correspondingVelocityNormalForm setup.figure.commonTimeOrigin
  change
    angularFrequencyInRadiansPerSecond setup.angularFrequency_omega = 6 / 5
      at hFrequency
  rw [hFigure.commonOriginIsZero, hFrequency] at hPositionLaw hVelocityLaw
  norm_num at hPositionLaw hVelocityLaw
  have hAmplitudeCos :
      lengthInCentimeters setup.amplitude_xm *
          Real.cos setup.phaseConstant_phi = 2 := by
    linarith
  have hAmplitudeSin :
      lengthInCentimeters setup.amplitude_xm *
          Real.sin setup.phaseConstant_phi = 10 / 3 := by
    nlinarith
  have hAmplitudePositive :=
    hPhysical.amplitudePositive
  have hAmplitudeNe :
      lengthInCentimeters setup.amplitude_xm ≠ 0 :=
    ne_of_gt hAmplitudePositive
  have hCosPositive : 0 < Real.cos setup.phaseConstant_phi := by
    nlinarith
  have hSinPositive : 0 < Real.sin setup.phaseConstant_phi := by
    nlinarith
  have hSinCos :
      Real.sin setup.phaseConstant_phi =
        (5 / 3) * Real.cos setup.phaseConstant_phi := by
    apply (mul_left_cancel₀ hAmplitudeNe)
    calc
      lengthInCentimeters setup.amplitude_xm *
            Real.sin setup.phaseConstant_phi =
          10 / 3 := hAmplitudeSin
      _ = (5 / 3) *
            (lengthInCentimeters setup.amplitude_xm *
              Real.cos setup.phaseConstant_phi) := by
        rw [hAmplitudeCos]
        norm_num
      _ = lengthInCentimeters setup.amplitude_xm *
            ((5 / 3) * Real.cos setup.phaseConstant_phi) := by
        ring
  have hTan :
      Real.tan setup.phaseConstant_phi = 5 / 3 := by
    rw [Real.tan_eq_sin_div_cos, hSinCos]
    field_simp
  have hPhaseLtHalfPi :
      setup.phaseConstant_phi < Real.pi / 2 := by
    by_contra hNot
    have hHalfPiLe :
        Real.pi / 2 ≤ setup.phaseConstant_phi :=
      le_of_not_gt hNot
    by_cases hBeforeThreeHalves :
        setup.phaseConstant_phi ≤ Real.pi + Real.pi / 2
    · have hCosNonpositive :=
        Real.cos_nonpos_of_pi_div_two_le_of_le
          hHalfPiLe hBeforeThreeHalves
      linarith
    · have hShiftedSinNegative :
          Real.sin (setup.phaseConstant_phi - 2 * Real.pi) < 0 := by
        apply Real.sin_neg_of_neg_of_neg_pi_lt
        · linarith [hPhysical.phaseWithinOneTurn]
        · have hAfterThreeHalves :
              Real.pi + Real.pi / 2 < setup.phaseConstant_phi :=
            lt_of_not_ge hBeforeThreeHalves
          linarith [Real.pi_pos]
      rw [Real.sin_sub_two_pi] at hShiftedSinNegative
      linarith
  have hPhase :
      setup.phaseConstant_phi = Real.arctan (5 / 3) := by
    symm
    apply Real.arctan_eq_of_tan_eq hTan
    constructor
    · linarith [hPhysical.phasePositive, Real.pi_pos]
    · exact hPhaseLtHalfPi

  have complexCosBound :
      ∀ {x : ℂ}, ‖x‖ / 13 ≤ (1 : ℝ) / 2 →
        ‖Complex.cos x -
            (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 +
              x ^ 8 / 40320 - x ^ 10 / 3628800)‖ ≤
          ‖x‖ ^ 12 / Nat.factorial 12 * 2 := by
    intro x hx
    calc
      _ =
          ‖(Complex.exp (-x * Complex.I) -
                ∑ m ∈ Finset.range 12,
                  (-x * Complex.I) ^ m / m.factorial) / 2 +
            (Complex.exp (x * Complex.I) -
                ∑ m ∈ Finset.range 12,
                  (x * Complex.I) ^ m / m.factorial) / 2‖ := by
        simp [Complex.cos, field, Finset.sum_range_succ, Nat.factorial]
        grind [Complex.I_sq, two_ne_zero]
      _ ≤
          ‖Complex.exp (-x * Complex.I) -
              ∑ m ∈ Finset.range 12,
                (-x * Complex.I) ^ m / m.factorial‖ / 2 +
            ‖Complex.exp (x * Complex.I) -
              ∑ m ∈ Finset.range 12,
                (x * Complex.I) ^ m / m.factorial‖ / 2 := by
        grw [norm_add_le]
        simp
      _ ≤
          (‖-x * Complex.I‖ ^ 12 / Nat.factorial 12 * 2) / 2 +
            (‖x * Complex.I‖ ^ 12 / Nat.factorial 12 * 2) / 2 := by
        grw [
          Complex.exp_bound' (by convert hx using 1 <;> norm_num),
          Complex.exp_bound' (by convert hx using 1 <;> norm_num)]
      _ = ‖x‖ ^ 12 / Nat.factorial 12 * 2 := by
        simp
        ring
  have complexSinBound :
      ∀ {x : ℂ}, ‖x‖ / 13 ≤ (1 : ℝ) / 2 →
        ‖Complex.sin x -
            (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 +
              x ^ 9 / 362880 - x ^ 11 / 39916800)‖ ≤
          ‖x‖ ^ 12 / Nat.factorial 12 * 2 := by
    intro x hx
    calc
      _ =
          ‖(Complex.exp (-x * Complex.I) -
                ∑ m ∈ Finset.range 12,
                  (-x * Complex.I) ^ m / m.factorial) *
              Complex.I / 2 -
            (Complex.exp (x * Complex.I) -
                ∑ m ∈ Finset.range 12,
                  (x * Complex.I) ^ m / m.factorial) *
              Complex.I / 2‖ := by
        simp [Complex.sin, field, Finset.sum_range_succ, Nat.factorial]
        congr 1
        ring_nf
        rw [
          show Complex.I ^ 2 = -1 by
            norm_num [pow_succ, Complex.I_mul_I],
          show Complex.I ^ 4 = 1 by
            norm_num [pow_succ, Complex.I_mul_I],
          show Complex.I ^ 6 = -1 by
            norm_num [pow_succ, Complex.I_mul_I],
          show Complex.I ^ 8 = 1 by
            norm_num [pow_succ, Complex.I_mul_I],
          show Complex.I ^ 10 = -1 by
            norm_num [pow_succ, Complex.I_mul_I],
          show Complex.I ^ 12 = 1 by
            norm_num [pow_succ, Complex.I_mul_I]]
        ring
      _ ≤
          ‖Complex.exp (-x * Complex.I) -
              ∑ m ∈ Finset.range 12,
                (-x * Complex.I) ^ m / m.factorial‖ / 2 +
            ‖Complex.exp (x * Complex.I) -
              ∑ m ∈ Finset.range 12,
                (x * Complex.I) ^ m / m.factorial‖ / 2 := by
        grw [norm_sub_le]
        simp
      _ ≤
          (‖-x * Complex.I‖ ^ 12 / Nat.factorial 12 * 2) / 2 +
            (‖x * Complex.I‖ ^ 12 / Nat.factorial 12 * 2) / 2 := by
        grw [
          Complex.exp_bound' (by convert hx using 1 <;> norm_num),
          Complex.exp_bound' (by convert hx using 1 <;> norm_num)]
      _ = ‖x‖ ^ 12 / Nat.factorial 12 * 2 := by
        simp
        ring
  have realCosBound :
      ∀ {x : ℝ}, |x| / 13 ≤ (1 : ℝ) / 2 →
        |Real.cos x -
            (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 +
              x ^ 8 / 40320 - x ^ 10 / 3628800)| ≤
          |x| ^ 12 / Nat.factorial 12 * 2 := by
    intro x hx
    have hxc : ‖(x : ℂ)‖ / 13 ≤ (1 : ℝ) / 2 := by
      exact_mod_cast hx
    exact_mod_cast complexCosBound hxc
  have realSinBound :
      ∀ {x : ℝ}, |x| / 13 ≤ (1 : ℝ) / 2 →
        |Real.sin x -
            (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 +
              x ^ 9 / 362880 - x ^ 11 / 39916800)| ≤
          |x| ^ 12 / Nat.factorial 12 * 2 := by
    intro x hx
    have hxc : ‖(x : ℂ)‖ / 13 ≤ (1 : ℝ) / 2 := by
      exact_mod_cast hx
    exact_mod_cast complexSinBound hxc

  have hSinLowerEndpoint :=
    realSinBound (x := (205 / 200 : ℝ)) (by
      norm_num [abs_of_nonneg])
  have hCosLowerEndpoint :=
    realCosBound (x := (205 / 200 : ℝ)) (by
      norm_num [abs_of_nonneg])
  have hSinUpperEndpoint :=
    realSinBound (x := (207 / 200 : ℝ)) (by
      norm_num [abs_of_nonneg])
  have hCosUpperEndpoint :=
    realCosBound (x := (207 / 200 : ℝ)) (by
      norm_num [abs_of_nonneg])
  rw [abs_le] at hSinLowerEndpoint
  rw [abs_le] at hCosLowerEndpoint
  rw [abs_le] at hSinUpperEndpoint
  rw [abs_le] at hCosUpperEndpoint
  have hCosLowerPositive : 0 < Real.cos (205 / 200 : ℝ) := by
    norm_num at hCosLowerEndpoint ⊢
    linarith [hCosLowerEndpoint.1]
  have hCosUpperPositive : 0 < Real.cos (207 / 200 : ℝ) := by
    norm_num at hCosUpperEndpoint ⊢
    linarith [hCosUpperEndpoint.1]
  have hTanLowerEndpoint :
      Real.tan (205 / 200 : ℝ) < 5 / 3 := by
    rw [Real.tan_eq_sin_div_cos,
      div_lt_iff₀ hCosLowerPositive]
    norm_num at hSinLowerEndpoint hCosLowerEndpoint ⊢
    linarith [hSinLowerEndpoint.2, hCosLowerEndpoint.1]
  have hTanUpperEndpoint :
      5 / 3 < Real.tan (207 / 200 : ℝ) := by
    rw [Real.tan_eq_sin_div_cos,
      lt_div_iff₀ hCosUpperPositive]
    norm_num at hSinUpperEndpoint hCosUpperEndpoint ⊢
    linarith [hSinUpperEndpoint.1, hCosUpperEndpoint.2]
  have hLowerEndpointLtHalfPi :
      (205 / 200 : ℝ) < Real.pi / 2 := by
    by_contra hNot
    have hCosNonpositive :=
      Real.cos_nonpos_of_pi_div_two_le_of_le
        (le_of_not_gt hNot)
        (by linarith [Real.two_le_pi] :
          (205 / 200 : ℝ) ≤ Real.pi + Real.pi / 2)
    linarith
  have hUpperEndpointLtHalfPi :
      (207 / 200 : ℝ) < Real.pi / 2 := by
    by_contra hNot
    have hCosNonpositive :=
      Real.cos_nonpos_of_pi_div_two_le_of_le
        (le_of_not_gt hNot)
        (by linarith [Real.two_le_pi] :
          (207 / 200 : ℝ) ≤ Real.pi + Real.pi / 2)
    linarith
  have hArctanLower :
      (205 / 200 : ℝ) < Real.arctan (5 / 3) := by
    calc
      (205 / 200 : ℝ) =
          Real.arctan (Real.tan (205 / 200 : ℝ)) := by
        symm
        apply Real.arctan_tan
        · linarith [Real.pi_pos]
        · exact hLowerEndpointLtHalfPi
      _ < Real.arctan (5 / 3) :=
        Real.arctan_strictMono hTanLowerEndpoint
  have hArctanUpper :
      Real.arctan (5 / 3) < (207 / 200 : ℝ) := by
    calc
      Real.arctan (5 / 3) <
          Real.arctan (Real.tan (207 / 200 : ℝ)) :=
        Real.arctan_strictMono hTanUpperEndpoint
      _ = (207 / 200 : ℝ) := by
        apply Real.arctan_tan
        · linarith [Real.pi_pos]
        · exact hUpperEndpointLtHalfPi
  have hRounded :
      |Real.arctan (5 / 3) - 103 / 100| < 1 / 200 := by
    rw [abs_lt]
    constructor <;> norm_num at * <;> linarith
  have hChoiceA :
      |Real.arctan (5 / 3) - 103 / 100| ≤
        |Real.arctan (5 / 3) - 65 / 100| := by
    apply hRounded.le.trans
    rw [abs_of_pos]
    · norm_num
      linarith
    · norm_num
      linarith
  have hChoiceB :
      |Real.arctan (5 / 3) - 103 / 100| ≤
        |Real.arctan (5 / 3) - 86 / 100| := by
    apply hRounded.le.trans
    rw [abs_of_pos]
    · norm_num
      linarith
    · norm_num
      linarith
  have hChoiceD :
      |Real.arctan (5 / 3) - 103 / 100| ≤
        |Real.arctan (5 / 3) - 121 / 100| := by
    apply hRounded.le.trans
    rw [abs_of_neg]
    · norm_num
      linarith
    · norm_num
      linarith
  refine ⟨hPhase, ?_, ?_⟩
  · simpa [MatchesAnswerToNearestHundredth, recordedAnswerChoice,
      answerChoiceInRadians, hPhase] using hRounded
  · rw [hPhase]
    intro choice
    cases choice with
    | A =>
        simpa [recordedAnswerChoice, answerChoiceInRadians] using hChoiceA
    | B =>
        simpa [recordedAnswerChoice, answerChoiceInRadians] using hChoiceB
    | C =>
        simp [recordedAnswerChoice, answerChoiceInRadians]
    | D =>
        simpa [recordedAnswerChoice, answerChoiceInRadians] using hChoiceD

end PhyXMiniProblems.ProblemPhyXMini0254
