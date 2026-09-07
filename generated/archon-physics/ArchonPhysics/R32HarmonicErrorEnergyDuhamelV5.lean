import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

/-!
# Harmonic error Duhamel estimate, clean-build repair

This isolated repair proves the dimension-free energy estimate for a forced
nonnegative harmonic system.  It uses the current explicit real-inner-product
API and does not import any of the broken earlier R32 Duhamel drafts.
-/

namespace ArchonPhysics.R32HarmonicErrorEnergyDuhamelV5

open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]

def IsSelfAdjointOperator (H : E →L[Real] E) : Prop :=
  ∀ x y, @inner Real E _ (H x) y = @inner Real E _ x (H y)

def IsNonnegativeOperator (H : E →L[Real] E) : Prop :=
  ∀ x, 0 ≤ @inner Real E _ x (H x)

def harmonicEnergySq (H : E →L[Real] E) (x y : E) : Real :=
  ‖y‖ ^ 2 + @inner Real E _ x (H x)

def harmonicEnergySeminorm (H : E →L[Real] E) (x y : E) : Real :=
  Real.sqrt (harmonicEnergySq H x y)

theorem harmonicEnergySq_nonneg {H : E →L[Real] E}
    (hH : IsNonnegativeOperator H) (x y : E) :
    0 ≤ harmonicEnergySq H x y := by
  exact add_nonneg (sq_nonneg ‖y‖) (hH x)

theorem harmonicEnergySeminorm_nonneg (H : E →L[Real] E) (x y : E) :
    0 ≤ harmonicEnergySeminorm H x y :=
  Real.sqrt_nonneg _

theorem harmonicEnergySeminorm_sq {H : E →L[Real] E}
    (hH : IsNonnegativeOperator H) (x y : E) :
    harmonicEnergySeminorm H x y ^ 2 = harmonicEnergySq H x y :=
  Real.sq_sqrt (harmonicEnergySq_nonneg hH x y)

theorem hasDerivAt_harmonicEnergySq
    (H : E →L[Real] E) (hHself : IsSelfAdjointOperator H)
    {deltaX deltaY F : Real → E} {s : Real}
    (hX : HasDerivAt deltaX (deltaY s) s)
    (hY : HasDerivAt deltaY (-H (deltaX s) + F s) s) :
    HasDerivAt
      (fun r => harmonicEnergySq H (deltaX r) (deltaY r))
      (2 * (@inner Real E _ (deltaY s) (F s))) s := by
  have hHX : HasDerivAt (fun r => H (deltaX r)) (H (deltaY s)) s :=
    H.hasFDerivAt.comp_hasDerivAt s hX
  have hkin := hY.norm_sq
  have hpot := hX.inner Real hHX
  have hsum := hkin.add hpot
  have hsymm :
      @inner Real E _ (deltaX s) (H (deltaY s)) =
        @inner Real E _ (deltaY s) (H (deltaX s)) := by
    rw [← hHself (deltaX s) (deltaY s)]
    exact (real_inner_comm (H (deltaX s)) (deltaY s)).symm
  have hderiv :
      2 * (@inner Real E _ (deltaY s) (-H (deltaX s) + F s)) +
          ((@inner Real E _ (deltaX s) (H (deltaY s))) +
            (@inner Real E _ (deltaY s) (H (deltaX s)))) =
        2 * (@inner Real E _ (deltaY s) (F s)) := by
    rw [inner_add_right, inner_neg_right, hsymm]
    ring
  have hsum' :
      HasDerivAt
        (fun r => ‖deltaY r‖ ^ 2 +
          @inner Real E _ (deltaX r) (H (deltaX r)))
        (2 * (@inner Real E _ (deltaY s) (-H (deltaX s) + F s)) +
          ((@inner Real E _ (deltaX s) (H (deltaY s))) +
            (@inner Real E _ (deltaY s) (H (deltaX s))))) s := by
    convert hsum using 1
    · rfl
    · apply Module.ext
      rfl
    · funext r
      rfl
  have hout := hsum'.congr_deriv hderiv
  simpa only [harmonicEnergySq] using hout

theorem hasDerivAt_regularizedHarmonicEnergy
    (H : E →L[Real] E)
    (hHself : IsSelfAdjointOperator H)
    (hHnonneg : IsNonnegativeOperator H)
    {deltaX deltaY F : Real → E} {s epsilon : Real}
    (hepsilon : 0 < epsilon)
    (hX : HasDerivAt deltaX (deltaY s) s)
    (hY : HasDerivAt deltaY (-H (deltaX s) + F s) s) :
    HasDerivAt
      (fun r => Real.sqrt
        (harmonicEnergySq H (deltaX r) (deltaY r) + epsilon ^ 2))
      ((@inner Real E _ (deltaY s) (F s)) /
        Real.sqrt
          (harmonicEnergySq H (deltaX s) (deltaY s) + epsilon ^ 2)) s := by
  have hargPos :
      0 < harmonicEnergySq H (deltaX s) (deltaY s) + epsilon ^ 2 :=
    add_pos_of_nonneg_of_pos
      (harmonicEnergySq_nonneg hHnonneg _ _)
      (sq_pos_of_pos hepsilon)
  have hsquare :=
    (hasDerivAt_harmonicEnergySq H hHself hX hY).add_const (epsilon ^ 2)
  have hsqrt := hsquare.sqrt hargPos.ne'
  have hsqrtPos :
      0 < Real.sqrt
        (harmonicEnergySq H (deltaX s) (deltaY s) + epsilon ^ 2) :=
    Real.sqrt_pos.2 hargPos
  have hcancel :
      2 * (@inner Real E _ (deltaY s) (F s)) /
          (2 * Real.sqrt
            (harmonicEnergySq H (deltaX s) (deltaY s) + epsilon ^ 2)) =
        (@inner Real E _ (deltaY s) (F s)) /
          Real.sqrt
            (harmonicEnergySq H (deltaX s) (deltaY s) + epsilon ^ 2) := by
    field_simp [ne_of_gt hsqrtPos]
  exact hsqrt.congr_deriv hcancel

theorem norm_deriv_regularizedHarmonicEnergy_le
    (H : E →L[Real] E)
    (hHself : IsSelfAdjointOperator H)
    (hHnonneg : IsNonnegativeOperator H)
    {deltaX deltaY F : Real → E} {s epsilon : Real}
    (hepsilon : 0 < epsilon)
    (hX : HasDerivAt deltaX (deltaY s) s)
    (hY : HasDerivAt deltaY (-H (deltaX s) + F s) s) :
    ‖deriv (fun r => Real.sqrt
        (harmonicEnergySq H (deltaX r) (deltaY r) + epsilon ^ 2)) s‖ ≤
      ‖F s‖ := by
  let radius := Real.sqrt
    (harmonicEnergySq H (deltaX s) (deltaY s) + epsilon ^ 2)
  have hargPos :
      0 < harmonicEnergySq H (deltaX s) (deltaY s) + epsilon ^ 2 :=
    add_pos_of_nonneg_of_pos
      (harmonicEnergySq_nonneg hHnonneg _ _)
      (sq_pos_of_pos hepsilon)
  have hradiusPos : 0 < radius := Real.sqrt_pos.2 hargPos
  have hradiusSq : radius ^ 2 =
      harmonicEnergySq H (deltaX s) (deltaY s) + epsilon ^ 2 :=
    Real.sq_sqrt hargPos.le
  have hYle : ‖deltaY s‖ ≤ radius := by
    have hposition := hHnonneg (deltaX s)
    have hepsilonSq := sq_nonneg epsilon
    have hradiusNonneg := hradiusPos.le
    unfold harmonicEnergySq at hradiusSq
    nlinarith [sq_nonneg ‖deltaY s‖]
  have hCauchy :
      abs (@inner Real E _ (deltaY s) (F s)) ≤ ‖deltaY s‖ * ‖F s‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := Real) (deltaY s) (F s))
  have hquotient :
      abs ((@inner Real E _ (deltaY s) (F s)) / radius) ≤ ‖F s‖ := by
    rw [abs_div, abs_of_pos hradiusPos, div_le_iff₀ hradiusPos]
    calc
      abs (@inner Real E _ (deltaY s) (F s)) ≤
          ‖deltaY s‖ * ‖F s‖ := hCauchy
      _ ≤ radius * ‖F s‖ :=
        mul_le_mul_of_nonneg_right hYle (norm_nonneg (F s))
      _ = ‖F s‖ * radius := mul_comm _ _
  rw [(hasDerivAt_regularizedHarmonicEnergy H hHself hHnonneg
    hepsilon hX hY).deriv]
  simpa only [radius, Real.norm_eq_abs] using hquotient

theorem harmonicEnergySeminorm_le_intervalIntegral_norm
    (H : E →L[Real] E)
    (hHself : IsSelfAdjointOperator H)
    (hHnonneg : IsNonnegativeOperator H)
    (deltaX deltaY F : Real → E) (t : Real)
    (ht : 0 ≤ t)
    (hXzero : deltaX 0 = 0)
    (hYzero : deltaY 0 = 0)
    (hX : ∀ s ∈ Icc (0 : Real) t,
      HasDerivAt deltaX (deltaY s) s)
    (hY : ∀ s ∈ Icc (0 : Real) t,
      HasDerivAt deltaY (-H (deltaX s) + F s) s)
    (hF : IntervalIntegrable (fun s => ‖F s‖) volume 0 t) :
    harmonicEnergySeminorm H (deltaX t) (deltaY t) ≤
      ∫ s in 0..t, ‖F s‖ := by
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  let regularized : Real → Real := fun s => Real.sqrt
    (harmonicEnergySq H (deltaX s) (deltaY s) + epsilon ^ 2)
  have hregularizedDeriv (s : Real) (hs : s ∈ Icc (0 : Real) t) :
      HasDerivAt regularized
        ((@inner Real E _ (deltaY s) (F s)) / regularized s) s := by
    simpa only [regularized] using
      hasDerivAt_regularizedHarmonicEnergy H hHself hHnonneg
        hepsilon (hX s hs) (hY s hs)
  have hregularizedContinuous : ContinuousOn regularized (Icc (0 : Real) t) := by
    intro s hs
    exact (hregularizedDeriv s hs).continuousAt.continuousWithinAt
  have hregularizedDifferentiable :
      DifferentiableOn Real regularized (Ioo (0 : Real) t) := by
    intro s hs
    exact (hregularizedDeriv s ⟨hs.1.le, hs.2.le⟩).differentiableAt.differentiableWithinAt
  have hderivBound :
      ∀ s ∈ Ioo (0 : Real) t, ‖deriv regularized s‖ ≤ ‖F s‖ := by
    intro s hs
    simpa only [regularized] using
      norm_deriv_regularizedHarmonicEnergy_le H hHself hHnonneg
        hepsilon (hX s ⟨hs.1.le, hs.2.le⟩)
          (hY s ⟨hs.1.le, hs.2.le⟩)
  have hdisplacement :
      ‖regularized t - regularized 0‖ ≤ ∫ s in 0..t, ‖F s‖ := by
    exact norm_sub_le_integral_of_norm_deriv_le_of_le ht
      hregularizedContinuous hregularizedDifferentiable
      (Filter.Eventually.of_forall (fun s hs => hderivBound s hs)) hF
  have hzero : regularized 0 = epsilon := by
    simp [regularized, harmonicEnergySq, hXzero, hYzero,
      Real.sqrt_sq_eq_abs, abs_of_pos hepsilon]
  have hregularizedUpper :
      regularized t ≤ (∫ s in 0..t, ‖F s‖) + epsilon := by
    have hsub : regularized t - regularized 0 ≤
        ∫ s in 0..t, ‖F s‖ := by
      exact (le_abs_self (regularized t - regularized 0)).trans
        (by simpa only [Real.norm_eq_abs] using hdisplacement)
    rw [hzero] at hsub
    linarith
  calc
    harmonicEnergySeminorm H (deltaX t) (deltaY t) ≤ regularized t := by
      unfold harmonicEnergySeminorm regularized
      exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg epsilon))
    _ ≤ (∫ s in 0..t, ‖F s‖) + epsilon := hregularizedUpper

theorem norm_bond_le_harmonicEnergySeminorm
    {B : Type*} [NormedAddCommGroup B]
    (H : E →L[Real] E) (hHnonneg : IsNonnegativeOperator H)
    (bond : E → B)
    (hbond : ∀ x, ‖bond x‖ ^ 2 ≤ @inner Real E _ x (H x))
    (x y : E) :
    ‖bond x‖ ≤ harmonicEnergySeminorm H x y := by
  have henergySq := harmonicEnergySeminorm_sq hHnonneg x y
  have hbondSq := hbond x
  have henergyNonneg := harmonicEnergySeminorm_nonneg H x y
  have hbondNonneg := norm_nonneg (bond x)
  unfold harmonicEnergySq at henergySq
  nlinarith [sq_nonneg ‖y‖]

theorem norm_bond_error_le_intervalIntegral_norm
    {B : Type*} [NormedAddCommGroup B]
    (H : E →L[Real] E)
    (hHself : IsSelfAdjointOperator H)
    (hHnonneg : IsNonnegativeOperator H)
    (bond : E → B)
    (hbond : ∀ x, ‖bond x‖ ^ 2 ≤ @inner Real E _ x (H x))
    (deltaX deltaY F : Real → E) (t : Real)
    (ht : 0 ≤ t)
    (hXzero : deltaX 0 = 0)
    (hYzero : deltaY 0 = 0)
    (hX : ∀ s ∈ Icc (0 : Real) t,
      HasDerivAt deltaX (deltaY s) s)
    (hY : ∀ s ∈ Icc (0 : Real) t,
      HasDerivAt deltaY (-H (deltaX s) + F s) s)
    (hF : IntervalIntegrable (fun s => ‖F s‖) volume 0 t) :
    ‖bond (deltaX t)‖ ≤ ∫ s in 0..t, ‖F s‖ := by
  exact (norm_bond_le_harmonicEnergySeminorm
    H hHnonneg bond hbond (deltaX t) (deltaY t)).trans
      (harmonicEnergySeminorm_le_intervalIntegral_norm
        H hHself hHnonneg deltaX deltaY F t ht hXzero hYzero hX hY hF)

#print axioms harmonicEnergySeminorm_le_intervalIntegral_norm
#print axioms norm_bond_error_le_intervalIntegral_norm

end

end ArchonPhysics.R32HarmonicErrorEnergyDuhamelV5
