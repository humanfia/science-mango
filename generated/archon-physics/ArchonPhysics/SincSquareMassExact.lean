import ArchonPhysics.NormalizedResonancePeakKernel
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact mass of the squared-sinc resonance profile

We compute the exact normalization constant of the scalar finite-time
resonance kernel.  The proof uses the Fourier transform of the indicator of
`[-1/2, 1/2]`, the convolution theorem, and Fourier inversion at zero.  In
Mathlib's `exp (-2 * pi * I * x * xi)` convention, this indicator transforms
to `sinc (pi * xi)`.
-/

namespace ArchonPhysics.SincSquareMassExact

open ArchonPhysics.NormalizedResonancePeakKernel
open Filter FourierTransform FourierTransformInv MeasureTheory Set
open scoped Convolution ComplexConjugate

noncomputable section

/-- The complex-valued indicator of the symmetric unit interval. -/
def halfBox (x : Real) : Complex :=
  Icc (-(1 / 2 : Real)) (1 / 2 : Real) |>.indicator (fun _ => (1 : Complex)) x

theorem integrable_halfBox : Integrable halfBox := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  exact integrableOn_const (by simp [Real.volume_Icc])

theorem halfBox_norm_le_one (x : Real) : ‖halfBox x‖ <= 1 := by
  simp only [halfBox, indicator]
  split_ifs <;> simp

theorem halfBox_neg (x : Real) : halfBox (-x) = halfBox x := by
  unfold halfBox
  by_cases hx : x ∈ Icc (-(1 / 2 : Real)) (1 / 2 : Real)
  · have hneg : -x ∈ Icc (-(1 / 2 : Real)) (1 / 2 : Real) := by
      constructor <;> linarith [hx.1, hx.2]
    rw [indicator_of_mem hneg, indicator_of_mem hx]
  · have hneg : -x ∉ Icc (-(1 / 2 : Real)) (1 / 2 : Real) := by
      intro h
      apply hx
      constructor <;> linarith [h.1, h.2]
    rw [indicator_of_notMem hneg, indicator_of_notMem hx]

theorem halfBox_mul_self (x : Real) : halfBox x * halfBox x = halfBox x := by
  unfold halfBox
  by_cases hx : x ∈ Icc (-(1 / 2 : Real)) (1 / 2 : Real)
  · rw [indicator_of_mem hx]
    simp
  · rw [indicator_of_notMem hx]
    simp

theorem continuousAt_halfBox_of_not_endpoint {x : Real}
    (hleft : x ≠ -(1 / 2 : Real)) (hright : x ≠ (1 / 2 : Real)) :
    ContinuousAt halfBox x := by
  apply (continuousOn_const : ContinuousOn (fun _ : Real => (1 : Complex))
    (interior (Icc (-(1 / 2 : Real)) (1 / 2 : Real)))).continuousAt_indicator
  rw [frontier_Icc (by norm_num : -(1 / 2 : Real) <= (1 / 2 : Real))]
  simpa [Set.mem_insert_iff] using And.intro hleft hright

/-- The self-convolution of `halfBox` is continuous at zero.  This is the only
continuity input needed by Fourier inversion. -/
theorem continuousAt_halfBoxConvolution_zero :
    ContinuousAt
      (halfBox ⋆[ContinuousLinearMap.mul Complex Complex] halfBox)
      (0 : Real) := by
  let L := ContinuousLinearMap.mul Complex Complex
  change ContinuousAt
    (fun x : Real => ∫ t : Real, L (halfBox t) (halfBox (x - t))) 0
  apply continuousAt_of_dominated
      (bound := fun t : Real => ‖halfBox t‖)
  · exact Eventually.of_forall fun x =>
      integrable_halfBox.aestronglyMeasurable.convolution_integrand_snd
        L integrable_halfBox.aestronglyMeasurable x
  · filter_upwards with x
    filter_upwards with t
    change ‖halfBox t * halfBox (x - t)‖ <= ‖halfBox t‖
    rw [norm_mul]
    simpa using
      (mul_le_mul_of_nonneg_left (halfBox_norm_le_one (x - t)) (norm_nonneg (halfBox t)))
  · exact integrable_halfBox.norm
  · filter_upwards
      [(volume : Measure Real).ae_ne (-(1 / 2 : Real)),
       (volume : Measure Real).ae_ne (1 / 2 : Real)] with t htleft htright
    have hleft : -t ≠ -(1 / 2 : Real) := by
      intro h
      apply htright
      linarith
    have hright : -t ≠ (1 / 2 : Real) := by
      intro h
      apply htleft
      linarith
    have hbox : ContinuousAt halfBox (-t) :=
      continuousAt_halfBox_of_not_endpoint hleft hright
    have hsub : ContinuousAt (fun x : Real => x - t) 0 :=
      continuousAt_id.sub continuousAt_const
    have hcomp : ContinuousAt (fun x : Real => halfBox (x - t)) 0 := by
      simpa only [Function.comp_def] using hbox.comp_of_eq hsub (by simp)
    exact continuousAt_const.mul hcomp

theorem halfBoxConvolution_zero :
    (halfBox ⋆[ContinuousLinearMap.mul Complex Complex] halfBox) (0 : Real) = 1 := by
  change (∫ t : Real, halfBox t * halfBox (0 - t)) = 1
  simp_rw [zero_sub, halfBox_neg, halfBox_mul_self]
  have hvol : (volume : Measure Real).real
      (Icc (-(1 / 2 : Real)) (1 / 2 : Real)) = 1 := by
    norm_num [Measure.real, Real.volume_Icc]
  simpa only [halfBox, hvol, one_smul] using
    (integral_indicator_const (μ := volume) (1 : Complex)
      (show MeasurableSet (Icc (-(1 / 2 : Real)) (1 / 2 : Real)) from measurableSet_Icc))

/-- Exact Fourier transform of the unit symmetric interval indicator. -/
theorem fourier_halfBox (xi : Real) :
    𝓕 halfBox xi = (Real.sinc (Real.pi * xi) : Complex) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [halfBox, indicator, smul_eq_mul]
  simp_rw [mul_ite, mul_one, mul_zero]
  have hind :
      (fun v : Real => if v ∈ Icc (-(1 / 2 : Real)) (1 / 2 : Real) then
        Complex.exp ((-2 * Real.pi * v * xi : Real) * Complex.I) else 0) =
      (Icc (-(1 / 2 : Real)) (1 / 2 : Real)).indicator
        (fun v => Complex.exp ((-2 * Real.pi * v * xi : Real) * Complex.I)) := by
    funext v
    by_cases hv : v ∈ Icc (-(1 / 2 : Real)) (1 / 2 : Real)
    · rw [if_pos hv, indicator_of_mem hv]
    · rw [if_neg hv, indicator_of_notMem hv]
  rw [hind, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : -(1 / 2 : Real) <= (1 / 2 : Real))]
  by_cases hxi : xi = 0
  · norm_num [hxi]
  · let c : Real := -(2 * Real.pi * xi)
    have hc : c ≠ 0 := by
      dsimp [c]
      exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hxi)
    have hscale := intervalIntegral.integral_comp_mul_left
      (f := fun y : Real => Complex.exp (y * Complex.I))
      (a := -(1 / 2 : Real)) (b := (1 / 2 : Real)) hc
    have hsymmetric :
        (∫ y : Real in c * (-(1 / 2 : Real))..c * (1 / 2 : Real),
          Complex.exp (y * Complex.I)) =
        2 * (-(Real.pi * xi)) * Real.sinc (-(Real.pi * xi)) := by
      have hleft : c * (-(1 / 2 : Real)) = -(-(Real.pi * xi)) := by
        dsimp [c]
        ring
      have hright : c * (1 / 2 : Real) = -(Real.pi * xi) := by
        dsimp [c]
        ring
      rw [hleft, hright]
      simpa using integral_exp_mul_I_eq_sinc (-(Real.pi * xi))
    have harg (x : Real) : -2 * Real.pi * x * xi = c * x := by
      dsimp [c]
      ring
    simp_rw [harg]
    rw [hscale, hsymmetric]
    have hreal :
        c⁻¹ * (2 * (-(Real.pi * xi)) * Real.sinc (-(Real.pi * xi))) =
          Real.sinc (Real.pi * xi) := by
      rw [Real.sinc_neg]
      dsimp [c]
      field_simp [Real.pi_ne_zero, hxi]
    rw [Complex.real_smul]
    exact_mod_cast hreal

theorem integrable_fourier_halfBoxConvolution :
    Integrable
      (𝓕 (halfBox ⋆[ContinuousLinearMap.mul Complex Complex] halfBox)) := by
  have hscaled : Integrable
      (fun xi : Real => sincSquareKernel (Real.pi * xi)) :=
    integrable_sincSquareKernel.comp_mul_left' Real.pi_ne_zero
  have hcomplex : Integrable
      (fun xi : Real => (sincSquareKernel (Real.pi * xi) : Complex)) := hscaled.ofReal
  refine hcomplex.congr (Eventually.of_forall fun xi => ?_)
  rw [Real.fourier_mul_convolution_eq integrable_halfBox integrable_halfBox,
    fourier_halfBox]
  simp [sincSquareKernel, pow_two]

/-- In Mathlib's Fourier normalization, the scaled squared-sinc profile has
unit mass. -/
theorem integral_sincSquareKernel_pi_mul :
    ∫ xi : Real, sincSquareKernel (Real.pi * xi) = 1 := by
  have hinv := integrable_halfBox.integrable_convolution
    (ContinuousLinearMap.mul Complex Complex) integrable_halfBox
  have hfourierInv := hinv.fourierInv_fourier_eq
    integrable_fourier_halfBoxConvolution continuousAt_halfBoxConvolution_zero
  have hcomplex :
      (∫ xi : Real, (sincSquareKernel (Real.pi * xi) : Complex)) = 1 := by
    calc
      (∫ xi : Real, (sincSquareKernel (Real.pi * xi) : Complex)) =
          ∫ xi : Real,
            𝓕 (halfBox ⋆[ContinuousLinearMap.mul Complex Complex] halfBox) xi := by
              apply integral_congr_ae
              filter_upwards with xi
              rw [Real.fourier_mul_convolution_eq integrable_halfBox integrable_halfBox,
                fourier_halfBox]
              simp [sincSquareKernel, pow_two]
      _ = 𝓕⁻ (𝓕 (halfBox ⋆[ContinuousLinearMap.mul Complex Complex] halfBox)) (0 : Real) := by
            rw [Real.fourierInv_eq']
            apply integral_congr_ae
            filter_upwards with xi
            simp
      _ = (halfBox ⋆[ContinuousLinearMap.mul Complex Complex] halfBox) (0 : Real) := hfourierInv
      _ = 1 := halfBoxConvolution_zero
  apply Complex.ofReal_injective
  calc
    ((∫ xi : Real, sincSquareKernel (Real.pi * xi) : Real) : Complex) =
        ∫ xi : Real, (sincSquareKernel (Real.pi * xi) : Complex) := by
          exact (integral_ofReal (μ := volume) (𝕜 := Complex)
            (f := fun xi : Real => sincSquareKernel (Real.pi * xi))).symm
    _ = 1 := hcomplex
    _ = ((1 : Real) : Complex) := by norm_num

/-- The exact mass of `sinc^2` on the real line is `pi`. -/
theorem sincSquareMass_eq_pi : sincSquareMass = Real.pi := by
  have hscale := Measure.integral_comp_mul_left sincSquareKernel Real.pi
  rw [abs_of_pos (inv_pos.mpr Real.pi_pos), integral_sincSquareKernel_pi_mul] at hscale
  have heq : (1 : Real) = Real.pi⁻¹ * sincSquareMass := by
    simpa only [smul_eq_mul, sincSquareMass] using hscale
  calc
    sincSquareMass = Real.pi * (Real.pi⁻¹ * sincSquareMass) := by
      field_simp [Real.pi_ne_zero]
    _ = Real.pi * 1 := by rw [← heq]
    _ = Real.pi := mul_one _

/-- The physical normalization denominator is exactly `2*pi`. -/
theorem two_mul_sincSquareMass_eq_two_pi :
    2 * sincSquareMass = 2 * Real.pi := by
  rw [sincSquareMass_eq_pi]

/-- The normalized physical peak is therefore division by the explicit
constant `2*pi`. -/
theorem normalizedFiniteTimeResonanceKernel_eq_div_two_pi (Omega T : Real) :
    normalizedFiniteTimeResonanceKernel Omega T =
      ArchonPhysics.FiniteTimeResonanceWeight.finiteTimeResonanceWeight Omega T /
        (2 * Real.pi) := by
  rw [normalizedFiniteTimeResonanceKernel, sincSquareMass_eq_pi]

/-- Consequently the unnormalized physical finite-time resonance weight has
total mass `2*pi` at every positive time. -/
theorem integral_finiteTimeResonanceWeight_eq_two_pi {T : Real} (hT : 0 < T) :
    ∫ Omega : Real,
      ArchonPhysics.FiniteTimeResonanceWeight.finiteTimeResonanceWeight Omega T =
      2 * Real.pi := by
  rw [show (fun Omega : Real =>
      ArchonPhysics.FiniteTimeResonanceWeight.finiteTimeResonanceWeight Omega T) =
      fun Omega => T * Real.sinc (Omega * T / 2) ^ 2 by
        funext Omega
        exact ArchonPhysics.ResonanceWeightSinc.finiteTimeResonanceWeight_eq_mul_sinc_sq Omega hT]
  rw [integral_const_mul]
  have hrewrite : (fun Omega : Real => Real.sinc (Omega * T / 2) ^ 2) =
      fun Omega => sincSquareKernel ((T / 2) * Omega) := by
    funext Omega
    simp only [sincSquareKernel]
    congr 2
    ring
  rw [hrewrite, Measure.integral_comp_mul_left sincSquareKernel (T / 2),
    show (∫ y : Real, sincSquareKernel y) = sincSquareMass by rfl,
    sincSquareMass_eq_pi, abs_of_pos (inv_pos.mpr (div_pos hT (by norm_num)))]
  have hcancel : T * T⁻¹ = 1 := mul_inv_cancel₀ hT.ne'
  rw [inv_div, div_eq_mul_inv, smul_eq_mul]
  calc
    T * (2 * T⁻¹ * Real.pi) = (T * T⁻¹) * (2 * Real.pi) := by ring
    _ = 2 * Real.pi := by rw [hcancel, one_mul]

end

end ArchonPhysics.SincSquareMassExact
