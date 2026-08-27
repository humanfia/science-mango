import ArchonPhysics.ResonanceWeightSinc
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.PeakFunction

/-!
# The finite-time resonance profile as an approximate identity

The squared sinc profile is integrable, has strictly positive mass, and its
normalization is a one-dimensional peak kernel.  Consequently the normalized
finite-time resonance weight converges, when tested against an integrable
function continuous at zero, to evaluation on the exact resonance surface.

This is the scalar phase-mismatch part of collision-kernel identification.
It does not identify the random-lattice density of states or justify replacing
a modal sum by the corresponding phase-mismatch integral.
-/

namespace ArchonPhysics.NormalizedResonancePeakKernel

open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.ResonanceWeightSinc
open Filter MeasureTheory Topology Bornology

noncomputable section

/-- The unnormalized one-dimensional squared-sinc profile. -/
def sincSquareKernel (x : Real) : Real := Real.sinc x ^ 2

theorem sincSquareKernel_nonneg (x : Real) : 0 <= sincSquareKernel x := by
  exact sq_nonneg _

theorem continuous_sincSquareKernel : Continuous sincSquareKernel := by
  exact Real.continuous_sinc.pow 2

/-- A convenient integrable majorant for the squared-sinc profile. -/
theorem sincSquareKernel_le_two_div_one_add_sq (x : Real) :
    sincSquareKernel x <= 2 / (1 + x ^ 2) := by
  have hsinc_sq_le_one : Real.sinc x ^ 2 <= 1 := by
    have hleft := Real.neg_one_le_sinc x
    have hright := Real.sinc_le_one x
    have hsum : 0 <= Real.sinc x + 1 := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hright) hsum]
  by_cases hxsmall : |x| <= 1
  · calc
      sincSquareKernel x <= 1 := hsinc_sq_le_one
      _ <= 2 / (1 + x ^ 2) := by
        have hx_sq : x ^ 2 <= 1 := by
          simpa [sq_abs] using
            ((sq_le_sq₀ (abs_nonneg x) zero_le_one).2 hxsmall)
        rw [le_div_iff₀ (by positivity : 0 < 1 + x ^ 2)]
        nlinarith
  · have hxabs : 1 < |x| := lt_of_not_ge hxsmall
    have hx : x ≠ 0 := by
      intro hzero
      simp [hzero] at hxabs
      norm_num at hxabs
    have hsin_sq_le_one : Real.sin x ^ 2 <= 1 := by
      have hsin := Real.abs_sin_le_one x
      simpa [sq_abs] using
        ((sq_le_sq₀ (abs_nonneg (Real.sin x)) zero_le_one).2 hsin)
    have hx_sq_pos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    have hsinc_tail : sincSquareKernel x <= 1 / x ^ 2 := by
      rw [sincSquareKernel, Real.sinc_of_ne_zero hx, div_pow]
      exact div_le_div_of_nonneg_right hsin_sq_le_one hx_sq_pos.le
    calc
      sincSquareKernel x <= 1 / x ^ 2 := hsinc_tail
      _ <= 2 / (1 + x ^ 2) := by
        rw [div_le_div_iff₀ hx_sq_pos (by positivity : 0 < 1 + x ^ 2)]
        have hx_sq_ge_one : 1 <= x ^ 2 := by
          nlinarith [sq_abs x]
        nlinarith

theorem integrable_sincSquareKernel : Integrable sincSquareKernel := by
  apply Integrable.mono'
      (integrable_inv_one_add_sq.const_mul 2)
      continuous_sincSquareKernel.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sincSquareKernel_nonneg x)]
  simpa [div_eq_mul_inv] using sincSquareKernel_le_two_div_one_add_sq x

/-- Total mass of the squared-sinc profile.  Its numerical value is not needed
for the approximate-identity argument. -/
def sincSquareMass : Real := ∫ x : Real, sincSquareKernel x

theorem sincSquareMass_pos : 0 < sincSquareMass := by
  unfold sincSquareMass
  apply integral_pos_of_integrable_nonneg_nonzero
      continuous_sincSquareKernel integrable_sincSquareKernel
      sincSquareKernel_nonneg (x := 0)
  simp [sincSquareKernel, Real.sinc_zero]

theorem sincSquareMass_ne_zero : sincSquareMass ≠ 0 :=
  sincSquareMass_pos.ne'

/-- Unit-mass squared-sinc kernel. -/
def normalizedSincSquareKernel (x : Real) : Real :=
  sincSquareMass⁻¹ * sincSquareKernel x

theorem normalizedSincSquareKernel_nonneg (x : Real) :
    0 <= normalizedSincSquareKernel x := by
  exact mul_nonneg (inv_nonneg.mpr sincSquareMass_pos.le)
    (sincSquareKernel_nonneg x)

theorem integral_normalizedSincSquareKernel :
    ∫ x : Real, normalizedSincSquareKernel x = 1 := by
  rw [show (fun x : Real => normalizedSincSquareKernel x) =
      fun x => sincSquareMass⁻¹ * sincSquareKernel x by rfl,
    integral_const_mul, sincSquareMass]
  exact inv_mul_cancel₀ sincSquareMass_ne_zero

/-- The normalized kernel has the decay required by Mathlib's peak-function
theorem. -/
theorem tendsto_norm_mul_normalizedSincSquareKernel_cobounded :
    Tendsto (fun x : Real => ‖x‖ * normalizedSincSquareKernel x)
      (cobounded Real) (nhds 0) := by
  have hinv : Tendsto (fun x : Real => ‖x‖⁻¹)
      (cobounded Real) (nhds 0) :=
    tendsto_norm_cobounded_atTop.inv_tendsto_atTop
  have hupper : Tendsto (fun x : Real => sincSquareMass⁻¹ * ‖x‖⁻¹)
      (cobounded Real) (nhds 0) := by
    simpa using tendsto_const_nhds.mul hinv
  apply squeeze_zero' (g := fun x : Real => sincSquareMass⁻¹ * ‖x‖⁻¹)
  · exact Eventually.of_forall fun x =>
      mul_nonneg (norm_nonneg x) (normalizedSincSquareKernel_nonneg x)
  · filter_upwards
      [eventually_ne_of_tendsto_norm_atTop tendsto_norm_cobounded_atTop (0 : Real)]
      with x hx
    have habs : |x| ≠ 0 := abs_ne_zero.mpr hx
    have hsinc_abs : |Real.sinc x| <= |x|⁻¹ := by
      rw [Real.sinc_of_ne_zero hx, abs_div]
      simpa [div_eq_mul_inv] using
        div_le_div_of_nonneg_right (Real.abs_sin_le_one x) (abs_nonneg x)
    have hsinc_sq : Real.sinc x ^ 2 <= |x|⁻¹ ^ 2 := by
      have habs_sq :=
        (sq_le_sq₀ (abs_nonneg (Real.sinc x))
          (inv_nonneg.mpr (abs_nonneg x))).2 hsinc_abs
      simpa [sq_abs] using habs_sq
    have htail : |x| * Real.sinc x ^ 2 <= |x|⁻¹ := by
      calc
        |x| * Real.sinc x ^ 2 <= |x| * (|x|⁻¹ ^ 2) :=
          mul_le_mul_of_nonneg_left hsinc_sq (abs_nonneg x)
        _ = |x|⁻¹ := by
          rw [pow_two, ← mul_assoc, mul_inv_cancel₀ habs, one_mul]
    rw [Real.norm_eq_abs, normalizedSincSquareKernel, sincSquareKernel]
    calc
      |x| * (sincSquareMass⁻¹ * Real.sinc x ^ 2) =
          sincSquareMass⁻¹ * (|x| * Real.sinc x ^ 2) := by ring
      _ <= sincSquareMass⁻¹ * |x|⁻¹ :=
        mul_le_mul_of_nonneg_left htail (inv_nonneg.mpr sincSquareMass_pos.le)
  · exact hupper

/-- The normalized squared-sinc profiles form an approximate identity on
`Real`: testing against an integrable function continuous at zero converges to
its exact-resonance value. -/
theorem tendsto_integral_scaled_normalizedSincSquareKernel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [CompleteSpace E] {g : Real -> E} (hg : Integrable g)
    (hcg : ContinuousAt g 0) :
    Tendsto
      (fun c : Real => ∫ x : Real,
        (c * normalizedSincSquareKernel (c * x)) • g x)
      atTop (nhds (g 0)) := by
  have hdecay : Tendsto
      (fun x : Real => ‖x‖ ^ Module.finrank Real Real *
        normalizedSincSquareKernel x)
      (cobounded Real) (nhds 0) := by
    simpa using tendsto_norm_mul_normalizedSincSquareKernel_cobounded
  simpa using
    (tendsto_integral_comp_smul_smul_of_integrable
      (F := Real)
      normalizedSincSquareKernel_nonneg
      integral_normalizedSincSquareKernel hdecay hg hcg)

/-- Unit-mass normalization of the physical finite-time resonance weight. -/
def normalizedFiniteTimeResonanceKernel (Omega T : Real) : Real :=
  finiteTimeResonanceWeight Omega T / (2 * sincSquareMass)

theorem normalizedFiniteTimeResonanceKernel_eq_scaled
    (Omega : Real) {T : Real} (hT : 0 < T) :
    normalizedFiniteTimeResonanceKernel Omega T =
      (T / 2) * normalizedSincSquareKernel ((T / 2) * Omega) := by
  rw [normalizedFiniteTimeResonanceKernel,
    finiteTimeResonanceWeight_eq_mul_sinc_sq Omega hT,
    normalizedSincSquareKernel, sincSquareKernel]
  have harg : Omega * T / 2 = (T / 2) * Omega := by ring
  rw [harg]
  field_simp [sincSquareMass_ne_zero]

/-- The normalized squared-sinc profile is integrable. -/
theorem integrable_normalizedSincSquareKernel :
    Integrable normalizedSincSquareKernel := by
  exact integrable_sincSquareKernel.const_mul sincSquareMass⁻¹

/-- At every positive time, the normalized physical resonance profile is
integrable. -/
theorem integrable_normalizedFiniteTimeResonanceKernel
    {T : Real} (hT : 0 < T) :
    Integrable (fun Omega : Real =>
      normalizedFiniteTimeResonanceKernel Omega T) := by
  have hc : 0 < T / 2 := by positivity
  have hscaled : Integrable (fun Omega : Real =>
      normalizedSincSquareKernel ((T / 2) * Omega)) :=
    integrable_normalizedSincSquareKernel.comp_mul_left' hc.ne'
  apply (hscaled.const_mul (T / 2)).congr
  filter_upwards with Omega
  exact (normalizedFiniteTimeResonanceKernel_eq_scaled Omega hT).symm

/-- At every positive observation time, the normalized physical resonance
profile has exactly unit mass. -/
theorem integral_normalizedFiniteTimeResonanceKernel_eq_one
    {T : Real} (hT : 0 < T) :
    ∫ Omega : Real, normalizedFiniteTimeResonanceKernel Omega T = 1 := by
  have hc : 0 < T / 2 := by positivity
  calc
    (∫ Omega : Real, normalizedFiniteTimeResonanceKernel Omega T) =
        ∫ Omega : Real,
          (T / 2) * normalizedSincSquareKernel ((T / 2) * Omega) := by
      apply integral_congr_ae
      filter_upwards with Omega
      exact normalizedFiniteTimeResonanceKernel_eq_scaled Omega hT
    _ = (T / 2) * ∫ Omega : Real,
        normalizedSincSquareKernel ((T / 2) * Omega) := by
      rw [integral_const_mul]
    _ = 1 := by
      rw [Measure.integral_comp_mul_left,
        integral_normalizedSincSquareKernel]
      rw [abs_of_pos (inv_pos.mpr hc)]
      simp only [smul_eq_mul]
      rw [mul_one, mul_inv_cancel₀ hc.ne']

/-- The normalized physical finite-time resonance profile converges weakly to
evaluation at exact resonance. -/
theorem tendsto_integral_normalizedFiniteTimeResonanceKernel
    {g : Real -> Real} (hg : Integrable g) (hcg : ContinuousAt g 0) :
    Tendsto
      (fun T : Real => ∫ Omega : Real,
        normalizedFiniteTimeResonanceKernel Omega T * g Omega)
      atTop (nhds (g 0)) := by
  have hscale : Tendsto (fun T : Real => T / 2) atTop atTop :=
    Tendsto.atTop_div_const (by norm_num) tendsto_id
  have hpeak :=
    (tendsto_integral_scaled_normalizedSincSquareKernel
      (E := Real) hg hcg).comp hscale
  refine hpeak.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : Real)] with T hT
  apply integral_congr_ae
  filter_upwards with Omega
  rw [normalizedFiniteTimeResonanceKernel_eq_scaled Omega hT]
  simp only [smul_eq_mul]

end

end ArchonPhysics.NormalizedResonancePeakKernel
