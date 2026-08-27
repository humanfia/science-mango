import ArchonPhysics.LennardJonesNormalizedForceScaling

/-!
# Integrating the LJ force remainder over a kinetic time window

The normalized pointwise LJ/FPUT force discrepancy is `O(g^3)`.  On the
kinetic window `0 ≤ t ≤ L/g^2`, a uniform strain/amplitude tube therefore
gives an accumulated scalar discrepancy of order `O(g)`.

The theorem takes interval integrability and the tube bounds as explicit
inputs.  It does not prove that the exact LJ trajectory stays in the tube,
nor does it control nonlinear stability or random-phase propagation.
-/

namespace ArchonPhysics.LennardJonesKineticTimeForceRemainder

open Set
open ArchonPhysics.LennardJonesForceTaylorTube
open ArchonPhysics.LennardJonesNormalizedForceScaling

noncomputable section

/-- Physical time corresponding to the fixed kinetic horizon `L`. -/
def kineticWindowTime (g L : Real) : Real := L / g ^ 2

/-- Coupling-independent coefficient in the integrated force-remainder
bound. -/
def kineticForceRemainderCoefficient (r₀ rho amplitudeBound : Real) : Real :=
  r₀ / 72 * forceRemainderTubeConstant rho *
    (amplitudeBound / r₀) ^ 4

/-- A pointwise `O(g^3)` force discrepancy accumulates to `O(g)` over the
`L/g^2` kinetic time window.  Interval integrability is returned alongside
the estimate to keep the integral's physical semantics explicit. -/
theorem intervalIntegrable_and_norm_integral_forceRemainder_le_kinetic
    {depth r₀ g rho L amplitudeBound : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) (hg : 0 < g)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hL : 0 ≤ L) (_hAmplitude : 0 ≤ amplitudeBound)
    (amplitude : Real → Real)
    (hIntegrable : IntervalIntegrable
      (fun t => normalizedForceRemainder depth r₀ g (amplitude t))
      MeasureTheory.volume 0 (kineticWindowTime g L))
    (htube : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      |g * amplitude t| ≤ rho * r₀)
    (hamplitude : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      |amplitude t| ≤ amplitudeBound) :
    IntervalIntegrable
        (fun t => normalizedForceRemainder depth r₀ g (amplitude t))
        MeasureTheory.volume 0 (kineticWindowTime g L) ∧
      ‖∫ t in 0..kineticWindowTime g L,
          normalizedForceRemainder depth r₀ g (amplitude t)‖ ≤
        kineticForceRemainderCoefficient r₀ rho amplitudeBound * L * g := by
  refine ⟨hIntegrable, ?_⟩
  have hgNe : g ≠ 0 := ne_of_gt hg
  have htime : 0 ≤ kineticWindowTime g L := by
    unfold kineticWindowTime
    exact div_nonneg hL (sq_nonneg g)
  have hcoefficient :
      0 ≤ r₀ / 72 * forceRemainderTubeConstant rho * |g| ^ 3 := by
    exact mul_nonneg
      (mul_nonneg (div_nonneg hr₀.le (by norm_num))
        (forceRemainderTubeConstant_pos hrho0 hrho1).le)
      (pow_nonneg (abs_nonneg g) 3)
  calc
    ‖∫ t in 0..kineticWindowTime g L,
        normalizedForceRemainder depth r₀ g (amplitude t)‖ ≤
      (r₀ / 72 * forceRemainderTubeConstant rho * g ^ 3 *
          (amplitudeBound / r₀) ^ 4) *
        |kineticWindowTime g L - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      have htIcc : t ∈ Icc 0 (kineticWindowTime g L) := by
        simpa only [uIcc_of_le htime] using Set.uIoc_subset_uIcc ht
      have hpoint := abs_normalizedForceRemainder_le_g_cubed
        hdepth hr₀ hgNe hrho0 hrho1 (htube t htIcc)
      have hratio : |amplitude t| / r₀ ≤ amplitudeBound / r₀ :=
        (div_le_div_iff_of_pos_right hr₀).2 (hamplitude t htIcc)
      have hpow : (|amplitude t| / r₀) ^ 4 ≤
          (amplitudeBound / r₀) ^ 4 :=
        pow_le_pow_left₀ (div_nonneg (abs_nonneg _) hr₀.le) hratio 4
      have hbounded := hpoint.trans
        (mul_le_mul_of_nonneg_left hpow hcoefficient)
      simpa [Real.norm_eq_abs, abs_of_pos hg, mul_assoc] using hbounded
    _ = kineticForceRemainderCoefficient r₀ rho amplitudeBound * L * g := by
      rw [sub_zero, abs_of_nonneg htime]
      unfold kineticWindowTime kineticForceRemainderCoefficient
      field_simp [hgNe]

/-- Consequently the explicit kinetic-window bound tends to zero as the
weak coupling tends to zero through positive values. -/
theorem kinetic_integrated_force_bound_tendsto_zero
    {r₀ rho amplitudeBound L : Real} :
    Filter.Tendsto
      (fun g : Real =>
        kineticForceRemainderCoefficient r₀ rho amplitudeBound * L * g)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hfull : Filter.Tendsto
      (fun g : Real =>
        kineticForceRemainderCoefficient r₀ rho amplitudeBound * L * g)
      (nhds 0) (nhds 0) := by
    have hcont : ContinuousAt
        (fun g : Real =>
          kineticForceRemainderCoefficient r₀ rho amplitudeBound * L * g) 0 := by
      fun_prop
    have hout :
        nhds (kineticForceRemainderCoefficient r₀ rho amplitudeBound * L * 0) =
          nhds 0 := by
      simp
    nth_rewrite 2 [← hout]
    exact hcont
  exact hfull.mono_left inf_le_left

end

end ArchonPhysics.LennardJonesKineticTimeForceRemainder
