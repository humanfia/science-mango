import ArchonPhysics.PhyslibFPUTCoupledKineticShadowingClosure

/-!
# Cubic weak-coupling defects close FPUT kinetic-time shadowing

For a fixed positive restart time `T`, the kinetic step is
`step_n = g_n^2 T`.  This file replaces the two abstract little-o hypotheses
in the coupled-restart closure by the concrete, checkable estimates

`referenceDefectMax_n <= C_ref |g_n|^3`,

`couplingDefectMax_n <= C_coupling |g_n|^3`.

At fixed `T` and fixed constants, division by the kinetic step leaves a
constant multiple of `|g_n|`, hence both normalized defects tend to zero as
`g_n -> 0`.  Eventual nonvanishing of `g_n` is enough: the kinetic shadowing
corollary discards the finite prefix on which the step could vanish.

The final counterexample records the sharp scale distinction.  A defect
equal to `g_n^2 T` is nonnegative and is `O(g_n^2 T)`, but its normalized
ratio is eventually exactly one rather than zero.  Thus a merely quadratic
one-block estimate cannot close a kinetic-time limit without cancellation.
-/

namespace ArchonPhysics.PhyslibFPUTCubicDefectKineticShadowing

open Filter
open MeasureTheory
open Topology
open ArchonPhysics.PhyslibFPUTCoupledKineticShadowingClosure
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing

noncomputable section

/-! ## The concrete cubic-to-little-o calculation -/

/-- A nonnegative `O(|g|^3)` defect is little-o of the fixed-time kinetic
step `g^2 T` when `g -> 0` and is eventually nonzero. -/
theorem cubicDefect_div_kineticStep_tendsto_zero
    (g defect : Nat → Real) {T C : Real}
    (hT : 0 < T) (hC : 0 ≤ C)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : ∀ᶠ n in atTop, g n ≠ 0)
    (hdefect0 : ∀ n, 0 ≤ defect n)
    (hcubic : ∀ n, defect n ≤ C * |g n| ^ 3) :
    Tendsto (fun n ↦ defect n / (g n ^ 2 * T)) atTop (nhds 0) := by
  have habs : Tendsto (fun n ↦ |g n|) atTop (nhds 0) := by
    simpa using hg.abs
  have hCT : |C / T| = C / T :=
    abs_of_nonneg (div_nonneg hC hT.le)
  have hupper : Tendsto (fun n ↦ (C / T) * |g n|)
      atTop (nhds 0) := by
    simpa only [hCT, mul_zero] using (tendsto_const_nhds.mul habs :
      Tendsto (fun n ↦ |C / T| * |g n|) atTop
        (nhds (|C / T| * 0)))
  apply squeeze_zero'
  · filter_upwards [hg0] with n hgn
    exact div_nonneg (hdefect0 n)
      (mul_nonneg (sq_nonneg _) hT.le)
  · filter_upwards [hg0] with n hgn
    have hstep : 0 < g n ^ 2 * T :=
      mul_pos (sq_pos_of_ne_zero hgn) hT
    apply (div_le_iff₀ hstep).2
    calc
      defect n ≤ C * |g n| ^ 3 := hcubic n
      _ = ((C / T) * |g n|) * (g n ^ 2 * T) := by
        rw [show g n ^ 2 = |g n| ^ 2 by
          exact (sq_abs (g n)).symm]
        field_simp [hT.ne']
  · exact hupper

/-- The two concrete cubic estimates provide exactly the pair of normalized
little-o hypotheses consumed by the coupled kinetic shadowing theorem. -/
theorem cubicReferenceAndCoupling_ratios_tendsto_zero
    (g referenceDefectMax couplingDefectMax : Nat → Real)
    {T Cref Ccoupling : Real}
    (hT : 0 < T) (hCref : 0 ≤ Cref) (hCcoupling : 0 ≤ Ccoupling)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : ∀ᶠ n in atTop, g n ≠ 0)
    (href0 : ∀ n, 0 ≤ referenceDefectMax n)
    (hcoupling0 : ∀ n, 0 ≤ couplingDefectMax n)
    (hrefCubic : ∀ n,
      referenceDefectMax n ≤ Cref * |g n| ^ 3)
    (hcouplingCubic : ∀ n,
      couplingDefectMax n ≤ Ccoupling * |g n| ^ 3) :
    Tendsto
        (fun n ↦ referenceDefectMax n / (g n ^ 2 * T))
        atTop (nhds 0) ∧
      Tendsto
        (fun n ↦ couplingDefectMax n / (g n ^ 2 * T))
        atTop (nhds 0) := by
  exact ⟨
    cubicDefect_div_kineticStep_tendsto_zero
      g referenceDefectMax hT hCref hg hg0 href0 hrefCubic,
    cubicDefect_div_kineticStep_tendsto_zero
      g couplingDefectMax hT hCcoupling hg hg0
        hcoupling0 hcouplingCubic⟩

/-! ## Direct coupled kinetic-time closure -/

/-- Concrete weak-coupling closure for the coupled-restart family.

The abstract normalized-defect assumptions have disappeared.  The reference
and coupling envelopes only need uniform cubic bounds.  All other fields are
the transparent dynamical, Lipschitz, and kinetic-time inputs already used by
`actualSecondMoment_kineticEuler_shadowing_tendsto_zero`.

Only eventual nonvanishing of `g` is assumed.  We shift past its possible
finite zero prefix, apply the existing coupled closure there, and use
`tendsto_add_atTop_iff_nat` to return to the original sequence. -/
theorem actualSecondMoment_kineticEuler_shadowing_of_cubicDefects
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {M : Real} (hM : 0 ≤ M)
    (g : Nat → Real) {T : Real} (hT : 0 < T)
    (Q : Real → Real) (L : Real)
    (referenceDefectMax couplingDefectMax : Nat → Real)
    (family : CoupledSecondMomentKineticFamilyCertificate
      mu M (fun n ↦ g n ^ 2 * T) Q
        referenceDefectMax couplingDefectMax)
    (V : Nat → Nat → Real) (K : Nat → Nat) (tau : Real)
    (Cref Ccoupling : Real)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : ∀ᶠ n in atTop, g n ≠ 0)
    (hCref : 0 ≤ Cref) (hCcoupling : 0 ≤ Ccoupling)
    (hrefCubic : ∀ n,
      referenceDefectMax n ≤ Cref * |g n| ^ 3)
    (hcouplingCubic : ∀ n,
      couplingDefectMax n ≤ Ccoupling * |g n| ^ 3)
    (hL : 0 ≤ L)
    (hQ : ∀ x y, |Q x - Q y| ≤ L * |x - y|)
    (hkinetic : ∀ n,
      IsKineticEulerTrajectory (V n) (g n ^ 2 * T) Q)
    (hkineticBudget : ∀ n,
      (g n ^ 2 * T) * (K n : Real) ≤ tau)
    (hinitial : Tendsto
      (fun n ↦ |family.actualSecondMoment n 0 - V n 0|)
      atTop (nhds 0)) :
    Tendsto
      (fun n ↦
        |family.actualSecondMoment n (K n) - V n (K n)|)
      atTop (nhds 0) := by
  obtain ⟨N₀, hgN₀⟩ := (eventually_atTop.1 hg0)
  let shiftedFamily : CoupledSecondMomentKineticFamilyCertificate
      mu M (fun n ↦ g (n + N₀) ^ 2 * T) Q
        (fun n ↦ referenceDefectMax (n + N₀))
        (fun n ↦ couplingDefectMax (n + N₀)) :=
    { coupling := fun n ↦ family.coupling (n + N₀)
      referenceDefect := fun n j ↦ family.referenceDefect (n + N₀) j
      reference_residual := fun n j ↦
        family.reference_residual (n + N₀) j
      reference_defect_le := fun n j ↦
        family.reference_defect_le (n + N₀) j
      coupling_endpoint_defect_le := fun n j ↦
        family.coupling_endpoint_defect_le (n + N₀) j }
  have hgShift : Tendsto (fun n ↦ g (n + N₀)) atTop (nhds 0) :=
    hg.comp (tendsto_add_atTop_nat N₀)
  have hstepShift : ∀ n, 0 < g (n + N₀) ^ 2 * T := by
    intro n
    exact mul_pos (sq_pos_of_ne_zero (hgN₀ (n + N₀) (by omega))) hT
  have hstepShift0 : Tendsto (fun n ↦ g (n + N₀) ^ 2 * T)
      atTop (nhds 0) := by
    simpa using (hgShift.pow 2).mul_const T
  have href0 : ∀ n, 0 ≤ referenceDefectMax n :=
    family.referenceDefectMax_nonneg
  have hcoupling0 : ∀ n, 0 ≤ couplingDefectMax n :=
    family.couplingDefectMax_nonneg hM
  obtain ⟨hrefRatio, hcouplingRatio⟩ :=
    cubicReferenceAndCoupling_ratios_tendsto_zero
      g referenceDefectMax couplingDefectMax hT hCref hCcoupling
        hg hg0 href0 hcoupling0 hrefCubic hcouplingCubic
  have hrefRatioShift : Tendsto
      (fun n ↦ referenceDefectMax (n + N₀) /
        (g (n + N₀) ^ 2 * T)) atTop (nhds 0) :=
    hrefRatio.comp (tendsto_add_atTop_nat N₀)
  have hcouplingRatioShift : Tendsto
      (fun n ↦ couplingDefectMax (n + N₀) /
        (g (n + N₀) ^ 2 * T)) atTop (nhds 0) :=
    hcouplingRatio.comp (tendsto_add_atTop_nat N₀)
  have hinitialShift : Tendsto
      (fun n ↦
        |family.actualSecondMoment (n + N₀) 0 - V (n + N₀) 0|)
      atTop (nhds 0) :=
    hinitial.comp (tendsto_add_atTop_nat N₀)
  have hshifted :=
    shiftedFamily.actualSecondMoment_kineticEuler_shadowing_tendsto_zero
      mu hM (fun n ↦ g (n + N₀) ^ 2 * T) Q L
      (fun n ↦ referenceDefectMax (n + N₀))
      (fun n ↦ couplingDefectMax (n + N₀))
      (fun n j ↦ V (n + N₀) j) (fun n ↦ K (n + N₀)) tau
      hstepShift hstepShift0 hL hQ
      (fun n ↦ hkinetic (n + N₀))
      (fun n ↦ hkineticBudget (n + N₀))
      (by simpa [shiftedFamily,
          CoupledSecondMomentKineticFamilyCertificate.actualSecondMoment]
        using hinitialShift)
      hrefRatioShift hcouplingRatioShift
  have hshifted' : Tendsto
      (fun n ↦
        |family.actualSecondMoment (n + N₀) (K (n + N₀)) -
          V (n + N₀) (K (n + N₀))|)
      atTop (nhds 0) := by
    simpa [shiftedFamily,
      CoupledSecondMomentKineticFamilyCertificate.actualSecondMoment]
      using hshifted
  exact (tendsto_add_atTop_iff_nat N₀).mp hshifted'

/-! ## Why a quadratic estimate is insufficient -/

/-- The kinetic step divided by itself is eventually one when `g` is
eventually nonzero. -/
theorem kineticStep_self_ratio_eventually_eq_one
    (g : Nat → Real) {T : Real} (hT : 0 < T)
    (hg0 : ∀ᶠ n in atTop, g n ≠ 0) :
    ∀ᶠ n in atTop, (g n ^ 2 * T) / (g n ^ 2 * T) = 1 := by
  filter_upwards [hg0] with n hgn
  exact div_self (mul_ne_zero (pow_ne_zero 2 hgn) hT.ne')

/-- Formal scale counterexample: `defect_n = g_n^2 T` is nonnegative and
bounded by one times the kinetic step, but its normalized ratio does not tend
to zero.  Hence `O(g^2 T)` alone is not a sufficient kinetic-time input. -/
theorem quadraticKineticStep_bound_not_sufficient
    (g : Nat → Real) {T : Real} (hT : 0 < T)
    (hg0 : ∀ᶠ n in atTop, g n ≠ 0) :
    (∀ n, 0 ≤ g n ^ 2 * T) ∧
      (∀ n, g n ^ 2 * T ≤ 1 * (g n ^ 2 * T)) ∧
      ¬ Tendsto (fun n ↦ (g n ^ 2 * T) / (g n ^ 2 * T))
        atTop (nhds 0) := by
  refine ⟨fun n ↦ mul_nonneg (sq_nonneg _) hT.le,
    fun n ↦ by simp, ?_⟩
  intro hzero
  have hone : Tendsto
      (fun n ↦ (g n ^ 2 * T) / (g n ^ 2 * T))
      atTop (nhds 1) := by
    exact (tendsto_congr' (kineticStep_self_ratio_eventually_eq_one
      g hT hg0)).mpr tendsto_const_nhds
  have : (1 : Real) = 0 := tendsto_nhds_unique hone hzero
  norm_num at this

end

end ArchonPhysics.PhyslibFPUTCubicDefectKineticShadowing
