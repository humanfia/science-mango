import ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging
import ArchonPhysics.FrozenAndersonOneSitePoissonAveraging
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Frozen-mass one-site fractional moments

This module proves the first analytic fractional-moment estimate for the actual
frozen uniform mass law.  The estimate is uniform in the affine center, has an
explicit constant, and is then exposed as the scalar one-step Schur/Green
contraction factor.  No localization or model EFC conclusion is assumed here.
-/

namespace ArchonPhysics.FrozenMassOneSiteFractionalMoment

open ArchonPhysics
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.FrozenAndersonDiagonalPotentialDensity
open ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging
open ArchonPhysics.FrozenAndersonOneSitePoissonAveraging
open MeasureTheory
open Set
open scoped ENNReal

noncomputable section

/-- The integrable singular part used to dominate every translate of
`x ↦ |x|⁻ˢ`: it is truncated to the unit interval. -/
def unitFractionalSingularKernel (s x : Real) : Real :=
  Set.Icc (-1 : Real) 1 |>.indicator (fun y => |y| ^ (-s)) x

theorem unitFractionalSingularKernel_nonneg (s x : Real) :
    0 ≤ unitFractionalSingularKernel s x := by
  simp only [unitFractionalSingularKernel]
  exact Set.indicator_nonneg (fun y _ => Real.rpow_nonneg (abs_nonneg y) _) x

private theorem intervalIntegrable_abs_rpow_neg
    {s : Real} (hs : s < 1) :
    IntervalIntegrable (fun x : Real => |x| ^ (-s)) volume (-1) 1 := by
  have hpow : -1 < -s := by linarith
  have hpos0 :
      IntervalIntegrable (fun x : Real => x ^ (-s)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' hpow
  have hpos :
      IntervalIntegrable (fun x : Real => |x| ^ (-s)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hpos0 ⊢
    refine hpos0.congr_fun ?_ measurableSet_Ioc
    intro x hx
    change x ^ (-s) = |x| ^ (-s)
    rw [abs_of_pos hx.1]
  have hneg :
      IntervalIntegrable (fun x : Real => |x| ^ (-s)) volume (-1) 0 := by
    rw [IntervalIntegrable.iff_comp_neg]
    simpa only [neg_neg, neg_zero, abs_neg] using hpos.symm
  exact hneg.trans hpos

theorem integral_unitFractionalSingularKernel
    {s : Real} (hs : s < 1) :
    ∫ x : Real, unitFractionalSingularKernel s x =
      2 / (1 - s) := by
  have hpow : -1 < -s := by linarith
  have hpos :
      ∫ x in (0 : Real)..1, |x| ^ (-s) = 1 / (1 - s) := by
    calc
      ∫ x in (0 : Real)..1, |x| ^ (-s) =
          ∫ x in (0 : Real)..1, x ^ (-s) := by
            apply intervalIntegral.integral_congr
            intro x hx
            change |x| ^ (-s) = x ^ (-s)
            rw [Set.uIcc_of_le (by norm_num)] at hx
            rw [abs_of_nonneg hx.1]
      _ = (1 ^ (-s + 1) - 0 ^ (-s + 1)) / (-s + 1) :=
        integral_rpow (Or.inl hpow)
      _ = 1 / (1 - s) := by
        have hne : -s + 1 ≠ 0 := by linarith
        simp [hne]
        ring
  have hneg :
      ∫ x in (-1 : Real)..0, |x| ^ (-s) = 1 / (1 - s) := by
    calc
      ∫ x in (-1 : Real)..0, |x| ^ (-s) =
          ∫ x in (0 : Real)..1, |-x| ^ (-s) := by
            simpa only [neg_neg, neg_zero] using
              (intervalIntegral.integral_comp_neg
                (a := (0 : Real)) (b := 1)
                (f := fun x : Real => |x| ^ (-s))).symm
      _ = ∫ x in (0 : Real)..1, |x| ^ (-s) := by
        apply intervalIntegral.integral_congr
        intro x _
        change |-x| ^ (-s) = |x| ^ (-s)
        rw [abs_neg]
      _ = 1 / (1 - s) := hpos
  have hinterval :
      ∫ x in (-1 : Real)..1, |x| ^ (-s) = 2 / (1 - s) := by
    have hintNeg :
        IntervalIntegrable (fun x : Real => |x| ^ (-s)) volume (-1) 0 :=
      (intervalIntegrable_abs_rpow_neg hs).mono_set (by
        grind [Set.uIcc])
    have hintPos :
        IntervalIntegrable (fun x : Real => |x| ^ (-s)) volume 0 1 :=
      (intervalIntegrable_abs_rpow_neg hs).mono_set (by
        grind [Set.uIcc])
    rw [← intervalIntegral.integral_add_adjacent_intervals hintNeg hintPos]
    rw [hneg, hpos]
    ring
  change (∫ x : Real, (Set.Icc (-1 : Real) 1).indicator
    (fun y => |y| ^ (-s)) x) = 2 / (1 - s)
  rw [integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  exact hinterval

theorem integrable_unitFractionalSingularKernel
    {s : Real} (hs : s < 1) :
    Integrable (unitFractionalSingularKernel s) volume := by
  apply IntegrableOn.integrable_indicator
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
      (intervalIntegrable_abs_rpow_neg hs)
  · exact measurableSet_Icc

/-- Every affine singularity is bounded by one plus its unit-window singular
part.  This elementary split is what makes the density estimate uniform in
the affine center. -/
theorem fractionalSingularPower_le_one_add_kernel
    {s : Real} (hs : 0 ≤ s) (c x : Real) :
    |c + x| ^ (-s) ≤
      1 + unitFractionalSingularKernel s (c + x) := by
  by_cases hsmall : |c + x| ≤ 1
  · have hmem : c + x ∈ Set.Icc (-1 : Real) 1 := by
      exact (abs_le.mp hsmall)
    rw [unitFractionalSingularKernel, Set.indicator_of_mem hmem]
    exact le_add_of_nonneg_left (by norm_num)
  · have hlarge : 1 ≤ |c + x| := le_of_lt (lt_of_not_ge hsmall)
    have hnotmem : c + x ∉ Set.Icc (-1 : Real) 1 := by
      intro hmem
      exact hsmall (abs_le.mpr hmem)
    rw [unitFractionalSingularKernel, Set.indicator_of_notMem hnotmem, add_zero]
    exact Real.rpow_le_one_of_one_le_of_nonpos hlarge (neg_nonpos.mpr hs)

/-- Translation does not change integrability of the truncated singular
kernel. -/
theorem integrable_translatedUnitFractionalSingularKernel
    {s : Real} (hs : s < 1) (c : Real) :
    Integrable (fun x : Real =>
      unitFractionalSingularKernel s (c + x)) volume := by
  have hcomp :=
    (measurePreserving_add_right volume c).integrable_comp_of_integrable
      (integrable_unitFractionalSingularKernel hs)
  simpa only [Function.comp_def, add_comm] using hcomp

/-- Translation does not change the explicit value of the truncated singular
integral. -/
theorem integral_translatedUnitFractionalSingularKernel
    {s : Real} (hs : s < 1) (c : Real) :
    ∫ x : Real, unitFractionalSingularKernel s (c + x) =
      2 / (1 - s) := by
  calc
    ∫ x : Real, unitFractionalSingularKernel s (c + x) =
        ∫ x : Real, unitFractionalSingularKernel s x := by
          simpa only [add_comm] using
            (integral_add_right_eq_self
              (unitFractionalSingularKernel s) c)
    _ = 2 / (1 - s) := integral_unitFractionalSingularKernel hs

/-- The translated truncated kernel remains integrable for the actual frozen
mass law, solely by its sharp density ceiling. -/
theorem integrable_translatedUnitFractionalSingularKernel_massCoordinateLaw
    {s : Real} (hs : s < 1) (c : Real) :
    Integrable (fun x : Real =>
      unitFractionalSingularKernel s (c + x)) massCoordinateLaw := by
  apply Integrable.mono_measure
    ((integrable_translatedUnitFractionalSingularKernel hs c).smul_measure
      (by finiteness : (5 / 2 : ENNReal) ≠ ∞))
  exact massCoordinateLaw_le_fiveHalves_smul_volume

/-- Sharp-density consequence: the singular unit window costs at most
`5 / (1-s)`, uniformly in its center. -/
theorem integral_translatedUnitFractionalSingularKernel_massCoordinateLaw_le
    {s : Real} (hs : s < 1) (c : Real) :
    (∫ x : Real, unitFractionalSingularKernel s (c + x)
        ∂massCoordinateLaw) ≤ 5 / (1 - s) := by
  have hsmul :
      Integrable (fun x : Real =>
        unitFractionalSingularKernel s (c + x))
        ((5 / 2 : ENNReal) • (volume : Measure Real)) :=
    (integrable_translatedUnitFractionalSingularKernel hs c).smul_measure
      (by finiteness)
  calc
    (∫ x : Real, unitFractionalSingularKernel s (c + x)
        ∂massCoordinateLaw) ≤
        ∫ x : Real, unitFractionalSingularKernel s (c + x)
          ∂((5 / 2 : ENNReal) • (volume : Measure Real)) :=
      integral_mono_measure
        massCoordinateLaw_le_fiveHalves_smul_volume
        (Filter.Eventually.of_forall fun x =>
          unitFractionalSingularKernel_nonneg s (c + x))
        hsmul
    _ = (5 / 2 : ENNReal).toReal *
        (∫ x : Real, unitFractionalSingularKernel s (c + x)) := by
      rw [integral_smul_measure]
      rfl
    _ = 5 / (1 - s) := by
      rw [integral_translatedUnitFractionalSingularKernel hs c]
      have hne : 1 - s ≠ 0 := by linarith
      norm_num
      field_simp [hne]
/-! ## Actual frozen one-site fractional moment -/

/-- Borel measurability of the negative real power, including its totalized
value at the affine zero. -/
theorem measurable_fractionalSingularPower (s c : Real) :
    Measurable (fun mass : Real => |c + mass| ^ (-s)) := by
  let g : Real → Real := fun mass =>
    if |c + mass| = 0 then (0 : Real) ^ (-s)
    else Real.exp (Real.log |c + mass| * (-s))
  have habs : Measurable (fun mass : Real => |c + mass|) := by
    fun_prop
  have hlog : Measurable
      (fun mass : Real => Real.log |c + mass|) :=
    Real.measurable_log.comp habs
  have hlogMul : Measurable
      (fun mass : Real => Real.log |c + mass| * (-s)) :=
    hlog.mul (measurable_const : Measurable (fun _ : Real => (-s)))
  have hg : Measurable g := by
    unfold g
    exact Measurable.ite
      (habs (measurableSet_singleton (0 : Real)))
      measurable_const
      (Real.measurable_exp.comp hlogMul)
  have heq :
      (fun mass : Real => |c + mass| ^ (-s)) = g := by
    funext mass
    by_cases hz : |c + mass| = 0
    · simp only [g, hz, if_pos]
    · simp only [g, hz]
      exact Real.rpow_def_of_pos
        (lt_of_le_of_ne (abs_nonneg (c + mass)) (Ne.symm hz)) (-s)
  rw [heq]
  exact hg
/-- The affine singular power is integrable under the frozen mass law.
The only probabilistic input is the one-site `Uniform[4/5,6/5]` law; this
statement does not perform an iid conditional reconstruction in a chain. -/
theorem integrable_fractionalSingularPower_massCoordinateLaw
    {s : Real} (hs0 : 0 ≤ s) (hs1 : s < 1) (c : Real) :
    Integrable (fun mass : Real => |c + mass| ^ (-s))
      massCoordinateLaw := by
  have hone : Integrable (fun _ : Real => (1 : Real))
      massCoordinateLaw := by simp
  have hkernel :=
    integrable_translatedUnitFractionalSingularKernel_massCoordinateLaw hs1 c
  have hupper := hone.add hkernel
  apply hupper.mono_nonneg
  · exact (measurable_fractionalSingularPower s c).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun mass =>
      Real.rpow_nonneg (abs_nonneg (c + mass)) _
  · exact Filter.Eventually.of_forall fun mass =>
      fractionalSingularPower_le_one_add_kernel hs0 c mass

/-- Uniform one-site fractional-moment bound for the actual frozen mass law:
for `0 ≤ s < 1`, every affine center costs at most
`1 + 5/(1-s)`.  The constant is dimension-free because the theorem concerns
one conditional site law, not because spatial contraction has been proved. -/
theorem integral_fractionalSingularPower_massCoordinateLaw_le
    {s : Real} (hs0 : 0 ≤ s) (hs1 : s < 1) (c : Real) :
    (∫ mass : Real, |c + mass| ^ (-s) ∂massCoordinateLaw) ≤
      1 + 5 / (1 - s) := by
  have htarget :=
    integrable_fractionalSingularPower_massCoordinateLaw hs0 hs1 c
  have hone : Integrable (fun _ : Real => (1 : Real))
      massCoordinateLaw := by simp
  have hkernel :=
    integrable_translatedUnitFractionalSingularKernel_massCoordinateLaw hs1 c
  have hupper := hone.add hkernel
  calc
    (∫ mass : Real, |c + mass| ^ (-s) ∂massCoordinateLaw) ≤
        ∫ mass : Real,
          (1 + unitFractionalSingularKernel s (c + mass))
            ∂massCoordinateLaw :=
      integral_mono_ae htarget hupper
        (Filter.Eventually.of_forall fun mass =>
          fractionalSingularPower_le_one_add_kernel hs0 c mass)
    _ = 1 + (∫ mass : Real,
        unitFractionalSingularKernel s (c + mass)
          ∂massCoordinateLaw) := by
      rw [integral_add hone hkernel]
      simp
    _ ≤ 1 + 5 / (1 - s) :=
      by
        simpa only [add_comm] using
          add_le_add_left
            (integral_translatedUnitFractionalSingularKernel_massCoordinateLaw_le hs1 c) 1

private theorem affine_scale_fractionalSingularPower
    {s a lambda mass : Real} (hlambda : lambda ≠ 0) :
    |a + lambda * mass| ^ (-s) =
      |lambda| ^ (-s) * |a / lambda + mass| ^ (-s) := by
  have hfactor :
      a + lambda * mass = lambda * (a / lambda + mass) := by
    field_simp [hlambda]
  rw [hfactor, abs_mul, Real.mul_rpow (abs_nonneg lambda)
    (abs_nonneg (a / lambda + mass))]

/-- Integrability companion to the affine scaling estimate. -/
theorem integrable_affine_fractionalSingularPower_massCoordinateLaw
    {s a lambda : Real} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hlambda : lambda ≠ 0) :
    Integrable (fun mass : Real => |a + lambda * mass| ^ (-s))
      massCoordinateLaw := by
  have hbase :=
    integrable_fractionalSingularPower_massCoordinateLaw
      hs0 hs1 (a / lambda)
  have hmul := hbase.const_mul (|lambda| ^ (-s))
  exact hmul.congr (Filter.Eventually.of_forall fun mass =>
    (affine_scale_fractionalSingularPower hlambda).symm)
/-- The requested actual affine one-site spectral average.  For
`0 ≤ s < 1` and `lambda ≠ 0`, it is uniform in `a` and scales explicitly
as `|lambda|⁻ˢ`. -/
theorem integral_affine_fractionalSingularPower_massCoordinateLaw_le
    {s a lambda : Real} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hlambda : lambda ≠ 0) :
    (∫ mass : Real, |a + lambda * mass| ^ (-s)
        ∂massCoordinateLaw) ≤
      (1 + 5 / (1 - s)) * |lambda| ^ (-s) := by
  calc
    (∫ mass : Real, |a + lambda * mass| ^ (-s)
        ∂massCoordinateLaw) =
        ∫ mass : Real,
          |lambda| ^ (-s) * |a / lambda + mass| ^ (-s)
            ∂massCoordinateLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun mass =>
        affine_scale_fractionalSingularPower hlambda
    _ = |lambda| ^ (-s) *
        (∫ mass : Real, |a / lambda + mass| ^ (-s)
          ∂massCoordinateLaw) := by
      rw [integral_const_mul]
    _ ≤ |lambda| ^ (-s) * (1 + 5 / (1 - s)) :=
      mul_le_mul_of_nonneg_left
        (integral_fractionalSingularPower_massCoordinateLaw_le
          hs0 hs1 (a / lambda))
        (Real.rpow_nonneg (abs_nonneg lambda) _)
    _ = (1 + 5 / (1 - s)) * |lambda| ^ (-s) := by
      rw [mul_comm]

/-! ## Honest scalar one-site Schur step -/

/-- Scalar Green denominator for one Schur-complement step. -/
def scalarOneSiteSchurGreen (a lambda mass : Real) : Real :=
  (a + lambda * mass)⁻¹

/-- A scalar one-step transfer: `tail` is the environment-dependent quantity
held fixed while averaging the fresh site mass.  This is not a claim that a
finite chain has already been conditionally disintegrated. -/
def scalarOneSiteSchurTransfer
    (a lambda hop tail mass : Real) : Real :=
  hop * tail * scalarOneSiteSchurGreen a lambda mass

theorem abs_scalarOneSiteSchurGreen_rpow
    (s a lambda mass : Real) :
    |scalarOneSiteSchurGreen a lambda mass| ^ s =
      |a + lambda * mass| ^ (-s) := by
  rw [scalarOneSiteSchurGreen, abs_inv,
    Real.inv_rpow (abs_nonneg (a + lambda * mass)),
    Real.rpow_neg (abs_nonneg (a + lambda * mass))]

/-- The exact one-site Schur transfer inherits the frozen affine
fractional-moment bound. -/
theorem integral_scalarOneSiteSchurTransfer_rpow_le
    {s a lambda hop tail : Real}
    (hs0 : 0 ≤ s) (hs1 : s < 1) (hlambda : lambda ≠ 0) :
    (∫ mass : Real,
        |scalarOneSiteSchurTransfer a lambda hop tail mass| ^ s
          ∂massCoordinateLaw) ≤
      ((1 + 5 / (1 - s)) * |lambda| ^ (-s) * |hop| ^ s) *
        |tail| ^ s := by
  have hpointwise (mass : Real) :
      |scalarOneSiteSchurTransfer a lambda hop tail mass| ^ s =
        (|hop| ^ s * |tail| ^ s) *
          |a + lambda * mass| ^ (-s) := by
    rw [scalarOneSiteSchurTransfer, abs_mul, abs_mul,
      Real.mul_rpow (mul_nonneg (abs_nonneg hop) (abs_nonneg tail))
        (abs_nonneg (scalarOneSiteSchurGreen a lambda mass)),
      Real.mul_rpow (abs_nonneg hop) (abs_nonneg tail),
      abs_scalarOneSiteSchurGreen_rpow]
  calc
    (∫ mass : Real,
        |scalarOneSiteSchurTransfer a lambda hop tail mass| ^ s
          ∂massCoordinateLaw) =
        (|hop| ^ s * |tail| ^ s) *
          (∫ mass : Real, |a + lambda * mass| ^ (-s)
            ∂massCoordinateLaw) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpointwise
    _ ≤ (|hop| ^ s * |tail| ^ s) *
        ((1 + 5 / (1 - s)) * |lambda| ^ (-s)) :=
      mul_le_mul_of_nonneg_left
        (integral_affine_fractionalSingularPower_massCoordinateLaw_le
          hs0 hs1 hlambda)
        (mul_nonneg (Real.rpow_nonneg (abs_nonneg hop) _)
          (Real.rpow_nonneg (abs_nonneg tail) _))
    _ = ((1 + 5 / (1 - s)) * |lambda| ^ (-s) * |hop| ^ s) *
        |tail| ^ s := by ring

/-- The explicit one-site factor.  Spatial iteration requires a separate iid
conditional/fresh-site theorem; no such premise is hidden in this definition. -/
def scalarOneSiteFractionalMomentFactor
    (s lambda hop : Real) : Real :=
  (1 + 5 / (1 - s)) * |lambda| ^ (-s) * |hop| ^ s

/-- If the displayed large-disorder/weak-hop inequality makes the one-site
factor less than one, every nonzero fixed tail is strictly contracted in this
single conditional average.  A hard energy band alone does not discharge
`hq`. -/
theorem integral_scalarOneSiteSchurTransfer_rpow_lt_tail
    {s a lambda hop tail : Real}
    (hs0 : 0 < s) (hs1 : s < 1) (hlambda : lambda ≠ 0)
    (htail : tail ≠ 0)
    (hq : scalarOneSiteFractionalMomentFactor s lambda hop < 1) :
    (∫ mass : Real,
        |scalarOneSiteSchurTransfer a lambda hop tail mass| ^ s
          ∂massCoordinateLaw) < |tail| ^ s := by
  have hbound :=
    integral_scalarOneSiteSchurTransfer_rpow_le
      hs0.le hs1 hlambda (a := a) (hop := hop) (tail := tail)
  have htailPos : 0 < |tail| ^ s :=
    Real.rpow_pos_of_pos (abs_pos.mpr htail) s
  change (∫ mass : Real,
      |scalarOneSiteSchurTransfer a lambda hop tail mass| ^ s
        ∂massCoordinateLaw) <
    |tail| ^ s
  change scalarOneSiteFractionalMomentFactor s lambda hop < 1 at hq
  change (∫ mass : Real,
      |scalarOneSiteSchurTransfer a lambda hop tail mass| ^ s
        ∂massCoordinateLaw) ≤
    scalarOneSiteFractionalMomentFactor s lambda hop * |tail| ^ s at hbound
  nlinarith
/-! ## Actual finite-volume local Green function -/

/-- The sharp density ceiling implies that the frozen one-site mass law has
no atoms.  This is used only to discard the one affine real zero in the
complex Green comparison. -/
noncomputable instance frozenMassCoordinateLawNullSingletonClass :
    NullSingletonClass massCoordinateLaw where
  measure_singleton x := by
    have hsingle := Measure.le_iff.mp
      massCoordinateLaw_le_fiveHalves_smul_volume
      ({x} : Set Real) (measurableSet_singleton x)
    simpa [Measure.smul_apply] using hsingle

/-- Finite-volume one-site Green fractional moment.  The environment
`background` is fixed (quenched), the mass average is only the fresh frozen
`Uniform[4/5,6/5]` site, `z` stays in the upper half-plane, and the bound is
uniform in the finite index type.  Iterating this estimate along an iid chain
still requires a separate conditional-product reconstruction. -/
theorem integral_norm_finiteFrozenOneSiteGreen_rpow_le
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real)
    (hbackground : background.IsHermitian)
    (i : index) (z : Complex) (hz : 0 < z.im)
    (reference : Real)
    {s lambda : Real} (hs0 : 0 < s) (hs1 : s < 1)
    (hlambda : lambda ≠ 0) :
    (∫ mass : Real,
        ‖finiteFrozenOneSiteGreen background i z lambda mass‖ ^ s
          ∂massCoordinateLaw) ≤
      (1 + 5 / (1 - s)) * |lambda| ^ (-s) := by
  let alpha :=
    oneSiteEffectiveHerglotzParameter background i z reference
  have hgreen (mass : Real) :
      finiteFrozenOneSiteGreen background i z lambda mass =
        (alpha - ((lambda * mass : Real) : Complex))⁻¹ := by
    unfold finiteFrozenOneSiteGreen
    rw [finiteHermitianOneSiteGreen_eq_inv_sub
      background hbackground i z hz reference]
    rfl
  have hright :
      Integrable (fun mass : Real =>
        |alpha.re - lambda * mass| ^ (-s)) massCoordinateLaw := by
    simpa only [sub_eq_add_neg, neg_mul] using
      (integrable_affine_fractionalSingularPower_massCoordinateLaw
        hs0.le hs1 (neg_ne_zero.mpr hlambda)
        (a := alpha.re) (lambda := -lambda))
  have hgreenMeas :
      AEStronglyMeasurable
        (fun mass : Real =>
          ‖finiteFrozenOneSiteGreen background i z lambda mass‖ ^ s)
        massCoordinateLaw := by
    have hdenom : Measurable
        (fun mass : Real =>
          alpha - ((lambda * mass : Real) : Complex)) := by
      fun_prop
    have hexplicit : Measurable
        (fun mass : Real =>
          ‖(alpha - ((lambda * mass : Real) : Complex))⁻¹‖ ^ s) :=
      hdenom.inv.norm.pow_const s
    exact hexplicit.aestronglyMeasurable.congr
      (Filter.Eventually.of_forall fun mass =>
        (congrArg (fun q : Complex => ‖q‖ ^ s) (hgreen mass)).symm)
  have hpointwise :
      ∀ᵐ mass ∂massCoordinateLaw,
        ‖finiteFrozenOneSiteGreen background i z lambda mass‖ ^ s ≤
          |alpha.re - lambda * mass| ^ (-s) := by
    filter_upwards [massCoordinateLaw.ae_ne (alpha.re / lambda)]
      with mass hmass
    have hrealne : alpha.re - lambda * mass ≠ 0 := by
      intro hzero
      apply hmass
      apply (eq_div_iff hlambda).2
      calc
        mass * lambda = lambda * mass := mul_comm _ _
        _ = alpha.re := by linarith
    have hrealpos : 0 < |alpha.re - lambda * mass| :=
      abs_pos.mpr hrealne
    have hnorm :
        |alpha.re - lambda * mass| ≤
          ‖alpha - ((lambda * mass : Real) : Complex)‖ := by
      simpa using
        (Complex.abs_re_le_norm
          (alpha - ((lambda * mass : Real) : Complex)))
    rw [hgreen mass, norm_inv,
      Real.inv_rpow
        (norm_nonneg (alpha - ((lambda * mass : Real) : Complex))),
      ← Real.rpow_neg
        (norm_nonneg (alpha - ((lambda * mass : Real) : Complex)))]
    exact Real.rpow_le_rpow_of_nonpos
      hrealpos hnorm (neg_nonpos.mpr hs0.le)
  have hgreenInt :
      Integrable
        (fun mass : Real =>
          ‖finiteFrozenOneSiteGreen background i z lambda mass‖ ^ s)
        massCoordinateLaw :=
    hright.mono_nonneg hgreenMeas
      (Filter.Eventually.of_forall fun mass =>
        Real.rpow_nonneg
          (norm_nonneg
            (finiteFrozenOneSiteGreen background i z lambda mass)) _)
      hpointwise
  calc
    (∫ mass : Real,
        ‖finiteFrozenOneSiteGreen background i z lambda mass‖ ^ s
          ∂massCoordinateLaw) ≤
        ∫ mass : Real, |alpha.re - lambda * mass| ^ (-s)
          ∂massCoordinateLaw :=
      integral_mono_ae hgreenInt hright hpointwise
    _ ≤ (1 + 5 / (1 - s)) * |lambda| ^ (-s) := by
      simpa only [sub_eq_add_neg, neg_mul, abs_neg] using
        (integral_affine_fractionalSingularPower_massCoordinateLaw_le
          hs0.le hs1 (neg_ne_zero.mpr hlambda)
          (a := alpha.re) (lambda := -lambda))
end

end ArchonPhysics.FrozenMassOneSiteFractionalMoment
