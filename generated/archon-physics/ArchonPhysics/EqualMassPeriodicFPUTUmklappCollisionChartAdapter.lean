import ArchonPhysics.EqualMassPeriodicFPUTUmklappFiniteAtlas
import ArchonPhysics.EqualMassPeriodicFPUTUmklappCollisionDensity

/-!
# Adapter from the explicit Umklapp atlas to collision charts

The finite atlas and the two arcsine roots determine the local interval,
positive derivative, strict monotonicity, and unique resonant root.  The only
data left to construct a `PositiveUmklappCollisionChart` are the density and
mark change-of-variables assumptions: continuity, integrability, support,
and factorization.

No kinetic equation or statistical closure is assumed.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTUmklappCollisionChartAdapter

open Set
open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTUmklappCollisionDensity
open ArchonPhysics.EqualMassPeriodicFPUTUmklappFiniteAtlas
open ArchonPhysics.EqualMassPeriodicFPUTUmklappOnShellJacobian
open ArchonPhysics.EqualMassPeriodicFPUTUmklappTransversality
open ArchonPhysics.NormalizedResonancePeakKernel
open Filter MeasureTheory Topology

noncomputable section

/-! ## Deterministic branch and interval selection -/

/-- The principal arcsine root lies in the central patch.  The outer root
lies in the upper or lower patch according to the sign of the resonance
ratio. -/
def umklappArcsineAtlasBranch
    (rootBranch : UmklappArcsineBranch) (k₀ k₁ : Real) :
    UmklappAtlasBranch :=
  match rootBranch with
  | .principal => .central
  | .outer =>
      if 0 ≤ umklappResonanceRatio k₀ k₁ then .upper else .lower

def umklappArcsineLocalLeft
    (rootBranch : UmklappArcsineBranch) (k₀ k₁ : Real) : Real :=
  umklappAtlasLocalLeft (umklappArcsineAtlasBranch rootBranch k₀ k₁)
    k₀ k₁ (umklappArcsineRoot rootBranch k₀ k₁)

def umklappArcsineLocalRight
    (rootBranch : UmklappArcsineBranch) (k₀ k₁ : Real) : Real :=
  umklappAtlasLocalRight (umklappArcsineAtlasBranch rootBranch k₀ k₁)
    k₀ k₁ (umklappArcsineRoot rootBranch k₀ k₁)

/-- Explicit orientation condition selecting precisely the arcsine branch
whose physical `k₂` derivative is positive. -/
def UmklappArcsinePositiveOrientation
    (rootBranch : UmklappArcsineBranch) (k₀ k₁ : Real) : Prop :=
  match rootBranch with
  | .principal => umklappResonanceDenominator k₀ k₁ < 0
  | .outer => 0 < umklappResonanceDenominator k₀ k₁

/-- Canonical positively oriented arcsine branch: outer when the structural
cosine is positive and principal when it is negative. -/
def umklappPositiveArcsineBranch (k₀ k₁ : Real) : UmklappArcsineBranch :=
  if 0 < umklappResonanceDenominator k₀ k₁ then .outer else .principal

theorem umklappPositiveArcsineBranch_orientation
    {k₀ k₁ : Real}
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁) :
    UmklappArcsinePositiveOrientation
      (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁ := by
  have hne :=
    umklappResonanceDenominator_ne_zero_of_discriminant_pos hdisc
  by_cases hpositive : 0 < umklappResonanceDenominator k₀ k₁
  · simp [umklappPositiveArcsineBranch, hpositive,
      UmklappArcsinePositiveOrientation]
  · have hnegative : umklappResonanceDenominator k₀ k₁ < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpositive) hne
    simp [umklappPositiveArcsineBranch, hpositive,
      UmklappArcsinePositiveOrientation, hnegative]

theorem umklappArcsineRoot_mem_selectedAtlasPatch
    {rootBranch : UmklappArcsineBranch} {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁)
    (hroot0 : 0 < umklappArcsineRoot rootBranch k₀ k₁)
    (hroot2pi : umklappArcsineRoot rootBranch k₀ k₁ < 2 * Real.pi) :
    umklappArcsineRoot rootBranch k₀ k₁ ∈
      umklappAtlasPatch (umklappArcsineAtlasBranch rootBranch k₀ k₁)
        k₀ k₁ := by
  have hratio := umklappResonanceRatio_mem_Ioo hdisc
  have hangle := umklappMovingAngle_mem_Ioo_neg_pi_pi
    hk₀0 hk₀2pi hk₁0 hk₁2pi hroot0 hroot2pi
  have hangleEq :
      umklappMovingAngle k₀ k₁
          (umklappArcsineRoot rootBranch k₀ k₁) =
        umklappArcsineAngle rootBranch
          (umklappResonanceRatio k₀ k₁) := by
    exact umklappMovingAngle_rootFromAngle _ _ _
  cases rootBranch
  · rw [umklappAtlasPatch_angle]
    simp only [umklappArcsineAtlasBranch]
    rw [hangleEq]
    change Real.arcsin (umklappResonanceRatio k₀ k₁) ∈
      Ioo (-(Real.pi / 2)) (Real.pi / 2)
    exact ⟨Real.neg_pi_div_two_lt_arcsin.mpr hratio.1,
      Real.arcsin_lt_pi_div_two.mpr hratio.2⟩
  · by_cases hnonnegative : 0 ≤ umklappResonanceRatio k₀ k₁
    · have hpositive : 0 < umklappResonanceRatio k₀ k₁ := by
        by_contra hnotPositive
        have hzero : umklappResonanceRatio k₀ k₁ = 0 := by
          linarith
        have hanglePi :
            umklappMovingAngle k₀ k₁
                (umklappArcsineRoot .outer k₀ k₁) = Real.pi := by
          rw [hangleEq]
          simp [umklappArcsineAngle, hzero]
        linarith [hangle.2]
      rw [umklappAtlasPatch_angle]
      simp only [umklappArcsineAtlasBranch, if_pos hnonnegative]
      rw [hangleEq]
      simp only [umklappArcsineAngle, if_pos hnonnegative]
      constructor
      · have := Real.arcsin_lt_pi_div_two.mpr hratio.2
        linarith
      · have := Real.arcsin_pos.mpr hpositive
        linarith
    · have hnegative : umklappResonanceRatio k₀ k₁ < 0 :=
        lt_of_not_ge hnonnegative
      rw [umklappAtlasPatch_angle]
      simp only [umklappArcsineAtlasBranch, if_neg hnonnegative]
      rw [hangleEq]
      simp only [umklappArcsineAngle, if_neg hnonnegative]
      constructor
      · have := Real.arcsin_lt_zero.mpr hnegative
        linarith
      · have := Real.neg_pi_div_two_lt_arcsin.mpr hratio.1
        linarith

theorem umklappK₂DerivativeFactor_pos_on_selectedAtlasPatch
    {rootBranch : UmklappArcsineBranch} {k₀ k₁ : Real}
    (horientation : UmklappArcsinePositiveOrientation rootBranch k₀ k₁) :
    ∀ z ∈ umklappAtlasPatch
        (umklappArcsineAtlasBranch rootBranch k₀ k₁) k₀ k₁,
      0 < umklappK₂DerivativeFactor k₀ k₁ z := by
  intro z hz
  cases rootBranch
  · have hcos : 0 < Real.cos (umklappMovingAngle k₀ k₁ z) := by
      rw [umklappAtlasPatch_angle] at hz
      exact Real.cos_pos_of_mem_Ioo hz
    have hstructural : Real.cos ((k₀ + k₁) / 4) < 0 := by
      simpa [UmklappArcsinePositiveOrientation,
        umklappResonanceDenominator] using horientation
    rw [umklappK₂DerivativeFactor]
    exact mul_pos (mul_pos_of_neg_of_neg (by norm_num) hstructural) hcos
  · have hbranchNe :
        umklappArcsineAtlasBranch .outer k₀ k₁ ≠ .central := by
      simp only [umklappArcsineAtlasBranch]
      split <;> decide
    have hcos : Real.cos (umklappMovingAngle k₀ k₁ z) < 0 := by
      rcases movingCosine_sign_on_umklappAtlasPatch
          (umklappArcsineAtlasBranch .outer k₀ k₁) k₀ k₁ with
        ⟨hcentral, _hpositive⟩ | ⟨_houter, hnegative⟩
      · exact False.elim (hbranchNe hcentral)
      · exact hnegative z hz
    have hstructural : 0 < Real.cos ((k₀ + k₁) / 4) := by
      simpa [UmklappArcsinePositiveOrientation,
        umklappResonanceDenominator] using horientation
    rw [umklappK₂DerivativeFactor]
    exact mul_pos_of_neg_of_neg
      (mul_neg_of_neg_of_pos (by norm_num) hstructural) hcos

/-! ## Geometry certificate: interval, monotonicity, and unique root -/

structure ExplicitPositiveUmklappArcsineGeometry
    (rootBranch : UmklappArcsineBranch) (k₀ k₁ : Real) : Prop where
  interval_lt : umklappArcsineLocalLeft rootBranch k₀ k₁ <
    umklappArcsineLocalRight rootBranch k₀ k₁
  root_mem : umklappArcsineRoot rootBranch k₀ k₁ ∈
    Ioo (umklappArcsineLocalLeft rootBranch k₀ k₁)
      (umklappArcsineLocalRight rootBranch k₀ k₁)
  root_resonant : umklappReducedFourWaveMismatch k₀ k₁
    (umklappArcsineRoot rootBranch k₀ k₁) = 0
  derivative_pos : ∀ z ∈ uIcc
      (umklappArcsineLocalLeft rootBranch k₀ k₁)
      (umklappArcsineLocalRight rootBranch k₀ k₁),
    0 < umklappK₂DerivativeFactor k₀ k₁ z
  mismatch_strictMono : StrictMonoOn
    (fun z ↦ umklappReducedFourWaveMismatch k₀ k₁ z)
    (Icc (umklappArcsineLocalLeft rootBranch k₀ k₁)
      (umklappArcsineLocalRight rootBranch k₀ k₁))
  unique_root : ∀ z ∈ Icc
      (umklappArcsineLocalLeft rootBranch k₀ k₁)
      (umklappArcsineLocalRight rootBranch k₀ k₁),
    umklappReducedFourWaveMismatch k₀ k₁ z = 0 →
      z = umklappArcsineRoot rootBranch k₀ k₁

/-- All geometric fields are derived from the discriminant, principal-zone
membership, and the explicit orientation inequality. -/
theorem explicitPositiveUmklappArcsineGeometry
    {rootBranch : UmklappArcsineBranch} {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁)
    (hroot0 : 0 < umklappArcsineRoot rootBranch k₀ k₁)
    (hroot2pi : umklappArcsineRoot rootBranch k₀ k₁ < 2 * Real.pi)
    (horientation : UmklappArcsinePositiveOrientation rootBranch k₀ k₁) :
    ExplicitPositiveUmklappArcsineGeometry rootBranch k₀ k₁ := by
  let root := umklappArcsineRoot rootBranch k₀ k₁
  let branch := umklappArcsineAtlasBranch rootBranch k₀ k₁
  let a := umklappArcsineLocalLeft rootBranch k₀ k₁
  let b := umklappArcsineLocalRight rootBranch k₀ k₁
  have hpatch : root ∈ umklappAtlasPatch branch k₀ k₁ := by
    exact umklappArcsineRoot_mem_selectedAtlasPatch
      hk₀0 hk₀2pi hk₁0 hk₁2pi hdisc hroot0 hroot2pi
  have hrootLocal : root ∈ Ioo a b := by
    exact root_mem_umklappAtlasLocalInterval hpatch
  have hab : a < b := hrootLocal.1.trans hrootLocal.2
  have hderivativePatch :=
    umklappK₂DerivativeFactor_pos_on_selectedAtlasPatch horientation
  have hderivativeIcc : ∀ z ∈ Icc a b,
      0 < umklappK₂DerivativeFactor k₀ k₁ z := by
    intro z hz
    exact hderivativePatch z (umklappAtlasLocalIcc_subset_patch hpatch hz)
  have hcontinuous : Continuous
      (fun z ↦ umklappReducedFourWaveMismatch k₀ k₁ z) := by
    have hdiff : Differentiable Real
        (fun z ↦ umklappReducedFourWaveMismatch k₀ k₁ z) := fun z ↦
      (hasDerivAt_umklappReducedFourWaveMismatch_k₂_factor
        k₀ k₁ z).differentiableAt
    exact hdiff.continuous
  have hstrict : StrictMonoOn
      (fun z ↦ umklappReducedFourWaveMismatch k₀ k₁ z) (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b) hcontinuous.continuousOn
    intro z hz
    rw [deriv_umklappReducedFourWaveMismatch_k₂]
    exact hderivativeIcc z (interior_subset hz)
  have hresonant : umklappReducedFourWaveMismatch k₀ k₁ root = 0 :=
    umklappArcsineRoot_resonant hdisc rootBranch
  refine {
    interval_lt := hab
    root_mem := hrootLocal
    root_resonant := hresonant
    derivative_pos := ?_
    mismatch_strictMono := hstrict
    unique_root := ?_ }
  · intro z hz
    rw [uIcc_of_le hab.le] at hz
    exact hderivativeIcc z hz
  · intro z hz hzroot
    apply hstrict.injOn hz ⟨hrootLocal.1.le, hrootLocal.2.le⟩
    change umklappReducedFourWaveMismatch k₀ k₁ z =
      umklappReducedFourWaveMismatch k₀ k₁ root
    exact hzroot.trans hresonant.symm

/-- Geometry constructor with the positive arcsine branch selected
automatically from the structural cosine. -/
theorem explicitCanonicalPositiveUmklappArcsineGeometry
    {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁)
    (hroot0 : 0 < umklappArcsineRoot
      (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁)
    (hroot2pi : umklappArcsineRoot
      (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁ < 2 * Real.pi) :
    ExplicitPositiveUmklappArcsineGeometry
      (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁ :=
  explicitPositiveUmklappArcsineGeometry
    hk₀0 hk₀2pi hk₁0 hk₁2pi hdisc hroot0 hroot2pi
      (umklappPositiveArcsineBranch_orientation hdisc)

/-! ## Measure-only data and adapter -/

/-- Remaining measure-theoretic data after the explicit geometry has been
constructed.  There is no derivative, monotonicity, or root hypothesis in
this structure. -/
structure UmklappArcsineCollisionMeasureData
    (rootBranch : UmklappArcsineBranch) (k₀ k₁ : Real)
    (mark density : Real → Real) : Prop where
  density_continuous : Continuous density
  density_integrable : Integrable density
  density_support : Function.support density ⊆
    Ioc
      (umklappReducedFourWaveMismatch k₀ k₁
        (umklappArcsineLocalLeft rootBranch k₀ k₁))
      (umklappReducedFourWaveMismatch k₀ k₁
        (umklappArcsineLocalRight rootBranch k₀ k₁))
  mark_factorization : ∀ z ∈ uIcc
      (umklappArcsineLocalLeft rootBranch k₀ k₁)
      (umklappArcsineLocalRight rootBranch k₀ k₁),
    mark z = density (umklappReducedFourWaveMismatch k₀ k₁ z) *
      umklappK₂DerivativeFactor k₀ k₁ z

/-- Adapter into the existing positive Umklapp collision-chart API. -/
theorem UmklappArcsineCollisionMeasureData.toPositiveUmklappCollisionChart
    {rootBranch : UmklappArcsineBranch} {k₀ k₁ : Real}
    {mark density : Real → Real}
    (data : UmklappArcsineCollisionMeasureData
      rootBranch k₀ k₁ mark density)
    (geometry : ExplicitPositiveUmklappArcsineGeometry
      rootBranch k₀ k₁) :
    PositiveUmklappCollisionChart k₀ k₁ mark density
      (umklappArcsineLocalLeft rootBranch k₀ k₁)
      (umklappArcsineLocalRight rootBranch k₀ k₁) where
  derivative_pos := geometry.derivative_pos
  density_continuous := data.density_continuous
  density_integrable := data.density_integrable
  density_support := data.density_support
  mark_factorization := data.mark_factorization

/-- The complete long-time collision-chart conclusion.  All geometric and
root data are generated automatically; only `data` remains model-specific. -/
theorem tendsto_umklappArcsineCollisionChart_exactJacobian
    {rootBranch : UmklappArcsineBranch} {k₀ k₁ : Real}
    {mark density : Real → Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁)
    (hroot0 : 0 < umklappArcsineRoot rootBranch k₀ k₁)
    (hroot2pi : umklappArcsineRoot rootBranch k₀ k₁ < 2 * Real.pi)
    (horientation : UmklappArcsinePositiveOrientation rootBranch k₀ k₁)
    (data : UmklappArcsineCollisionMeasureData
      rootBranch k₀ k₁ mark density) :
    Tendsto
      (fun T : Real ↦ ∫ z in
        umklappArcsineLocalLeft rootBranch k₀ k₁..
          umklappArcsineLocalRight rootBranch k₀ k₁,
        normalizedFiniteTimeResonanceKernel
          (umklappReducedFourWaveMismatch k₀ k₁ z) T * mark z)
      atTop
      (nhds (mark (umklappArcsineRoot rootBranch k₀ k₁) /
        (2 * Real.sqrt (umklappTransverseDiscriminant k₀ k₁)))) := by
  let geometry := explicitPositiveUmklappArcsineGeometry
    hk₀0 hk₀2pi hk₁0 hk₁2pi hdisc hroot0 hroot2pi horientation
  let chart := data.toPositiveUmklappCollisionChart geometry
  apply tendsto_positiveUmklappCollisionChart_exactJacobian
    chart
  · rw [uIcc_of_le geometry.interval_lt.le]
    exact ⟨geometry.root_mem.1.le, geometry.root_mem.2.le⟩
  · exact hdisc
  · exact geometry.root_resonant

/-- Fully canonical positive-branch endpoint.  Apart from the explicit open
geometric conditions, the only bundled input is the measure data. -/
theorem tendsto_canonicalPositiveUmklappArcsineCollisionChart
    {k₀ k₁ : Real} {mark density : Real → Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁)
    (hroot0 : 0 < umklappArcsineRoot
      (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁)
    (hroot2pi : umklappArcsineRoot
      (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁ < 2 * Real.pi)
    (data : UmklappArcsineCollisionMeasureData
      (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁ mark density) :
    Tendsto
      (fun T : Real ↦ ∫ z in
        umklappArcsineLocalLeft (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁..
          umklappArcsineLocalRight
            (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁,
        normalizedFiniteTimeResonanceKernel
          (umklappReducedFourWaveMismatch k₀ k₁ z) T * mark z)
      atTop
      (nhds (mark (umklappArcsineRoot
          (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁) /
        (2 * Real.sqrt (umklappTransverseDiscriminant k₀ k₁)))) :=
  tendsto_umklappArcsineCollisionChart_exactJacobian
    hk₀0 hk₀2pi hk₁0 hk₁2pi hdisc hroot0 hroot2pi
      (umklappPositiveArcsineBranch_orientation hdisc) data

end

end ArchonPhysics.EqualMassPeriodicFPUTUmklappCollisionChartAdapter
