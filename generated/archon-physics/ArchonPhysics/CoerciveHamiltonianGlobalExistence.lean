import ArchonPhysics.CoerciveHamiltonianContinuation
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Global trajectories for the coercive reduced Hamiltonian

This module turns the finite-endpoint continuation bounds into an actual
global solution.  The construction first proves global existence for a
bounded globally Lipschitz `C¹` vector field using Mathlib's uniform-time
integral-curve theorem.  A smooth compactly supported cutoff of the reduced
Hamilton vector field is then used.  Energy is conserved even for a scalar
multiple of a Hamilton vector field, and coercivity forces the cutoff to stay
identically one along the resulting trajectory.
-/

namespace ArchonPhysics.CoerciveHamiltonianGlobalExistence

open Set Metric Manifold
open CoerciveHamiltonianContinuation
open CoerciveHamiltonianPhyslib ConcreteHamiltonGradients
open InnerProductSpace
open scoped NNReal Topology Manifold

noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- A globally bounded, globally Lipschitz `C¹` autonomous field on a
finite-dimensional real normed space has a global integral curve through
every point. -/
theorem exists_global_integralCurve_of_uniform_bound_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [ContinuousSMul Real E] [FiniteDimensional Real E]
    {f : E → E} (hf : ContDiff Real 1 f)
    (L K : NNReal) (hbound : ∀ x, ‖f x‖ ≤ (L : Real))
    (hlip : LipschitzWith K f) (x0 : E) :
    ∃ gamma : Real → E, gamma 0 = x0 ∧
      ∀ t : Real, HasDerivAt gamma (f (gamma t)) t := by
  let epsilon : Real := (1 : Real) / ((L : Real) + 1)
  have hden : 0 < (L : Real) + 1 := by positivity
  have hepsilon : 0 < epsilon := div_pos zero_lt_one hden
  let v : ∀ x : E, TangentSpace (modelWithCornersSelf Real E) x := fun x ↦ f x
  have hv : CMDiff 1
      (fun x ↦ (⟨x, v x⟩ : TangentBundle (modelWithCornersSelf Real E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hf
  have hlocal : ∀ x : E, ∃ gamma : Real → E,
      gamma 0 = x ∧ IsMIntegralCurveOn gamma v (Ioo (-epsilon) epsilon) := by
    intro x
    have htime : (L : Real) * max (epsilon - 0) (0 - (-epsilon)) ≤
        (1 : Real) - 0 := by
      simp only [sub_zero, zero_sub, neg_neg, max_self, epsilon]
      calc
        (L : Real) * (1 / ((L : Real) + 1)) =
            (L : Real) / ((L : Real) + 1) := by ring
        _ ≤ 1 := (div_le_one hden).2 (by linarith)
    have hzero : (0 : Real) ∈ Icc (-epsilon) epsilon := by
      constructor <;> linarith
    have hpicard : IsPicardLindelof (fun _ ↦ f)
        (tmin := -epsilon) (tmax := epsilon)
        ⟨0, hzero⟩ x 1 0 L K :=
      IsPicardLindelof.of_time_independent (fun y _ ↦ hbound y)
        hlip.lipschitzOnWith htime
    obtain ⟨gamma, hgamma0, hgamma⟩ :=
      hpicard.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    refine ⟨gamma, hgamma0, fun t ht ↦ ?_⟩
    have hderiv := (hgamma t (Ioo_subset_Icc_self ht)).mono Ioo_subset_Icc_self
    rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
    exact hderiv.hasFDerivWithinAt.hasMFDerivWithinAt
  obtain ⟨gamma, hgamma0, hgamma⟩ :=
    exists_isMIntegralCurve_of_isMIntegralCurveOn hv hepsilon hlocal x0
  refine ⟨gamma, hgamma0, fun t ↦ ?_⟩
  rw [hasDerivAt_iff_hasFDerivAt,
    ← ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
  exact (hgamma t).hasFDerivAt

/-- A compactly supported `C¹` vector field is globally bounded and globally
Lipschitz, hence admits a global integral curve through every point. -/
theorem exists_global_integralCurve_of_contDiff_hasCompactSupport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [ContinuousSMul Real E] [FiniteDimensional Real E]
    {f : E → E} (hf : ContDiff Real 1 f)
    (hcompact : HasCompactSupport f) (x0 : E) :
    ∃ gamma : Real → E, gamma 0 = x0 ∧
      ∀ t : Real, HasDerivAt gamma (f (gamma t)) t := by
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuous hf.continuous
  have hCnonneg : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  let L : NNReal := ⟨C, hCnonneg⟩
  obtain ⟨K, hK⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hcompact hf one_ne_zero
  exact exists_global_integralCurve_of_uniform_bound_lipschitz
    hf L K (fun x ↦ hC x) hK x0

/-- A smooth bump which is one on the radius-`R` ball and supported in the
radius-`R+2` ball. -/
def normCutoffBump
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    (R : Real) (hR : 0 ≤ R) : ContDiffBump (0 : E) where
  rIn := R + 1
  rOut := R + 2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

/-- Smooth compactly supported truncation of a vector field. -/
def normCutoffVectorField
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    (f : E → E) (R : Real) (hR : 0 ≤ R) : E → E :=
  fun x ↦ normCutoffBump (E := E) R hR x • f x

theorem normCutoffVectorField_eq_of_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    (f : E → E) (R : Real) (hR : 0 ≤ R) {x : E}
    (hx : ‖x‖ ≤ R) : normCutoffVectorField f R hR x = f x := by
  unfold normCutoffVectorField
  rw [(normCutoffBump (E := E) R hR).one_of_mem_closedBall, one_smul]
  simpa [normCutoffBump, mem_closedBall_iff_norm] using hx.trans (by linarith)

theorem normCutoffVectorField_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {f : E → E} (hf : ContDiff Real 1 f) (R : Real) (hR : 0 ≤ R) :
    ContDiff Real 1 (normCutoffVectorField f R hR) := by
  change ContDiff Real 1 ((normCutoffBump (E := E) R hR : E → Real) • f)
  exact (normCutoffBump (E := E) R hR).contDiff.smul hf

theorem normCutoffVectorField_hasCompactSupport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    (f : E → E) (R : Real) (hR : 0 ≤ R) :
    HasCompactSupport (normCutoffVectorField f R hR) := by
  change HasCompactSupport ((normCutoffBump (E := E) R hR : E → Real) • f)
  exact (normCutoffBump (E := E) R hR).hasCompactSupport.smul_right

/-- The reduced Hamiltonian is conserved along an arbitrary scalar multiple
of its Hamilton vector field.  This is the algebraic fact that permits the
compactly supported cutoff construction. -/
theorem reducedHamiltonian_hasDerivWithinAt_zero_of_smulVectorField
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (kappa beta g a : Real)
    {z : Real → ReducedPhaseSpace m} {s : Set Real} {t : Real}
    (hz : HasDerivWithinAt z
      (a • reducedVectorField m kappa beta g (z t)) s t) :
    HasDerivWithinAt
      (fun u ↦ reducedHamiltonian m kappa beta g (z u)) 0 s t := by
  have hqSub : HasDerivWithinAt (fun u ↦ (z u).1)
      (a • reducedVelocity m (z t).2) s t := by
    simpa [reducedVectorField] using
      hz.hasFDerivWithinAt.fst.hasDerivWithinAt
  have hpSub : HasDerivWithinAt (fun u ↦ (z u).2)
      (a • (-reducedPotentialGradient m kappa beta g (z t).1)) s t := by
    simpa [reducedVectorField] using
      hz.hasFDerivWithinAt.snd.hasDerivWithinAt
  have hq :=
    (ReducedPositionSpace m).subtypeL.hasFDerivAt.comp_hasDerivWithinAt t hqSub
  have hp :=
    (ReducedMomentumSpace N).subtypeL.hasFDerivAt.comp_hasDerivWithinAt t hpSub
  have hkin :=
    (hasGradientAt_kineticEnergy m
      ((z t).2 : HilbertConfiguration N)).hasFDerivAt
      |>.comp_hasDerivWithinAt t hp
  have hpot :=
    (hasGradientAt_potentialEnergy kappa beta g
      ((z t).1 : HilbertConfiguration N)).hasFDerivAt
      |>.comp_hasDerivWithinAt t hq
  have hsum := hkin.add hpot
  simpa [reducedHamiltonian, CoerciveLatticeEnergy.hamiltonian,
    Function.comp_def, InnerProductSpace.toDual_apply_apply,
    real_inner_comm, real_inner_smul_right] using! hsum

/-- Every initial condition in the translation-reduced coercive Hamiltonian
system has an actual two-sided global trajectory. -/
theorem exists_global_reducedTrajectory
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {kappa beta : Real} (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (g : Real) (z0 : ReducedPhaseSpace m) :
    ∃ z : Real → ReducedPhaseSpace m, z 0 = z0 ∧
      ∀ t : Real,
        HasDerivAt z (reducedVectorField m kappa beta g (z t)) t := by
  let initialEnergy := reducedHamiltonian m kappa beta g z0
  obtain ⟨R, hR⟩ :=
    exists_reducedPhaseSpace_norm_bound_of_energy_le
      m hbeta g initialEnergy
  have hz0Norm : ‖z0‖ ≤ R := hR z0 le_rfl
  have hRnonneg : 0 ≤ R := (norm_nonneg z0).trans hz0Norm
  let truncated : ReducedPhaseSpace m → ReducedPhaseSpace m :=
    normCutoffVectorField (reducedVectorField m kappa beta g) R hRnonneg
  have htruncatedContDiff : ContDiff Real 1 truncated := by
    exact normCutoffVectorField_contDiff
      (reducedVectorField_contDiff m kappa beta g) R hRnonneg
  have htruncatedCompact : HasCompactSupport truncated := by
    exact normCutoffVectorField_hasCompactSupport
      (reducedVectorField m kappa beta g) R hRnonneg
  obtain ⟨z, hz0, hz⟩ :=
    exists_global_integralCurve_of_contDiff_hasCompactSupport
      htruncatedContDiff htruncatedCompact z0
  have henergyDeriv : ∀ t : Real,
      HasDerivAt (fun u ↦ reducedHamiltonian m kappa beta g (z u)) 0 t := by
    intro t
    have hzScaled : HasDerivAt z
        ((normCutoffBump (E := ReducedPhaseSpace m) R hRnonneg (z t)) •
          reducedVectorField m kappa beta g (z t)) t := by
      simpa [truncated, normCutoffVectorField] using hz t
    exact (reducedHamiltonian_hasDerivWithinAt_zero_of_smulVectorField
      m kappa beta g
      (normCutoffBump (E := ReducedPhaseSpace m) R hRnonneg (z t))
      (s := univ) hzScaled.hasDerivWithinAt).hasDerivAt Filter.univ_mem
  have henergy : ∀ t : Real,
      reducedHamiltonian m kappa beta g (z t) = initialEnergy := by
    intro t
    let energy : Real → Real :=
      fun u ↦ reducedHamiltonian m kappa beta g (z u)
    have hbound := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (C := 0) (fun u _ ↦ (henergyDeriv u).hasDerivWithinAt)
      (fun _ _ ↦ by simp) (mem_univ (0 : Real)) (mem_univ t)
    have heq : energy t = energy 0 := by
      simpa only [norm_zero, zero_mul, norm_le_zero_iff, sub_eq_zero]
        using hbound
    simpa [energy, initialEnergy, hz0] using heq
  refine ⟨z, hz0, fun t ↦ ?_⟩
  have hnorm : ‖z t‖ ≤ R := hR (z t) (henergy t).le
  have hzTruncated := hz t
  change HasDerivAt z
    (normCutoffVectorField (reducedVectorField m kappa beta g)
      R hRnonneg (z t)) t at hzTruncated
  rw [normCutoffVectorField_eq_of_norm_le
    (reducedVectorField m kappa beta g) R hRnonneg hnorm] at hzTruncated
  exact hzTruncated

end

end ArchonPhysics.CoerciveHamiltonianGlobalExistence
