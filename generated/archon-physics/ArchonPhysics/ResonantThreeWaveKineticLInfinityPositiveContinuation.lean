import ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
import ArchonPhysics.FiniteDimensionalGlobalContinuation

/-!
# Positive local data and continuation for the unclipped canonical L-infinity flow

This module adds three facts to the canonical `L-infinity` construction.

* The genuine, unclipped RN collision map obeys the quadratic estimate
  `‖Q n‖_∞ ≤ 3 ‖n‖_∞²`.
* A strictly positive essential lower bound is retained for the local solution
  supplied by Picard--Lindelöf, provided the prescribed solution ball is
  smaller than that lower bound.
* A solution which remains bounded before a finite forward endpoint has a
  strict continuation through that endpoint.  Consequently finite-time
  maximality can occur only together with `L-infinity` norm blow-up.

The continuation proof is genuinely infinite-dimensional.  It does not use
compactness of bounded subsets: the explicit quadratic field bound makes the
trajectory Lipschitz in time, completeness supplies its endpoint limit, and
the local unclipped flow through that limit is glued to the old trajectory.
-/

namespace ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation

open Filter MeasureTheory Metric Set
open ArchonPhysics.FiniteDimensionalGlobalContinuation
open ArchonPhysics.ResonantThreeWaveMeasure
open ArchonPhysics.ResonantThreeWaveKineticAEBounded
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open scoped ENNReal NNReal MeasureTheory Topology

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- An order statement on canonical `L-infinity`, interpreted relative to the
canonical three-leg reference measure. -/
def AELowerBound
    (collision : ResonantThreeWaveMeasure Mode) (floor : Real)
    (action : CanonicalLInfinity collision) : Prop :=
  ∀ᵐ mode ∂collisionReferenceMeasure collision, floor ≤ action mode

/-- Essential nonnegativity in canonical `L-infinity`. -/
def AENonnegative
    (collision : ResonantThreeWaveMeasure Mode)
    (action : CanonicalLInfinity collision) : Prop :=
  AELowerBound collision 0 action

/-- The canonical representative is nonnegative almost everywhere whenever
the quotient class is. -/
theorem linfinityRepresentative_nonnegative_ae
    (collision : ResonantThreeWaveMeasure Mode)
    (action : CanonicalLInfinity collision)
    (haction : AENonnegative collision action) :
    ∀ᵐ mode ∂collisionReferenceMeasure collision,
      0 ≤ linfinityRepresentative collision action mode := by
  filter_upwards [haction,
    linfinityRepresentative_ae_eq collision action] with mode hmode heq
  rwa [heq]

/-- The unclipped quotient collision map has the same sharp elementary
quadratic bound as its pointwise RN representative. -/
theorem norm_collisionMap_le
    (collision : ResonantThreeWaveMeasure Mode)
    (action : CanonicalLInfinity collision) :
    ‖collisionMap collision action‖ ≤ 3 * ‖action‖ ^ 2 := by
  have hpointwise : ∀ᵐ mode ∂collisionReferenceMeasure collision,
      ‖collisionMap collision action mode‖ ≤ 3 * ‖action‖ ^ 2 := by
    filter_upwards [coeFn_collisionMap_ae_eq collision action,
      collisionVector_norm_le_ae collision
        (measurable_linfinityRepresentative collision action)
        (norm_linfinityRepresentative_le collision action)]
      with mode hcollision hbound
    rw [hcollision]
    exact hbound
  have hnonneg : 0 ≤ 3 * ‖action‖ ^ 2 := by positivity
  have hess := eLpNormEssSup_le_of_ae_bound hpointwise
  calc
    ‖collisionMap collision action‖ =
        (eLpNormEssSup (collisionMap collision action)
          (collisionReferenceMeasure collision)).toReal := by
      rw [Lp.norm_def, eLpNorm_exponent_top]
    _ ≤ (ENNReal.ofReal (3 * ‖action‖ ^ 2)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hess
    _ = 3 * ‖action‖ ^ 2 := ENNReal.toReal_ofReal hnonneg

/-- The coupling-scaled unclipped vector field has explicit quadratic growth. -/
theorem norm_rnCollisionVectorField_le
    (collision : ResonantThreeWaveMeasure Mode) (g : Real)
    (action : CanonicalLInfinity collision) :
    ‖rnCollisionVectorField collision g action‖ ≤
      3 * g ^ 2 * ‖action‖ ^ 2 := by
  rw [rnCollisionVectorField, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg g)]
  nlinarith [norm_collisionMap_le collision action, sq_nonneg g]

/-- Essential-supremum distance controls loss of an essential lower bound. -/
theorem aeLowerBound_sub_norm
    (collision : ResonantThreeWaveMeasure Mode)
    {initial action : CanonicalLInfinity collision} {floor : Real}
    (hinitial : AELowerBound collision floor initial) :
    AELowerBound collision (floor - ‖action - initial‖) action := by
  have hsubBound₀ := ae_le_lpNorm_exponent_top (Lp.memLp (action - initial))
  have hsubBound : ∀ᵐ mode ∂collisionReferenceMeasure collision,
      ‖(action - initial) mode‖ ≤ ‖action - initial‖ := by
    simpa only [Lp.norm_def,
      toReal_eLpNorm (Lp.aestronglyMeasurable (action - initial))] using hsubBound₀
  filter_upwards [hinitial, Lp.coeFn_sub action initial, hsubBound]
    with mode hfloor hsub hnorm
  simp only [Pi.sub_apply] at hsub
  rw [hsub] at hnorm
  have hlower : -(‖action - initial‖) ≤ action mode - initial mode := by
    exact (neg_le_of_abs_le (by simpa [Real.norm_eq_abs] using hnorm))
  linarith

/-- Membership in a prescribed closed ball gives a uniform version of
`aeLowerBound_sub_norm`. -/
theorem aeLowerBound_of_mem_closedBall
    (collision : ResonantThreeWaveMeasure Mode)
    {initial action : CanonicalLInfinity collision} {floor radius : Real}
    (hinitial : AELowerBound collision floor initial)
    (haction : action ∈ closedBall initial radius) :
    AELowerBound collision (floor - radius) action := by
  have hdist : ‖action - initial‖ ≤ radius := by
    simpa only [mem_closedBall_iff_norm] using haction
  exact (aeLowerBound_sub_norm collision hinitial).mono fun mode hmode ↦ by
    linarith

/-- Strictly positive initial data have a genuine unclipped local solution
which retains an explicit positive essential floor. -/
theorem exists_unique_local_rnCollisionODE_with_positive_floor
    (collision : ResonantThreeWaveMeasure Mode) (g : Real)
    (initial : CanonicalLInfinity collision)
    (floor : Real) (hfloor : AELowerBound collision floor initial)
    (a : NNReal) (ha : 0 < a) (haFloor : (a : Real) < floor) :
    ∃ ε : Real, 0 < ε ∧
      ∃ D : Real → CanonicalLInfinity collision,
        SolvesRNCollisionODEOn collision g initial ε D ∧
        RemainsInCanonicalLInfinityBall collision initial a ε D ∧
        (∀ t ∈ Icc (-ε) ε,
          AELowerBound collision (floor - (a : Real)) (D t)) ∧
        0 < floor - (a : Real) ∧
        ∀ E : Real → CanonicalLInfinity collision,
          SolvesRNCollisionODEOn collision g initial ε E →
          RemainsInCanonicalLInfinityBall collision initial a ε E →
          EqOn D E (Icc (-ε) ε) := by
  obtain ⟨ε, hε, D, hD, hDball, hunique⟩ :=
    exists_unique_local_rnCollisionODE collision g initial a ha
  refine ⟨ε, hε, D, hD, hDball, ?_, by linarith, hunique⟩
  intro t ht
  exact aeLowerBound_of_mem_closedBall collision hfloor (hDball t ht)

/-- A norm bound for an integral curve gives the explicit time-Lipschitz
constant inherited from the quadratic collision estimate. -/
theorem lipschitzOnWith_of_rnCollisionODE_norm_le
    (collision : ResonantThreeWaveMeasure Mode) (g : Real)
    {D : Real → CanonicalLInfinity collision} {t₀ b radius : Real}
    (_hradius : 0 ≤ radius)
    (hD : IsIntegralCurveOn D
      (fun _ ↦ rnCollisionVectorField collision g) (Ico t₀ b))
    (hbound : ∀ t ∈ Ico t₀ b, ‖D t‖ ≤ radius) :
    LipschitzOnWith (Real.toNNReal (3 * g ^ 2 * radius ^ 2)) D
      (Ico t₀ b) := by
  have hconstant : 0 ≤ 3 * g ^ 2 * radius ^ 2 := by positivity
  apply (convex_Ico t₀ b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hD
  intro t ht
  apply NNReal.coe_le_coe.mp
  rw [Real.coe_toNNReal _ hconstant]
  calc
    ‖rnCollisionVectorField collision g (D t)‖ ≤
        3 * g ^ 2 * ‖D t‖ ^ 2 :=
      norm_rnCollisionVectorField_le collision g (D t)
    _ ≤ 3 * g ^ 2 * radius ^ 2 := by
      gcongr
      exact hbound t ht

/-- A bounded unclipped canonical `L-infinity` solution has a state-space
limit at every finite forward endpoint.  No local compactness is used. -/
theorem exists_forward_endpoint_limit_of_rnCollisionODE_norm_le
    (collision : ResonantThreeWaveMeasure Mode) (g : Real)
    {D : Real → CanonicalLInfinity collision} {t₀ b radius : Real}
    (ht : t₀ < b) (hradius : 0 ≤ radius)
    (hD : IsIntegralCurveOn D
      (fun _ ↦ rnCollisionVectorField collision g) (Ico t₀ b))
    (hbound : ∀ t ∈ Ico t₀ b, ‖D t‖ ≤ radius) :
    ∃ endpoint : CanonicalLInfinity collision,
      Tendsto D (𝓝[<] b) (𝓝 endpoint) := by
  have hLip := lipschitzOnWith_of_rnCollisionODE_norm_le
    collision g hradius hD hbound
  have hdomainCauchy : Cauchy (𝓝[<] b) := by
    exact cauchy_nhds.mono inf_le_left
  have hdomain : 𝓝[<] b ≤ 𝓟 (Ico t₀ b) := by
    exact le_principal_iff.mpr (Ico_mem_nhdsLT ht)
  have himageCauchy : Cauchy (Filter.map D (𝓝[<] b)) :=
    hdomainCauchy.map_of_le hLip.uniformContinuousOn hdomain
  exact cauchy_map_iff_exists_tendsto.mp himageCauchy

/-- Boundedness before a finite endpoint yields a strict forward extension
of the genuine unclipped canonical `L-infinity` equation. -/
theorem exists_strictForwardExtension_of_rnCollisionODE_norm_le
    (collision : ResonantThreeWaveMeasure Mode) (g : Real)
    {D : Real → CanonicalLInfinity collision} {t₀ b radius : Real}
    (ht : t₀ < b) (hradius : 0 ≤ radius)
    (hD : IsIntegralCurveOn D
      (fun _ ↦ rnCollisionVectorField collision g) (Ico t₀ b))
    (hbound : ∀ t ∈ Ico t₀ b, ‖D t‖ ≤ radius) :
    ∃ (bNext : Real) (delta : Real → CanonicalLInfinity collision),
      IsStrictForwardExtension (rnCollisionVectorField collision g)
        D delta t₀ b bNext := by
  obtain ⟨endpoint, hendpoint⟩ :=
    exists_forward_endpoint_limit_of_rnCollisionODE_norm_le
      collision g ht hradius hD hbound
  obtain ⟨ε, hε, E, hE, _hEball, _hEunique⟩ :=
    exists_unique_local_rnCollisionODE collision g endpoint 1 zero_lt_one
  let beta : Real → CanonicalLInfinity collision := fun t ↦ E (t - b)
  have hbetaValue : beta b = endpoint := by
    simpa [beta] using hE.1
  have hbeta : IsIntegralCurveOn beta
      (fun _ ↦ rnCollisionVectorField collision g)
      (Ioo (b - ε) (b + ε)) := by
    intro t htBeta
    have hshift : t - b ∈ Ioo (-ε) ε := by
      constructor <;> linarith [htBeta.1, htBeta.2]
    have hshiftIcc : t - b ∈ Icc (-ε) ε := Ioo_subset_Icc_self hshift
    have hEAt : HasDerivAt E
        (rnCollisionVectorField collision g (E (t - b))) (t - b) :=
      (hE.2 (t - b) hshiftIcc).hasDerivAt
        (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hshift)
          Ioo_subset_Icc_self)
    have hsub : HasDerivAt (fun u : Real ↦ u - b) 1 t :=
      (hasDerivAt_id t).sub_const b
    simpa only [beta, Function.comp_def, one_smul] using
      (hEAt.scomp t hsub).hasDerivWithinAt
  exact (hasForwardEndpointGluing_of_continuous
      (locallyLipschitz_rnCollisionVectorField collision g).continuous)
    ht hε hD hendpoint hbetaValue hbeta

/-- Blow-up alternative: a finite forward endpoint can be maximal only if
the canonical `L-infinity` norm is unbounded on the preceding interval. -/
theorem norm_unbounded_of_isForwardMaximalAt_rnCollisionODE
    (collision : ResonantThreeWaveMeasure Mode) (g : Real)
    {D : Real → CanonicalLInfinity collision} {t₀ b : Real}
    (ht : t₀ < b)
    (hD : IsIntegralCurveOn D
      (fun _ ↦ rnCollisionVectorField collision g) (Ico t₀ b))
    (hmaximal : IsForwardMaximalAt
      (rnCollisionVectorField collision g) D t₀ b) :
    ∀ radius : Real, 0 ≤ radius →
      ∃ t ∈ Ico t₀ b, radius < ‖D t‖ := by
  intro radius hradius
  by_contra hnot
  push Not at hnot
  exact hmaximal (exists_strictForwardExtension_of_rnCollisionODE_norm_le
    collision g ht hradius hD hnot)

end

end ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation
