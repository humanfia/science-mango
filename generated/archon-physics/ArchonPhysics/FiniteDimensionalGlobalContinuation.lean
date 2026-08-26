import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Finite-dimensional ODE continuation data

This module proves the bounded-trajectory continuation criterion available
from the pinned Mathlib primitives.  For a finite-dimensional autonomous `C¹`
vector field, a solution on `[t₀, b)` with bounded image has a genuine left
limit at `b`; Mathlib's local Picard--Lindelof theorem supplies a local
solution through that endpoint value, and one-sided derivative extension
glues the two curves.

The pinned ODE library has no maximal-solution object.  We therefore formulate
finite-endpoint maximality directly in terms of strict extensions.  The
endpoint-gluing proposition below is proved from continuity and is never an
external hypothesis or an assumed global solution.
-/

namespace ArchonPhysics.FiniteDimensionalGlobalContinuation

open Filter Set
open scoped NNReal Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]

/-- A strict forward extension agrees with the old trajectory on `[t₀, b)`
and solves the same autonomous ODE on a strictly longer interval. -/
def IsStrictForwardExtension (f : E → E) (gamma delta : Real → E)
    (t₀ b b' : Real) : Prop :=
  b < b' ∧ EqOn gamma delta (Ico t₀ b) ∧
    IsIntegralCurveOn delta (fun _ ↦ f) (Ico t₀ b')

/-- Maximality at a finite forward endpoint, formulated without postulating a
maximal-solution object in the dependency. -/
def IsForwardMaximalAt (f : E → E) (gamma : Real → E) (t₀ b : Real) : Prop :=
  ¬ ∃ (b' : Real) (delta : Real → E),
    IsStrictForwardExtension f gamma delta t₀ b b'

/--
The minimal endpoint-gluing adapter absent from the pinned Mathlib ODE API.

It says only that an old integral curve with a left endpoint limit can be
glued to a local integral curve through that limit.  It does not assume the
existence of a global solution.
-/
def HasForwardEndpointGluing (f : E → E) : Prop :=
  ∀ ⦃t₀ b : Real⦄ ⦃gamma beta : Real → E⦄ ⦃x : E⦄ ⦃epsilon : Real⦄,
    t₀ < b → 0 < epsilon →
    IsIntegralCurveOn gamma (fun _ ↦ f) (Ico t₀ b) →
    Tendsto gamma (𝓝[<] b) (𝓝 x) → beta b = x →
    IsIntegralCurveOn beta (fun _ ↦ f) (Ioo (b - epsilon) (b + epsilon)) →
    ∃ (b' : Real) (delta : Real → E),
      IsStrictForwardExtension f gamma delta t₀ b b'

omit [FiniteDimensional Real E] in
/-- A continuous autonomous vector field satisfies the endpoint-gluing
adapter.  The proof joins the two curves at the limiting state and uses
Mathlib's one-sided derivative extension theorem at the joining time. -/
theorem hasForwardEndpointGluing_of_continuous {f : E → E}
    (hf : Continuous f) : HasForwardEndpointGluing f := by
  intro t₀ b gamma beta x epsilon ht hepsilon hgamma hx hbetaValue hbeta
  let delta : Real → E := fun t ↦ if t < b then gamma t else beta t
  have hdeltaLeft : Tendsto delta (𝓝[<] b) (𝓝 x) := by
    refine hx.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htb : t < b := ht
    simp [delta, htb]
  have hdeltaValue : delta b = x := by
    simp [delta, hbetaValue]
  have hdeltaDifferentiable : DifferentiableOn Real delta (Ico t₀ b) := by
    intro t htOld
    have hderiv := hgamma t htOld
    have heq : ∀ y ∈ Ico t₀ b, delta y = gamma y := by
      intro y hy
      simp [delta, hy.2]
    exact (hderiv.congr heq (heq t htOld)).differentiableWithinAt
  have hdeltaContinuous : ContinuousWithinAt delta (Ico t₀ b) b := by
    change Tendsto delta (𝓝[Ico t₀ b] b) (𝓝 (delta b))
    rw [nhdsWithin_Ico_eq_nhdsLT ht, hdeltaValue]
    exact hdeltaLeft
  have hderivLimit :
      Tendsto (fun t ↦ deriv delta t) (𝓝[<] b) (𝓝 (f x)) := by
    have hfieldLimit :
        Tendsto (fun t ↦ f (delta t)) (𝓝[<] b) (𝓝 (f x)) :=
      hf.continuousAt.tendsto.comp hdeltaLeft
    refine hfieldLimit.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT ht] with t htInterior
    have hgammaAt : HasDerivAt gamma (f (gamma t)) t :=
      (hgamma t ⟨htInterior.1.le, htInterior.2⟩).hasDerivAt
        (Ico_mem_nhds_iff.mpr htInterior)
    have hlocal : delta =ᶠ[𝓝 t] gamma := by
      filter_upwards [Iio_mem_nhds htInterior.2] with y hy
      have hyb : y < b := hy
      simp [delta, hyb]
    have hdeltaAt : HasDerivAt delta (f (gamma t)) t :=
      hgammaAt.congr_of_eventuallyEq hlocal
    simpa [delta, htInterior.2] using hdeltaAt.deriv.symm
  have hleft : HasDerivWithinAt delta (f x) (Iic b) b :=
    hasDerivWithinAt_Iic_of_tendsto_deriv hdeltaDifferentiable
      hdeltaContinuous (Ico_mem_nhdsLT ht) hderivLimit
  have hbLocal : b ∈ Ioo (b - epsilon) (b + epsilon) := by
    constructor <;> linarith
  have hbetaAt : HasDerivAt beta (f (beta b)) b :=
    (hbeta b hbLocal).hasDerivAt (isOpen_Ioo.mem_nhds hbLocal)
  have hrightEq : delta =ᶠ[𝓝[Ici b] b] beta := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hbt : b ≤ t := ht
    simp [delta, not_lt.mpr hbt]
  have hright : HasDerivWithinAt delta (f x) (Ici b) b := by
    have hderiv : HasDerivWithinAt delta (f (beta b)) (Ici b) b :=
      hbetaAt.hasDerivWithinAt.congr_of_eventuallyEq hrightEq (by simp [delta])
    simpa [hbetaValue] using hderiv
  have hjoin : HasDerivAt delta (f (delta b)) b := by
    have hunion : HasDerivWithinAt delta (f x) (Iic b ∪ Ici b) b :=
      hleft.union hright
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at hunion
    simpa [hdeltaValue] using hunion
  refine ⟨b + epsilon, delta, ?_⟩
  refine ⟨lt_add_of_pos_right b hepsilon, ?_, ?_⟩
  · intro t htOld
    simp [delta, htOld.2]
  · intro t htNew
    by_cases htb : t < b
    · have htOld : t ∈ Ico t₀ b := ⟨htNew.1, htb⟩
      have hsets : Ico t₀ b =ᶠ[𝓝 t] Ico t₀ (b + epsilon) := by
        filter_upwards [Iio_mem_nhds htb] with y hy
        have hyb : y < b := hy
        apply propext
        change (t₀ ≤ y ∧ y < b) ↔ (t₀ ≤ y ∧ y < b + epsilon)
        constructor
        · intro h
          exact ⟨h.1, h.2.trans (lt_add_of_pos_right b hepsilon)⟩
        · intro h
          exact ⟨h.1, hyb⟩
      have hderiv :
          HasDerivWithinAt gamma (f (gamma t)) (Ico t₀ (b + epsilon)) t :=
        (hgamma t htOld).congr_set hsets
      have hlocal : delta =ᶠ[𝓝 t] gamma := by
        filter_upwards [Iio_mem_nhds htb] with y hy
        have hyb : y < b := hy
        simp [delta, hyb]
      have hlocalWithin : delta =ᶠ[𝓝[Ico t₀ (b + epsilon)] t] gamma :=
        hlocal.filter_mono inf_le_left
      have hdeltaDeriv :=
        hderiv.congr_of_eventuallyEq hlocalWithin (by simp [delta, htb])
      simpa [delta, htb] using hdeltaDeriv
    · by_cases hEq : t = b
      · subst t
        exact hjoin.hasDerivWithinAt
      · have hbt : b < t := lt_of_le_of_ne (not_lt.mp htb) (Ne.symm hEq)
        have htBeta : t ∈ Ioo (b - epsilon) (b + epsilon) := by
          exact ⟨(sub_lt_self b hepsilon).trans hbt, htNew.2⟩
        have hbetaDeriv : HasDerivAt beta (f (beta t)) t :=
          (hbeta t htBeta).hasDerivAt (isOpen_Ioo.mem_nhds htBeta)
        have hlocal : delta =ᶠ[𝓝 t] beta := by
          filter_upwards [Ioi_mem_nhds hbt] with y hy
          have hby : b < y := hy
          simp [delta, not_lt.mpr hby.le]
        have hdeltaDeriv : HasDerivAt delta (f (beta t)) t :=
          hbetaDeriv.congr_of_eventuallyEq hlocal
        simpa [delta, htb] using hdeltaDeriv.hasDerivWithinAt

/-- A bounded finite-dimensional trajectory has compact state-space closure. -/
theorem isCompact_closure_image_Ico_of_isBounded
    {gamma : Real → E} {t₀ b : Real}
    (hbounded : Bornology.IsBounded (gamma '' Ico t₀ b)) :
    IsCompact (closure (gamma '' Ico t₀ b)) := by
  let _ : ProperSpace E := FiniteDimensional.proper Real E
  exact hbounded.isCompact_closure

/--
A bounded solution of a continuous autonomous ODE on `[t₀, b)` has a global
Lipschitz extension as a function of time.  The extension is used only to
produce the endpoint limit; it is not claimed to solve the ODE off the old
interval.
-/
theorem exists_lipschitz_extension_of_bounded_forward_solution
    {f : E → E} {gamma : Real → E} {t₀ b : Real}
    (hf : Continuous f)
    (hgamma : IsIntegralCurveOn gamma (fun _ ↦ f) (Ico t₀ b))
    (hbounded : Bornology.IsBounded (gamma '' Ico t₀ b)) :
    ∃ (K : NNReal) (g : Real → E), LipschitzWith K g ∧
      EqOn gamma g (Ico t₀ b) := by
  let _ : ProperSpace E := FiniteDimensional.proper Real E
  have hcompact : IsCompact (closure (gamma '' Ico t₀ b)) :=
    hbounded.isCompact_closure
  have hfieldCompact : IsCompact (f '' closure (gamma '' Ico t₀ b)) :=
    hcompact.image hf
  obtain ⟨R, hR, hfieldBound⟩ := hfieldCompact.isBounded.exists_pos_norm_le
  let K : NNReal := ⟨R, hR.le⟩
  have hderivBound : ∀ t ∈ Ico t₀ b, ‖f (gamma t)‖₊ ≤ K := by
    intro t ht
    apply NNReal.coe_le_coe.mp
    change ‖f (gamma t)‖ ≤ R
    apply hfieldBound
    exact ⟨gamma t, subset_closure ⟨t, ht, rfl⟩, rfl⟩
  have hLipschitz : LipschitzOnWith K gamma (Ico t₀ b) :=
    (convex_Ico t₀ b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      hgamma hderivBound
  obtain ⟨g, hg, heq⟩ := hLipschitz.extend_finite_dimension
  exact ⟨_, g, hg, heq⟩

/-- Boundedness prevents loss of an endpoint state at a finite forward time. -/
theorem exists_forward_endpoint_limit
    {f : E → E} {gamma : Real → E} {t₀ b : Real}
    (ht : t₀ < b) (hf : Continuous f)
    (hgamma : IsIntegralCurveOn gamma (fun _ ↦ f) (Ico t₀ b))
    (hbounded : Bornology.IsBounded (gamma '' Ico t₀ b)) :
    ∃ x : E, Tendsto gamma (𝓝[<] b) (𝓝 x) := by
  obtain ⟨K, g, hg, heq⟩ :=
    exists_lipschitz_extension_of_bounded_forward_solution hf hgamma hbounded
  refine ⟨g b, ?_⟩
  have heventually : gamma =ᶠ[𝓝[<] b] g :=
    heq.eventuallyEq_of_mem (Ico_mem_nhdsLT ht)
  have hgleft : Tendsto g (𝓝[<] b) (𝓝 (g b)) :=
    hg.continuous.continuousAt.tendsto.mono_left inf_le_left
  exact hgleft.congr' heventually.symm

/-- A `C¹` autonomous field has a local solution through every endpoint state. -/
theorem exists_local_solution_through
    {f : E → E} (hf : ContDiff Real 1 f) (b : Real) (x : E) :
    ∃ (beta : Real → E) (epsilon : Real), beta b = x ∧ 0 < epsilon ∧
      IsIntegralCurveOn beta (fun _ ↦ f) (Ioo (b - epsilon) (b + epsilon)) := by
  obtain ⟨beta, hbeta, epsilon, hepsilon, hderiv⟩ :=
    hf.contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ b
  refine ⟨beta, epsilon, hbeta, hepsilon, fun t ht ↦ ?_⟩
  exact (hderiv t ht).hasDerivWithinAt

/--
All continuation data available before the missing endpoint-gluing step:
a limiting state and a local integral curve through it.
-/
theorem bounded_forward_solution_has_endpoint_data
    {f : E → E} {gamma : Real → E} {t₀ b : Real}
    (ht : t₀ < b) (hf : ContDiff Real 1 f)
    (hgamma : IsIntegralCurveOn gamma (fun _ ↦ f) (Ico t₀ b))
    (hbounded : Bornology.IsBounded (gamma '' Ico t₀ b)) :
    ∃ (x : E) (beta : Real → E) (epsilon : Real),
      Tendsto gamma (𝓝[<] b) (𝓝 x) ∧ beta b = x ∧ 0 < epsilon ∧
        IsIntegralCurveOn beta (fun _ ↦ f) (Ioo (b - epsilon) (b + epsilon)) := by
  obtain ⟨x, hx⟩ := exists_forward_endpoint_limit ht hf.continuous hgamma hbounded
  obtain ⟨beta, epsilon, hbeta, hepsilon, hbetaSolution⟩ :=
    exists_local_solution_through hf b x
  exact ⟨x, beta, epsilon, hx, hbeta, hepsilon, hbetaSolution⟩

/-- A bounded `C¹` trajectory admits a strict forward extension past every
finite endpoint. -/
theorem exists_strictForwardExtension_of_bounded
    {f : E → E} {gamma : Real → E} {t₀ b : Real}
    (ht : t₀ < b) (hf : ContDiff Real 1 f)
    (hgamma : IsIntegralCurveOn gamma (fun _ ↦ f) (Ico t₀ b))
    (hbounded : Bornology.IsBounded (gamma '' Ico t₀ b)) :
    ∃ (b' : Real) (delta : Real → E),
      IsStrictForwardExtension f gamma delta t₀ b b' := by
  obtain ⟨x, beta, epsilon, hx, hbeta, hepsilon, hbetaSolution⟩ :=
    bounded_forward_solution_has_endpoint_data ht hf hgamma hbounded
  exact (hasForwardEndpointGluing_of_continuous hf.continuous)
    ht hepsilon hgamma hx hbeta hbetaSolution

/-- Consequently, a bounded finite-endpoint solution cannot be forward maximal
for a `C¹` autonomous vector field. -/
theorem not_isForwardMaximalAt_of_bounded
    {f : E → E} {gamma : Real → E} {t₀ b : Real}
    (ht : t₀ < b) (hf : ContDiff Real 1 f)
    (hgamma : IsIntegralCurveOn gamma (fun _ ↦ f) (Ico t₀ b))
    (hbounded : Bornology.IsBounded (gamma '' Ico t₀ b)) :
    ¬ IsForwardMaximalAt f gamma t₀ b := by
  intro hmaximal
  exact hmaximal
    (exists_strictForwardExtension_of_bounded ht hf hgamma hbounded)

end

end ArchonPhysics.FiniteDimensionalGlobalContinuation
