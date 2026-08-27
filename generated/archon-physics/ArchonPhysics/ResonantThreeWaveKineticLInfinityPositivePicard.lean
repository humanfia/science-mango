import ArchonPhysics.ResonantThreeWaveKineticLInfinityQuasipositivity
import Mathlib.Analysis.ODE.PicardLindelof

/-!
# Positive-cone Picard fixed points for canonical L-infinity

This module supplies the ordered-Banach-space step that is absent from the
standard Picard--Lindelof API.  On a forward time interval, if a vector field
maps the nonnegative cone into itself, then the Picard operator preserves
nonnegative curves.  A contracting iterate is started from a nonnegative
constant curve; closedness of the cone then puts its fixed-point limit in the
same cone.

The final section identifies the native order on canonical `L-infinity` with
almost-everywhere nonnegativity.  Consequently the quasipositivity theorem for
the genuine, unclipped collision map can be consumed as an ordered quotient
statement, without choosing representatives downstream.
-/

namespace ArchonPhysics.ResonantThreeWaveKineticLInfinityPositivePicard

open Filter Function MeasureTheory Metric Set
open ArchonPhysics.ResonantThreeWaveMeasure
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation
open ArchonPhysics.ResonantThreeWaveKineticLInfinityQuasipositivity
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open scoped ENNReal NNReal MeasureTheory Topology

noncomputable section

/-! ## An ordered Picard fixed-point adapter -/

section OrderedPicard

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [PartialOrder E] [IsOrderedAddMonoid E]
  [IsOrderedModule Real E] [ClosedIciTopology E]
  {f : Real → E → E} {tmin tmax : Real}
  {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : NNReal}

/-- Pointwise nonnegativity for a curve in Mathlib's Picard fun space. -/
def IsNonnegativeCurve
    (alpha : ODE.FunSpace t₀ x₀ r L) : Prop :=
  ∀ t, 0 ≤ alpha t

/-- A forward interval integral of an ordered-Banach-valued nonnegative
function is nonnegative. -/
theorem intervalIntegral_nonnegative
    {integrand : Real → E} {left right : Real}
    (hle : left ≤ right)
    (hintegrand : ∀ t ∈ Ioc left right, 0 ≤ integrand t) :
    0 ≤ ∫ t in left..right, integrand t := by
  rw [intervalIntegral.integral_of_le hle]
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact hintegrand t ht

/-- If the initial point is nonnegative and the vector field is nonnegative
on nonnegative states in the Picard ball, one Picard step preserves
pointwise nonnegativity.  The hypothesis `t₀ = tmin` is precisely the
forward-time orientation needed by the integral equation. -/
theorem isNonnegativeCurve_next
    (hpl : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ (r : Real))
    (ht₀ : (t₀ : Real) = tmin)
    (hxnonnegative : 0 ≤ x)
    (hfield : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ (a : Real),
      0 ≤ y → 0 ≤ f t y)
    {alpha : ODE.FunSpace t₀ x₀ r L}
    (halpha : IsNonnegativeCurve alpha) :
    IsNonnegativeCurve (ODE.FunSpace.next hpl hx alpha) := by
  intro t
  rw [ODE.FunSpace.next_apply, ODE.picard_apply]
  apply add_nonneg hxnonnegative
  apply intervalIntegral_nonnegative
  · rw [ht₀]
    exact t.2.1
  · intro tau htau
    have htauIcc : tau ∈ Icc tmin tmax := by
      constructor
      · rw [← ht₀]
        exact htau.1.le
      · exact htau.2.trans t.2.2
    apply hfield tau htauIcc (alpha.compProj tau)
      (alpha.compProj_mem_closedBall hpl.mul_max_le)
    exact halpha _

/-- Positive-cone refinement of `ODE.FunSpace.exists_isFixedPt_next`.

Mathlib proves that some iterate of `next` is a contraction.  We start that
iterate from the constant nonnegative curve, use preservation at every
iterate, and pass to the limit through the closed cone `Ici 0`.  The unique
fixed point of the contracting iterate is also a fixed point of `next`.
-/
theorem exists_isFixedPt_next_isNonnegative
    [CompleteSpace E]
    (hpl : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ (r : Real))
    (ht₀ : (t₀ : Real) = tmin)
    (hxnonnegative : 0 ≤ x)
    (hfield : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ (a : Real),
      0 ≤ y → 0 ≤ f t y) :
    ∃ alpha : ODE.FunSpace t₀ x₀ r L,
      IsFixedPt (ODE.FunSpace.next hpl hx) alpha ∧ IsNonnegativeCurve alpha := by
  let T := ODE.FunSpace.next hpl hx
  let beta : ODE.FunSpace t₀ x₀ r L :=
    { toFun := fun _ ↦ x
      lipschitzWith := (LipschitzWith.const _).weaken zero_le
      mem_closedBall₀ := hx }
  have hbeta : IsNonnegativeCurve beta := fun _ ↦ hxnonnegative
  have hpreserves : ∀ gamma : ODE.FunSpace t₀ x₀ r L,
      IsNonnegativeCurve gamma → IsNonnegativeCurve (T gamma) := by
    intro gamma hgamma
    exact isNonnegativeCurve_next hpl hx ht₀ hxnonnegative
      hfield hgamma
  have hiterate : ∀ (n : Nat) (gamma : ODE.FunSpace t₀ x₀ r L),
      IsNonnegativeCurve gamma → IsNonnegativeCurve ((T^[n]) gamma) := by
    intro n gamma hgamma
    induction n with
    | zero => simpa using hgamma
    | succ n hn =>
        rw [Function.iterate_succ_apply']
        exact hpreserves _ hn
  obtain ⟨n, C, hcontract⟩ :=
    ODE.FunSpace.exists_contractingWith_iterate_next hpl
  let H : ContractingWith C (T^[n]) := hcontract x hx
  let alpha : ODE.FunSpace t₀ x₀ r L := H.fixedPoint (T^[n])
  have halphaFixed : IsFixedPt T alpha := H.isFixedPt_fixedPoint_iterate
  have halphaNonnegative : IsNonnegativeCurve alpha := by
    intro t
    have hlimit : Tendsto (fun k ↦ ((T^[n])^[k]) beta) atTop (nhds alpha) :=
      H.tendsto_iterate_fixedPoint beta
    have hevaluation : Continuous
        (fun gamma : ODE.FunSpace t₀ x₀ r L ↦ gamma t) := by
      change Continuous
        (fun gamma : ODE.FunSpace t₀ x₀ r L ↦ gamma.toContinuousMap t)
      fun_prop
    apply isClosed_Ici.mem_of_tendsto
      (hevaluation.continuousAt.tendsto.comp hlimit)
    apply Eventually.of_forall
    intro k
    have hpositive : IsNonnegativeCurve (((T^[n])^[k]) beta) := by
      induction k with
      | zero => simpa using hbeta
      | succ k hk =>
          rw [Function.iterate_succ_apply']
          exact hiterate n _ hk
    exact hpositive t
  exact ⟨alpha, halphaFixed, halphaNonnegative⟩

end OrderedPicard

/-! ## Native `Lp` order and the canonical collision map -/

variable {Mode : Type*} [MeasurableSpace Mode]

/-- Native order on the canonical `Lp` quotient is exactly the previously
used almost-everywhere nonnegativity predicate. -/
theorem aeNonnegative_iff_nonnegative
    (collision : ResonantThreeWaveMeasure Mode)
    (action : CanonicalLInfinity collision) :
    AENonnegative collision action ↔ 0 ≤ action := by
  constructor
  · intro h
    apply (Lp.coeFn_le (0 : CanonicalLInfinity collision) action).mp
    exact (Lp.coeFn_zero Real ∞
      (collisionReferenceMeasure collision)).trans_le h
  · intro h
    have hquotient :=
      (Lp.coeFn_le (0 : CanonicalLInfinity collision) action).mpr h
    exact hquotient.congr
      (Lp.coeFn_zero Real ∞ (collisionReferenceMeasure collision))
      EventuallyEq.rfl

/-- Nonnegative real scalar multiplication preserves the native order on
canonical `L-infinity`.  Mathlib's `Lp` order currently does not export this
ordered-module instance, although it follows directly from its a.e. order. -/
theorem smul_nonnegative
    (collision : ResonantThreeWaveMeasure Mode)
    {scalar : Real} {action : CanonicalLInfinity collision}
    (hscalar : 0 ≤ scalar) (haction : 0 ≤ action) :
    0 ≤ scalar • action := by
  rw [← aeNonnegative_iff_nonnegative collision]
  have hactionAE :=
    (aeNonnegative_iff_nonnegative collision action).mpr haction
  filter_upwards [Lp.coeFn_smul scalar action, hactionAE]
    with mode hsmul hmode
  rw [hsmul]
  exact mul_nonneg hscalar hmode

/-- The missing ordered real-module structure on canonical `L-infinity`,
derived faithfully from the quotient's a.e. order. -/
noncomputable instance canonicalLInfinityIsOrderedModule
    (collision : ResonantThreeWaveMeasure Mode) :
    IsOrderedModule Real (CanonicalLInfinity collision) :=
  IsOrderedModule.of_smul_nonneg fun _scalar hscalar _action haction ↦
    smul_nonnegative collision hscalar haction

/-- Ordered-quotient form of collision quasipositivity. -/
theorem collisionMap_add_two_mul_nonnegative
    (collision : ResonantThreeWaveMeasure Mode)
    (action : CanonicalLInfinity collision)
    (haction : 0 ≤ action) :
    0 ≤ collisionMap collision action + (2 * ‖action‖) • action := by
  rw [← aeNonnegative_iff_nonnegative collision] at haction
  rw [← Lp.coeFn_le]
  filter_upwards [Lp.coeFn_zero Real ∞
      (collisionReferenceMeasure collision),
    Lp.coeFn_add (collisionMap collision action) ((2 * ‖action‖) • action),
    Lp.coeFn_smul (2 * ‖action‖) action,
    collisionMap_add_two_mul_nonnegative_ae collision action haction]
    with mode hzero hadd hsmul hquasi
  simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hzero hadd hsmul
  rw [hzero, hadd, hsmul]
  exact hquasi

end

end ArchonPhysics.ResonantThreeWaveKineticLInfinityPositivePicard
