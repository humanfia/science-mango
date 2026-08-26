import FamilyStickyGrounding.FamilyStickyKatzTaoAtEveryScaleOverlapMultiplicityConsumerV1
import FamilyStickyGrounding.FamilyStickyHierarchyEndpointPrefixShadingTransportV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyKatzTaoParentAggregatedMultiplicityConsumerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyKatzTaoAtEveryScaleOverlapMultiplicityConsumerV1
open FamilyStickyKatzTaoAtEveryScaleOverlapMultiplicityConsumerV1.KatzTaoOverlapRowGeometry
open FamilyStickyFinalMultiscaleAssemblyCertificateV1

noncomputable section

/-!
# Returning the coarse Katz--Tao multiplicity bound to the fine shading

Parent aggregation preserves the literal shaded union, while the already
proved fibre-cardinality estimate controls how much summed shading mass can
be lost when fine pieces inside one parent are merged.  Consequently an
average-multiplicity bound for the parent-aggregated coarse shading returns
to the active fine shading with exactly the maximum parent-fibre cardinality
as loss.

Combining this transport with the first Katz--Tao overlap consumer closes the
coarse-to-fine deterministic seam at any supplied scale.  The geometric row
certificate remains explicit; no multiplicity conclusion is stored in it.
-/

/-- Parent aggregation transports average multiplicity back to the active
fine shading with the literal uniform fibre-cardinality loss. -/
theorem activeFineShading_averageMultiplicity_le_nsmul_parent
    {delta rho : NNReal} {iota : Type*}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily) (M : Nat)
    (hM : forall k : {k // k ∈ S.activeCoarse},
      ((activeIndexFactorization S).fiber k).card <= M) :
    (activeFineShading S Y).averageMultiplicity <=
      M • (parentAggregatedShading S Y).averageMultiplicity := by
  unfold Shading.averageMultiplicity
  calc
    (activeFineShading S Y).shadingMass /
          volume (activeFineShading S Y).shadedUnion <=
      (M • (parentAggregatedShading S Y).shadingMass) /
          volume (activeFineShading S Y).shadedUnion :=
      ENNReal.div_le_div_right
        (activeFineShading_shadingMass_le_nsmul_parent_of_fiberCard_le
          S Y M hM) _
    _ = (M • (parentAggregatedShading S Y).shadingMass) /
          volume (parentAggregatedShading S Y).shadedUnion := by
      rw [parentAggregatedShading_shadedUnion S Y]
    _ = M • ((parentAggregatedShading S Y).shadingMass /
          volume (parentAggregatedShading S Y).shadedUnion) := by
      simp only [nsmul_eq_mul, div_eq_mul_inv]
      ac_rfl

/-- At one actual Sticky scale, Katz--Tao non-concentration and overlap-row
geometry for the parent shading imply a fine-shading multiplicity estimate.
The only transport loss is the stated fibre-cardinality bound. -/
theorem activeFine_averageMultiplicity_le_of_isKatzTaoAtScale
    {delta rho : NNReal} {iota : Type*}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (S : StickyScaleCover fine rho) {C : ENNReal}
    (hKT : S.IsKatzTaoAtScale C)
    (Y : Shading fine.bodyFamily) (M : Nat)
    (hM : forall k : {k // k ∈ S.activeCoarse},
      ((activeIndexFactorization S).fiber k).card <= M)
    (R : KatzTaoOverlapRowGeometry (parentAggregatedShading S Y)) :
    (activeFineShading S Y).averageMultiplicity <=
      M • (C * R.scaleFactor) := by
  calc
    (activeFineShading S Y).averageMultiplicity <=
        M • (parentAggregatedShading S Y).averageMultiplicity :=
      activeFineShading_averageMultiplicity_le_nsmul_parent S Y M hM
    _ <= M • (C * R.scaleFactor) := by
      simpa only [nsmul_eq_mul] using
        (mul_le_mul' le_rfl
          (FamilyStickyKatzTaoAtEveryScaleOverlapMultiplicityConsumerV1.StickyScaleCover.averageMultiplicity_le_of_isKatzTaoAtScale
            S hKT (parentAggregatedShading S Y) R))

/-- At every requested radius, the all-scale Katz--Tao predicate supplies
the non-concentration input automatically. -/
theorem activeFine_averageMultiplicity_le_of_isKatzTaoAtEveryScale
    {delta : NNReal} {iota : Type*}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (cover : StickyMultiscaleCover fine) {C : ENNReal}
    (hKT : cover.IsKatzTaoAtEveryScale C)
    (rho : NNReal) (hdelta : delta <= rho) (hrho : rho <= 1)
    (Y : Shading fine.bodyFamily) (M : Nat)
    (hM : forall k :
      {k // k ∈ (cover.cover rho hdelta hrho).activeCoarse},
      ((activeIndexFactorization (cover.cover rho hdelta hrho)).fiber k).card <= M)
    (R : KatzTaoOverlapRowGeometry
      (parentAggregatedShading (cover.cover rho hdelta hrho) Y)) :
    (activeFineShading (cover.cover rho hdelta hrho) Y).averageMultiplicity <=
      M • (C * R.scaleFactor) := by
  exact activeFine_averageMultiplicity_le_of_isKatzTaoAtScale
    (cover.cover rho hdelta hrho) (hKT rho hdelta hrho) Y M hM R

/-! ## Final multiscale assembly specialization -/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry H}
  {P : FamilyStickyHierarchyPreMotionHullTestSupportV1.HierarchyPackingPlan.Plan H}
  {C : FamilyStickyScaleChainCoherentIntervalProducerV1.CoherentStickyMultiscaleCover
    (H.effectiveFamily 0)}
  {S : FamilyStickyDividingScalesFiniteStoppingV1.FiniteScaleSequence
    (H.effectiveRadius 0) depth}
  {epsilon : Real}
  {massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal}

/-- The final assembly supplies the all-scale Katz--Tao input.  A concrete
parent-row geometry and a literal fibre-card cap now yield an estimate on the
original active fine shading, not merely on its coarse aggregation. -/
theorem finalAssembly_activeFine_averageMultiplicity_le
    (A : Certificate H G P C S epsilon
      massLoss bodyLoss katzTaoLoss frostmanError katzTaoError)
    (rho : NNReal) (hdelta : H.effectiveRadius 0 <= rho) (hrho : rho <= 1)
    (Y : Shading (H.effectiveFamily 0).bodyFamily) (M : Nat)
    (hM : forall k : {k // k ∈ (C.base.cover rho hdelta hrho).activeCoarse},
      ((activeIndexFactorization (C.base.cover rho hdelta hrho)).fiber k).card <= M)
    (R : KatzTaoOverlapRowGeometry
      (parentAggregatedShading (C.base.cover rho hdelta hrho) Y)) :
    (activeFineShading (C.base.cover rho hdelta hrho) Y).averageMultiplicity <=
      M • ((katzTaoLoss * katzTaoError) * R.scaleFactor) := by
  exact activeFine_averageMultiplicity_le_of_isKatzTaoAtEveryScale
    C.base A.stickyAtEveryScale.katzTao rho hdelta hrho Y M hM R

#print axioms activeFineShading_averageMultiplicity_le_nsmul_parent
#print axioms activeFine_averageMultiplicity_le_of_isKatzTaoAtScale
#print axioms activeFine_averageMultiplicity_le_of_isKatzTaoAtEveryScale
#print axioms finalAssembly_activeFine_averageMultiplicity_le

end

end FamilyStickyKatzTaoParentAggregatedMultiplicityConsumerV1
