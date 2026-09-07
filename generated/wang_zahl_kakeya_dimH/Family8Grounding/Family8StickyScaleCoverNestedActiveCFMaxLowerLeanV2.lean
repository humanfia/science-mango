import Family8Grounding.Family8StickyScaleCoverActiveFineSameCoarseFiberBodyV1
import Family8Grounding.Family8StickyActiveRestrictedCoarseKatzTaoV1
import Family8Grounding.Family8StickySelectedParentGreedyBlockFrostmanV3
import Family8Grounding.Family8NormalizedCFDividingWitnessBridgeV2

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8StickyScaleCoverNestedActiveCFMaxLowerLeanV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyActiveRestrictedCoarseKatzTaoV1
open Family8StickyScaleCoverActiveFineSameCoarseCoverV1.StickyScaleCover
open Family8StickyScaleCoverActiveFineSameCoarseFiberEquivV1.StickyScaleCover
open Family8StickyScaleCoverActiveFineSameCoarseFiberBodyV1.StickyScaleCover
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover

noncomputable section

namespace StickyScaleCover

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The normalized worst-parent constant can only increase after the two
active-index reindexings used by the literal long-core bounded assembly. -/
theorem parentNormalizedFiberCFMax_le_nestedActiveRestriction
    (S : StickyScaleCover fine rho) :
    parentNormalizedFiberCFMax S ≤
      parentNormalizedFiberCFMax
        (activeFineRestrictedScaleCover (activeFineSameCoarseCover S)) := by
  let T := activeFineSameCoarseCover S
  have hparent (i : {i // i ∈ T.activeFine}) :
      restrictedCoarseEquivActive T
          ((activeFineRestrictedScaleCover T).parent i) =
        ⟨T.parent i.1, T.parent_mem i.1 i.2⟩ := by
    unfold restrictedCoarseEquivActive activeFineRestrictedScaleCover
    exact T.activeCoarse.equivFin.symm_apply_apply
      ⟨T.parent i.1, T.parent_mem i.1 i.2⟩
  let e (q : Fin (activeFineRestrictedScaleCover T).coarseCard) :
      {j // j ∈ (activeFineRestrictedScaleCover T).fiber q} ≃
        {i // i ∈ T.fiber (restrictedCoarseEquivActive T q).1} := by
    classical
    have hiff (j : {i // i ∈ T.activeFine}) :
        j ∈ (activeFineRestrictedScaleCover T).fiber q ↔
          j.1 ∈ T.fiber (restrictedCoarseEquivActive T q).1 := by
      rw [(activeFineRestrictedScaleCover T).mem_fiber, T.mem_fiber]
      constructor
      · intro hj
        refine ⟨j.2, ?_⟩
        have hp := congrArg (restrictedCoarseEquivActive T) hj.2
        rw [hparent] at hp
        exact congrArg Subtype.val hp
      · intro hj
        refine ⟨Finset.mem_univ _, ?_⟩
        apply (restrictedCoarseEquivActive T).injective
        rw [hparent]
        apply Subtype.ext
        exact hj.2
    exact
      (Equiv.subtypeEquivRight hiff).trans
        (Equiv.subtypeSubtypeEquivSubtype fun h =>
          ((T.mem_fiber _ (restrictedCoarseEquivActive T q).1).1 h).1)
  have hbody (q : Fin (activeFineRestrictedScaleCover T).coarseCard)
      (j : {j // j ∈ (activeFineRestrictedScaleCover T).fiber q}) :
      (activeFineRestrictedScaleCover T).fiberFamily q j =
        T.fiberFamily (restrictedCoarseEquivActive T q).1 (e q j) := by
    rfl
  have hrestricted
      (q : {q // q ∈ (activeFineRestrictedScaleCover T).activeCoarse}) :
      parentNormalizedFiberCFAt (activeFineRestrictedScaleCover T) q =
        parentNormalizedFiberCFAt T (restrictedCoarseEquivActive T q.1) := by
    unfold parentNormalizedFiberCFAt
    exact canonicalFrostmanConstant_eq_of_bodyPreservingEquiv
      (e := e q.1)
      (F := (activeFineRestrictedScaleCover T).fiberFamily q.1)
      (G := T.fiberFamily (restrictedCoarseEquivActive T q.1).1)
      (hbody := hbody q.1)
      (K := T.activeCoarseFamily (restrictedCoarseEquivActive T q.1))
  have hsame (k : {k // k ∈ S.activeCoarse}) :
      parentNormalizedFiberCFAt T ⟨k.1, k.2⟩ =
        parentNormalizedFiberCFAt S k := by
    unfold parentNormalizedFiberCFAt
    exact canonicalFrostmanConstant_eq_of_bodyPreservingEquiv
      (e := activeFineSameCoarseFiberEquiv S k.1)
      (F := T.fiberFamily k.1)
      (G := S.fiberFamily k.1)
      (hbody := activeFineSameCoarseFiberEquiv_body S k.1)
      (K := S.activeCoarseFamily k)
  unfold parentNormalizedFiberCFMax
  apply iSup_le
  intro k
  let k' : {k // k ∈ T.activeCoarse} := ⟨k.1, k.2⟩
  let q : {q // q ∈ (activeFineRestrictedScaleCover T).activeCoarse} :=
    ⟨(restrictedCoarseEquivActive T).symm k', by
      rw [activeFineRestrictedScaleCover_activeCoarse]
      exact Finset.mem_univ _⟩
  have hq : restrictedCoarseEquivActive T q.1 = k' :=
    (restrictedCoarseEquivActive T).apply_symm_apply k'
  calc
    parentNormalizedFiberCFAt S k =
        parentNormalizedFiberCFAt T k' := (hsame k).symm
    _ = parentNormalizedFiberCFAt T
          (restrictedCoarseEquivActive T q.1) := by rw [hq]
    _ = parentNormalizedFiberCFAt
          (activeFineRestrictedScaleCover T) q := (hrestricted q).symm
    _ ≤ ⨆ q : {q // q ∈ (activeFineRestrictedScaleCover T).activeCoarse},
          parentNormalizedFiberCFAt (activeFineRestrictedScaleCover T) q :=
      le_iSup _ q

end StickyScaleCover

end
end Family8StickyScaleCoverNestedActiveCFMaxLowerLeanV2
