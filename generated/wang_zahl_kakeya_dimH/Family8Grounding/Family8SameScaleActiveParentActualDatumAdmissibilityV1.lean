import Family8Grounding.Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
import FamilyStickySameRadiusTubeContainmentCarrierV1
import Mathlib.Tactic

/-!
# Admissibility of same-scale active parents

When a sticky cover has the same radius as its fine family, every active
parent contains an active child of that same radius.  Same-radius carrier
rigidity identifies their carriers.  Unit-ball support and overlap-based
essential distinctness therefore pass directly from the original admissible
datum to the literal active-parent datum, with no parent selection,
reindexing, or equality premise.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8SameScaleActiveParentActualDatumAdmissibilityV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickySameRadiusTubeContainmentCarrierV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The literal active-parent datum of a same-scale sticky cover inherits
admissibility from its fine datum. -/
theorem activeParentActualTubeDatum_isAdmissible_of_sameScale
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family delta)
    (Y : Shading D.family.bodyFamily) :
    (activeParentActualTubeDatum S Y).IsAdmissible := by
  classical
  refine
    { delta_pos := hD.delta_pos
      delta_le_half := hD.delta_le_half
      contained_in_unit_ball := ?_
      pairwise_essentiallyDistinct := ?_ }
  · intro p
    obtain ⟨i, hi, hparent⟩ := S.parent_surjective p.1 p.2
    have hchildParent :
        (D.family.tubes i).carrier ⊆ (S.coarse.tubes p.1).carrier := by
      simpa only [hparent] using S.carrier_subset i hi
    have hcarrier :
        (D.family.tubes i).carrier = (S.coarse.tubes p.1).carrier :=
      tubeCarrierEqOfSameRadiusCarrierSubset
        (D.family.tubes i) (S.coarse.tubes p.1) hchildParent
    change (S.coarse.tubes p.1).carrier ⊆
      Metric.closedBall (0 : Space) 1
    rw [← hcarrier]
    exact hD.contained_in_unit_ball i
  · intro p _hp q _hq hpq
    obtain ⟨i, hi, hparentI⟩ := S.parent_surjective p.1 p.2
    obtain ⟨j, hj, hparentJ⟩ := S.parent_surjective q.1 q.2
    have hchildParentI :
        (D.family.tubes i).carrier ⊆ (S.coarse.tubes p.1).carrier := by
      simpa only [hparentI] using S.carrier_subset i hi
    have hchildParentJ :
        (D.family.tubes j).carrier ⊆ (S.coarse.tubes q.1).carrier := by
      simpa only [hparentJ] using S.carrier_subset j hj
    have hcarrierI :
        (D.family.tubes i).carrier = (S.coarse.tubes p.1).carrier :=
      tubeCarrierEqOfSameRadiusCarrierSubset
        (D.family.tubes i) (S.coarse.tubes p.1) hchildParentI
    have hcarrierJ :
        (D.family.tubes j).carrier = (S.coarse.tubes q.1).carrier :=
      tubeCarrierEqOfSameRadiusCarrierSubset
        (D.family.tubes j) (S.coarse.tubes q.1) hchildParentJ
    have hij : i ≠ j := by
      intro hij
      apply hpq
      apply Subtype.ext
      rw [← hparentI, ← hparentJ, hij]
    have hdistinct := hD.pairwise_essentiallyDistinct
      (Set.mem_univ i) (Set.mem_univ j) hij
    change EssentiallyDistinct (S.coarse.tubes p.1) (S.coarse.tubes q.1)
    simpa only [EssentiallyDistinct, ← hcarrierI, ← hcarrierJ] using
      hdistinct

#print axioms activeParentActualTubeDatum_isAdmissible_of_sameScale

end
end Family8SameScaleActiveParentActualDatumAdmissibilityV1
