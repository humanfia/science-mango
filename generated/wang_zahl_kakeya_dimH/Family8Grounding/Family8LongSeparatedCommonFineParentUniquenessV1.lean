import Family8Grounding.Family8CompatibleStickyScalePairCUniformFrostmanV1
import Family8Grounding.Family8TubeClosedThickeningInsideTwoFoldV2
import Submission.Kakeya.ConvexFactoring.TubeCommonSegment

/-!
# Parent uniqueness for a long-separated pair of sticky covers

If two active lower parents share their fine tubes with an upper cover and
`4 * r <= R`, then upper doubled-parent partitioning forces every fine tube in
one lower fibre to have the same upper parent.  The proof uses the actual
common fine tube supplied by lower-parent surjectivity; it does not assume a
cross-scale parent map.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8LongSeparatedCommonFineParentUniquenessV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8TubeClosedThickeningInsideTwoFoldV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta r R : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {lower : StickyScaleCover fine r}
  {upper : StickyScaleCover fine R}

/-- One active lower fibre has a genuine common upper parent.  Besides parent
uniqueness, the result records the `4r`-neighborhood containment used to
construct a buffered cross-scale cover. -/
theorem exists_upperParent_of_lower_active
    (hr : 0 < r) (hsep : 4 * r <= R)
    (hpartition : IsDoubledParentPartitioning upper)
    (q : Fin lower.coarseCard) (hq : q ∈ lower.activeCoarse) :
    exists k : Fin upper.coarseCard,
      k ∈ upper.activeCoarse ∧
      (lower.coarse.tubes q).carrier ⊆
        Metric.cthickening (4 * (r : Real))
          (upper.coarse.tubes k).carrier ∧
      forall i, i ∈ lower.fiber q -> upper.parent i = k := by
  obtain ⟨j, hjActive, hjParent⟩ := lower.parent_surjective q hq
  let k : Fin upper.coarseCard := upper.parent j
  have hjUpperActive : j ∈ upper.activeFine := by
    rw [upper.activeFine_eq_refined, ← lower.activeFine_eq_refined]
    exact hjActive
  have hkActive : k ∈ upper.activeCoarse := by
    exact upper.parent_mem j hjUpperActive
  have hjLower :
      (fine.tubes j).carrier ⊆ (lower.coarse.tubes q).carrier := by
    simpa only [hjParent] using lower.carrier_subset j hjActive
  have hjUpper :
      (fine.tubes j).carrier ⊆ (upper.coarse.tubes k).carrier := by
    simpa only [k] using upper.carrier_subset j hjUpperActive
  have hnear :
      (lower.coarse.tubes q).carrier ⊆
        Metric.cthickening (4 * (r : Real))
          (upper.coarse.tubes k).carrier :=
    Tube.carrier_subset_four_mul_cthickening_of_commonFineTube
      (fine.tubes j) (lower.coarse.tubes q) (upper.coarse.tubes k)
        hjLower hjUpper
  refine ⟨k, hkActive, hnear, ?_⟩
  intro i hiFiber
  have hiData := (lower.mem_fiber i q).1 hiFiber
  have hiUpperActive : i ∈ upper.activeFine := by
    rw [upper.activeFine_eq_refined, ← lower.activeFine_eq_refined]
    exact hiData.1
  have hiOwnActive : upper.parent i ∈ upper.activeCoarse :=
    upper.parent_mem i hiUpperActive
  have hfourPos : 0 < 4 * r := by positivity
  have hR : 0 < R := hfourPos.trans_le hsep
  have hnearToDouble :
      Metric.cthickening (4 * (r : Real))
          (upper.coarse.tubes k).carrier ⊆
        twoFoldTubeCarrier (upper.coarse.tubes k) := by
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using
      (cthickening_subset_twoFoldTubeCarrier_of_subset_of_le
        hR (upper.coarse.tubes k) (A := (upper.coarse.tubes k).carrier)
          Set.Subset.rfl hsep)
  have hiChosenDouble : i ∈ doubledFiber upper k := by
    rw [mem_doubledFiber]
    refine ⟨hiUpperActive, ?_⟩
    have hiLower :
        (fine.tubes i).carrier ⊆ (lower.coarse.tubes q).carrier := by
      simpa only [hiData.2] using lower.carrier_subset i hiData.1
    exact hiLower.trans (hnear.trans hnearToDouble)
  have hiOwnDouble : i ∈ doubledFiber upper (upper.parent i) :=
    fiber_subset_doubledFiber upper (upper.parent i)
      ((upper.mem_fiber i (upper.parent i)).2 ⟨hiUpperActive, rfl⟩)
  by_contra hne
  exact (Finset.disjoint_left.mp
    (hpartition (upper.parent i) hiOwnActive k hkActive hne)
      hiOwnDouble hiChosenDouble).elim

#print axioms exists_upperParent_of_lower_active

end
end Family8LongSeparatedCommonFineParentUniquenessV1
