import Family8Grounding.Family8LongSeparatedCommonFineParentUniquenessV1
import Submission.Kakeya.ConvexFactoring.MultiscaleTubeHierarchy

/-!
# A genuine buffered compatible pair from two long-separated covers

For each active lower parent, choose one of its actual fine children.  The
upper parent of that child is forced to be the upper parent of every sibling
by `Family8LongSeparatedCommonFineParentUniquenessV1`.  Buffering each upper
tube by `4r` then turns the proved closed-neighborhood containment into the
literal carrier containment required by `CompatibleStickyScalePair`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8LongSeparatedBufferedCompatiblePairV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CompatibleStickyScalePairCUniformFrostmanV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8LongSeparatedCommonFineParentUniquenessV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta r R : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {lower : StickyScaleCover fine r}
  {upper : StickyScaleCover fine R}

/-- An actual fine child selected from an active lower fibre.  On inactive
indices a fixed refined fine tube is used only to make the map total. -/
noncomputable def selectedLowerFine
    (hFine : fine.refinement.refined.Nonempty)
    (q : Fin lower.coarseCard) : iota :=
  if hq : q ∈ lower.activeCoarse then
    Classical.choose (lower.parent_surjective q hq)
  else Classical.choose hFine

theorem selectedLowerFine_mem_fiber
    (hFine : fine.refinement.refined.Nonempty)
    (q : Fin lower.coarseCard) (hq : q ∈ lower.activeCoarse) :
    selectedLowerFine (lower := lower) hFine q ∈ lower.fiber q := by
  rw [lower.mem_fiber]
  simp only [selectedLowerFine, dif_pos hq]
  exact Classical.choose_spec (lower.parent_surjective q hq)

/-- The cross-parent map obtained from the selected actual fine child. -/
noncomputable def selectedUpperParent
    (hFine : fine.refinement.refined.Nonempty) :
    Fin lower.coarseCard -> Fin upper.coarseCard :=
  fun q => upper.parent (selectedLowerFine (lower := lower) hFine q)

/-- Buffer only the coarse upper tubes; the fine family, active sets and
parent assignment remain literally unchanged. -/
noncomputable def bufferedUpperScaleCover
    (upper : StickyScaleCover fine R) (q : NNReal) :
    StickyScaleCover fine (R + q) where
  coarseCard := upper.coarseCard
  coarse := upper.coarse.buffer q
  activeFine := upper.activeFine
  activeCoarse := upper.activeCoarse
  parent := upper.parent
  activeFine_eq_refined := upper.activeFine_eq_refined
  activeCoarse_eq_refined := upper.activeCoarse_eq_refined
  parent_mem := upper.parent_mem
  parent_surjective := upper.parent_surjective
  carrier_subset := by
    intro i hi
    simpa only [UniformTubeFamily.buffer_tubes] using
      (upper.carrier_subset i hi).trans
        (Tube.carrier_subset_buffer (upper.coarse.tubes (upper.parent i)) q)

@[simp] theorem bufferedUpperScaleCover_parent
    (upper : StickyScaleCover fine R) (q : NNReal) (i : iota) :
    (bufferedUpperScaleCover upper q).parent i = upper.parent i :=
  rfl

@[simp] theorem bufferedUpperScaleCover_activeFine
    (upper : StickyScaleCover fine R) (q : NNReal) :
    (bufferedUpperScaleCover upper q).activeFine = upper.activeFine :=
  rfl

@[simp] theorem bufferedUpperScaleCover_activeCoarse
    (upper : StickyScaleCover fine R) (q : NNReal) :
    (bufferedUpperScaleCover upper q).activeCoarse = upper.activeCoarse :=
  rfl

/-- Parent uniqueness identifies every fine child with the selected-child
cross parent. -/
theorem upper_parent_eq_selectedUpperParent
    (hFine : fine.refinement.refined.Nonempty)
    (hr : 0 < r) (hsep : 4 * r <= R)
    (hpartition : IsDoubledParentPartitioning upper)
    (q : Fin lower.coarseCard) (hq : q ∈ lower.activeCoarse)
    (i : iota) (hi : i ∈ lower.fiber q) :
    upper.parent i = selectedUpperParent (lower := lower) (upper := upper) hFine q := by
  obtain ⟨k, _hk, _hnear, hall⟩ :=
    exists_upperParent_of_lower_active hr hsep hpartition q hq
  have hselected :
      selectedLowerFine (lower := lower) hFine q ∈ lower.fiber q :=
    selectedLowerFine_mem_fiber hFine q hq
  calc
    upper.parent i = k := hall i hi
    _ = upper.parent (selectedLowerFine (lower := lower) hFine q) :=
      (hall _ hselected).symm
    _ = selectedUpperParent (lower := lower) (upper := upper) hFine q := rfl

/-- The selected cross-parent map is surjective on active upper parents. -/
theorem selectedUpperParent_surjective
    (hFine : fine.refinement.refined.Nonempty)
    (hr : 0 < r) (hsep : 4 * r <= R)
    (hpartition : IsDoubledParentPartitioning upper)
    (k : Fin upper.coarseCard) (hk : k ∈ upper.activeCoarse) :
    exists q, q ∈ lower.activeCoarse ∧
      selectedUpperParent (lower := lower) (upper := upper) hFine q = k := by
  obtain ⟨i, hiUpper, hiParent⟩ := upper.parent_surjective k hk
  have hiLower : i ∈ lower.activeFine := by
    rw [lower.activeFine_eq_refined, ← upper.activeFine_eq_refined]
    exact hiUpper
  let q : Fin lower.coarseCard := lower.parent i
  have hq : q ∈ lower.activeCoarse := lower.parent_mem i hiLower
  have hiFiber : i ∈ lower.fiber q :=
    (lower.mem_fiber i q).2 ⟨hiLower, rfl⟩
  refine ⟨q, hq, ?_⟩
  exact (upper_parent_eq_selectedUpperParent hFine hr hsep hpartition
    q hq i hiFiber).symm.trans hiParent

/-- The honest compatible pair with effective upper radius `R + 4r`. -/
noncomputable def longSeparatedBufferedPair
    (hFine : fine.refinement.refined.Nonempty)
    (hr : 0 < r) (hsep : 4 * r <= R)
    (hpartition : IsDoubledParentPartitioning upper) :
    CompatibleStickyScalePair lower
      (bufferedUpperScaleCover upper (4 * r)) where
  crossParent := selectedUpperParent (lower := lower) (upper := upper) hFine
  crossParent_mem := by
    intro q hq
    have hselected := selectedLowerFine_mem_fiber
      (lower := lower) hFine q hq
    have hselectedLower := (lower.mem_fiber _ q).1 hselected |>.1
    have hselectedUpper :
        selectedLowerFine (lower := lower) hFine q ∈ upper.activeFine := by
      rw [upper.activeFine_eq_refined, ← lower.activeFine_eq_refined]
      exact hselectedLower
    exact upper.parent_mem _ hselectedUpper
  crossParent_surjective := by
    intro k hk
    exact selectedUpperParent_surjective hFine hr hsep hpartition k hk
  carrier_subset := by
    intro q hq
    have hjFiber := selectedLowerFine_mem_fiber
      (lower := lower) hFine q hq
    have hjData := (lower.mem_fiber _ q).1 hjFiber
    have hjUpperActive :
        selectedLowerFine (lower := lower) hFine q ∈ upper.activeFine := by
      rw [upper.activeFine_eq_refined, ← lower.activeFine_eq_refined]
      exact hjData.1
    have hjLower :
        (fine.tubes (selectedLowerFine (lower := lower) hFine q)).carrier ⊆
          (lower.coarse.tubes q).carrier := by
      simpa only [hjData.2] using
        lower.carrier_subset
          (selectedLowerFine (lower := lower) hFine q) hjData.1
    have hjUpper :
        (fine.tubes (selectedLowerFine (lower := lower) hFine q)).carrier ⊆
          (upper.coarse.tubes
            (selectedUpperParent (lower := lower) (upper := upper) hFine q)).carrier := by
      exact upper.carrier_subset _ hjUpperActive
    change (lower.coarse.tubes q).carrier ⊆
      ((upper.coarse.tubes
        (selectedUpperParent (lower := lower) (upper := upper) hFine q)).buffer
          (4 * r)).carrier
    rw [Tube.buffer_carrier]
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using
      (Tube.carrier_subset_four_mul_cthickening_of_commonFineTube
        (fine.tubes (selectedLowerFine (lower := lower) hFine q))
        (lower.coarse.tubes q)
        (upper.coarse.tubes
          (selectedUpperParent (lower := lower) (upper := upper) hFine q))
        hjLower hjUpper)
  fine_parent_commutes := by
    intro i hi
    have hq : lower.parent i ∈ lower.activeCoarse := lower.parent_mem i hi
    have hiFiber : i ∈ lower.fiber (lower.parent i) :=
      (lower.mem_fiber i (lower.parent i)).2 ⟨hi, rfl⟩
    exact upper_parent_eq_selectedUpperParent hFine hr hsep hpartition
      (lower.parent i) hq i hiFiber

#print axioms selectedLowerFine_mem_fiber
#print axioms bufferedUpperScaleCover
#print axioms upper_parent_eq_selectedUpperParent
#print axioms selectedUpperParent_surjective
#print axioms longSeparatedBufferedPair

end
end Family8LongSeparatedBufferedCompatiblePairV1
