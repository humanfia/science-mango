import Family8Grounding.Family8Def212ConvexWolffAtEveryScaleV2
import Family8Grounding.Family8SelectedFiberJohnCanonicalCoherentFactorV1

/-!
# Exact Definition 2.12 gives compositional source parents

This file supplies the source-hierarchy certificate needed before one can
honestly restrict a coherent sticky cover to the descendants of a selected
parent.  Doubled-parent partitioning identifies, at every pair of scales, the
direct parent of an original fine tube with its cross-scale parent.  The
surjectivity already stored by `CoherentStickyMultiscaleCover` then forces the
cross-scale parent maps to compose.

The result concerns the actual source cover only.  It deliberately does not
place the canonical identity-radius cover on a contracted-John proxy and does
not assert a proxy transport theorem without a cross-scale proxy-nesting
lemma.
-/

open Set
open scoped ENNReal NNReal

namespace Family8ExactDef212CompositionalParentsV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8SelectedFiberJohnCanonicalCoherentFactorV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- At any two scales, doubled-parent partitioning at the upper scale forces
the upper cover's direct fine parent to equal the coherent cross-scale parent
of the lower cover's direct fine parent. -/
theorem fine_parent_compatible_of_doubledParentPartitioning
    (C : CoherentStickyMultiscaleCover fine)
    (tau rho : NNReal) (hdeltaTau : delta <= tau)
    (hTauRho : tau <= rho) (hRhoOne : rho <= 1)
    (hpartition : IsDoubledParentPartitioning
      (C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne))
    (i : iota)
    (hi : i ∈ (C.base.cover tau hdeltaTau
      (hTauRho.trans hRhoOne)).activeFine) :
    (C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne).parent i =
      C.parent tau rho hdeltaTau hTauRho hRhoOne
        ((C.base.cover tau hdeltaTau
          (hTauRho.trans hRhoOne)).parent i) := by
  let T := C.base.cover tau hdeltaTau (hTauRho.trans hRhoOne)
  let R := C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne
  let l : Fin R.coarseCard :=
    C.parent tau rho hdeltaTau hTauRho hRhoOne (T.parent i)
  have hiR : i ∈ R.activeFine := by
    rw [R.activeFine_eq_refined, ← T.activeFine_eq_refined]
    exact hi
  have hk : R.parent i ∈ R.activeCoarse := R.parent_mem i hiR
  have hTi : T.parent i ∈ T.activeCoarse := T.parent_mem i hi
  have hl : l ∈ R.activeCoarse := by
    simpa only [l, R, T] using
      C.parent_mem tau rho hdeltaTau hTauRho hRhoOne
        (T.parent i) hTi
  change R.parent i = l
  by_contra hne
  have hik : i ∈ doubledFiber R (R.parent i) := by
    exact fiber_subset_doubledFiber R (R.parent i)
      ((R.mem_fiber i (R.parent i)).2 ⟨hiR, rfl⟩)
  have hil : i ∈ doubledFiber R l := by
    rw [mem_doubledFiber]
    refine ⟨hiR, ?_⟩
    have hFineCross :
        (fine.tubes i).carrier ⊆ (R.coarse.tubes l).carrier := by
      simpa only [l, R, T] using
        (T.carrier_subset i hi).trans
          (C.carrier_subset tau rho hdeltaTau hTauRho hRhoOne
            (T.parent i) hTi)
    exact hFineCross.trans
      (carrier_subset_twoFoldTubeCarrier (R.coarse.tubes l))
  exact (Finset.disjoint_left.mp
    (hpartition (R.parent i) hk l hl hne) hik hil)

/-- All-scale doubled-parent partitioning forces the cross-scale parent maps
of the source coherent cover to compose. -/
theorem hasCompositionalParents_of_doubledParentPartitioning
    (C : CoherentStickyMultiscaleCover fine)
    (hpartition : ∀ (rho : NNReal) (hdeltaRho : delta <= rho)
      (hRhoOne : rho <= 1),
      IsDoubledParentPartitioning
        (C.base.cover rho hdeltaRho hRhoOne)) :
    HasCompositionalParents C := by
  intro r s t hdeltaR hRS hST hTOne k hk
  let R := C.base.cover r hdeltaR (hRS.trans (hST.trans hTOne))
  let S := C.base.cover s (hdeltaR.trans hRS) (hST.trans hTOne)
  let T := C.base.cover t
    (hdeltaR.trans (hRS.trans hST)) hTOne
  obtain ⟨i, hi, hik⟩ := R.parent_surjective k hk
  have hiS : i ∈ S.activeFine := by
    rw [S.activeFine_eq_refined, ← R.activeFine_eq_refined]
    exact hi
  have hrs := fine_parent_compatible_of_doubledParentPartitioning
    C r s hdeltaR hRS (hST.trans hTOne)
    (hpartition s (hdeltaR.trans hRS) (hST.trans hTOne)) i hi
  have hst := fine_parent_compatible_of_doubledParentPartitioning
    C s t (hdeltaR.trans hRS) hST hTOne
    (hpartition t (hdeltaR.trans (hRS.trans hST)) hTOne) i hiS
  have hrt := fine_parent_compatible_of_doubledParentPartitioning
    C r t hdeltaR (hRS.trans hST) hTOne
    (hpartition t (hdeltaR.trans (hRS.trans hST)) hTOne) i hi
  have hrs' : S.parent i =
      C.parent r s hdeltaR hRS (hST.trans hTOne) k := by
    simpa only [R, S, hik] using hrs
  have hrt' : T.parent i =
      C.parent r t hdeltaR (hRS.trans hST) hTOne k := by
    simpa only [R, T, hik] using hrt
  calc
    C.parent s t (hdeltaR.trans hRS) hST hTOne
        (C.parent r s hdeltaR hRS (hST.trans hTOne) k) =
      C.parent s t (hdeltaR.trans hRS) hST hTOne (S.parent i) := by
        rw [hrs']
    _ = T.parent i := by
      simpa only [S, T] using hst.symm
    _ = C.parent r t hdeltaR (hRS.trans hST) hTOne k := hrt'

/-- The exact Definition 2.12 input package therefore supplies the missing
compositional-parent certificate for its coherent source cover. -/
theorem hasCompositionalParents_of_exactScaleDef212Inputs
    (C : CoherentStickyMultiscaleCover fine) {K : NNReal}
    (H : ExactScaleDef212Inputs C.base K) :
    HasCompositionalParents C :=
  hasCompositionalParents_of_doubledParentPartitioning C
    H.doubled_parent_partitioning

/-- With exact Definition 2.12 inputs, every intermediate ancestor of a
selected `tau`-parent remains a descendant of the same selected `rho`-parent.
This is the directly consumable source-subtree readiness statement. -/
theorem intermediate_parent_remains_in_selected_subtree_of_exactScaleDef212Inputs
    (C : CoherentStickyMultiscaleCover fine) {K : NNReal}
    (H : ExactScaleDef212Inputs C.base K)
    (tau rho : NNReal) (hdeltaTau : delta <= tau)
    (hTauRho : tau <= rho) (hRhoOne : rho <= 1)
    (sigma : NNReal) (hTauSigma : tau <= sigma)
    (hSigmaRho : sigma <= rho)
    (i : Fin ((C.base.cover tau hdeltaTau
      (hTauRho.trans hRhoOne)).coarseCard))
    (hi : i ∈ (C.base.cover tau hdeltaTau
      (hTauRho.trans hRhoOne)).activeCoarse)
    (q : Fin ((C.base.cover rho (hdeltaTau.trans hTauRho)
      hRhoOne).coarseCard))
    (hiq : C.parent tau rho hdeltaTau hTauRho hRhoOne i = q) :
    C.parent sigma rho (hdeltaTau.trans hTauSigma) hSigmaRho hRhoOne
        (C.parent tau sigma hdeltaTau hTauSigma
          (hSigmaRho.trans hRhoOne) i) = q :=
  intermediate_parent_remains_in_selected_subtree C
    (hasCompositionalParents_of_exactScaleDef212Inputs C H)
    hdeltaTau hTauRho hRhoOne sigma hTauSigma hSigmaRho i hi q hiq


/-- Every index retained by the bad-parent fresh selector has a coherent
source ancestor at every intermediate scale, and that ancestor remains below
the same selected upper parent.  The nested subtype `{j // j ∈ selected}` is
definitionally the index type of the restricted fresh successor datum; the
claim intentionally stays on the source hierarchy, before John/proxy
transport. -/
theorem badParentFresh_index_intermediate_source_parent_eq_of_exactScaleDef212Inputs
    (C : CoherentStickyMultiscaleCover fine) {K : NNReal}
    (H : ExactScaleDef212Inputs C.base K)
    (tau rho : NNReal) (hdeltaTau : delta <= tau)
    (hTauRho : tau <= rho) (hRhoOne : rho <= 1)
    (sigma : NNReal) (hTauSigma : tau <= sigma)
    (hSigmaRho : sigma <= rho)
    (q : {q // q ∈ (C.intervalScaleCover tau rho hdeltaTau
      hTauRho hRhoOne).activeCoarse})
    (selected : Finset {i // i ∈
      (C.intervalScaleCover tau rho hdeltaTau
        hTauRho hRhoOne).fiber q.1})
    (x : {j // j ∈ selected}) :
    C.parent sigma rho (hdeltaTau.trans hTauSigma) hSigmaRho hRhoOne
        (C.parent tau sigma hdeltaTau hTauSigma
          (hSigmaRho.trans hRhoOne) x.1.1) = q.1 := by
  let I := C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne
  have hxFiber : x.1.1 ∈ I.fiber q.1 := x.1.2
  have hxData := (I.mem_fiber x.1.1 q.1).1 hxFiber
  exact
    intermediate_parent_remains_in_selected_subtree_of_exactScaleDef212Inputs
      C H tau rho hdeltaTau hTauRho hRhoOne sigma hTauSigma hSigmaRho
      x.1.1 hxData.1 q.1 hxData.2

#print axioms fine_parent_compatible_of_doubledParentPartitioning
#print axioms hasCompositionalParents_of_doubledParentPartitioning
#print axioms hasCompositionalParents_of_exactScaleDef212Inputs
#print axioms intermediate_parent_remains_in_selected_subtree_of_exactScaleDef212Inputs
#print axioms badParentFresh_index_intermediate_source_parent_eq_of_exactScaleDef212Inputs

end
end Family8ExactDef212CompositionalParentsV1
