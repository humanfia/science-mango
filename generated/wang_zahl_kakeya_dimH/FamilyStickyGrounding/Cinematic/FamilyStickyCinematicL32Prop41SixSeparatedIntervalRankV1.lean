import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosFact1BoolParityV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41SixSeparatedIntervalRankV1

open FamilyStickyCinematicL32Prop41MarcusTardosFact1BoolParityV1

/-!
# Canonical rank of six pairwise separated intervals

Six nonempty closed intervals which are pairwise strictly ordered have
distinct left endpoints.  Sorting those endpoints gives an order-preserving
equivalence with `Fin 6`.  A wrapper type is used internally so the lifted
endpoint order cannot conflict with the pre-existing product order on
`Fin 2 x Fin 3`.
-/

structure SixSeparatedIntervals where
  left : K23Edge -> Real
  right : K23Edge -> Real
  left_lt_right : forall e, left e < right e
  pair_ordered : forall {e q}, e ≠ q ->
    right e < left q \/ right q < left e

theorem SixSeparatedIntervals.left_injective (S : SixSeparatedIntervals) :
    Function.Injective S.left := by
  intro e q heq
  by_contra hne
  rcases S.pair_ordered hne with h | h
  · linarith [S.left_lt_right e]
  · linarith [S.left_lt_right q]

structure WrappedEdge where
  edge : K23Edge
deriving Fintype, DecidableEq

def wrappedEdgeEquiv : K23Edge ≃ WrappedEdge where
  toFun e := ⟨e⟩
  invFun e := e.edge
  left_inv _ := rfl
  right_inv _ := rfl

structure SixIntervalRankData (S : SixSeparatedIntervals) where
  rankEquiv : K23Edge ≃ Fin 6
  rank_lt_iff_left_lt : forall e q,
    rankEquiv e < rankEquiv q <-> S.left e < S.left q

noncomputable def SixSeparatedIntervals.rankData
    (S : SixSeparatedIntervals) : SixIntervalRankData S := by
  let leftW : WrappedEdge -> Real := fun e => S.left e.edge
  have hleftW : Function.Injective leftW :=
    S.left_injective.comp wrappedEdgeEquiv.symm.injective
  letI : LinearOrder WrappedEdge := LinearOrder.lift' leftW hleftW
  let E : Fin 6 ≃o WrappedEdge :=
    Fintype.orderIsoFinOfCardEq WrappedEdge (by decide)
  refine
    { rankEquiv := wrappedEdgeEquiv.trans E.symm.toEquiv
      rank_lt_iff_left_lt := ?_ }
  intro e q
  change E.symm ⟨e⟩ < E.symm ⟨q⟩ <-> S.left e < S.left q
  rw [OrderIso.lt_iff_lt]
  rfl

noncomputable def SixSeparatedIntervals.rank (S : SixSeparatedIntervals) :
    K23Edge -> Fin 6 := S.rankData.rankEquiv

theorem SixSeparatedIntervals.rank_injective (S : SixSeparatedIntervals) :
    Function.Injective S.rank := S.rankData.rankEquiv.injective

theorem SixSeparatedIntervals.rank_lt_iff_left_lt
    (S : SixSeparatedIntervals) (e q : K23Edge) :
    S.rank e < S.rank q <-> S.left e < S.left q :=
  S.rankData.rank_lt_iff_left_lt e q

#print axioms SixSeparatedIntervals.left_injective
#print axioms SixSeparatedIntervals.rank_injective
#print axioms SixSeparatedIntervals.rank_lt_iff_left_lt

end FamilyStickyCinematicL32Prop41SixSeparatedIntervalRankV1
