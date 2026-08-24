import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalMoonOpenSupportSeparationCoreCleanV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualMoonCyclicPortSelectionOnItemsV1RepoV2

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41PairLocalMoonCyclicPortRankTransferCleanV2

open FamilyStickyCinematicL32Prop41MarcusTardosFact1BoolParityV1
open FamilyStickyCinematicL32Prop41PairLocalActualMoonCyclicPortSelectionOnItemsV1
open FamilyStickyCinematicL32Prop41PairLocalMoonOpenSupportSeparationCoreCleanV1
open FamilyStickyCinematicL32Prop41SixSeparatedIntervalRankV1

noncomputable section

def HostRankCyclicPositive (rank : K23Edge -> Fin 6) (h : Fin 2) : Prop :=
  (rank (h, 0) < rank (h, 1) /\ rank (h, 1) < rank (h, 2)) \/
  (rank (h, 1) < rank (h, 2) /\ rank (h, 2) < rank (h, 0)) \/
  (rank (h, 2) < rank (h, 0) /\ rank (h, 0) < rank (h, 1))

theorem innerRank_lt_of_port_lt
    (S : PairLocalMoonOpenSupportData) (port : K23Edge -> Real)
    (hport : forall e, port e ∈ Ioo (S.left e) (S.right e))
    {e q : K23Edge} (heq : e ≠ q) (hlt : port e < port q) :
    S.innerSeparatedIntervals.rank e < S.innerSeparatedIntervals.rank q := by
  rw [S.innerSeparatedIntervals.rank_lt_iff_left_lt]
  rcases S.pair_ordered_le heq with hforward | hbackward
  · have heInner := S.innerLeft_lt_innerRight e
    have heInnerRight := S.innerRight_lt_right e
    have hqInnerLeft := S.left_lt_innerLeft q
    change S.innerLeft e < S.innerLeft q
    linarith
  · rcases hport e with ⟨heLeft, heRight⟩
    rcases hport q with ⟨hqLeft, hqRight⟩
    exfalso
    linarith

theorem hostRankCyclicPositive_of_cyclic_ports
    (S : PairLocalMoonOpenSupportData) (port : K23Edge -> Real)
    (hport : forall e, port e ∈ Ioo (S.left e) (S.right e))
    (hcyclic : forall h, PortCyclicPositive (fun j => port (h, j))) :
    forall h, HostRankCyclicPositive S.innerSeparatedIntervals.rank h := by
  intro h
  have hedge_ne (j k : Fin 3) (hjk : j ≠ k) : (h, j) ≠ (h, k) := by
    intro heq
    exact hjk (congrArg Prod.snd heq)
  rcases hcyclic h with h012 | h120 | h201
  · exact Or.inl ⟨
      innerRank_lt_of_port_lt S port hport (hedge_ne 0 1 (by decide)) h012.1,
      innerRank_lt_of_port_lt S port hport (hedge_ne 1 2 (by decide)) h012.2⟩
  · exact Or.inr (Or.inl ⟨
      innerRank_lt_of_port_lt S port hport (hedge_ne 1 2 (by decide)) h120.1,
      innerRank_lt_of_port_lt S port hport (hedge_ne 2 0 (by decide)) h120.2⟩)
  · exact Or.inr (Or.inr ⟨
      innerRank_lt_of_port_lt S port hport (hedge_ne 2 0 (by decide)) h201.1,
      innerRank_lt_of_port_lt S port hport (hedge_ne 0 1 (by decide)) h201.2⟩)

#print axioms innerRank_lt_of_port_lt
#print axioms hostRankCyclicPositive_of_cyclic_ports

end

end FamilyStickyCinematicL32Prop41PairLocalMoonCyclicPortRankTransferCleanV2
