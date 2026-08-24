import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41RankedIntervalSamplesV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41PairLocalMoonOpenSupportSeparationCoreCleanV1

open FamilyStickyCinematicL32Prop41MarcusTardosFact1BoolParityV1
open FamilyStickyCinematicL32Prop41RankedIntervalSamplesV1
open FamilyStickyCinematicL32Prop41SixSeparatedIntervalRankV1

noncomputable section

/-!
# Pair-local moon signs force separation of all six open supports

Incident supports are supplied disjoint.  If two nonincident supports met,
the two own-positive and two foreign-nonpositive graph inequalities would
force the two host graphs to be strictly above one another.  A centered
one-third shrink then turns possible endpoint contact into strict separation.
-/

structure PairLocalMoonOpenSupportData where
  A : Real
  B : Real
  left : K23Edge -> Real
  right : K23Edge -> Real
  left_mem : forall e, left e ∈ Icc A B
  right_mem : forall e, right e ∈ Icc A B
  left_lt_right : forall e, left e < right e
  hostGraph : Fin 2 -> Real -> Real
  neighborGraph : Fin 3 -> Real -> Real
  positive_iff : forall e theta, theta ∈ Icc A B ->
    (theta ∈ Ioo (left e) (right e) <->
      neighborGraph e.2 theta < hostGraph e.1 theta)
  sameHost_disjoint : forall h : Fin 2, forall {j k : Fin 3}, j ≠ k ->
    ¬ (Ioo (left (h, j)) (right (h, j)) ∩
      Ioo (left (h, k)) (right (h, k))).Nonempty
  sameNeighbor_disjoint : forall j : Fin 3, forall {h k : Fin 2}, h ≠ k ->
    ¬ (Ioo (left (h, j)) (right (h, j)) ∩
      Ioo (left (k, j)) (right (k, j))).Nonempty

namespace PairLocalMoonOpenSupportData

theorem interval_subset_Icc
    (S : PairLocalMoonOpenSupportData) (e : K23Edge) :
    Ioo (S.left e) (S.right e) ⊆ Icc S.A S.B := by
  intro theta htheta
  exact ⟨(S.left_mem e).1.trans htheta.1.le,
    htheta.2.le.trans (S.right_mem e).2⟩

theorem nonincident_disjoint
    (S : PairLocalMoonOpenSupportData)
    {e q : K23Edge} (hhost : e.1 ≠ q.1) (_hneighbor : e.2 ≠ q.2) :
    ¬ (Ioo (S.left e) (S.right e) ∩
      Ioo (S.left q) (S.right q)).Nonempty := by
  rintro ⟨theta, hthetaE, hthetaQ⟩
  have hthetaAB : theta ∈ Icc S.A S.B := S.interval_subset_Icc e hthetaE
  have hnotQE : theta ∉ Ioo (S.left (q.1, e.2)) (S.right (q.1, e.2)) := by
    intro hthetaQE
    exact S.sameNeighbor_disjoint e.2 hhost
      ⟨theta, hthetaE, hthetaQE⟩
  have hnotEQ : theta ∉ Ioo (S.left (e.1, q.2)) (S.right (e.1, q.2)) := by
    intro hthetaEQ
    exact S.sameNeighbor_disjoint q.2 hhost
      ⟨theta, hthetaEQ, hthetaQ⟩
  have hownE : S.neighborGraph e.2 theta < S.hostGraph e.1 theta :=
    (S.positive_iff e theta hthetaAB).mp hthetaE
  have hforeignE : S.hostGraph q.1 theta <= S.neighborGraph e.2 theta :=
    le_of_not_gt (fun hlt => hnotQE
      ((S.positive_iff (q.1, e.2) theta hthetaAB).mpr hlt))
  have hownQ : S.neighborGraph q.2 theta < S.hostGraph q.1 theta :=
    (S.positive_iff q theta hthetaAB).mp hthetaQ
  have hforeignQ : S.hostGraph e.1 theta <= S.neighborGraph q.2 theta :=
    le_of_not_gt (fun hlt => hnotEQ
      ((S.positive_iff (e.1, q.2) theta hthetaAB).mpr hlt))
  linarith

theorem pairwise_disjoint
    (S : PairLocalMoonOpenSupportData) {e q : K23Edge} (heq : e ≠ q) :
    ¬ (Ioo (S.left e) (S.right e) ∩
      Ioo (S.left q) (S.right q)).Nonempty := by
  rcases e with ⟨eh, ej⟩
  rcases q with ⟨qh, qj⟩
  by_cases hhost : eh = qh
  · subst qh
    have hneighbor : ej ≠ qj := by
      intro h
      subst qj
      exact heq rfl
    exact S.sameHost_disjoint eh hneighbor
  · by_cases hneighbor : ej = qj
    · subst qj
      exact S.sameNeighbor_disjoint ej hhost
    · exact S.nonincident_disjoint hhost hneighbor

theorem pair_ordered_le
    (S : PairLocalMoonOpenSupportData) {e q : K23Edge} (heq : e ≠ q) :
    S.right e <= S.left q ∨ S.right q <= S.left e := by
  by_cases hforward : S.right e <= S.left q
  · exact Or.inl hforward
  · right
    by_contra hbackward
    have hqLeft_eRight : S.left q < S.right e := lt_of_not_ge hforward
    have heLeft_qRight : S.left e < S.right q := lt_of_not_ge hbackward
    apply S.pairwise_disjoint heq
    rw [Ioo_inter_Ioo, nonempty_Ioo]
    exact lt_min
      (max_lt (S.left_lt_right e) hqLeft_eRight)
      (max_lt heLeft_qRight (S.left_lt_right q))

def innerLeft (S : PairLocalMoonOpenSupportData) (e : K23Edge) : Real :=
  (2 * S.left e + S.right e) / 3

def innerRight (S : PairLocalMoonOpenSupportData) (e : K23Edge) : Real :=
  (S.left e + 2 * S.right e) / 3

theorem left_lt_innerLeft
    (S : PairLocalMoonOpenSupportData) (e : K23Edge) :
    S.left e < S.innerLeft e := by
  unfold innerLeft
  linarith [S.left_lt_right e]

theorem innerLeft_lt_innerRight
    (S : PairLocalMoonOpenSupportData) (e : K23Edge) :
    S.innerLeft e < S.innerRight e := by
  unfold innerLeft innerRight
  linarith [S.left_lt_right e]

theorem innerRight_lt_right
    (S : PairLocalMoonOpenSupportData) (e : K23Edge) :
    S.innerRight e < S.right e := by
  unfold innerRight
  linarith [S.left_lt_right e]

def innerSeparatedIntervals
    (S : PairLocalMoonOpenSupportData) : SixSeparatedIntervals where
  left := S.innerLeft
  right := S.innerRight
  left_lt_right := S.innerLeft_lt_innerRight
  pair_ordered := by
    intro e q heq
    rcases S.pair_ordered_le heq with hforward | hbackward
    · exact Or.inl <| (S.innerRight_lt_right e).trans
        (hforward.trans_lt (S.left_lt_innerLeft q))
    · exact Or.inr <| (S.innerRight_lt_right q).trans
        (hbackward.trans_lt (S.left_lt_innerLeft e))

theorem intervalMidpoint_innerSeparatedIntervals
    (S : PairLocalMoonOpenSupportData) (e : K23Edge) :
    intervalMidpoint S.innerSeparatedIntervals e =
      (S.left e + S.right e) / 2 := by
  unfold intervalMidpoint innerSeparatedIntervals innerLeft innerRight
  ring

theorem intervalMidpoint_inner_mem_original_Ioo
    (S : PairLocalMoonOpenSupportData) (e : K23Edge) :
    intervalMidpoint S.innerSeparatedIntervals e ∈
      Ioo (S.left e) (S.right e) := by
  rw [S.intervalMidpoint_innerSeparatedIntervals]
  constructor <;> linarith [S.left_lt_right e]

theorem intervalMidpoint_inner_mem_Icc
    (S : PairLocalMoonOpenSupportData) (e : K23Edge) :
    intervalMidpoint S.innerSeparatedIntervals e ∈ Icc S.A S.B :=
  S.interval_subset_Icc e (S.intervalMidpoint_inner_mem_original_Ioo e)

#print axioms PairLocalMoonOpenSupportData
#print axioms PairLocalMoonOpenSupportData.nonincident_disjoint
#print axioms PairLocalMoonOpenSupportData.pairwise_disjoint
#print axioms PairLocalMoonOpenSupportData.pair_ordered_le
#print axioms PairLocalMoonOpenSupportData.innerSeparatedIntervals
#print axioms PairLocalMoonOpenSupportData.intervalMidpoint_innerSeparatedIntervals

end PairLocalMoonOpenSupportData

end

end FamilyStickyCinematicL32Prop41PairLocalMoonOpenSupportSeparationCoreCleanV1
