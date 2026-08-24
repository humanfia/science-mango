import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41K23BalancedRankReductionCleanV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41SixSeparatedIntervalRankV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41RankedIntervalSamplesV1

open Set
open FamilyStickyCinematicL32Prop41MarcusTardosFact1BoolParityV1
open FamilyStickyCinematicL32Prop41K23BalancedRankReductionCleanV1
open FamilyStickyCinematicL32Prop41SixSeparatedIntervalRankV1

noncomputable section

/-!
# Ordered interior samples from four alternating ranked intervals

The midpoint of every nonempty interval is interior.  Since the six closed
intervals are pairwise strictly separated and rank sorts their left
endpoints, increasing rank puts the whole earlier interval before the later
one.  Hence an `AlternatingFour` witness yields four strictly ordered
interior sample points with the same alternating labels.
-/

def intervalMidpoint (S : SixSeparatedIntervals) (e : K23Edge) : Real :=
  (S.left e + S.right e) / 2

theorem intervalMidpoint_mem_Ioo
    (S : SixSeparatedIntervals) (e : K23Edge) :
    intervalMidpoint S e ∈ Ioo (S.left e) (S.right e) := by
  unfold intervalMidpoint
  constructor <;> linarith [S.left_lt_right e]

theorem right_lt_left_of_rank_lt
    (S : SixSeparatedIntervals) {e q : K23Edge}
    (hrank : S.rank e < S.rank q) :
    S.right e < S.left q := by
  have heq : e ≠ q := by
    intro h
    subst q
    exact (lt_irrefl _ hrank)
  rcases S.pair_ordered heq with hforward | hbackward
  · exact hforward
  · have hleft := (S.rank_lt_iff_left_lt e q).mp hrank
    linarith [S.left_lt_right q]

theorem intervalMidpoint_lt_of_rank_lt
    (S : SixSeparatedIntervals) {e q : K23Edge}
    (hrank : S.rank e < S.rank q) :
    intervalMidpoint S e < intervalMidpoint S q := by
  have hsep := right_lt_left_of_rank_lt S hrank
  have he := intervalMidpoint_mem_Ioo S e
  have hq := intervalMidpoint_mem_Ioo S q
  linarith [he.2, hq.1]

def AlternatingMidpointWitness
    {alpha : Type*} [DecidableEq alpha]
    (S : SixSeparatedIntervals) (label : K23Edge -> alpha) : Prop :=
  exists e0 e1 e2 e3 : K23Edge,
    intervalMidpoint S e0 < intervalMidpoint S e1 ∧
      intervalMidpoint S e1 < intervalMidpoint S e2 ∧
        intervalMidpoint S e2 < intervalMidpoint S e3 ∧
    intervalMidpoint S e0 ∈ Ioo (S.left e0) (S.right e0) ∧
      intervalMidpoint S e1 ∈ Ioo (S.left e1) (S.right e1) ∧
        intervalMidpoint S e2 ∈ Ioo (S.left e2) (S.right e2) ∧
          intervalMidpoint S e3 ∈ Ioo (S.left e3) (S.right e3) ∧
    label e0 = label e2 ∧ label e1 = label e3 ∧ label e0 ≠ label e1

theorem alternatingMidpointWitness_of_alternatingFour
    {alpha : Type*} [DecidableEq alpha]
    (S : SixSeparatedIntervals) (label : K23Edge -> alpha)
    (halt : AlternatingFour S.rank label) :
    AlternatingMidpointWitness S label := by
  rcases halt with ⟨e0, e1, e2, e3, h01, h12, h23, h02, h13, hne⟩
  exact ⟨e0, e1, e2, e3,
    intervalMidpoint_lt_of_rank_lt S h01,
    intervalMidpoint_lt_of_rank_lt S h12,
    intervalMidpoint_lt_of_rank_lt S h23,
    intervalMidpoint_mem_Ioo S e0, intervalMidpoint_mem_Ioo S e1,
    intervalMidpoint_mem_Ioo S e2, intervalMidpoint_mem_Ioo S e3,
    h02, h13, hne⟩

#print axioms intervalMidpoint_mem_Ioo
#print axioms right_lt_left_of_rank_lt
#print axioms intervalMidpoint_lt_of_rank_lt
#print axioms alternatingMidpointWitness_of_alternatingFour

end

end FamilyStickyCinematicL32Prop41RankedIntervalSamplesV1
