import FamilyStickyGrounding.FamilyStickyScaleSequenceRefinesAtV2
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleSequenceRatioTelescopeV2

open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleSequenceRefinesAtV2
open FamilyStickyScaleSequenceRefinesAtV2.FiniteScaleSequence

noncomputable section

/-!
# Exact adjacent-scale ratio telescoping

This module records the algebraic conservation law for a finite decreasing
scale sequence.  Positivity of `delta` makes every radius nonzero, so the
product of all adjacent quotients cancels exactly to the quotient of the two
endpoints.  Inserting a radius therefore preserves the total product, while
the old quotient at the split interval is exactly the product of its two new
quotients.

The final theorem is deliberately abstract: it turns a separately supplied
positive per-split increase and a separately supplied potential bound into a
bound on the number of successful splits.  It does not assert any geometric
or analytic increase for the Family 7 construction.
-/

/-- Adjacent quotients in a nonzero finite vector telescope to the quotient
of its first and last entries. -/
theorem prod_fin_adjacent_div
    (n : Nat) (a : Fin (n + 1) → NNReal) (ha : ∀ i, a i ≠ 0) :
    (∏ i : Fin n, a i.castSucc / a i.succ) =
      a 0 / a (Fin.last n) := by
  induction n with
  | zero =>
      simp only [Fin.prod_univ_zero]
      simpa using (div_self (ha 0)).symm
  | succ n ih =>
      let b : Fin (n + 1) → NNReal := fun i => a i.succ
      have hb : ∀ i, b i ≠ 0 := fun i => ha i.succ
      have hprod :
          (∏ i : Fin n, a i.succ.castSucc / a i.succ.succ) =
            ∏ i : Fin n, b i.castSucc / b i.succ := by
        apply Finset.prod_congr rfl
        intro i _
        dsimp only [b]
        have hidx : i.succ.castSucc = i.castSucc.succ := by
          apply Fin.ext
          rfl
        rw [hidx]
      rw [Fin.prod_univ_succ, hprod, ih b hb]
      dsimp only [b]
      have hlast : (Fin.last n).succ = Fin.last (n + 1) := by
        apply Fin.ext
        rfl
      rw [hlast]
      field_simp [ha]
      apply congrArg a
      apply Fin.ext
      rfl

namespace FiniteScaleSequence

variable {delta : NNReal} {depth : Nat}

/-- The adjacent upper-to-lower scale quotient. -/
def adjacentRatio
    (S : FiniteScaleSequence delta depth) (m : Fin depth) : NNReal :=
  S.theta m / S.tau m

/-- Positivity of the bottom scale makes every coordinate positive. -/
theorem radius_pos
    (S : FiniteScaleSequence delta depth) (delta_pos : 0 < delta)
    (i : Fin (depth + 1)) :
    0 < S.radius i := by
  calc
    0 < delta := delta_pos
    _ = S.radius (Fin.last depth) := S.bottom_eq.symm
    _ ≤ S.radius i := S.antitone_radius (Fin.le_last i)

/-- Exact NNReal telescope for all adjacent scale ratios. -/
theorem prod_adjacentRatio
    (S : FiniteScaleSequence delta depth) (delta_pos : 0 < delta) :
    (∏ m : Fin depth, adjacentRatio S m) = 1 / delta := by
  change (∏ m : Fin depth, S.radius m.castSucc / S.radius m.succ) = 1 / delta
  rw [prod_fin_adjacent_div depth S.radius
    (fun i => (radius_pos S delta_pos i).ne'), S.top_eq, S.bottom_eq]

/-- The same telescope after coercion to `ENNReal`. -/
theorem prod_adjacentRatio_ennreal
    (S : FiniteScaleSequence delta depth) (delta_pos : 0 < delta) :
    (∏ m : Fin depth, (adjacentRatio S m : ENNReal)) =
      1 / (delta : ENNReal) := by
  rw [← ENNReal.ofNNReal_finsetProd, prod_adjacentRatio S delta_pos,
    ENNReal.coe_div delta_pos.ne']
  simp only [ENNReal.coe_one]

/-- The upper endpoint of the first child is the old upper endpoint. -/
theorem theta_upperChild_of_refinesAt
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    (S' : FiniteScaleSequence delta (depth + 1))
    (hRef : ScaleSequenceRefinesAt S m rho S') :
    S'.theta m.castSucc = S.theta m := by
  change S'.radius m.castSucc.castSucc = S.radius m.castSucc
  rw [← oldIndexEmbedding_upperEndpoint m]
  exact hRef.old_radius m.castSucc

/-- The lower endpoint of the first child is the inserted radius. -/
theorem tau_upperChild_of_refinesAt
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    (S' : FiniteScaleSequence delta (depth + 1))
    (hRef : ScaleSequenceRefinesAt S m rho S') :
    S'.tau m.castSucc = rho := by
  change S'.radius m.castSucc.succ = rho
  simpa only [insertedIndex] using hRef.inserted_radius

/-- The upper endpoint of the second child is the inserted radius. -/
theorem theta_lowerChild_of_refinesAt
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    (S' : FiniteScaleSequence delta (depth + 1))
    (hRef : ScaleSequenceRefinesAt S m rho S') :
    S'.theta m.succ = rho := by
  change S'.radius m.succ.castSucc = rho
  have hindex : m.succ.castSucc = insertedIndex m := by
    apply Fin.ext
    rfl
  rw [hindex]
  exact hRef.inserted_radius

/-- The lower endpoint of the second child is the old lower endpoint. -/
theorem tau_lowerChild_of_refinesAt
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    (S' : FiniteScaleSequence delta (depth + 1))
    (hRef : ScaleSequenceRefinesAt S m rho S') :
    S'.tau m.succ = S.tau m := by
  change S'.radius m.succ.succ = S.radius m.succ
  rw [← oldIndexEmbedding_lowerEndpoint m]
  exact hRef.old_radius m.succ

/-- A refinement splits one old adjacent quotient into exactly the product of
the two child quotients. -/
theorem adjacentRatio_split_of_refinesAt
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    (S' : FiniteScaleSequence delta (depth + 1)) (delta_pos : 0 < delta)
    (hRef : ScaleSequenceRefinesAt S m rho S') :
    adjacentRatio S m =
      adjacentRatio S' m.castSucc * adjacentRatio S' m.succ := by
  have hrho_pos : 0 < rho := by
    rw [← hRef.inserted_radius]
    exact radius_pos S' delta_pos (insertedIndex m)
  have htau_pos : 0 < S.tau m := by
    exact radius_pos S delta_pos m.succ
  unfold adjacentRatio
  rw [theta_upperChild_of_refinesAt S m rho S' hRef,
    tau_upperChild_of_refinesAt S m rho S' hRef,
    theta_lowerChild_of_refinesAt S m rho S' hRef,
    tau_lowerChild_of_refinesAt S m rho S' hRef]
  field_simp [ne_of_gt hrho_pos, ne_of_gt htau_pos]

/-- The concrete insertion constructor satisfies the exact local split law. -/
theorem adjacentRatio_insertRadius_split
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m ≤ rho) (hRhoTheta : rho ≤ S.theta m)
    (delta_pos : 0 < delta) :
    adjacentRatio S m =
      adjacentRatio (insertRadius S m rho hTauRho hRhoTheta) m.castSucc *
        adjacentRatio (insertRadius S m rho hTauRho hRhoTheta) m.succ := by
  exact adjacentRatio_split_of_refinesAt S m rho
    (insertRadius S m rho hTauRho hRhoTheta) delta_pos
    (insertRadius_refinesAt S m rho hTauRho hRhoTheta)

/-- Inserting a radius leaves the total product of adjacent quotients
unchanged. -/
theorem prod_adjacentRatio_insertRadius
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m ≤ rho) (hRhoTheta : rho ≤ S.theta m)
    (delta_pos : 0 < delta) :
    (∏ j : Fin (depth + 1),
        adjacentRatio (insertRadius S m rho hTauRho hRhoTheta) j) =
      ∏ j : Fin depth, adjacentRatio S j := by
  rw [prod_adjacentRatio (insertRadius S m rho hTauRho hRhoTheta) delta_pos,
    prod_adjacentRatio S delta_pos]

/-- ENNReal form of total-product conservation under insertion. -/
theorem prod_adjacentRatio_insertRadius_ennreal
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m ≤ rho) (hRhoTheta : rho ≤ S.theta m)
    (delta_pos : 0 < delta) :
    (∏ j : Fin (depth + 1),
        (adjacentRatio (insertRadius S m rho hTauRho hRhoTheta) j : ENNReal)) =
      ∏ j : Fin depth, (adjacentRatio S j : ENNReal) := by
  rw [prod_adjacentRatio_ennreal
      (insertRadius S m rho hTauRho hRhoTheta) delta_pos,
    prod_adjacentRatio_ennreal S delta_pos]

end FiniteScaleSequence

/-- A positive increment accumulated at every successful step forces a step
bound once the total nonnegative potential fits inside `N` increments. -/
theorem steps_le_of_nonnegative_potential_growth
    (steps N : Nat) (potential : Nat → Real) (increment upper : Real)
    (potential_zero_nonneg : 0 ≤ potential 0)
    (increment_pos : 0 < increment)
    (grows : ∀ k, k < steps → potential k + increment ≤ potential (k + 1))
    (terminal_le : potential steps ≤ upper)
    (upper_le_budget : upper ≤ (N : Real) * increment) :
    steps ≤ N := by
  have accumulated : ∀ k, k ≤ steps →
      potential 0 + (k : Real) * increment ≤ potential k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        have hk_lt : k < steps := by omega
        calc
          potential 0 + ((k + 1 : Nat) : Real) * increment =
              (potential 0 + (k : Real) * increment) + increment := by
                norm_num
                ring
          _ ≤ potential k + increment := by
            linarith [ih (by omega)]
          _ ≤ potential (k + 1) := grows k hk_lt
  have hbudget : (steps : Real) * increment ≤ (N : Real) * increment := by
    calc
      (steps : Real) * increment ≤
          potential 0 + (steps : Real) * increment := by linarith
      _ ≤ potential steps := accumulated steps le_rfl
      _ ≤ upper := terminal_le
      _ ≤ (N : Real) * increment := upper_le_budget
  have hcast : (steps : Real) ≤ (N : Real) := by
    nlinarith
  exact_mod_cast hcast

#print axioms prod_fin_adjacent_div
#print axioms FiniteScaleSequence.prod_adjacentRatio
#print axioms FiniteScaleSequence.prod_adjacentRatio_ennreal
#print axioms FiniteScaleSequence.adjacentRatio_split_of_refinesAt
#print axioms FiniteScaleSequence.adjacentRatio_insertRadius_split
#print axioms FiniteScaleSequence.prod_adjacentRatio_insertRadius
#print axioms FiniteScaleSequence.prod_adjacentRatio_insertRadius_ennreal
#print axioms steps_le_of_nonnegative_potential_growth

end
end FamilyStickyScaleSequenceRatioTelescopeV2
