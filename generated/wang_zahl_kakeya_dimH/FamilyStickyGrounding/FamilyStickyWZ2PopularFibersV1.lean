import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyWZ2PopularFibersV1

noncomputable section

/-!
# WZ2 finite popular-fiber selection

This is the finite double-counting step used in Section 7 of
Wang--Zahl, *The Assouad dimension of Kakeya sets in R3*, in the proof of
the strengthened `L^{3/2}` upper bound feeding Theorem 5.2.  After restricting
the shading to a popular projection set, the paper discards tubes on which
the restricted shading has less than a prescribed fraction of the tube mass.

The relevant WZ2 source is the Assouad-dimension paper (local source
`/tmp/wz2401/Wang-Zahl__Assouad_dim_of_Kakeya_sets_revised2.tex`), not
arXiv:2210.09581, which is the earlier sticky paper cited there as WZ1.

The theorem below proves the finite selection itself.  It neither assumes
Theorem 5.2 nor packages its conclusion as a callback.
-/

variable {ι : Type*}

/-- Indices whose weight reaches the displayed threshold. -/
def popularIndices (s : Finset ι) (weight : ι -> Real) (threshold : Real) :
    Finset ι :=
  s.filter fun i => threshold <= weight i

/-- The complementary indices inside the same finite ambient family. -/
def unpopularIndices (s : Finset ι) (weight : ι -> Real) (threshold : Real) :
    Finset ι :=
  s.filter fun i => ¬ threshold <= weight i

/-- Popular and unpopular fibers split the total weight exactly. -/
theorem sum_eq_popular_add_unpopular
    (s : Finset ι) (weight : ι -> Real) (threshold : Real) :
    (∑ i ∈ s, weight i) =
      (∑ i ∈ popularIndices s weight threshold, weight i) +
        ∑ i ∈ unpopularIndices s weight threshold, weight i := by
  simpa [popularIndices, unpopularIndices] using
    (Finset.sum_filter_add_sum_filter_not s
      (fun i => threshold <= weight i) weight).symm

/-- If every fiber has weight at most `cap`, then the total weight is bounded
by `cap` on popular indices and by `threshold` on the complement. -/
theorem sum_le_popular_cap_add_unpopular_threshold
    (s : Finset ι) (weight : ι -> Real) (threshold cap : Real)
    (hcap : forall i, i ∈ s -> weight i <= cap) :
    (∑ i ∈ s, weight i) <=
      (popularIndices s weight threshold).card * cap +
        (unpopularIndices s weight threshold).card * threshold := by
  rw [sum_eq_popular_add_unpopular]
  apply add_le_add
  · calc
      (∑ i ∈ popularIndices s weight threshold, weight i) <=
          ∑ _i ∈ popularIndices s weight threshold, cap := by
        apply Finset.sum_le_sum
        intro i hi
        rw [popularIndices, Finset.mem_filter] at hi
        exact hcap i hi.1
      _ = (popularIndices s weight threshold).card * cap := by simp
  · calc
      (∑ i ∈ unpopularIndices s weight threshold, weight i) <=
          ∑ _i ∈ unpopularIndices s weight threshold, threshold := by
        apply Finset.sum_le_sum
        intro i hi
        rw [unpopularIndices, Finset.mem_filter] at hi
        exact le_of_lt (lt_of_not_ge hi.2)
      _ = (unpopularIndices s weight threshold).card * threshold := by simp

/-- Half-threshold popularity lemma.  If the average weight is at least
`alpha * cap`, at least an `alpha / 2` fraction of the indices have weight at
least `(alpha / 2) * cap`.

This is the quantitative finite kernel of the tube-retention step in WZ2.
The assumptions on `cap` are precisely what is needed to cancel the common
mass scale; no geometric or measure-theoretic conclusion is assumed. -/
theorem half_density_card_le_popular_card
    (s : Finset ι) (weight : ι -> Real) (alpha cap : Real)
    (halpha0 : 0 <= alpha) (hcap0 : 0 < cap)
    (hcap : forall i, i ∈ s -> weight i <= cap)
    (hmass : alpha * s.card * cap <= ∑ i ∈ s, weight i) :
    alpha / 2 * s.card <=
      (popularIndices s weight (alpha / 2 * cap)).card := by
  let p : Real := (popularIndices s weight (alpha / 2 * cap)).card
  let q : Real := (unpopularIndices s weight (alpha / 2 * cap)).card
  let n : Real := s.card
  have hupper := sum_le_popular_cap_add_unpopular_threshold
    s weight (alpha / 2 * cap) cap hcap
  have hcardNat :
      (popularIndices s weight (alpha / 2 * cap)).card +
        (unpopularIndices s weight (alpha / 2 * cap)).card = s.card := by
    simpa [popularIndices, unpopularIndices] using
      (Finset.card_filter_add_card_filter_not
        (s := s) (fun i => alpha / 2 * cap <= weight i))
  have hcard : p + q = n := by
    dsimp [p, q, n]
    rw [← Nat.cast_add, hcardNat]
  have hp0 : 0 <= p := Nat.cast_nonneg _
  have hq0 : 0 <= q := Nat.cast_nonneg _
  have hn0 : 0 <= n := Nat.cast_nonneg _
  change alpha / 2 * n <= p
  change alpha * n * cap <= ∑ i ∈ s, weight i at hmass
  change (∑ i ∈ s, weight i) <= p * cap + q * (alpha / 2 * cap) at hupper
  have hmassUpper :
      alpha * n * cap <= p * cap + q * (alpha / 2 * cap) :=
    hmass.trans hupper
  have hcancel : alpha * n <= p + q * (alpha / 2) := by
    by_contra hnot
    have hlt : p + q * (alpha / 2) < alpha * n := lt_of_not_ge hnot
    have hmul := mul_lt_mul_of_pos_right hlt hcap0
    have hrearrange :
        p * cap + q * (alpha / 2 * cap) =
          (p + q * (alpha / 2)) * cap := by ring
    rw [hrearrange] at hmassUpper
    exact (not_lt_of_ge hmassUpper) hmul
  have halphaP0 : 0 <= alpha * p := mul_nonneg halpha0 hp0
  nlinarith

#print axioms sum_eq_popular_add_unpopular
#print axioms sum_le_popular_cap_add_unpopular_threshold
#print axioms half_density_card_le_popular_card

end

end FamilyStickyWZ2PopularFibersV1
