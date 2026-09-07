import Family8Grounding.Family8ZeroColorHeterogeneousChernoffV1

open scoped BigOperators

namespace Family8ZeroColorChernoffSimultaneousRetentionV1

open Family8GeneralizedKatzTaoMultiplicityV1
open Family8ZeroColorHeterogeneousChernoffV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

/-!
# Simultaneous retention and logarithmic-cost upper tails

The heterogeneous Chernoff bound controls all members of a finite test
catalogue for one zero-colour outcome.  This file makes the same outcome also
retain a fixed fraction of an arbitrary nonnegative weight.  The point is a
cardinality lower bound for the set of retention-good outcomes, rather than a
mere existence theorem.  It can therefore be intersected with the complement
of the Chernoff bad union.
-/

/-- Zero-colour outcomes retaining at least half of the expected total
weight. -/
def zeroColorRetentionGoodOutcomes
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (k : Nat) [NeZero k] (weight : iota → Real) :
    Finset (iota → Fin k) :=
  Finset.univ.filter fun omega =>
    (∑ i : iota, weight i) / (2 * (k : Real)) ≤
      zeroColorSampleRealWeight k weight omega

/-- Every selected nonnegative weight is bounded by the original total
weight. -/
theorem zeroColorSampleRealWeight_le_total
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (k : Nat) [NeZero k] (weight : iota → Real)
    (hweight : ∀ i, 0 ≤ weight i) (omega : iota → Fin k) :
    zeroColorSampleRealWeight k weight omega ≤ ∑ i : iota, weight i := by
  unfold zeroColorSampleRealWeight
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ _) (fun i _hi _hnot => hweight i)

/-- A positive nonnegative weight has a quantitatively large set of
retention-good colourings.  In real-cardinality form, at least a `1/(2k)`
fraction of all colourings are good. -/
theorem card_zeroColorRetentionGoodOutcomes_lower
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (k : Nat) [NeZero k] (weight : iota → Real)
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightPos : 0 < ∑ i : iota, weight i) :
    ((Finset.univ : Finset (iota → Fin k)).card : Real) ≤
      (2 * (k : Real)) *
        ((zeroColorRetentionGoodOutcomes k weight).card : Real) := by
  classical
  let W : Real := ∑ i : iota, weight i
  let threshold : Real := W / (2 * (k : Real))
  let good : Finset (iota → Fin k) :=
    zeroColorRetentionGoodOutcomes k weight
  have hk : 0 < (k : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have hthreshold : 0 ≤ threshold := by
    exact div_nonneg hweightPos.le (mul_nonneg zero_le_two hk.le)
  have hpoint : ∀ omega : iota → Fin k,
      zeroColorSampleRealWeight k weight omega ≤
        threshold + if omega ∈ good then W else 0 := by
    intro omega
    by_cases homega : omega ∈ good
    · rw [if_pos homega]
      have hupper := zeroColorSampleRealWeight_le_total k weight hweight omega
      dsimp only [W]
      linarith
    · rw [if_neg homega, add_zero]
      have hlow : ¬ threshold ≤
          zeroColorSampleRealWeight k weight omega := by
        simpa [good, zeroColorRetentionGoodOutcomes, threshold, W] using homega
      exact le_of_lt (lt_of_not_ge hlow)
  have hsumUpper :
      (∑ omega : iota → Fin k,
          zeroColorSampleRealWeight k weight omega) ≤
        ((Finset.univ : Finset (iota → Fin k)).card : Real) * threshold +
          (good.card : Real) * W := by
    calc
      (∑ omega : iota → Fin k,
          zeroColorSampleRealWeight k weight omega) ≤
        ∑ omega : iota → Fin k,
          (threshold + if omega ∈ good then W else 0) := by
            exact Finset.sum_le_sum fun omega _homega => hpoint omega
      _ = ((Finset.univ : Finset (iota → Fin k)).card : Real) * threshold +
          (good.card : Real) * W := by
            simp [Finset.sum_add_distrib]
  have hspacePos :
      0 < ((Finset.univ : Finset (iota → Fin k)).card : Real) := by
    exact_mod_cast (Finset.univ_nonempty.card_pos)
  have hspaceNe :
      ((Fintype.card (iota → Fin k) : Nat) : Real) ≠ 0 := by
    simpa using hspacePos.ne'
  have hmean := expect_zeroColorSample_realWeight k weight
  rw [Fintype.expect_eq_sum_div_card] at hmean
  have hsumExact :
      (∑ omega : iota → Fin k,
          zeroColorSampleRealWeight k weight omega) =
        ((Finset.univ : Finset (iota → Fin k)).card : Real) *
          (W / (k : Real)) := by
    calc
      (∑ omega : iota → Fin k,
          zeroColorSampleRealWeight k weight omega) =
        ((∑ omega : iota → Fin k,
            zeroColorSampleRealWeight k weight omega) /
              (Fintype.card (iota → Fin k) : Real)) *
            (Fintype.card (iota → Fin k) : Real) := by
              field_simp [hspaceNe]
      _ = (W / (k : Real)) *
          (Fintype.card (iota → Fin k) : Real) := by
            rw [hmean]
      _ = ((Finset.univ : Finset (iota → Fin k)).card : Real) *
          (W / (k : Real)) := by simp [mul_comm]
  have hcancel :
      ((Finset.univ : Finset (iota → Fin k)).card : Real) /
          (k : Real) ≤
        ((Finset.univ : Finset (iota → Fin k)).card : Real) /
            (2 * (k : Real)) + (good.card : Real) := by
    have hfactLeft :
        ((Finset.univ : Finset (iota → Fin k)).card : Real) *
            (W / (k : Real)) =
          W * (((Finset.univ : Finset (iota → Fin k)).card : Real) /
            (k : Real)) := by ring
    have hfactRight :
        ((Finset.univ : Finset (iota → Fin k)).card : Real) * threshold +
            (good.card : Real) * W =
          W *
            (((Finset.univ : Finset (iota → Fin k)).card : Real) /
                (2 * (k : Real)) + (good.card : Real)) := by
      dsimp only [threshold]
      ring
    rw [hsumExact, hfactLeft, hfactRight] at hsumUpper
    exact le_of_mul_le_mul_left hsumUpper hweightPos
  have hdouble :
      ((Finset.univ : Finset (iota → Fin k)).card : Real) /
          (k : Real) =
        2 *
          (((Finset.univ : Finset (iota → Fin k)).card : Real) /
            (2 * (k : Real))) := by
    field_simp [hk.ne']
  have hhalf :
      ((Finset.univ : Finset (iota → Fin k)).card : Real) /
          (2 * (k : Real)) ≤ (good.card : Real) := by
    rw [hdouble] at hcancel
    linarith
  change ((Finset.univ : Finset (iota → Fin k)).card : Real) ≤
    (2 * (k : Real)) * (good.card : Real)
  simpa [mul_comm] using
    (div_le_iff₀ (mul_pos zero_lt_two hk)).mp hhalf

#print axioms zeroColorSampleRealWeight_le_total
#print axioms card_zeroColorRetentionGoodOutcomes_lower

end

end Family8ZeroColorChernoffSimultaneousRetentionV1
