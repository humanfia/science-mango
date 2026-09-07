import Family8Grounding.Family8ZeroColorChernoffSimultaneousRetentionV1

open scoped BigOperators

namespace Family8ZeroColorChernoffSimultaneousSelectionV1

open Family8GeneralizedKatzTaoMultiplicityV1
open Family8ZeroColorHeterogeneousChernoffV1
open Family8ZeroColorChernoffSimultaneousRetentionV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

/-!
# One zero-colour outcome with retention and finite-test tails

The lower-retention event from the preceding module occupies at least a
`1/(2k)` fraction of the literal product colouring space.  A Chernoff union
bound whose bad fraction is smaller therefore has a witness outside every bad
test and inside the retention event.  This is an honest simultaneous selection,
not a separately chosen good subfamily.
-/

/-- Union of the upper-tail bad events associated to a finite test
catalogue. -/
def zeroColorWeightedTestBadUnion
    {iota test : Type} [Fintype iota] [DecidableEq iota]
    [Fintype test] [DecidableEq test]
    (tests : Finset test) (k : Nat) [NeZero k]
    (weight : test → iota → Real) (cap : test → Real) (A : Real) :
    Finset (iota → Fin k) :=
  tests.biUnion fun K =>
    zeroColorWeightedBadOutcomes k (weight K) (A * cap K)

/-- Cardinal form of the logarithmic finite union bound. -/
theorem card_zeroColorWeightedTestBadUnion_mul_exp_le
    {iota test : Type} [Fintype iota] [DecidableEq iota]
    [Fintype test] [DecidableEq test]
    (tests : Finset test) (k : Nat) [NeZero k]
    (weight : test → iota → Real) (cap : test → Real) (A : Real)
    (hcap : ∀ K ∈ tests, 0 < cap K)
    (hweight0 : ∀ K ∈ tests, ∀ i, 0 ≤ weight K i)
    (hweightCap : ∀ K ∈ tests, ∀ i, weight K i ≤ cap K)
    (hscale : ∀ K ∈ tests,
      (∑ i : iota, weight K i) / (k : Real) ≤ cap K) :
    ((zeroColorWeightedTestBadUnion tests k weight cap A).card : Real) *
        Real.exp A ≤
      (tests.card : Real) *
        (((Finset.univ : Finset (iota → Fin k)).card : Real) *
          Real.exp (Real.exp 1 - 1)) := by
  classical
  calc
    ((zeroColorWeightedTestBadUnion tests k weight cap A).card : Real) *
        Real.exp A ≤
      ((∑ K ∈ tests,
        (zeroColorWeightedBadOutcomes k
          (weight K) (A * cap K)).card : Nat) : Real) *
            Real.exp A := by
      gcongr
      exact Finset.card_biUnion_le
    _ = ∑ K ∈ tests,
        ((zeroColorWeightedBadOutcomes k
          (weight K) (A * cap K)).card : Real) *
            Real.exp A := by
      push_cast
      rw [Finset.sum_mul]
    _ ≤ ∑ _K ∈ tests,
        ((Finset.univ : Finset (iota → Fin k)).card : Real) *
          Real.exp (Real.exp 1 - 1) := by
      apply Finset.sum_le_sum
      intro K hK
      simpa using
        card_zeroColorWeightedBadOutcomes_mul_exp_le_fixed
          k (weight K) (hcap K hK) (hweight0 K hK)
          (hweightCap K hK) (hscale K hK)
    _ = (tests.card : Real) *
        (((Finset.univ : Finset (iota → Fin k)).card : Real) *
          Real.exp (Real.exp 1 - 1)) := by simp

/-- One literal zero-colour outcome simultaneously retains half of the
expected target weight and obeys every catalogue upper-tail bound.  The factor
`2k` in the displayed room condition is exactly the reciprocal of the
quantitative retention-good fraction. -/
theorem exists_zeroColorSample_retention_and_all_weightedLoads_le_of_pos
    {iota test : Type} [Fintype iota] [DecidableEq iota]
    [Fintype test] [DecidableEq test]
    (tests : Finset test) (k : Nat) [NeZero k]
    (retainedWeight : iota → Real)
    (weight : test → iota → Real) (cap : test → Real) (A : Real)
    (hretained0 : ∀ i, 0 ≤ retainedWeight i)
    (hretainedPos : 0 < ∑ i : iota, retainedWeight i)
    (hcap : ∀ K ∈ tests, 0 < cap K)
    (hweight0 : ∀ K ∈ tests, ∀ i, 0 ≤ weight K i)
    (hweightCap : ∀ K ∈ tests, ∀ i, weight K i ≤ cap K)
    (hscale : ∀ K ∈ tests,
      (∑ i : iota, weight K i) / (k : Real) ≤ cap K)
    (htailRoom :
      (2 * (k : Real)) *
          ((tests.card : Real) * Real.exp (Real.exp 1 - 1)) <
        Real.exp A) :
    ∃ omega : iota → Fin k,
      (∑ i : iota, retainedWeight i) / (2 * (k : Real)) ≤
          zeroColorSampleRealWeight k retainedWeight omega ∧
        ∀ K ∈ tests,
          zeroColorSampleRealWeight k (weight K) omega ≤ A * cap K := by
  classical
  let good : Finset (iota → Fin k) :=
    zeroColorRetentionGoodOutcomes k retainedWeight
  let bad : Finset (iota → Fin k) :=
    zeroColorWeightedTestBadUnion tests k weight cap A
  let spaceCard : Real :=
    ((Finset.univ : Finset (iota → Fin k)).card : Real)
  let loss : Real := 2 * (k : Real)
  let tailCost : Real :=
    (tests.card : Real) * Real.exp (Real.exp 1 - 1)
  have hk : 0 < (k : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have hloss : 0 < loss := mul_pos zero_lt_two hk
  have hspace : 0 < spaceCard := by
    dsimp only [spaceCard]
    exact_mod_cast (Finset.univ_nonempty.card_pos)
  have hgood : spaceCard ≤ loss * (good.card : Real) := by
    simpa [good, spaceCard, loss] using
      card_zeroColorRetentionGoodOutcomes_lower
        k retainedWeight hretained0 hretainedPos
  have hbad : (bad.card : Real) * Real.exp A ≤
      tailCost * spaceCard := by
    have h := card_zeroColorWeightedTestBadUnion_mul_exp_le
      tests k weight cap A hcap hweight0 hweightCap hscale
    simpa [bad, tailCost, spaceCard, mul_comm, mul_left_comm,
      mul_assoc] using h
  have hbadScaled : loss * (bad.card : Real) < spaceCard := by
    have hmul :
        (loss * (bad.card : Real)) * Real.exp A <
          spaceCard * Real.exp A := by
      calc
        (loss * (bad.card : Real)) * Real.exp A =
            loss * ((bad.card : Real) * Real.exp A) := by ring
        _ ≤ loss * (tailCost * spaceCard) :=
          mul_le_mul_of_nonneg_left hbad hloss.le
        _ = spaceCard * (loss * tailCost) := by ring
        _ < spaceCard * Real.exp A :=
          mul_lt_mul_of_pos_left
            (by simpa [loss, tailCost] using htailRoom) hspace
    exact lt_of_mul_lt_mul_right hmul (Real.exp_pos A).le
  have hbadGoodReal : (bad.card : Real) < (good.card : Real) := by
    have hscaled : loss * (bad.card : Real) <
        loss * (good.card : Real) :=
      hbadScaled.trans_le hgood
    exact lt_of_mul_lt_mul_left hscaled hloss.le
  have hbadGood : bad.card < good.card := by
    exact_mod_cast hbadGoodReal
  have hwitness : ∃ omega, omega ∈ good ∧ omega ∉ bad := by
    by_contra hnone
    push Not at hnone
    have hsubset : good ⊆ bad := by
      intro omega homega
      exact hnone omega homega
    exact (not_lt_of_ge (Finset.card_le_card hsubset)) hbadGood
  obtain ⟨omega, homegaGood, homegaBad⟩ := hwitness
  refine ⟨omega, ?_, ?_⟩
  · simpa [good, zeroColorRetentionGoodOutcomes] using homegaGood
  · intro K hK
    have hnot : omega ∉
        zeroColorWeightedBadOutcomes k (weight K) (A * cap K) := by
      intro homegaK
      exact homegaBad
        (Finset.mem_biUnion.mpr ⟨K, hK, homegaK⟩)
    simpa [zeroColorWeightedBadOutcomes] using hnot

/-- Total version: zero target weight is handled without a positivity
hypothesis, while the positive branch uses the quantitative good-event
intersection. -/
theorem exists_zeroColorSample_retention_and_all_weightedLoads_le
    {iota test : Type} [Fintype iota] [DecidableEq iota]
    [Fintype test] [DecidableEq test]
    (tests : Finset test) (k : Nat) [NeZero k]
    (retainedWeight : iota → Real)
    (weight : test → iota → Real) (cap : test → Real) (A : Real)
    (hretained0 : ∀ i, 0 ≤ retainedWeight i)
    (hcap : ∀ K ∈ tests, 0 < cap K)
    (hweight0 : ∀ K ∈ tests, ∀ i, 0 ≤ weight K i)
    (hweightCap : ∀ K ∈ tests, ∀ i, weight K i ≤ cap K)
    (hscale : ∀ K ∈ tests,
      (∑ i : iota, weight K i) / (k : Real) ≤ cap K)
    (htailRoom :
      (2 * (k : Real)) *
          ((tests.card : Real) * Real.exp (Real.exp 1 - 1)) <
        Real.exp A) :
    ∃ omega : iota → Fin k,
      (∑ i : iota, retainedWeight i) / (2 * (k : Real)) ≤
          zeroColorSampleRealWeight k retainedWeight omega ∧
        ∀ K ∈ tests,
          zeroColorSampleRealWeight k (weight K) omega ≤ A * cap K := by
  have htotal0 : 0 ≤ ∑ i : iota, retainedWeight i :=
    Finset.sum_nonneg fun i _hi => hretained0 i
  rcases htotal0.eq_or_lt with hzero | hpos
  · obtain ⟨omega, homega⟩ :=
      exists_zeroColorSample_all_weightedLoads_le
        tests k weight cap A hcap hweight0 hweightCap hscale
        (by
          have hk : 0 < (k : Real) := by
            exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
          have hloss : 1 ≤ 2 * (k : Real) := by
            have hkNat : 1 ≤ k :=
              Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
            have hkOne : (1 : Real) ≤ (k : Real) := by
              exact_mod_cast hkNat
            nlinarith
          have hcost : 0 ≤
              (tests.card : Real) * Real.exp (Real.exp 1 - 1) :=
            mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
          calc
            (tests.card : Real) * Real.exp (Real.exp 1 - 1) =
                1 * ((tests.card : Real) *
                  Real.exp (Real.exp 1 - 1)) := by ring
            _ ≤ (2 * (k : Real)) *
                ((tests.card : Real) *
                  Real.exp (Real.exp 1 - 1)) :=
              mul_le_mul_of_nonneg_right hloss hcost
            _ < Real.exp A := htailRoom)
    refine ⟨omega, ?_, homega⟩
    rw [← hzero, zero_div]
    unfold zeroColorSampleRealWeight
    exact Finset.sum_nonneg fun i _hi => hretained0 i
  · exact exists_zeroColorSample_retention_and_all_weightedLoads_le_of_pos
      tests k retainedWeight weight cap A hretained0 hpos
      hcap hweight0 hweightCap hscale htailRoom

#print axioms card_zeroColorWeightedTestBadUnion_mul_exp_le
#print axioms exists_zeroColorSample_retention_and_all_weightedLoads_le_of_pos
#print axioms exists_zeroColorSample_retention_and_all_weightedLoads_le

end

end Family8ZeroColorChernoffSimultaneousSelectionV1
