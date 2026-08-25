import FamilyStickyGrounding.FamilyStickyRandomTestDependentChernoffV1

open scoped BigOperators

namespace FamilyStickyRandomTwoFamilyChernoffV1

open FamilyStickyRandomFiniteChernoffV3
open FamilyStickyRandomTestDependentChernoffV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# One finite product choice for two families of tests

The random-motion application has two genuinely different collections of bad
events: the analytic load tests of GWZ Appendix lines 2681--2706 and the
model-tube collision tests from lines 2655--2677.  Their useful tail parameters
are different.  This module performs the one required union bound without
replacing either tail by a common, artificially larger value.

The proof uses the fixed-test exponential-moment estimate from
`FamilyStickyRandomTestDependentChernoffV1`; it is not a Markov-only tail
argument.  Zero caps are discharged from the actual pointwise zero-load
conclusion exactly as in the one-family theorem.
-/

variable {choice test : Type*}
  [Fintype choice] [DecidableEq choice] [DecidableEq test]

/-- Positive-cap tests whose product load exceeds their own scaled cap. -/
def testBadUnion
    (tests : Finset test) (repetitions : Nat)
    (load : test -> choice -> Real) (cap : test -> Real) (A : Real) :
    Finset (Fin repetitions -> choice) :=
  (tests.filter fun K => 0 < cap K).biUnion fun K =>
    badOutcomes repetitions (load K) (A * cap K)

/-- Exponential-cardinality estimate for one finite family of heterogeneous
caps.  This is the reusable part of the one-family union-bound proof. -/
theorem card_testBadUnion_mul_exp_le
    (tests : Finset test) (repetitions : Nat)
    (load : test -> choice -> Real) (cap mean : test -> Real) (A : Real)
    (hmean : forall K, K ∈ tests -> 0 <= mean K)
    (hload0 : forall K, K ∈ tests -> forall g, 0 <= load K g)
    (hloadCap : forall K, K ∈ tests -> forall g, load K g <= cap K)
    (hsum : forall K, K ∈ tests ->
      (∑ g : choice, load K g) <=
        (Fintype.card choice : Real) * mean K)
    (hscale : forall K, K ∈ tests ->
      (repetitions : Real) * mean K <= cap K) :
    ((testBadUnion tests repetitions load cap A).card : Real) * Real.exp A <=
      (tests.card : Real) *
        ((Fintype.card choice : Real) ^ repetitions *
          Real.exp (Real.exp 1 - 1)) := by
  classical
  let positiveTests : Finset test := tests.filter fun K => 0 < cap K
  have hpositive_subset : positiveTests ⊆ tests :=
    Finset.filter_subset _ _
  calc
    ((testBadUnion tests repetitions load cap A).card : Real) * Real.exp A <=
        ((∑ K ∈ positiveTests,
            (badOutcomes repetitions (load K) (A * cap K)).card : Nat) :
          Real) * Real.exp A := by
      gcongr
      exact Finset.card_biUnion_le
    _ = ∑ K ∈ positiveTests,
        ((badOutcomes repetitions (load K) (A * cap K)).card : Real) *
          Real.exp A := by
      push_cast
      rw [Finset.sum_mul]
    _ <= ∑ _K ∈ positiveTests,
        (Fintype.card choice : Real) ^ repetitions *
          Real.exp (Real.exp 1 - 1) := by
      apply Finset.sum_le_sum
      intro K hK
      have hKtests : K ∈ tests := hpositive_subset hK
      have hKpos : 0 < cap K := (Finset.mem_filter.mp hK).2
      exact card_badOutcomes_mul_exp_le_fixed_of_cap_pos
        repetitions (load K) hKpos (hmean K hKtests)
        (hload0 K hKtests) (hloadCap K hKtests)
        (hsum K hKtests) (hscale K hKtests)
    _ = (positiveTests.card : Real) *
        ((Fintype.card choice : Real) ^ repetitions *
          Real.exp (Real.exp 1 - 1)) := by simp
    _ <= (tests.card : Real) *
        ((Fintype.card choice : Real) ^ repetitions *
          Real.exp (Real.exp 1 - 1)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_le_card hpositive_subset

variable {test₁ test₂ : Type*}
  [DecidableEq test₁] [DecidableEq test₂]

/-- Two heterogeneous test families share one product outcome while retaining
their distinct thresholds `A₁` and `A₂`.

The displayed `htailRoom` is precisely the two-family union-bound inequality:
after multiplying by `exp A₁ * exp A₂`, its two summands are the analytic and
collision bad-event bounds respectively. -/
theorem exists_product_choice_two_load_bounds
    [Nonempty choice]
    (tests₁ : Finset test₁) (tests₂ : Finset test₂) (repetitions : Nat)
    (load₁ : test₁ -> choice -> Real) (cap₁ mean₁ : test₁ -> Real)
    (load₂ : test₂ -> choice -> Real) (cap₂ mean₂ : test₂ -> Real)
    (A₁ A₂ : Real)
    (hcap₁ : forall K, K ∈ tests₁ -> 0 <= cap₁ K)
    (hmean₁ : forall K, K ∈ tests₁ -> 0 <= mean₁ K)
    (hload0₁ : forall K, K ∈ tests₁ -> forall g, 0 <= load₁ K g)
    (hloadCap₁ : forall K, K ∈ tests₁ -> forall g, load₁ K g <= cap₁ K)
    (hsum₁ : forall K, K ∈ tests₁ ->
      (∑ g : choice, load₁ K g) <=
        (Fintype.card choice : Real) * mean₁ K)
    (hscale₁ : forall K, K ∈ tests₁ ->
      (repetitions : Real) * mean₁ K <= cap₁ K)
    (hcap₂ : forall K, K ∈ tests₂ -> 0 <= cap₂ K)
    (hmean₂ : forall K, K ∈ tests₂ -> 0 <= mean₂ K)
    (hload0₂ : forall K, K ∈ tests₂ -> forall g, 0 <= load₂ K g)
    (hloadCap₂ : forall K, K ∈ tests₂ -> forall g, load₂ K g <= cap₂ K)
    (hsum₂ : forall K, K ∈ tests₂ ->
      (∑ g : choice, load₂ K g) <=
        (Fintype.card choice : Real) * mean₂ K)
    (hscale₂ : forall K, K ∈ tests₂ ->
      (repetitions : Real) * mean₂ K <= cap₂ K)
    (htailRoom :
      (tests₁.card : Real) * Real.exp (Real.exp 1 - 1) * Real.exp A₂ +
          (tests₂.card : Real) * Real.exp (Real.exp 1 - 1) * Real.exp A₁ <
        Real.exp A₁ * Real.exp A₂) :
    exists omega : Fin repetitions -> choice,
      (forall K, K ∈ tests₁ ->
        productLoad (load₁ K) omega <= A₁ * cap₁ K) ∧
      (forall K, K ∈ tests₂ ->
        productLoad (load₂ K) omega <= A₂ * cap₂ K) := by
  classical
  let bad₁ : Finset (Fin repetitions -> choice) :=
    testBadUnion tests₁ repetitions load₁ cap₁ A₁
  let bad₂ : Finset (Fin repetitions -> choice) :=
    testBadUnion tests₂ repetitions load₂ cap₂ A₂
  let bad : Finset (Fin repetitions -> choice) := bad₁ ∪ bad₂
  have htail₁ :
      (bad₁.card : Real) * Real.exp A₁ <=
        (tests₁.card : Real) *
          ((Fintype.card choice : Real) ^ repetitions *
            Real.exp (Real.exp 1 - 1)) := by
    exact card_testBadUnion_mul_exp_le tests₁ repetitions load₁ cap₁ mean₁ A₁
      hmean₁ hload0₁ hloadCap₁ hsum₁ hscale₁
  have htail₂ :
      (bad₂.card : Real) * Real.exp A₂ <=
        (tests₂.card : Real) *
          ((Fintype.card choice : Real) ^ repetitions *
            Real.exp (Real.exp 1 - 1)) := by
    exact card_testBadUnion_mul_exp_le tests₂ repetitions load₂ cap₂ mean₂ A₂
      hmean₂ hload0₂ hloadCap₂ hsum₂ hscale₂
  have hcardPos : 0 < (Fintype.card choice : Real) := by
    exact_mod_cast Fintype.card_pos
  have hcardPowPos : 0 < (Fintype.card choice : Real) ^ repetitions :=
    pow_pos hcardPos repetitions
  have hbadCardCast : (bad.card : Real) <=
      (bad₁.card : Real) + (bad₂.card : Real) := by
    exact_mod_cast Finset.card_union_le bad₁ bad₂
  have hbadMul :
      ((bad.card : Real) * Real.exp A₁) * Real.exp A₂ <
        ((Fintype.card choice : Real) ^ repetitions * Real.exp A₁) *
          Real.exp A₂ := by
    calc
      ((bad.card : Real) * Real.exp A₁) * Real.exp A₂ <=
          (((bad₁.card : Real) + (bad₂.card : Real)) * Real.exp A₁) *
            Real.exp A₂ := by
        gcongr
      _ = ((bad₁.card : Real) * Real.exp A₁) * Real.exp A₂ +
          ((bad₂.card : Real) * Real.exp A₂) * Real.exp A₁ := by ring
      _ <= ((tests₁.card : Real) *
            ((Fintype.card choice : Real) ^ repetitions *
              Real.exp (Real.exp 1 - 1))) * Real.exp A₂ +
          ((tests₂.card : Real) *
            ((Fintype.card choice : Real) ^ repetitions *
              Real.exp (Real.exp 1 - 1))) * Real.exp A₁ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right htail₁ (Real.exp_pos A₂).le)
          (mul_le_mul_of_nonneg_right htail₂ (Real.exp_pos A₁).le)
      _ = (Fintype.card choice : Real) ^ repetitions *
          ((tests₁.card : Real) * Real.exp (Real.exp 1 - 1) * Real.exp A₂ +
            (tests₂.card : Real) * Real.exp (Real.exp 1 - 1) * Real.exp A₁) := by
        ring
      _ < (Fintype.card choice : Real) ^ repetitions *
          (Real.exp A₁ * Real.exp A₂) :=
        mul_lt_mul_of_pos_left htailRoom hcardPowPos
      _ = ((Fintype.card choice : Real) ^ repetitions * Real.exp A₁) *
          Real.exp A₂ := by ring
  have hbadCardReal :
      (bad.card : Real) < (Fintype.card choice : Real) ^ repetitions := by
    have hpos : 0 < Real.exp A₁ * Real.exp A₂ := mul_pos (Real.exp_pos _) (Real.exp_pos _)
    nlinarith [hbadMul]
  have hcardOutcomes :
      ((Finset.univ : Finset (Fin repetitions -> choice)).card : Real) =
        (Fintype.card choice : Real) ^ repetitions := by simp
  have hbadCard : bad.card <
      (Finset.univ : Finset (Fin repetitions -> choice)).card := by
    exact_mod_cast (show (bad.card : Real) <
      ((Finset.univ : Finset (Fin repetitions -> choice)).card : Real) by
        rw [hcardOutcomes]
        exact hbadCardReal)
  have hproper : bad ⊂
      (Finset.univ : Finset (Fin repetitions -> choice)) :=
    Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ bad, fun heq =>
        (ne_of_lt hbadCard) (congrArg Finset.card heq)⟩
  obtain ⟨omega, _homega, homegaBad⟩ := Finset.exists_of_ssubset hproper
  refine ⟨omega, ?_, ?_⟩
  · intro K hK
    by_cases hKpos : 0 < cap₁ K
    · have hnot : omega ∉
          badOutcomes repetitions (load₁ K) (A₁ * cap₁ K) := by
        intro homegaK
        apply homegaBad
        exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
          ⟨K, Finset.mem_filter.mpr ⟨hK, hKpos⟩, homegaK⟩)
      simpa [badOutcomes] using hnot
    · have hcapZero : cap₁ K = 0 :=
        le_antisymm (le_of_not_gt hKpos) (hcap₁ K hK)
      have hloadZero : forall g, load₁ K g = 0 := by
        intro g
        exact le_antisymm (by simpa [hcapZero] using hloadCap₁ K hK g)
          (hload0₁ K hK g)
      simp [productLoad, hloadZero, hcapZero]
  · intro K hK
    by_cases hKpos : 0 < cap₂ K
    · have hnot : omega ∉
          badOutcomes repetitions (load₂ K) (A₂ * cap₂ K) := by
        intro homegaK
        apply homegaBad
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨K, Finset.mem_filter.mpr ⟨hK, hKpos⟩, homegaK⟩)
      simpa [badOutcomes] using hnot
    · have hcapZero : cap₂ K = 0 :=
        le_antisymm (le_of_not_gt hKpos) (hcap₂ K hK)
      have hloadZero : forall g, load₂ K g = 0 := by
        intro g
        exact le_antisymm (by simpa [hcapZero] using hloadCap₂ K hK g)
          (hload0₂ K hK g)
      simp [productLoad, hloadZero, hcapZero]

#print axioms card_testBadUnion_mul_exp_le
#print axioms exists_product_choice_two_load_bounds

end

end FamilyStickyRandomTwoFamilyChernoffV1
