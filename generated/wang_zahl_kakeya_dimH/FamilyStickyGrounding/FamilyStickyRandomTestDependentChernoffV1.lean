import FamilyStickyGrounding.FamilyStickyRandomPaperTailNumericsV1

open scoped BigOperators

namespace FamilyStickyRandomTestDependentChernoffV1

open FamilyStickyRandomFiniteChernoffV3
open FamilyStickyRandomTranslationIncidenceV1
open FamilyStickyRandomTranslationIncidenceV1.TranslationIncidenceModel
open FamilyStickyRandomPaperTailNumericsV1

noncomputable section

/-!
# Finite Chernoff with a test-dependent cap

GWZ Appendix lines 2681--2706 fix a test body `K` and use
`M_K = Delta_max(T) |K| / |T_delta|`.  Thus the cap and mean are naturally
test-dependent.  This module performs the finite union bound without replacing
them by a global worst-case cap.

For `cap K > 0`, use `lambda_K = (cap K)⁻¹`; the hypotheses
`repetitions * mean K <= cap K` give the same fixed chord loss for every K.
For `cap K = 0`, the actual assumptions `0 <= load <= cap` force every load to
be exactly zero, so that test contributes no bad outcomes.  No positive-cap
assumption is hidden.
-/

variable {choice test : Type*}
  [Fintype choice] [DecidableEq choice]

/-- Fixed-K tail-cardinality estimate with its own positive cap and mean. -/
theorem card_badOutcomes_mul_exp_le_fixed_of_cap_pos
    (repetitions : Nat) (load : choice -> Real)
    {cap mean A : Real}
    (hcap : 0 < cap) (hmean : 0 <= mean)
    (hload0 : forall g, 0 <= load g)
    (hloadCap : forall g, load g <= cap)
    (hsum : (∑ g : choice, load g) <=
      (Fintype.card choice : Real) * mean)
    (hscale : (repetitions : Real) * mean <= cap) :
    ((badOutcomes repetitions load (A * cap)).card : Real) *
        Real.exp A <=
      (Fintype.card choice : Real) ^ repetitions *
        Real.exp (Real.exp 1 - 1) := by
  let factor : Real :=
    1 + (mean / cap) * (Real.exp 1 - 1)
  have hlambda : 0 <= cap⁻¹ := inv_nonneg.mpr hcap.le
  have hinvCap : cap⁻¹ * cap = 1 := inv_mul_cancel₀ hcap.ne'
  have honeMoment :
      (∑ g : choice, Real.exp (cap⁻¹ * load g)) <=
        (Fintype.card choice : Real) * factor := by
    simpa [factor, hinvCap] using
      (sum_exp_load_le_card_mul_chord load hcap hlambda
        hload0 hloadCap hsum)
  have hmarkov := card_badOutcomes_mul_exp_le_pow
    repetitions load (threshold := A * cap) hlambda honeMoment
  have harg : cap⁻¹ * (A * cap) = A := by
    field_simp [hcap.ne']
  have hfactor := chord_factor_pow_le_exp_fixed
    repetitions hmean hcap hscale
  calc
    ((badOutcomes repetitions load (A * cap)).card : Real) *
        Real.exp A =
      ((badOutcomes repetitions load (A * cap)).card : Real) *
        Real.exp (cap⁻¹ * (A * cap)) := by rw [harg]
    _ <= ((Fintype.card choice : Real) * factor) ^ repetitions :=
      hmarkov
    _ = (Fintype.card choice : Real) ^ repetitions *
        factor ^ repetitions := by rw [mul_pow]
    _ <= (Fintype.card choice : Real) ^ repetitions *
        Real.exp (Real.exp 1 - 1) :=
      mul_le_mul_of_nonneg_left hfactor
        (pow_nonneg (Nat.cast_nonneg _) repetitions)

/-- Test-dependent finite Chernoff/union-bound producer. -/
theorem exists_product_choice_load_le_A_mul_cap
    [Nonempty choice]
    (tests : Finset test) (repetitions : Nat)
    (load : test -> choice -> Real) (cap mean : test -> Real) (A : Real)
    (hcap : forall K, K ∈ tests -> 0 <= cap K)
    (hmean : forall K, K ∈ tests -> 0 <= mean K)
    (hload0 : forall K, K ∈ tests -> forall g, 0 <= load K g)
    (hloadCap : forall K, K ∈ tests -> forall g,
      load K g <= cap K)
    (hsum : forall K, K ∈ tests ->
      (∑ g : choice, load K g) <=
        (Fintype.card choice : Real) * mean K)
    (hscale : forall K, K ∈ tests ->
      (repetitions : Real) * mean K <= cap K)
    (htailRoom :
      (tests.card : Real) * Real.exp (Real.exp 1 - 1) < Real.exp A) :
    exists omega : Fin repetitions -> choice,
      forall K, K ∈ tests ->
        productLoad (load K) omega <= A * cap K := by
  classical
  let positiveTests : Finset test := tests.filter fun K => 0 < cap K
  let bad : Finset (Fin repetitions -> choice) :=
    positiveTests.biUnion fun K =>
      badOutcomes repetitions (load K) (A * cap K)
  have hpositive_subset : positiveTests ⊆ tests :=
    Finset.filter_subset _ _
  have htail :
      (bad.card : Real) * Real.exp A <=
        (tests.card : Real) *
          ((Fintype.card choice : Real) ^ repetitions *
            Real.exp (Real.exp 1 - 1)) := by
    calc
      (bad.card : Real) * Real.exp A <=
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
  have hcardPos : 0 < (Fintype.card choice : Real) := by
    exact_mod_cast Fintype.card_pos
  have hcardPowPos :
      0 < (Fintype.card choice : Real) ^ repetitions :=
    pow_pos hcardPos repetitions
  have hbadMul :
      (bad.card : Real) * Real.exp A <
        (Fintype.card choice : Real) ^ repetitions * Real.exp A := by
    calc
      (bad.card : Real) * Real.exp A <=
          (tests.card : Real) *
            ((Fintype.card choice : Real) ^ repetitions *
              Real.exp (Real.exp 1 - 1)) := htail
      _ = (Fintype.card choice : Real) ^ repetitions *
          ((tests.card : Real) * Real.exp (Real.exp 1 - 1)) := by ring
      _ < (Fintype.card choice : Real) ^ repetitions * Real.exp A :=
        mul_lt_mul_of_pos_left htailRoom hcardPowPos
  have hbadCardReal :
      (bad.card : Real) < (Fintype.card choice : Real) ^ repetitions :=
    lt_of_mul_lt_mul_right hbadMul (Real.exp_pos A).le
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
  refine ⟨omega, ?_⟩
  intro K hK
  by_cases hKpos : 0 < cap K
  · have hKpositive : K ∈ positiveTests :=
      Finset.mem_filter.mpr ⟨hK, hKpos⟩
    have hnot : omega ∉
        badOutcomes repetitions (load K) (A * cap K) := by
      intro homegaK
      exact homegaBad (Finset.mem_biUnion.mpr
        ⟨K, hKpositive, homegaK⟩)
    simpa [badOutcomes] using hnot
  · have hcapZero : cap K = 0 :=
      le_antisymm (le_of_not_gt hKpos) (hcap K hK)
    have hloadZero : forall g, load K g = 0 := by
      intro g
      exact le_antisymm (by simpa [hcapZero] using hloadCap K hK g)
        (hload0 K hK g)
    simp [productLoad, hloadZero, hcapZero]

#print axioms card_badOutcomes_mul_exp_le_fixed_of_cap_pos
#print axioms exists_product_choice_load_le_A_mul_cap

end


end FamilyStickyRandomTestDependentChernoffV1
