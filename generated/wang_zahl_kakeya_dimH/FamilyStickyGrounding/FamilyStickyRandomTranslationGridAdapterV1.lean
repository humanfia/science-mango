import FamilyStickyGrounding.FamilyStickyRandomTranslationIncidenceV1

open scoped BigOperators

namespace FamilyStickyRandomTranslationGridAdapterV1

open FamilyStickyRandomFiniteChernoffV3
open FamilyStickyRandomTranslationIncidenceV1

noncomputable section

namespace TranslationIncidenceModel

variable {translation tube test : Type*}
  [Fintype translation] [DecidableEq translation]
  [DecidableEq tube]

/-!
# From literal grid incidences to simultaneous good translations

The hypotheses below are local and geometric:

* for each tube and test, at most `translationBudget K` grid translations
  move that tube into the test;
* the resulting total incidence count fits the desired mean;
* each single translated family has the indicated load cap.

All exponential amplification and the union over test bodies are supplied by
the imported finite Chernoff module.
-/

/-- Cast the exact natural-number double count into the real mean bound used
by the exponential-moment theorem. -/
theorem sum_load_le_of_gridHitsTube_le
    (M : TranslationIncidenceModel translation tube test)
    (K : test) (translationBudget : Nat) (mean : Real)
    (hgrid : forall T, T ∈ M.tubes ->
      M.gridHitsTube K T <= translationBudget)
    (hbalance :
      (M.tubes.card : Real) * (translationBudget : Real) <=
        (Fintype.card translation : Real) * mean) :
    (∑ g : translation, M.load K g) <=
      (Fintype.card translation : Real) * mean := by
  have hnat :=
    M.sum_loadNat_le_card_mul_of_gridHitsTube_le K translationBudget hgrid
  calc
    (∑ g : translation, M.load K g) =
        ((∑ g : translation, M.loadNat K g : Nat) : Real) := by
      simp [FamilyStickyRandomTranslationIncidenceV1.TranslationIncidenceModel.load]
    _ <= ((M.tubes.card * translationBudget : Nat) : Real) := by
      exact_mod_cast hnat
    _ = (M.tubes.card : Real) * (translationBudget : Real) := by
      norm_num
    _ <= (Fintype.card translation : Real) * mean := hbalance

/-- The all-test exponential tail obtained directly from per-tube grid
incidence bounds.  No probabilistic conclusion appears among the inputs. -/
theorem card_bad_all_tests_mul_exp_le_of_gridIncidence
    [DecidableEq test]
    (M : TranslationIncidenceModel translation tube test)
    (translationBudget : test -> Nat) (repetitions : Nat)
    {cap mean lambda threshold : Real}
    (hcap : 0 < cap) (hlambda : 0 <= lambda)
    (hloadCap : forall K, K ∈ M.tests -> forall g,
      M.load K g <= cap)
    (hgrid : forall K, K ∈ M.tests -> forall T, T ∈ M.tubes ->
      M.gridHitsTube K T <= translationBudget K)
    (hbalance : forall K, K ∈ M.tests ->
      (M.tubes.card : Real) * (translationBudget K : Real) <=
        (Fintype.card translation : Real) * mean) :
    (((M.tests.biUnion fun K =>
          badOutcomes repetitions (M.load K) threshold).card : Nat) : Real) *
        Real.exp (lambda * threshold) <=
      (M.tests.card : Real) *
        ((Fintype.card translation : Real) *
          (1 + (mean / cap) *
            (Real.exp (lambda * cap) - 1))) ^ repetitions := by
  apply M.card_bad_all_tests_mul_exp_le repetitions hcap hlambda hloadCap
  intro K hK
  exact sum_load_le_of_gridHitsTube_le M K (translationBudget K) mean
    (hgrid K hK) (hbalance K hK)

/-- Source-shaped finite random-motion conclusion: under the explicit
numerical tail condition, a tuple of grid translations simultaneously keeps
every test load below `threshold`. -/
theorem exists_product_choice_load_le_of_gridIncidence
    [DecidableEq test]
    (M : TranslationIncidenceModel translation tube test)
    (translationBudget : test -> Nat) (repetitions : Nat)
    {cap mean lambda threshold : Real}
    (hcap : 0 < cap) (hlambda : 0 <= lambda)
    (hloadCap : forall K, K ∈ M.tests -> forall g,
      M.load K g <= cap)
    (hgrid : forall K, K ∈ M.tests -> forall T, T ∈ M.tubes ->
      M.gridHitsTube K T <= translationBudget K)
    (hbalance : forall K, K ∈ M.tests ->
      (M.tubes.card : Real) * (translationBudget K : Real) <=
        (Fintype.card translation : Real) * mean)
    (hnumerical :
      (M.tests.card : Real) *
          ((Fintype.card translation : Real) *
            (1 + (mean / cap) *
              (Real.exp (lambda * cap) - 1))) ^ repetitions <
        ((Finset.univ : Finset (Fin repetitions -> translation)).card : Real) *
          Real.exp (lambda * threshold)) :
    exists omega : Fin repetitions -> translation,
      forall K, K ∈ M.tests ->
        productLoad (M.load K) omega <= threshold := by
  apply M.exists_product_choice_load_le repetitions hcap hlambda hloadCap
  · intro K hK
    exact sum_load_le_of_gridHitsTube_le M K (translationBudget K) mean
      (hgrid K hK) (hbalance K hK)
  · exact hnumerical

#print axioms sum_load_le_of_gridHitsTube_le
#print axioms card_bad_all_tests_mul_exp_le_of_gridIncidence
#print axioms exists_product_choice_load_le_of_gridIncidence

end TranslationIncidenceModel

end

end FamilyStickyRandomTranslationGridAdapterV1
