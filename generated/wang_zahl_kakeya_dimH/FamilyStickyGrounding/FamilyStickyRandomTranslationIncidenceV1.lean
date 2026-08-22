import FamilyStickyGrounding.FamilyStickyRandomFiniteChernoffV3
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.BigOperators.Field

open scoped BigOperators

namespace FamilyStickyRandomTranslationIncidenceV1

open FamilyStickyRandomFiniteChernoffV3

noncomputable section

/-!
# Finite translation-incidence adapter for sticky Kakeya

This module turns literal incidence counts on a finite translation grid into
the one-coordinate exponential moment required by the finite Chernoff
engine.  It does not assume the random-motion conclusion.  In particular,
the geometric inputs are only a cap on one translated load and a bound on
how many grid translations can move one tube into one test body.
-/

/-- Finite data used in place of continuous uniformly random translations. -/
structure TranslationIncidenceModel
    (translation tube test : Type*) [Fintype translation]
    [DecidableEq translation] [DecidableEq tube] where
  tubes : Finset tube
  tests : Finset test
  hits : translation -> tube -> test -> Bool

namespace TranslationIncidenceModel

variable {translation tube test : Type*}
  [Fintype translation] [DecidableEq translation]
  [DecidableEq tube]

/-- Number of tubes moved into one test body by one grid translation. -/
def loadNat (M : TranslationIncidenceModel translation tube test)
    (K : test) (g : translation) : Nat :=
  (M.tubes.filter fun T => M.hits g T K = true).card

/-- The same load embedded in the reals for exponential moments. -/
def load (M : TranslationIncidenceModel translation tube test)
    (K : test) (g : translation) : Real :=
  M.loadNat K g

/-- Number of translations in the grid that move one fixed tube into a
fixed test body. -/
def gridHitsTube (M : TranslationIncidenceModel translation tube test)
    (K : test) (T : tube) : Nat :=
  (Finset.univ.filter fun g => M.hits g T K = true).card

/-- Exact finite double counting of translation--tube incidences. -/
theorem sum_loadNat_eq_sum_gridHitsTube
    (M : TranslationIncidenceModel translation tube test) (K : test) :
    (∑ g : translation, M.loadNat K g) =
      ∑ T ∈ M.tubes, M.gridHitsTube K T := by
  simpa [loadNat, gridHitsTube, Finset.bipartiteAbove,
    Finset.bipartiteBelow] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (s := (Finset.univ : Finset translation)) (t := M.tubes)
        (r := fun g T => M.hits g T K = true))

/-- A per-tube grid-incidence cap gives the total one-translation load
bound required in the moment estimate. -/
theorem sum_loadNat_le_card_mul_of_gridHitsTube_le
    (M : TranslationIncidenceModel translation tube test)
    (K : test) (translationBudget : Nat)
    (hgrid : forall T, T ∈ M.tubes ->
      M.gridHitsTube K T <= translationBudget) :
    (∑ g : translation, M.loadNat K g) <=
      M.tubes.card * translationBudget := by
  rw [M.sum_loadNat_eq_sum_gridHitsTube K]
  calc
    (∑ T ∈ M.tubes, M.gridHitsTube K T) <=
        ∑ _T ∈ M.tubes, translationBudget := by
      exact Finset.sum_le_sum fun T hT => hgrid T hT
    _ = M.tubes.card * translationBudget := by simp

/-- Exponential convexity on the interval `[0, cap]`. -/
theorem exp_le_endpoint_chord
    {x cap lambda : Real}
    (hx0 : 0 <= x) (hxcap : x <= cap) (hcap : 0 < cap) :
    Real.exp (lambda * x) <=
      1 + (x / cap) * (Real.exp (lambda * cap) - 1) := by
  have hratio0 : 0 <= x / cap := div_nonneg hx0 hcap.le
  have hratio1 : x / cap <= 1 := (div_le_one hcap).mpr hxcap
  have hconv := convexOn_exp.2
    (Set.mem_univ (0 : Real)) (Set.mem_univ (lambda * cap))
    (sub_nonneg.mpr hratio1) hratio0 (by ring)
  have harg :
      (1 - x / cap) * 0 + (x / cap) * (lambda * cap) =
        lambda * x := by
    field_simp [hcap.ne']; ring
  have hrhs :
      (1 - x / cap) * Real.exp 0 +
          (x / cap) * Real.exp (lambda * cap) =
        1 + (x / cap) * (Real.exp (lambda * cap) - 1) := by
    rw [Real.exp_zero]
    ring
  simpa only [smul_eq_mul, harg, hrhs] using hconv

/-- A cap and a total incidence bound imply the local exponential-moment
bound.  This is the finite analogue of the one-translation computation in
the proof of `lemrandommotion`. -/
theorem sum_exp_load_le_card_mul_chord
    {choice : Type*} [Fintype choice] [DecidableEq choice]
    (x : choice -> Real) {cap mean lambda : Real}
    (hcap : 0 < cap) (hlambda : 0 <= lambda)
    (hx0 : forall g, 0 <= x g) (hxcap : forall g, x g <= cap)
    (hsum : (∑ g : choice, x g) <= (Fintype.card choice : Real) * mean) :
    (∑ g : choice, Real.exp (lambda * x g)) <=
      (Fintype.card choice : Real) *
        (1 + (mean / cap) * (Real.exp (lambda * cap) - 1)) := by
  have hexp : 0 <= Real.exp (lambda * cap) - 1 := by
    exact sub_nonneg.mpr
      (Real.one_le_exp_iff.mpr (mul_nonneg hlambda hcap.le))
  calc
    (∑ g : choice, Real.exp (lambda * x g)) <=
        ∑ g : choice,
          (1 + (x g / cap) * (Real.exp (lambda * cap) - 1)) := by
      exact Finset.sum_le_sum fun g _ =>
        exp_le_endpoint_chord (hx0 g) (hxcap g) hcap
    _ = (Fintype.card choice : Real) +
          ((∑ g : choice, x g) / cap) *
            (Real.exp (lambda * cap) - 1) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      rw [← Finset.sum_mul, ← Finset.sum_div]
    _ <= (Fintype.card choice : Real) +
          (((Fintype.card choice : Real) * mean) / cap) *
            (Real.exp (lambda * cap) - 1) := by
      gcongr
    _ = (Fintype.card choice : Real) *
          (1 + (mean / cap) *
            (Real.exp (lambda * cap) - 1)) := by
      ring

/-- All-test many-translation tail bound, produced from literal local load
caps and literal total incidence estimates. -/
theorem card_bad_all_tests_mul_exp_le
    [DecidableEq test]
    (M : TranslationIncidenceModel translation tube test)
    (repetitions : Nat) {cap mean lambda threshold : Real}
    (hcap : 0 < cap) (hlambda : 0 <= lambda)
    (hloadCap : forall K, K ∈ M.tests -> forall g,
      M.load K g <= cap)
    (hsum : forall K, K ∈ M.tests ->
      (∑ g : translation, M.load K g) <=
        (Fintype.card translation : Real) * mean) :
    (((M.tests.biUnion fun K =>
          badOutcomes repetitions (M.load K) threshold).card : Nat) : Real) *
        Real.exp (lambda * threshold) <=
      (M.tests.card : Real) *
        ((Fintype.card translation : Real) *
          (1 + (mean / cap) *
            (Real.exp (lambda * cap) - 1))) ^ repetitions := by
  apply card_biUnion_badOutcomes_mul_exp_le M.tests repetitions M.load
    hlambda
  intro K hK
  exact sum_exp_load_le_card_mul_chord (M.load K) hcap hlambda
    (fun _ => Nat.cast_nonneg _) (hloadCap K hK) (hsum K hK)

/-- If the union-tail cardinal bound is strictly smaller than the finite
product sample space, one tuple of translations is simultaneously good for
every test body. -/
theorem exists_product_choice_load_le
    [DecidableEq test]
    (M : TranslationIncidenceModel translation tube test)
    (repetitions : Nat) {cap mean lambda threshold : Real}
    (hcap : 0 < cap) (hlambda : 0 <= lambda)
    (hloadCap : forall K, K ∈ M.tests -> forall g,
      M.load K g <= cap)
    (hsum : forall K, K ∈ M.tests ->
      (∑ g : translation, M.load K g) <=
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
  classical
  let bad : Finset (Fin repetitions -> translation) :=
    M.tests.biUnion fun K => badOutcomes repetitions (M.load K) threshold
  have htail :
      (bad.card : Real) * Real.exp (lambda * threshold) <=
        (M.tests.card : Real) *
          ((Fintype.card translation : Real) *
            (1 + (mean / cap) *
              (Real.exp (lambda * cap) - 1))) ^ repetitions := by
    exact M.card_bad_all_tests_mul_exp_le repetitions hcap hlambda
      hloadCap hsum
  have hcardReal :
      (bad.card : Real) <
        ((Finset.univ : Finset (Fin repetitions -> translation)).card : Real) := by
    exact lt_of_mul_lt_mul_right (htail.trans_lt hnumerical)
      (Real.exp_pos (lambda * threshold)).le
  have hcard : bad.card <
      (Finset.univ : Finset (Fin repetitions -> translation)).card := by
    exact_mod_cast hcardReal
  have hproper : bad ⊂
      (Finset.univ : Finset (Fin repetitions -> translation)) := by
    exact Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ bad, fun h =>
        (ne_of_lt hcard) (congrArg Finset.card h)⟩
  obtain ⟨omega, _homega, homegaBad⟩ := Finset.exists_of_ssubset hproper
  refine ⟨omega, ?_⟩
  intro K hK
  have hnot : omega ∉ badOutcomes repetitions (M.load K) threshold := by
    intro homegaK
    exact homegaBad (Finset.mem_biUnion.mpr ⟨K, hK, homegaK⟩)
  simpa [badOutcomes] using hnot

#print axioms sum_loadNat_eq_sum_gridHitsTube
#print axioms sum_loadNat_le_card_mul_of_gridHitsTube_le
#print axioms exp_le_endpoint_chord
#print axioms sum_exp_load_le_card_mul_chord
#print axioms card_bad_all_tests_mul_exp_le
#print axioms exists_product_choice_load_le

end TranslationIncidenceModel

end

end FamilyStickyRandomTranslationIncidenceV1
