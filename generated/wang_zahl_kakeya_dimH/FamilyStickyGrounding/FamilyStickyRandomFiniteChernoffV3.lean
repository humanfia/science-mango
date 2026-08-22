import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators

namespace FamilyStickyRandomFiniteChernoffV3

noncomputable section

/-!
# A finite-product exponential tail and union bound

The sample space is the literal finite product `Fin repetitions -> choice`.
Independence is therefore the proved product-sum identity below, rather than
an assumption about a continuous probability space.  A local one-translation
moment estimate is amplified before exponential Markov and the union bound
are applied.
-/

def productLoad {choice : Type*} {repetitions : Nat}
    (load : choice -> Real) (omega : Fin repetitions -> choice) : Real :=
  ∑ j, load (omega j)

def badOutcomes {choice : Type*} [Fintype choice]
    (repetitions : Nat) (load : choice -> Real) (threshold : Real) :
    Finset (Fin repetitions -> choice) := by
  classical
  exact Finset.univ.filter fun omega =>
    threshold < productLoad load omega

/-- Exact finite-product factorization of the exponential moment. -/
theorem sum_exp_productLoad
    {choice : Type*} [Fintype choice] [DecidableEq choice]
    (repetitions : Nat) (load : choice -> Real) (lambda : Real) :
    (∑ omega : Fin repetitions -> choice,
        Real.exp (lambda * productLoad load omega)) =
      (∑ g : choice, Real.exp (lambda * load g)) ^ repetitions := by
  unfold productLoad
  simp_rw [Finset.mul_sum, Real.exp_sum]
  calc
    (∑ omega : Fin repetitions -> choice,
        ∏ j, Real.exp (lambda * load (omega j))) =
      ∏ _j : Fin repetitions,
        ∑ g : choice, Real.exp (lambda * load g) :=
      (Fintype.prod_sum
        (fun _j : Fin repetitions =>
          fun g : choice => Real.exp (lambda * load g))).symm
    _ = (∑ g : choice, Real.exp (lambda * load g)) ^ repetitions := by
      simp

/-- Finite exponential Markov inequality, in cardinal form. -/
theorem card_badOutcomes_mul_exp_le_sum
    {choice : Type*} [Fintype choice] [DecidableEq choice]
    (repetitions : Nat) (load : choice -> Real)
    {lambda threshold : Real} (hlambda : 0 <= lambda) :
    ((badOutcomes repetitions load threshold).card : Real) *
        Real.exp (lambda * threshold) <=
      ∑ omega : Fin repetitions -> choice,
        Real.exp (lambda * productLoad load omega) := by
  classical
  calc
    ((badOutcomes repetitions load threshold).card : Real) *
          Real.exp (lambda * threshold) =
        ∑ omega ∈ badOutcomes repetitions load threshold,
          Real.exp (lambda * threshold) := by simp
    _ <= ∑ omega ∈ badOutcomes repetitions load threshold,
          Real.exp (lambda * productLoad load omega) := by
      apply Finset.sum_le_sum
      intro omega homega
      rw [badOutcomes, Finset.mem_filter] at homega
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left homega.2.le hlambda)
    _ <= ∑ omega : Fin repetitions -> choice,
          Real.exp (lambda * productLoad load omega) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => (Real.exp_pos _).le)

/-- Chernoff amplification of a local one-choice moment estimate. -/
theorem card_badOutcomes_mul_exp_le_pow
    {choice : Type*} [Fintype choice] [DecidableEq choice]
    (repetitions : Nat) (load : choice -> Real)
    {lambda threshold moment : Real}
    (hlambda : 0 <= lambda)
    (honeMoment : (∑ g : choice, Real.exp (lambda * load g)) <= moment) :
    ((badOutcomes repetitions load threshold).card : Real) *
        Real.exp (lambda * threshold) <= moment ^ repetitions := by
  calc
    ((badOutcomes repetitions load threshold).card : Real) *
          Real.exp (lambda * threshold) <=
        ∑ omega : Fin repetitions -> choice,
          Real.exp (lambda * productLoad load omega) :=
      card_badOutcomes_mul_exp_le_sum repetitions load hlambda
    _ = (∑ g : choice, Real.exp (lambda * load g)) ^ repetitions :=
      sum_exp_productLoad repetitions load lambda
    _ <= moment ^ repetitions := by
      apply pow_le_pow_left₀
      · exact Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
      · exact honeMoment

/-- Finite union bound over all literal test bodies. -/
theorem card_biUnion_badOutcomes_mul_exp_le
    {choice test : Type*}
    [Fintype choice] [DecidableEq choice] [DecidableEq test]
    (tests : Finset test) (repetitions : Nat)
    (load : test -> choice -> Real)
    {lambda threshold moment : Real}
    (hlambda : 0 <= lambda)
    (honeMoment : forall K, K ∈ tests ->
      (∑ g : choice, Real.exp (lambda * load K g)) <= moment) :
    (((tests.biUnion fun K =>
          badOutcomes repetitions (load K) threshold).card : Nat) : Real) *
        Real.exp (lambda * threshold) <=
      (tests.card : Real) * moment ^ repetitions := by
  classical
  calc
    (((tests.biUnion fun K =>
            badOutcomes repetitions (load K) threshold).card : Nat) : Real) *
          Real.exp (lambda * threshold) <=
        ((∑ K ∈ tests,
            (badOutcomes repetitions (load K) threshold).card : Nat) : Real) *
          Real.exp (lambda * threshold) := by
      gcongr
      exact Finset.card_biUnion_le
    _ = ∑ K ∈ tests,
          ((badOutcomes repetitions (load K) threshold).card : Real) *
            Real.exp (lambda * threshold) := by
      push_cast
      rw [Finset.sum_mul]
    _ <= ∑ K ∈ tests, moment ^ repetitions := by
      apply Finset.sum_le_sum
      intro K hK
      exact card_badOutcomes_mul_exp_le_pow repetitions (load K)
        hlambda (honeMoment K hK)
    _ = (tests.card : Real) * moment ^ repetitions := by simp

#print axioms sum_exp_productLoad
#print axioms card_badOutcomes_mul_exp_le_sum
#print axioms card_badOutcomes_mul_exp_le_pow
#print axioms card_biUnion_badOutcomes_mul_exp_le

end

end FamilyStickyRandomFiniteChernoffV3
