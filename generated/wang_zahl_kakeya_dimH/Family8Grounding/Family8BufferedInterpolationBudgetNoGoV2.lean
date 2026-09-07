import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace Family8BufferedInterpolationBudgetNoGoV2

/-!
# A scalar obstruction for one common buffered interpolation exponent

This file deliberately contains no geometric imports.  It isolates the two
competing exponent constraints that remain after choosing
`b = tau^(1-t) * theta^t`.  In particular, it records that a fixed positive
ladder charge cannot be paid uniformly for every positive third-property
exponent when that exponent is quantified only after the ladder is fixed.
-/

/-- Feasibility of the middle and third exponent budgets at one buffered
interpolation exponent.  `thirdCost` includes the nonnegative fixed losses
remaining after the common factor `epsilon` has been extracted. -/
def InterpolationBudgetFeasible
    (epsilon middleGain middleTarget thirdEta etaPrime thirdCost : Real) : Prop :=
  exists t : Real,
    epsilon <= t /\ t <= 1 - epsilon /\
    middleTarget <= epsilon * t * middleGain /\
    thirdCost <= epsilon * ((1 - t) * thirdEta - etaPrime)

/-- If the most favorable buffered endpoint still leaves less third exponent
than the fixed ladder charge, no interpolation point can satisfy the budget. -/
theorem interpolationBudget_not_feasible_of_third_gap
    {epsilon middleGain middleTarget thirdEta etaPrime thirdCost : Real}
    (hepsilon : 0 < epsilon) (hthirdEta : 0 <= thirdEta)
    (hthirdCost : 0 <= thirdCost)
    (hgap : (1 - epsilon) * thirdEta < etaPrime) :
    ¬ InterpolationBudgetFeasible epsilon middleGain middleTarget
      thirdEta etaPrime thirdCost := by
  rintro ⟨t, het, _hte, _hmiddle, hthird⟩
  have hscale : (1 - t) * thirdEta <= (1 - epsilon) * thirdEta := by
    exact mul_le_mul_of_nonneg_right (by linarith) hthirdEta
  have hnegative :
      epsilon * ((1 - t) * thirdEta - etaPrime) < 0 := by
    have : (1 - t) * thirdEta - etaPrime < 0 := by linarith
    exact mul_neg_of_pos_of_neg hepsilon this
  linarith

/-- For every fixed positive ladder charge, the positive choice
`thirdEta = etaPrime / 2` defeats every buffered interpolation point,
independently of the middle-side parameters. -/
theorem exists_positive_thirdEta_for_which_no_interpolation
    {epsilon etaPrime : Real}
    (hepsilon : 0 < epsilon) (hetaPrime : 0 < etaPrime) :
    exists thirdEta : Real,
      0 < thirdEta /\
      forall middleGain middleTarget thirdCost : Real,
        0 <= thirdCost ->
        ¬ InterpolationBudgetFeasible epsilon middleGain middleTarget
          thirdEta etaPrime thirdCost := by
  refine ⟨etaPrime / 2, by positivity, ?_⟩
  intro middleGain middleTarget thirdCost hthirdCost
  apply interpolationBudget_not_feasible_of_third_gap
    hepsilon (by positivity) hthirdCost
  nlinarith

#print axioms InterpolationBudgetFeasible
#print axioms interpolationBudget_not_feasible_of_third_gap
#print axioms exists_positive_thirdEta_for_which_no_interpolation

end Family8BufferedInterpolationBudgetNoGoV2
