import ArchonPhysics.PhyslibFPUTActualBranchingA1SquareCutoffBudget

/-!
# Thermalization consumer: actual branching square-cutoff budgets

This consumer checks the bridge from the fixed-tree heterogeneous A1
`ENNReal` fiber-law estimate to the real bad-event budget used by the garden
power schedule.  At `gamma = |g|^2`, the coefficient retains the explicit
`order! * order^2` selector count.  A null compact exception, or a separately
proved `B_tail * |g|^2` compact-tail estimate, is absorbed into the same
square-cutoff form.

The final fixed-tree endpoint gives both `bad / |g| -> 0` for the quadratic
channel and `bad -> 0` for the quartic channel.  The common scalar-path
compatibility, compact differentiability domains, cumulative Jacobian lower
bounds, and compact tail remain explicit.  This is not a proof of the actual
garden good-set coupling powers or recollision decay.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.PhyslibFPUTActualBranchingA1SquareCutoffBudget

noncomputable section

/-- Consumer alias: the ENNReal fixed-tree estimate becomes a real regular
square-cutoff term plus the compact tail. -/
theorem problem_actual_branching_square_cutoff_real_budget :
    type_of% (@actualA1BranchingSquareCutoffBadBudget_le_regular_add_tail) :=
  @actualA1BranchingSquareCutoffBadBudget_le_regular_add_tail

/-- Consumer alias: a null compact exception gives the exact closure
interface `bad <= B * |g|^2`. -/
theorem problem_actual_branching_square_cutoff_zero_tail :
    type_of% (@actualA1BranchingSquareCutoffBadBudget_le_of_compactTail_zero) :=
  @actualA1BranchingSquareCutoffBadBudget_le_of_compactTail_zero

/-- Consumer alias: a quadratic compact-tail bound is absorbed by adding its
coefficient. -/
theorem problem_actual_branching_square_cutoff_tail_merge :
    type_of% (@actualA1BranchingSquareCutoffBadBudget_le_of_compactTail) :=
  @actualA1BranchingSquareCutoffBadBudget_le_of_compactTail

/-- Consumer alias: the displayed actual cumulative Jacobian bounds construct
the real-valued pointwise RPA bad-budget estimate. -/
theorem problem_actual_branching_square_cutoff_of_jacobian :
    type_of% (@exists_actualA1BranchingSquareCutoffBadBudget_le_of_jacobian) :=
  @exists_actualA1BranchingSquareCutoffBadBudget_le_of_jacobian

/-- Consumer alias: fixed-tree quadratic and quartic bad-budget limits. -/
theorem problem_actual_branching_square_cutoff_channel_limits :
    type_of% (@actualA1BranchingSquareCutoffBadBudget_quadratic_quartic_limits) :=
  @actualA1BranchingSquareCutoffBadBudget_quadratic_quartic_limits

/-- Consumer alias: explicit Jacobian hypotheses yield the pointwise budget
and both asymptotic channel endpoints. -/
theorem problem_actual_branching_square_cutoff_full_endpoint :
    type_of% (@exists_actualA1BranchingSquareCutoffBudget_and_limits_of_jacobian) :=
  @exists_actualA1BranchingSquareCutoffBudget_and_limits_of_jacobian

#print axioms ordinaryGardenCoordinateCompactAtlas_regularCoefficient_ne_top
#print axioms actualA1BranchingCompactAtlasUniformBudget_ne_top
#print axioms actualA1BranchingFactorialSquareCoefficientENNReal_ne_top
#print axioms actualA1BranchingSquareCutoffBadBudget_le_regular_add_tail
#print axioms actualA1BranchingSquareCutoffBadBudget_le_of_compactTail_zero
#print axioms actualA1BranchingSquareCutoffBadBudget_le_of_compactTail
#print axioms exists_actualA1BranchingSquareCutoffBadBudget_le_of_jacobian
#print axioms actualA1BranchingSquareCutoffBadBudget_quadratic_quartic_limits
#print axioms exists_actualA1BranchingSquareCutoffBudget_and_limits_of_jacobian
#print axioms problem_actual_branching_square_cutoff_real_budget
#print axioms problem_actual_branching_square_cutoff_zero_tail
#print axioms problem_actual_branching_square_cutoff_tail_merge
#print axioms problem_actual_branching_square_cutoff_of_jacobian
#print axioms problem_actual_branching_square_cutoff_channel_limits
#print axioms problem_actual_branching_square_cutoff_full_endpoint

end

end ArchonPhysicsConsumers.Thermalization
