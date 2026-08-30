import ArchonPhysics.PhyslibFPUTActualBranchingA1GardenScheduleAdapter

/-!
# Thermalization consumer: actual branching A1 garden schedule adapter

This consumer verifies that the genuine fixed-tree branching fiber-law bad
budget can replace both abstract exceptional probabilities in the quadratic
and quartic garden schedule.  Its square-cutoff estimate supplies the two
small-ball premises automatically.

The quadratic and quartic good-garden bounds remain explicit hypotheses.
Thus the result is a conditional kinetic-time weighted-source limit, not a
claim that the actual FPUT coupling powers or recollision estimates have
already been proved.  The atlas compatibility, cumulative Jacobian input,
and compact tail remain upstream visible conditions.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.PhyslibFPUTActualBranchingA1GardenScheduleAdapter

noncomputable section

/-- Consumer alias: an explicit quadratic compact-tail budget supplies the
actual branching exceptional schedule for both source channels. -/
theorem problem_actual_branching_a1_garden_schedule_adapter :
    type_of%
      (@coupling_channel_budget_tendsto_zero_at_kineticTime_actualA1Branching) :=
  @coupling_channel_budget_tendsto_zero_at_kineticTime_actualA1Branching

/-- Consumer alias: null compact exception specialization. -/
theorem problem_actual_branching_a1_garden_schedule_adapter_zero_tail :
    type_of% (
      @coupling_channel_budget_tendsto_zero_at_kineticTime_actualA1Branching_of_compactTail_zero
    ) :=
  @coupling_channel_budget_tendsto_zero_at_kineticTime_actualA1Branching_of_compactTail_zero

#print axioms coupling_channel_budget_tendsto_zero_at_kineticTime_actualA1Branching
#print axioms
  coupling_channel_budget_tendsto_zero_at_kineticTime_actualA1Branching_of_compactTail_zero
#print axioms problem_actual_branching_a1_garden_schedule_adapter
#print axioms problem_actual_branching_a1_garden_schedule_adapter_zero_tail

end

end ArchonPhysicsConsumers.Thermalization
