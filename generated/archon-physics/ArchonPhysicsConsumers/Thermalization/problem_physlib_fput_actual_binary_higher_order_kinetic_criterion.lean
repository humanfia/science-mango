import ArchonPhysics.PhyslibFPUTActualBinaryHigherOrderKineticCriterion

/-!
# Consumer: one binary actual FPUT factorization-defect bound

This consumer exposes the fixed-left/right finite-time criterion and its two
finite-budget algebra lemmas.  The imported result is conditional only on the
displayed actual Hamiltonian trajectory and unit source-slot bounds; it makes
no RPA, decay, or kinetic-limit conclusion.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.PhyslibFPUTActualBinaryHigherOrderKineticCriterion

#check binaryUnitSlotBudget
#check binaryUnitSlotBudget_nonneg
#check binary_couplingWeightedSlotSum_eq_channels
#check norm_actualFiniteCoerciveClusterFactorizationDefect_le_binary_channels

#print axioms binaryUnitSlotBudget_nonneg
#print axioms binary_couplingWeightedSlotSum_eq_channels
#print axioms
  norm_actualFiniteCoerciveClusterFactorizationDefect_le_binary_channels

end ArchonPhysicsConsumers.Thermalization
