import ArchonPhysics.PhyslibFPUTActualFixedRadiusHaarMomentClosure

/-!
# Consumer: actual one-block fixed-radius Haar closure

The imported endpoint checks the genuine Physlib Hamiltonian block against
the exact charge-balanced fixed-radius Haar target for all selected positive
modes.  It uses no Gaussian repeated-index replacement and no independent
re-Haar restart.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.PhyslibFPUTActualFixedRadiusHaarMomentClosure

#check actual_physlib_shortTime_chargeBalanced_two_and_four_moments

#print axioms actual_physlib_shortTime_chargeBalanced_two_and_four_moments

end ArchonPhysicsConsumers.Thermalization
