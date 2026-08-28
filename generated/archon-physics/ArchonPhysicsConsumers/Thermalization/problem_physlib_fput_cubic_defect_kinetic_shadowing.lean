import ArchonPhysics.PhyslibFPUTCubicDefectKineticShadowing

/-!
# Consumer: cubic weak-coupling defects at FPUT kinetic time

This consumer checks the concrete scale adapter and the resulting coupled
kinetic-time closure.  It also checks the formal counterexample showing that
a merely `O(g^2 T)` defect is not enough.
-/

open ArchonPhysics.PhyslibFPUTCubicDefectKineticShadowing

#check cubicDefect_div_kineticStep_tendsto_zero
#check cubicReferenceAndCoupling_ratios_tendsto_zero
#check actualSecondMoment_kineticEuler_shadowing_of_cubicDefects
#check kineticStep_self_ratio_eventually_eq_one
#check quadraticKineticStep_bound_not_sufficient

#print axioms cubicDefect_div_kineticStep_tendsto_zero
#print axioms cubicReferenceAndCoupling_ratios_tendsto_zero
#print axioms actualSecondMoment_kineticEuler_shadowing_of_cubicDefects
#print axioms quadraticKineticStep_bound_not_sufficient
