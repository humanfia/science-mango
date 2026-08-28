import ArchonPhysics.PhyslibFPUTKineticLittleOShadowingClosure

/-!
# Consumer: fixed-volume FPUT little-o kinetic Euler closure

This consumer exposes the exact composition theorem.  The microscopic
cubic-Lipschitz estimate supplies the one-block little-o ratio automatically;
the sole remaining conditional interface is the all-block restart/Haar
certificate.
-/

open ArchonPhysics.PhyslibFPUTKineticLittleOShadowingClosure

#check actualFPUT_oneBlock_is_momentKineticEulerResidual_cubicLittleO
#check FPUTAllBlockRestartHaarCertificate
#check FPUTAllBlockRestartHaarCertificate.defectMax
#check FPUTAllBlockRestartHaarCertificate.defectMax_nonneg
#check actualFPUT_moment_kineticEuler_shadowing_tendsto_zero

#print axioms actualFPUT_oneBlock_is_momentKineticEulerResidual_cubicLittleO
#print axioms FPUTAllBlockRestartHaarCertificate.defectMax_nonneg
#print axioms actualFPUT_moment_kineticEuler_shadowing_tendsto_zero
