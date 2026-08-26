import ArchonPhysics.PaperSpectralEntropyCriterion

/-!
# Consumer: independent paper spectral-entropy criterion

This consumer locks the complete late-window `xi >= 1/2` branch separately
from the primary finite `l1` equipartition criterion.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.PaperSpectralEntropyCriterion

/-- Kernel-lock the exact `g^2` rescaling of the paper half-threshold hit. -/
theorem problem_paperXi_half_hittingTime_kineticScale :
    (@lateWindowPaperXiHalfHittingTime_kineticScale_of_continuous) =
      @lateWindowPaperXiHalfHittingTime_kineticScale_of_continuous := rfl

/-- Kernel-lock the general energy-density high-probability transfer. -/
theorem problem_paperXi_energyDensity_highProbability :
    (@paperXi_energyDensity_corollary_of_highProbabilityG2Bounds) =
      @paperXi_energyDensity_corollary_of_highProbabilityG2Bounds := rfl

/-- Kernel-lock the explicit cubic `lambda^-2 epsilon^-1` transfer. -/
theorem problem_paperXi_cubic_energyDensity_highProbability :
    (@paperXi_cubic_energyDensity_corollary_of_highProbabilityG2Bounds) =
      @paperXi_cubic_energyDensity_corollary_of_highProbabilityG2Bounds := rfl

#print axioms problem_paperXi_half_hittingTime_kineticScale
#print axioms problem_paperXi_energyDensity_highProbability
#print axioms problem_paperXi_cubic_energyDensity_highProbability

end ArchonPhysicsConsumers.Thermalization
