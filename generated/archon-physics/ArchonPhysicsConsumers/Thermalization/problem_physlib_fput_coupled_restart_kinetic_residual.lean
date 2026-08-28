import ArchonPhysics.PhyslibFPUTCoupledRestartKineticResidual

/-!
# Consumer: coupled RPA restarts imply kinetic residuals

This consumer exposes the scalar endpoint-stability theorem, the explicit
common-source coupling adapters, and the kinetic-scale little-o criterion.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTCoupledRestartKineticResidual

open ArchonPhysics.PhyslibFPUTCoupledRestartKineticResidual
open ArchonPhysics.PhyslibFPUTCouplingMultiblockRestart
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing

theorem endpoint_residual_transfer_contract
    (actualInitial actualFinal referenceInitial referenceFinal : Real)
    (Q : Real → Real)
    {step L referenceDefect initialEndpointDefect finalEndpointDefect : Real}
    (hstep : 0 ≤ step) (hL : 0 ≤ L)
    (hreference : MomentKineticEulerResidual
      referenceInitial referenceFinal step (Q referenceInitial)
        referenceDefect)
    (hinitial : |actualInitial - referenceInitial| ≤ initialEndpointDefect)
    (hfinal : |actualFinal - referenceFinal| ≤ finalEndpointDefect)
    (hQ : ∀ x y, |Q x - Q y| ≤ L * |x - y|) :
    MomentKineticEulerResidual
      actualInitial actualFinal step (Q actualInitial)
        (referenceDefect + finalEndpointDefect +
          (1 + step * L) * initialEndpointDefect) := by
  simpa [endpointCoupledKineticResidualDefect] using
    momentKineticEulerResidual_of_reference_endpoint_control
      actualInitial actualFinal referenceInitial referenceFinal Q
      hstep hL hreference hinitial hfinal hQ

theorem explicit_second_moment_endpoint_defect_contract
    (M delta0 p0 delta1 p1 step L referenceDefect : Real) :
    endpointCoupledKineticResidualDefect step L referenceDefect
        (couplingSecondMomentDefect M delta0 p0)
        (couplingSecondMomentDefect M delta1 p1) =
      referenceDefect + (2 * M * delta1 + 2 * M ^ 2 * p1) +
        (1 + step * L) * (2 * M * delta0 + 2 * M ^ 2 * p0) := by
  simp [endpointCoupledKineticResidualDefect, couplingSecondMomentDefect]

#check coupled_secondMoment_is_momentKineticEulerResidual
#check coupled_fourthMoment_is_momentKineticEulerResidual
#check endpointCoupledKineticResidualDefect_ratio_tendsto_zero
#check couplingSecondMomentResidualDefect_ratio_tendsto_zero

#print axioms endpoint_residual_transfer_contract
#print axioms explicit_second_moment_endpoint_defect_contract
#print axioms momentKineticEulerResidual_of_reference_endpoint_control
#print axioms coupled_secondMoment_is_momentKineticEulerResidual
#print axioms coupled_fourthMoment_is_momentKineticEulerResidual
#print axioms endpointCoupledKineticResidualDefect_ratio_tendsto_zero
#print axioms couplingSecondMomentResidualDefect_ratio_tendsto_zero

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTCoupledRestartKineticResidual
