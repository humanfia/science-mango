import ArchonPhysics.PhyslibFPUTShiftedBlockMomentDiscrepancyTelescoping

/-!
# Consumer: shifted-block moment-discrepancy telescoping

This gate verifies the certificate-free reduction from shifted reference
endpoint discrepancies to a cumulative kinetic observable error.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTShiftedBlockMomentDiscrepancyTelescoping

open ArchonPhysics.PhyslibFPUTCoupledRestartKineticResidual
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing
open ArchonPhysics.PhyslibFPUTShiftedBlockMomentDiscrepancyTelescoping

noncomputable section

#check shiftedBlock_endpointMomentDiscrepancy_powerBound
#check shiftedBlock_commonMomentDiscrepancy_expBound
#check shiftedBlocks_second_fourth_collisionMoment_expBounds

/-- Consumer-level scalar collision-moment bound. -/
theorem shifted_collisionMoment_error_le_cumulative_discrepancy
    (actual kinetic referenceInitial referenceFinal : Nat -> Real)
    (Q : Real -> Real) (step L : Real)
    (referenceDefect epsilon : Nat -> Real)
    (hstep : 0 <= step) (hL : 0 <= L)
    (hreferenceDefect : forall j, 0 <= referenceDefect j)
    (hepsilon : forall j, 0 <= epsilon j)
    (hreference : forall j,
      MomentKineticEulerResidual
        (referenceInitial j) (referenceFinal j) step
        (Q (referenceInitial j)) (referenceDefect j))
    (hinitial : forall j,
      |actual j - referenceInitial j| <= epsilon j)
    (hfinal : forall j,
      |actual (j + 1) - referenceFinal j| <= epsilon j)
    (hkinetic : IsKineticEulerTrajectory kinetic step Q)
    (hQ : forall x y, |Q x - Q y| <= L * |x - y|)
    (K : Nat) :
    |actual K - kinetic K| <=
      (|actual 0 - kinetic 0| +
        ∑ j ∈ Finset.range K,
          (referenceDefect j + (2 + step * L) * epsilon j)) *
        Real.exp (L * step * (K : Real)) :=
  shiftedBlock_commonMomentDiscrepancy_expBound
    actual kinetic referenceInitial referenceFinal Q step L
      referenceDefect epsilon hstep hL hreferenceDefect hepsilon
      hreference hinitial hfinal hkinetic hQ K

#print axioms endpointCoupledKineticResidualDefect_sameEndpointDiscrepancy
#print axioms shiftedBlock_endpointMomentDiscrepancy_powerBound
#print axioms shiftedBlock_commonMomentDiscrepancy_expBound
#print axioms shiftedBlocks_second_fourth_collisionMoment_expBounds
#print axioms shifted_collisionMoment_error_le_cumulative_discrepancy

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTShiftedBlockMomentDiscrepancyTelescoping
