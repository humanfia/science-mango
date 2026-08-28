import ArchonPhysics.PhyslibFPUTCouplingMultiblockRestart

/-!
# Consumer: coupling-based multiblock Physlib restart

These contracts expose the blockwise coupling certificate, its explicit
second/fourth moment defects, and the resulting affine restart recurrences.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTCouplingMultiblockRestart

open MeasureTheory
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTCouplingMultiblockRestart
open ArchonPhysics.PhyslibFPUTMultiblockRPAMomentPropagation

noncomputable section

theorem coupling_certificate_pushforward_moments_contract
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {M : Real} (hM : 0 ≤ M)
    (certificate : AmplitudeCouplingRestartCertificate mu M)
    (j : Nat) :
    |∫ z, Complex.normSq z ∂certificate.actualLaw j -
        ∫ z, Complex.normSq z ∂certificate.referenceLaw j| ≤
      couplingSecondMomentDefect M
        (certificate.delta j) (certificate.failureProbability j) ∧
    |∫ z, Complex.normSq z ^ 2 ∂certificate.actualLaw j -
        ∫ z, Complex.normSq z ^ 2 ∂certificate.referenceLaw j| ≤
      couplingFourthMomentDefect M
        (certificate.delta j) (certificate.failureProbability j) :=
  certificate_pushforward_second_fourth_moment_errors
    mu hM certificate j

theorem coupling_corrected_defect_identification_contract
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N)
    (mUpper kappa beta g H M : Real)
    (observed : Site N) (h delta p : Real) :
    physlibCouplingSecondMomentRestartDefect
        m mUpper kappa beta g H M observed h delta p =
      2 * M * delta + 2 * M ^ 2 * p +
        physlibSecondMomentBlockDefect
          m mUpper kappa beta g H M observed h ∧
    physlibCouplingFourthMomentRestartDefect
        m mUpper kappa beta g H M observed h delta p =
      4 * M ^ 3 * delta + 2 * M ^ 4 * p +
        physlibFourthMomentBlockDefect
          m mUpper kappa beta g H M observed h := by
  simp [physlibCouplingSecondMomentRestartDefect,
    physlibCouplingFourthMomentRestartDefect,
    couplingSecondMomentDefect, couplingFourthMomentDefect]

theorem coupling_certificate_restart_recurrence_contract
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N)
    {mUpper kappa beta g H M L h : Real}
    (observed : Site N)
    (certificate : AmplitudeCouplingRestartCertificate mu M)
    (secondError fourthError : Nat → Real)
    (propagatedSecondError propagatedFourthError : Nat → Real)
    (hM : 0 ≤ M)
    (hsecondLipschitz : ∀ j,
      propagatedSecondError j ≤ (1 + L * h) * secondError j)
    (hfourthLipschitz : ∀ j,
      propagatedFourthError j ≤ (1 + L * h) * fourthError j)
    (hsecondDecomposition : ∀ j,
      secondError (j + 1) ≤ propagatedSecondError j +
        |∫ z, Complex.normSq z ∂certificate.actualLaw j -
          ∫ z, Complex.normSq z ∂certificate.referenceLaw j| +
        physlibSecondMomentBlockDefect
          m mUpper kappa beta g H M observed h)
    (hfourthDecomposition : ∀ j,
      fourthError (j + 1) ≤ propagatedFourthError j +
        |∫ z, Complex.normSq z ^ 2 ∂certificate.actualLaw j -
          ∫ z, Complex.normSq z ^ 2 ∂certificate.referenceLaw j| +
        physlibFourthMomentBlockDefect
          m mUpper kappa beta g H M observed h) :
    (∀ j, secondError (j + 1) ≤ (1 + L * h) * secondError j +
      physlibCouplingSecondMomentRestartDefect
        m mUpper kappa beta g H M observed h
          (certificate.delta j) (certificate.failureProbability j)) ∧
    (∀ j, fourthError (j + 1) ≤ (1 + L * h) * fourthError j +
      physlibCouplingFourthMomentRestartDefect
        m mUpper kappa beta g H M observed h
          (certificate.delta j) (certificate.failureProbability j)) :=
  physlib_restart_recurrences_of_coupling_certificate
    mu m observed certificate secondError fourthError
      propagatedSecondError propagatedFourthError hM
      hsecondLipschitz hfourthLipschitz
      hsecondDecomposition hfourthDecomposition

#print axioms coupling_certificate_pushforward_moments_contract
#print axioms coupling_corrected_defect_identification_contract
#print axioms coupling_certificate_restart_recurrence_contract
#print axioms certificate_pushforward_second_fourth_moment_errors
#print axioms physlib_restart_recurrences_of_coupling_certificate
#print axioms physlib_coupling_restart_multiblock_bounds

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTCouplingMultiblockRestart
