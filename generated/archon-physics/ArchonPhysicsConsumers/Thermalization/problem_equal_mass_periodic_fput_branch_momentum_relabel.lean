import ArchonPhysics.EqualMassPeriodicFPUTBranchMomentumRelabel

/-!
# Consumer endpoints for branch-to-physical momentum relabelling

These named statements close the convention bridge between the exact
Hamiltonian interaction picture and the signed Fourier three-wave shell.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ComplexFourierBranchAmplitude
open ArchonPhysics.EqualMassPeriodicFPUTBranchMomentumRelabel
open ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave
open ArchonPhysics.EqualMassPeriodicFPUTInteractionPicture
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.Lattice

noncomputable section

theorem equalMassPeriodicFPUT_branchPhysicalFrequency_consumer
    (N : Nat) [NeZero N] (sign : PhaseSign) (rawMode : Site N) :
    periodicSineFrequency N (phaseSignedMomentum sign rawMode) =
      periodicSineFrequency N rawMode :=
  periodicSineFrequency_phaseSignedMomentum N sign rawMode

theorem equalMassPeriodicFPUT_branchMomentumSelector_consumer
    {N : Nat} [NeZero N] (k l : Site N)
    (outputSign leftSign rightSign : PhaseSign) :
    FourierMomentumBalanced
      (branchRelabelledThreeWaveSign outputSign leftSign rightSign)
      (branchRelabelledThreeWaveMode k l
        outputSign leftSign rightSign) :=
  branchRelabelledThreeWave_fourierMomentumBalanced
    k l outputSign leftSign rightSign

theorem equalMassPeriodicFPUT_branchMismatchRelabel_consumer
    {N : Nat} [NeZero N] (k l : Site N)
    (outputSign leftSign rightSign : PhaseSign) :
    periodicSinePhaseMismatch
        (branchRelabelledThreeWaveSign outputSign leftSign rightSign)
        (branchRelabelledThreeWaveMode k l
          outputSign leftSign rightSign) =
      equalMassQuadraticBranchMismatch k l
        outputSign leftSign rightSign :=
  periodicSinePhaseMismatch_branchRelabelledThreeWave
    k l outputSign leftSign rightSign

theorem equalMassPeriodicFPUT_branchExactDecoration_consumer
    {N : Nat} [NeZero N] (k l : Site N)
    (outputSign leftSign rightSign : PhaseSign) :
    FourierMomentumBalanced
        (branchRelabelledThreeWaveSign outputSign leftSign rightSign)
        (branchRelabelledThreeWaveMode k l
          outputSign leftSign rightSign) ∧
      periodicSinePhaseMismatch
          (branchRelabelledThreeWaveSign outputSign leftSign rightSign)
          (branchRelabelledThreeWaveMode k l
            outputSign leftSign rightSign) =
        equalMassQuadraticBranchMismatch k l
          outputSign leftSign rightSign :=
  branchRelabelledThreeWave_exactDecoration
    k l outputSign leftSign rightSign

theorem equalMassPeriodicFPUT_nonzeroBranchOffThreeWaveShell_consumer
    {N : Nat} [NeZero N] {k l : Site N}
    (outputSign leftSign rightSign : PhaseSign)
    (hk : k ≠ 0) (hl : l ≠ 0) (hright : k - l ≠ 0) :
    equalMassQuadraticBranchMismatch k l
      outputSign leftSign rightSign ≠ 0 :=
  equalMassQuadraticBranchMismatch_ne_zero_of_nonzero
    outputSign leftSign rightSign hk hl hright

theorem equalMassPeriodicFPUT_nonzeroBranchFixedGap_consumer
    {N : Nat} [NeZero N] {k l : Site N}
    (outputSign leftSign rightSign : PhaseSign)
    (hk : k ≠ 0) (hl : l ≠ 0) (hright : k - l ≠ 0) :
    finiteNonzeroMomentumThreeWaveGap N ≤
      |equalMassQuadraticBranchMismatch k l
        outputSign leftSign rightSign| :=
  finiteNonzeroMomentumThreeWaveGap_le_branchMismatch
    outputSign leftSign rightSign hk hl hright

#print axioms equalMassPeriodicFPUT_branchPhysicalFrequency_consumer
#print axioms equalMassPeriodicFPUT_branchMomentumSelector_consumer
#print axioms equalMassPeriodicFPUT_branchMismatchRelabel_consumer
#print axioms equalMassPeriodicFPUT_branchExactDecoration_consumer
#print axioms equalMassPeriodicFPUT_nonzeroBranchOffThreeWaveShell_consumer
#print axioms equalMassPeriodicFPUT_nonzeroBranchFixedGap_consumer

end

end ArchonPhysicsConsumers.Thermalization
