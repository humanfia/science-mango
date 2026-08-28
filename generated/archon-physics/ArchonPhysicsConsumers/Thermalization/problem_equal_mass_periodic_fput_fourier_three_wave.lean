import ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave
open ArchonPhysics.FiniteNestedNormalFormExtraction
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.Lattice
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.QuadraticInteractionFirstNormalForm

noncomputable section

theorem equalMassPeriodic_dispersion_exact_consumer
    (N : Nat) [NeZero N] (k : Site N) :
    periodicSineFrequency N k ^ 2 =
      CleanCycleAcousticCountEnvelope.cleanCycleModeEnergy N k :=
  periodicSineFrequency_sq_eq_cleanCycleModeEnergy N k

theorem equalMassPeriodic_nonzero_threeWave_shell_empty_consumer
    {N : Nat} [NeZero N]
    (sign : Fin 3 → InteractionSign) (modes : Fin 3 → Site N)
    (hmomentum : FourierMomentumBalanced sign modes)
    (hfrequency : periodicSinePhaseMismatch sign modes = 0) :
    ∃ r, modes r = 0 :=
  threeWave_fourier_resonance_has_zero_mode
    sign modes hmomentum hfrequency

theorem equalMassPeriodic_fixedVolume_gap_consumer
    (N : Nat) [NeZero N] :
    0 < finiteNonzeroMomentumThreeWaveGap N ∧
      ∀ triple : SignedFourierTriple N,
        IsNonzeroMomentumTriple triple →
          finiteNonzeroMomentumThreeWaveGap N ≤
            |signedFourierTripleMismatch triple| :=
  ⟨finiteNonzeroMomentumThreeWaveGap_pos N,
    finiteNonzeroMomentumThreeWaveGap_le N⟩

theorem actualQuadraticPicard_fourier_shell_zero_leg_consumer
    {N : Nat} [NeZero N] (observed : Site N)
    (term : QuadraticPhaseTerm N)
    (hmomentum : QuadraticPhaseFourierMomentumBalanced observed term)
    (hfrequency :
      quadraticPhaseMismatch (periodicSineFrequency N) observed term = 0) :
    ∃ r, FreeFPUTCollisionMismatchBridge.quadraticCollisionModes
      observed term r = 0 :=
  quadraticPhase_fourier_resonance_has_zero_mode
    observed term hmomentum hfrequency

theorem equalMassPeriodic_firstNormalForm_inverseGap_consumer
    {N : Nat} [NeZero N]
    {Mode : Type*} [Fintype Mode]
    (vertex : Mode → Mode → Mode → Complex)
    (mismatch : Mode → Mode → Mode → Real)
    (decoration : Mode → Mode → Mode → SignedFourierTriple N)
    (amplitude : Mode → Complex) (time : Real) (out : Mode)
    (hmismatch : ∀ left right,
      mismatch out left right =
        signedFourierTripleMismatch (decoration out left right))
    (hactive : ∀ left right,
      IsNonzeroMomentumTriple (decoration out left right)) :
    ‖quadraticPrimitiveCorrection
        vertex mismatch amplitude time out‖ ≤
      (2 / finiteNonzeroMomentumThreeWaveGap N) *
        ∑ left, ∑ right,
          ‖vertex out left right‖ *
            ‖amplitude left‖ * ‖amplitude right‖ :=
  norm_quadraticPrimitiveCorrection_le_fixedFourierGap
    vertex mismatch decoration amplitude time out hmismatch hactive

theorem effectiveFourWave_finiteNestedExtraction_consumer
    {N : Nat} [NeZero N]
    (coefficient : ActiveQuadraticFourierTerm N → Complex)
    (outerMismatch : ActiveQuadraticFourierTerm N → Real)
    (time : Real) :
    finiteNestedPicardSum coefficient outerMismatch
        activeQuadraticFourierInnerMismatch time =
      finiteEffectiveInteractionSum coefficient outerMismatch
          activeQuadraticFourierInnerMismatch time -
        finiteNormalFormBoundarySum coefficient outerMismatch
          activeQuadraticFourierInnerMismatch time :=
  activeQuadraticFourierNestedPicard_eq_effective_sub_boundary
    coefficient outerMismatch time

#print axioms equalMassPeriodic_dispersion_exact_consumer
#print axioms equalMassPeriodic_nonzero_threeWave_shell_empty_consumer
#print axioms equalMassPeriodic_fixedVolume_gap_consumer
#print axioms actualQuadraticPicard_fourier_shell_zero_leg_consumer
#print axioms equalMassPeriodic_firstNormalForm_inverseGap_consumer
#print axioms effectiveFourWave_finiteNestedExtraction_consumer

end

end ArchonPhysicsConsumers.Thermalization
