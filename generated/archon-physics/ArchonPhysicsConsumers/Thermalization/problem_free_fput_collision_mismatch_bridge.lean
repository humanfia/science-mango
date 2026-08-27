import ArchonPhysics.FreeFPUTCollisionMismatchBridge

/-!
# Consumer checks for the free FPUT collision-mismatch bridge

These contracts expose the exact finite-volume algebraic identification between
the phase mismatch of a free quadratic FPUT Picard term and the signed
three-leg collision mismatch.  They do not assert a kinetic limit, nonlinear
random-phase propagation, or thermodynamic-limit thermalization.
-/

namespace ArchonPhysicsConsumers.Thermalization.FreeFPUTCollisionMismatchBridge

open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassPositiveCollisionData

noncomputable section

/-- For an arbitrary supplied frequency, the free quadratic FPUT mismatch is
exactly the output-plus signed collision sum over its three legs. -/
theorem supplied_frequency_signed_collision_sum_contract
    {N : Nat} [NeZero N]
    (frequency : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) :
    quadraticPhaseMismatch frequency observed term =
      ∑ r, (quadraticCollisionSign term r).coefficient *
        frequency (quadraticCollisionModes observed term r) :=
  quadraticPhaseMismatch_eq_signedCollisionSum frequency observed term

/-- With the random-mass harmonic spectrum, the same scalar is the existing
`ModalPhaseMismatch.phaseMismatch`. -/
theorem harmonic_mode_frequency_phase_mismatch_contract
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N) :
    quadraticPhaseMismatch (modeFrequency m) observed term =
      phaseMismatch m (quadraticCollisionSign term)
        (quadraticCollisionModes observed term) :=
  quadraticPhaseMismatch_modeFrequency_eq_phaseMismatch m observed term

/-- Pulling the canonical ordered spectrum back to physical indices identifies
the free quadratic mismatch with the existing ordered three-wave mismatch. -/
theorem ordered_pullback_three_wave_mismatch_contract
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) (leftSign rightSign : Fin 2) :
    quadraticPhaseMismatch (orderedPullbackFrequency m)
        (orderedIndexEquiv (modes 0))
        (orderedQuadraticPhaseTerm modes leftSign rightSign) =
      orderedThreeWaveMismatch m
        (quadraticCollisionSign
          (orderedQuadraticPhaseTerm modes leftSign rightSign)) modes :=
  quadraticPhaseMismatch_ordered_eq_orderedThreeWaveMismatch
    m modes leftSign rightSign

#check phaseSignToInputInteractionSign
#check orderedPullbackFrequency_eq_modeFrequency
#check quadraticCollisionModes_orderedQuadraticPhaseTerm

#print axioms supplied_frequency_signed_collision_sum_contract
#print axioms harmonic_mode_frequency_phase_mismatch_contract
#print axioms ordered_pullback_three_wave_mismatch_contract

end

end ArchonPhysicsConsumers.Thermalization.FreeFPUTCollisionMismatchBridge
