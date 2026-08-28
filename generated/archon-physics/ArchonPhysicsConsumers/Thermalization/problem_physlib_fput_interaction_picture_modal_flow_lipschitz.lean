import ArchonPhysics.PhyslibFPUTInteractionPictureModalFlowLipschitz

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalRandomMassGlobalFlow
open ArchonPhysics.ComplexModeAmplitude
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ParametricLocalHamiltonianFlow
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTInteractionPictureModalFlowLipschitz
open ArchonPhysics.PhyslibFPUTModalObservableFlowLipschitz
open ArchonPhysics.ReducedModeTransform

noncomputable section

variable {N : Nat} [NeZero N]

/-- Consumer check: fixed phase renormalization is an exact isometry. -/
example (theta : Real) : Isometry (phaseRenormalize theta) :=
  phaseRenormalize_isometry theta

/-- Consumer check: the actual interaction-picture block is the canonical
Hamiltonian flow, followed by the physical modal coordinate, followed by
the exact free-phase rotation. -/
example (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (t : Real) (x : ParametricPhaseSpace N) :
    canonicalFixedMassInteractionPictureAmplitudeAfter
        shell m observed t x =
      phaseRenormalize (modeFrequency m observed * t)
        (complexModeAmplitude (modeFrequency m observed)
          (modalCoordinates m
            (sqrtMassTransform m
              (canonicalRandomMassGlobalFlow shell (x, t)).2.1) observed)
          (modalCoordinates m
            (inverseSqrtMassTransform m
              (canonicalRandomMassGlobalFlow shell (x, t)).2.2) observed)) :=
  canonicalFixedMassInteractionPictureAmplitudeAfter_apply
    shell m observed t x

/-- Consumer check: interaction-picture rotation preserves the squared
amplitude used by the kinetic second moment. -/
example (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (t : Real) (x : ParametricPhaseSpace N) :
    Complex.normSq
        (canonicalFixedMassInteractionPictureAmplitudeAfter
          shell m observed t x) =
      Complex.normSq
        (canonicalFixedMassSelectedModeAmplitudeAfter
          shell m observed t x) :=
  normSq_canonicalFixedMassInteractionPictureAmplitudeAfter
    shell m observed t x

/-- Consumer check: this is the interaction-picture
`actualBlock_lipschitz` field, with exactly the same amplification as the
raw physical amplitude. -/
example (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (t : Real) :
    LipschitzWith
      (canonicalFixedMassSelectedModeAmplitudeAfterAmplification
        shell m observed t)
      (canonicalFixedMassInteractionPictureAmplitudeAfter
        shell m observed t) :=
  canonicalFixedMassInteractionPictureAmplitudeAfter_lipschitz
    shell m observed t

#print axioms phaseRenormalize_isometry
#print axioms canonicalFixedMassInteractionPictureAmplitudeAfter_apply
#print axioms normSq_canonicalFixedMassInteractionPictureAmplitudeAfter
#print axioms canonicalFixedMassInteractionPictureAmplitudeAfter_lipschitz

end

end ArchonPhysicsConsumers.Thermalization
