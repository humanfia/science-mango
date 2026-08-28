import ArchonPhysics.PhyslibFPUTFullStateEndpointCertificate
import ArchonPhysics.PhyslibFPUTModalObservableFlowLipschitz

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalRandomMassGlobalFlow
open ArchonPhysics.ComplexModeAmplitude
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ParametricLocalHamiltonianFlow
open ArchonPhysics.PhyslibFPUTModalObservableFlowLipschitz
open ArchonPhysics.ReducedModeTransform

noncomputable section

variable {N : Nat} [NeZero N]

/-- Consumer check: this is the exact physical complex amplitude, not an
abstract scalar observable. -/
example (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (x : ParametricPhaseSpace N) :
    fixedMassSelectedModeAmplitude m observed x =
      complexModeAmplitude (modeFrequency m observed)
        (modalCoordinates m (sqrtMassTransform m x.2.1) observed)
        (modalCoordinates m (inverseSqrtMassTransform m x.2.2) observed) :=
  fixedMassSelectedModeAmplitude_eq m observed x

/-- Consumer check: the initial physical modal observable supplies
`initialAmplitude_lipschitz` in full-state endpoint data. -/
example (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N) :
    LipschitzWith (fixedMassSelectedModeAmplitudeAmplification m observed)
      (fixedMassSelectedModeAmplitude m observed) :=
  fixedMassSelectedModeAmplitude_lipschitz m observed

/-- Consumer check: this has exactly the type required by the
`actualBlock_lipschitz` field when the full state is
`ParametricPhaseSpace N` and the actual block is the canonical Hamiltonian
flow followed by the selected physical amplitude. -/
example (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (t : Real) :
    LipschitzWith
      (canonicalFixedMassSelectedModeAmplitudeAfterAmplification
        shell m observed t)
      (canonicalFixedMassSelectedModeAmplitudeAfter shell m observed t) :=
  canonicalFixedMassSelectedModeAmplitudeAfter_lipschitz
    shell m observed t

#print axioms fixedMassSelectedModeAmplitude_eq
#print axioms fixedMassSelectedModeAmplitude_lipschitz
#print axioms fixedMassSelectedModeAmplitude_energy
#print axioms canonicalFixedMassSelectedModeAmplitudeAfter_lipschitz

end

end ArchonPhysicsConsumers.Thermalization
