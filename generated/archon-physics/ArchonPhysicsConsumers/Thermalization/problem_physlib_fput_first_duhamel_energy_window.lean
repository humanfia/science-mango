import ArchonPhysics.PhyslibFPUTFirstDuhamelEnergyWindow

/-!
# Consumer: first-Duhamel energy-window control
-/

namespace ArchonPhysicsConsumers.Thermalization

open Set
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTFirstDuhamelEnergyWindow
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.ReducedModeTransform

noncomputable section

theorem physlibFPUT_firstDuhamel_energyWindow_consumer
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {mUpper kappa beta g H T : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ time ∈ Icc 0 T, ∑ i, m.mass i *
        asConfiguration ((realReparametrize q) time) i = 0)
    (henergy : ∀ time ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize p) time))
        (asConfiguration ((realReparametrize q) time)) ≤ H) :
    ‖phaseRenormalize (modeFrequency m observed * T)
          (physlibModeAmplitude m observed p q T) -
        physlibModeAmplitude m observed p q 0‖ ≤
      firstDuhamelWindowEnvelope m kappa beta g observed
          (actualModalEnergyL1Envelope N mUpper kappa beta H) * T :=
  norm_interactionPicture_physlibMode_sub_initial_le_energyWindow
    m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton homega hT
      hgauge henergy

#print axioms physlibFPUT_firstDuhamel_energyWindow_consumer

end

end ArchonPhysicsConsumers.Thermalization
