import ArchonPhysics.PhyslibFPUTPhysicalOneBlockQuadraticMomentLittleO

/-!
# Consumer: physical one-block quadratic collision-moment little-o

This gate checks the direct Hamiltonian/Haar-to-residual theorem for one
observed quadratic modal-energy observable at fixed volume and block time.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTPhysicalOneBlockQuadraticMomentLittleO

open Filter
open MeasureTheory
open Set
open Topology
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTActualOneBlockKineticLittleO
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibFPUTPhysicalOneBlockQuadraticMomentLittleO
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.QuadraticTensorHistoryExpansion

noncomputable section

#check physicalHamiltonian_quadraticCollisionMoment_residual_and_littleO

/-- Consumer-level extraction of the actual normalized-residual limit. -/
theorem physical_oneBlock_quadraticCollision_normalizedResidual_tendsto_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper kappa beta H : Real)
    (hmUpper0 : 0 <= mUpper) (hmassUpper : forall i, m.mass i <= mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Lattice.Site N)
    (energy : Lattice.Site N -> Real)
    (homega : 0 < modeFrequency m observed)
    {T : Real} (hT : 0 < T)
    (g : Nat -> Real)
    (p q : Nat -> UnitAddTorus (Lattice.Site N) ->
      Time -> HilbertConfiguration N)
    (hp : forall n phase, Differentiable Real (p n phase))
    (hq : forall n phase, Differentiable Real (q n phase))
    (hHamilton : forall n phase,
      SatisfiesHamiltonEquations m kappa beta (g n)
        (p n phase) (q n phase))
    (hinitial : forall n phase mode,
      physlibModeAmplitude m mode (p n phase) (q n phase) 0 =
        canonicalFreeComplexInitialAmplitude
          (phaseEnergyRadius energy (modeFrequency m))
          (modeFrequency m) phase mode)
    (hgauge : forall n phase s, s ∈ Icc 0 T ->
      ∑ i, m.mass i *
        asConfiguration ((realReparametrize (q n phase)) s) i = 0)
    (henergyWindow : forall n phase s, s ∈ Icc 0 T ->
      CoerciveLatticeEnergy.hamiltonian m kappa beta (g n)
        (asConfiguration ((realReparametrize (p n phase)) s))
        (asConfiguration ((realReparametrize (q n phase)) s)) <= H)
    (hzeroHistory : forall n phase s, s ∈ Icc 0 T -> forall mode,
      modeFrequency m mode = 0 ->
        physlibModalHistoryDefect m (q n phase)
          (phaseEnergyRadius energy (modeFrequency m)) phase s mode = 0)
    (hmeasurable : forall n, Measurable
      (actualPostSecondPicardEnergyCorrection m kappa beta (g n) observed
        (q n) (phaseEnergyRadius energy (modeFrequency m)) T))
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : ∀ᶠ n in atTop, g n ≠ 0) :
    Tendsto
      (fun n =>
        |actualHaarModalMoment m observed (p n) (q n) T -
            actualHaarModalMoment m observed (p n) (q n) 0 -
            (g n ^ 2 * T) *
              normalizedSecondOrderHaarBroadening
                m kappa beta energy observed T| /
          (g n ^ 2 * T))
      atTop (nhds 0) :=
  (physicalHamiltonian_quadraticCollisionMoment_residual_and_littleO
    m mUpper kappa beta H hmUpper0 hmassUpper hbeta observed energy
      homega hT g p q hp hq hHamilton hinitial hgauge henergyWindow
      hzeroHistory hmeasurable hg hg0).2

#print axioms physicalHamiltonian_quadraticCollisionMoment_residual_and_littleO
#print axioms physical_oneBlock_quadraticCollision_normalizedResidual_tendsto_zero

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTPhysicalOneBlockQuadraticMomentLittleO
