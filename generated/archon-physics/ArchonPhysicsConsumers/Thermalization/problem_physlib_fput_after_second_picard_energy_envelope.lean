import ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
import ArchonPhysics.TruncatedGaussianMassPhaseEnsemble

/-!
# Named consumer: microscopic post-second-Picard energy envelope

This consumer specializes the deterministic result to one frozen sample of
the conditioned Gaussian mass ensemble.  The only dynamical assumptions are
the physical mass gauge and a Hamiltonian energy upper bound on the stated
time window.  No RPA or diagram-remainder certificate is assumed.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTAfterSecondPicardEnergyEnvelope

open UnitAddTorus
open Set
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.GaussianIIDMassPhaseEnsemble
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.TruncatedGaussianMassLaw

noncomputable section

def gaussianFrozenMass
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (sample : Omega) :
    Lattice.PositiveMassConfig N :=
  ensemble.restrictPositiveMass sample

/-- Frozen conditioned-Gaussian support supplies the literal mass upper bound
`6/5` in the microscopic energy-window estimate. -/
theorem gaussianSample_afterSecondPicardRemainderCoefficient_le_energyWindow
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (sample : Omega)
    {kappa beta g H T : Real}
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (homega : 0 < modeFrequency
      (gaussianFrozenMass ensemble sample) observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ time ∈ Icc 0 T,
      ∑ i, (gaussianFrozenMass ensemble sample).mass i *
        asConfiguration ((realReparametrize q) time) i = 0)
    (henergy : ∀ time ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian
        (gaussianFrozenMass ensemble sample) kappa beta g
        (asConfiguration ((realReparametrize p) time))
        (asConfiguration ((realReparametrize q) time)) ≤ H) :
    ‖physlibFPUTAfterSecondPicardRemainderCoefficient
        (gaussianFrozenMass ensemble sample) kappa beta g observed
        q radius phase T‖ ≤
      afterSecondPicardWindowEnvelope
        (gaussianFrozenMass ensemble sample) kappa beta g observed
        (actualModalEnergyL1Envelope N (6 / 5 : Real) kappa beta H)
        radius T * T := by
  have hmassUpper : ∀ i : Lattice.Site N,
      (gaussianFrozenMass ensemble sample).mass i ≤ (6 / 5 : Real) := by
    intro i
    simpa [gaussianFrozenMass, RandomEnsemble.massUpper] using
      (ensemble.mass_mem_support i.val sample).2
  exact norm_afterSecondPicardRemainderCoefficient_le_energyWindow
    (gaussianFrozenMass ensemble sample)
      (mUpper := (6 / 5 : Real)) (kappa := kappa) (beta := beta)
      (g := g) (H := H) (T := T)
      (by norm_num) hmassUpper hbeta observed p q radius phase
      homega hT hgauge henergy

/-- Direct frozen-Gaussian microscopic-solution error bound against the
complete two-step Picard amplitude. -/
theorem gaussianSample_interactionPicture_sub_twoStep_le_energyWindow
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (sample : Omega)
    {kappa beta g H T : Real}
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations
      (gaussianFrozenMass ensemble sample) kappa beta g p q)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (homega : 0 < modeFrequency
      (gaussianFrozenMass ensemble sample) observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ time ∈ Icc 0 T,
      ∑ i, (gaussianFrozenMass ensemble sample).mass i *
        asConfiguration ((realReparametrize q) time) i = 0)
    (henergy : ∀ time ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian
        (gaussianFrozenMass ensemble sample) kappa beta g
        (asConfiguration ((realReparametrize p) time))
        (asConfiguration ((realReparametrize q) time)) ≤ H) :
    ‖phaseRenormalize
          (modeFrequency (gaussianFrozenMass ensemble sample) observed * T)
          (physlibModeAmplitude
            (gaussianFrozenMass ensemble sample) observed p q T) -
        twoStepPerturbedAmplitude g
          (physlibModeAmplitude
            (gaussianFrozenMass ensemble sample) observed p q 0)
          (physlibQuadraticFirstPicardCoefficient
            (gaussianFrozenMass ensemble sample) kappa radius phase T observed)
          (physlibFPUTSecondPicardCoefficient
            (gaussianFrozenMass ensemble sample) kappa beta observed
              radius phase T)‖ ≤
      afterSecondPicardWindowEnvelope
        (gaussianFrozenMass ensemble sample) kappa beta g observed
        (actualModalEnergyL1Envelope N (6 / 5 : Real) kappa beta H)
        radius T * T := by
  have hmassUpper : ∀ i : Lattice.Site N,
      (gaussianFrozenMass ensemble sample).mass i ≤ (6 / 5 : Real) := by
    intro i
    simpa [gaussianFrozenMass, RandomEnsemble.massUpper] using
      (ensemble.mass_mem_support i.val sample).2
  exact norm_interactionPicture_physlibMode_sub_twoStep_le_energyWindow
    (gaussianFrozenMass ensemble sample)
      (mUpper := (6 / 5 : Real)) (kappa := kappa) (beta := beta)
      (g := g) (H := H) (T := T)
      (by norm_num) hmassUpper hbeta observed p q hp hq hHamilton
      radius phase homega hT hgauge henergy

/-- The energy-only triangle term exposed by the rigorous envelope carries a
literal inverse coupling on kinetic time. -/
theorem named_energyOnlyLinear_kineticTime_inverseCoupling
    {kappa g M2 radiusBound actualBound L : Real} (hg : 0 < g) :
    energyOnlyLinearIntegratedScale kappa g M2 radiusBound actualBound
        (L / g ^ 2) =
      2 * |kappa| * M2 * radiusBound *
        (actualBound + radiusBound) * L / g :=
  energyOnlyLinearIntegratedScale_kineticTime hg

/-- The explicit first-Picard growth inside the same triangle estimate gives
the still worse inverse-square coupling.  Thus this unconditional absolute
envelope does not close at `T = L/g²`. -/
theorem named_firstPicardTriangle_kineticTime_inverseSquare
    {kappa g M2 radiusBound firstPicardRate L : Real} (hg : 0 < g) :
    firstPicardTriangleIntegratedScale kappa g M2 radiusBound
        firstPicardRate (L / g ^ 2) =
      2 * |kappa| * M2 * radiusBound * firstPicardRate * L ^ 2 / g ^ 2 :=
  firstPicardTriangleIntegratedScale_kineticTime hg

#print axioms gaussianSample_afterSecondPicardRemainderCoefficient_le_energyWindow
#print axioms gaussianSample_interactionPicture_sub_twoStep_le_energyWindow
#print axioms named_energyOnlyLinear_kineticTime_inverseCoupling
#print axioms named_firstPicardTriangle_kineticTime_inverseSquare

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTAfterSecondPicardEnergyEnvelope
