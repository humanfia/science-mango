import ArchonPhysics.PhyslibFPUTActualOneBlockBoundedLipschitzLaw

/-!
# Consumer: actual one-block Physlib amplitude law

This contract packages the bounded-Lipschitz pushforward-law estimate and the
second/fourth moment endpoint for one actual short-time Physlib block.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTActualOneBlockBoundedLipschitzLaw

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.Lattice
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseEnergyModeCoordinates
open ArchonPhysics.PhyslibFPUTActualOneBlockBoundedLipschitzLaw
open ArchonPhysics.PhyslibFPUTCouplingLawMomentControl
open ArchonPhysics.PhyslibFPUTShortTimeRPAMomentStability
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.PhyslibHamiltonDuhamel

noncomputable section

theorem canonical_reference_law_moments_contract
    {N : Nat} [NeZero N]
    (radius frequency : Site N → Real) (observed : Site N) :
    (∫ z, Complex.normSq z
      ∂canonicalHaarInitialAmplitudeLaw radius frequency observed) =
        canonicalHaarInitialMagnitude radius frequency observed ^ 2 ∧
    (∫ z, Complex.normSq z ^ 2
      ∂canonicalHaarInitialAmplitudeLaw radius frequency observed) =
        canonicalHaarInitialMagnitude radius frequency observed ^ 4 :=
  ⟨integral_normSq_canonicalHaarInitialAmplitudeLaw
      radius frequency observed,
    integral_normSq_sq_canonicalHaarInitialAmplitudeLaw
      radius frequency observed⟩

theorem actual_physlib_one_block_law_endpoint_contract
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N)
    {mUpper kappa beta g H T L M : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Site N)
    (p q : UnitAddTorus (Site N) → Time → HilbertConfiguration N)
    (hp : ∀ phase, Differentiable Real (p phase))
    (hq : ∀ phase, Differentiable Real (q phase))
    (hHamilton : ∀ phase,
      SatisfiesHamiltonEquations m kappa beta g (p phase) (q phase))
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ phase time, time ∈ Set.Icc 0 T →
      ∑ i, m.mass i *
        asConfiguration ((realReparametrize (q phase)) time) i = 0)
    (henergy : ∀ phase time, time ∈ Set.Icc 0 T →
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p phase)) time))
        (asConfiguration ((realReparametrize (q phase)) time)) ≤ H)
    (radius : Site N → Real)
    (hinitial : ∀ phase,
      physlibModeAmplitude m observed (p phase) (q phase) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase observed)
    (hactualMeasurable : Measurable
      (fun phase : UnitAddTorus (Site N) ↦
        physlibModeAmplitude m observed (p phase) (q phase) T))
    (hL : 0 ≤ L)
    (hM : 0 ≤ M)
    (hactualBound : ∀ phase,
      ‖actualInteractionPictureHaarAmplitude m observed p q T phase‖ ≤ M)
    (hinitialBound : canonicalHaarInitialMagnitude
      radius (modeFrequency m) observed ≤ M) :
    BoundedLipschitzTestLawDistanceAtMost
      (actualPhyslibOneBlockAmplitudeLaw m observed p q T)
      (canonicalHaarInitialAmplitudeLaw radius (modeFrequency m) observed)
      L (L * shortTimeRPABlockError
        m mUpper kappa beta g H observed T) ∧
    |∫ z, Complex.normSq z
          ∂actualPhyslibOneBlockAmplitudeLaw m observed p q T -
        canonicalHaarInitialMagnitude radius (modeFrequency m) observed ^ 2| ≤
      2 * M * shortTimeRPABlockError
        m mUpper kappa beta g H observed T ∧
    |∫ z, Complex.normSq z ^ 2
          ∂actualPhyslibOneBlockAmplitudeLaw m observed p q T -
        canonicalHaarInitialMagnitude radius (modeFrequency m) observed ^ 4| ≤
      4 * M ^ 3 * shortTimeRPABlockError
        m mUpper kappa beta g H observed T := by
  constructor
  · exact actual_physlib_oneBlock_boundedLipschitz_law
      m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton homega hT
        hgauge henergy radius hinitial hactualMeasurable hL
  · exact actual_physlib_oneBlock_law_moments_to_canonical_values
      m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton homega hT
        hgauge henergy radius hinitial hactualMeasurable hM hactualBound
          hinitialBound

#print axioms canonical_reference_law_moments_contract
#print axioms actual_physlib_one_block_law_endpoint_contract
#print axioms actual_physlib_oneBlock_boundedLipschitz_law
#print axioms actual_physlib_oneBlock_pushforward_moment_errors
#print axioms actual_physlib_oneBlock_law_moments_to_canonical_values

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTActualOneBlockBoundedLipschitzLaw
