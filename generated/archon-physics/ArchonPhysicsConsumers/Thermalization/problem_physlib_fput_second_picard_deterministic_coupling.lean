import ArchonPhysics.PhyslibFPUTSecondPicardDeterministicCoupling

/-!
# Consumer: the Hamiltonian second-Picard common-source coupling

The contracts below expose the pointwise Hamiltonian-to-Picard displacement,
the zero-failure block-zero certificate, and its explicit cubic second-moment
cost.  Measurability and the reference radius are ensemble inputs; the
`|g|^3` closeness is proved from the exact Hamilton equations.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTSecondPicardDeterministicCoupling

open MeasureTheory
open Set
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.Lattice
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTCouplingMultiblockRestart
open ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder
open ArchonPhysics.PhyslibFPUTSecondPicardDeterministicCoupling
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.QuadraticTensorHistoryExpansion
open ArchonPhysics.ReducedModeTransform

noncomputable section

/-- Consumer-facing `2 M |g|^3 unit` second-moment contract for the
common-source coupling constructed from the exact Hamiltonian block. -/
theorem actual_hamiltonian_to_twoStepPicard_secondMoment_cost_is_cubic
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N)
    {mUpper kappa beta g H T referenceRadius : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta) (hH : 0 ≤ H)
    (observed : Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (hp : ∀ omega, Differentiable Real (p omega))
    (hq : ∀ omega, Differentiable Real (q omega))
    (hHamilton : ∀ omega,
      SatisfiesHamiltonEquations m kappa beta g (p omega) (q omega))
    (radius : Site N → Real)
    (phase : Omega → UnitAddTorus (Site N))
    (hinitial : ∀ omega mode,
      physlibModeAmplitude m mode (p omega) (q omega) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) (phase omega) mode)
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ omega, ∀ s ∈ Icc 0 T, ∑ i, m.mass i *
      asConfiguration ((realReparametrize (q omega)) s) i = 0)
    (henergy : ∀ omega, ∀ s ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p omega)) s))
        (asConfiguration ((realReparametrize (q omega)) s)) ≤ H)
    (hzeroHistory : ∀ omega, ∀ s ∈ Icc 0 T, ∀ mode,
      modeFrequency m mode = 0 →
        physlibModalHistoryDefect
          m (q omega) radius (phase omega) s mode = 0)
    (hreferenceRadius : 0 ≤ referenceRadius)
    (hactualMeasurable : Measurable
      (physlibSecondPicardActualAmplitude m observed p q T))
    (hreferenceMeasurable : Measurable
      (physlibSecondPicardReferenceAmplitude
        m kappa beta g observed radius phase T))
    (hreferenceBound : ∀ omega,
      ‖physlibSecondPicardReferenceAmplitude
          m kappa beta g observed radius phase T omega‖ ≤ referenceRadius) :
    let certificate := physlibSecondPicardBlockZeroCouplingCertificate
      mu m hmUpper0 hmassUpper hbeta hH observed p q hp hq hHamilton radius
        phase hinitial homega hT hgauge henergy hzeroHistory hreferenceRadius
          hactualMeasurable hreferenceMeasurable hreferenceBound
    |∫ z, Complex.normSq z ∂certificate.actualLaw 0 -
        ∫ z, Complex.normSq z ∂certificate.referenceLaw 0| ≤
      2 *
        (referenceRadius + physlibSecondPicardCouplingDelta
          m mUpper kappa beta g H radius T observed) *
        (|g| ^ 3 *
          cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
            m mUpper kappa beta g H radius T observed) :=
  physlibSecondPicardBlockZero_secondMomentError
    mu m hmUpper0 hmassUpper hbeta hH observed p q hp hq hHamilton radius
      phase hinitial homega hT hgauge henergy hzeroHistory hreferenceRadius
        hactualMeasurable hreferenceMeasurable hreferenceBound

#print axioms physlibSecondPicard_actual_sub_reference_eq_remainder
#print axioms physlibSecondPicard_uniformApproximation
#print axioms physlibSecondPicardBlockZeroCouplingCertificate
#print axioms physlibSecondPicardBlockZero_secondMomentError
#print axioms actual_hamiltonian_to_twoStepPicard_secondMoment_cost_is_cubic

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTSecondPicardDeterministicCoupling
