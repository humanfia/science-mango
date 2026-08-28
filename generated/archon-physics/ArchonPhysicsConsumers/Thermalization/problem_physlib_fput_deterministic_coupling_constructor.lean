import ArchonPhysics.PhyslibFPUTDeterministicCouplingConstructor

/-!
# Consumer: deterministic restart-coupling constructors

The contracts below expose the zero-failure constructor, its sharp
second/fourth moment costs, and the concrete block-zero coupling obtained from
the exact Physlib Hamiltonian Duhamel estimate.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTDeterministicCouplingConstructor

open MeasureTheory
open Set
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.Lattice
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTCouplingMultiblockRestart
open ArchonPhysics.PhyslibFPUTDeterministicCouplingConstructor
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.ReducedModeTransform

noncomputable section

theorem uniform_approximation_has_zero_failure_and_moment_cost_contract
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {M : Real} (hM : 0 ≤ M)
    (actual reference : Nat → Omega → Complex) (delta : Nat → Real)
    (hactual : ∀ j, Measurable (actual j))
    (hreference : ∀ j, Measurable (reference j))
    (hdelta : ∀ j, 0 ≤ delta j)
    (hnear : ∀ j omega, ‖actual j omega - reference j omega‖ ≤ delta j)
    (hactualBound : ∀ j omega, ‖actual j omega‖ ≤ M)
    (hreferenceBound : ∀ j omega, ‖reference j omega‖ ≤ M)
    (j : Nat) :
    let certificate :=
      AmplitudeCouplingRestartCertificate.ofUniformApproximation mu
        actual reference delta hactual hreference hdelta hnear
          hactualBound hreferenceBound
    certificate.bad j = ∅ ∧ certificate.failureProbability j = 0 ∧
    |∫ z, Complex.normSq z ∂certificate.actualLaw j -
        ∫ z, Complex.normSq z ∂certificate.referenceLaw j| ≤
          2 * M * delta j ∧
    |∫ z, Complex.normSq z ^ 2 ∂certificate.actualLaw j -
        ∫ z, Complex.normSq z ^ 2 ∂certificate.referenceLaw j| ≤
          4 * M ^ 3 * delta j := by
  dsimp only
  refine ⟨rfl, rfl, ?_⟩
  exact AmplitudeCouplingRestartCertificate.ofUniformApproximation_second_fourth_moment_errors
      mu hM actual reference delta hactual hreference hdelta hnear
        hactualBound hreferenceBound j

theorem physlib_hamiltonian_duhamel_builds_block_zero_coupling_contract
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
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
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ omega, ∀ time ∈ Icc 0 T, ∑ i, m.mass i *
      asConfiguration ((realReparametrize (q omega)) time) i = 0)
    (henergy : ∀ omega, ∀ time ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p omega)) time))
        (asConfiguration ((realReparametrize (q omega)) time)) ≤ H)
    (hreferenceRadius : 0 ≤ referenceRadius)
    (hactualMeasurable : Measurable
      (physlibFirstDuhamelActualAmplitude m observed p q T))
    (hreferenceMeasurable : Measurable
      (physlibFirstDuhamelReferenceAmplitude m observed p q))
    (hreferenceBound : ∀ omega,
      ‖physlibFirstDuhamelReferenceAmplitude m observed p q omega‖ ≤
        referenceRadius) :
    let certificate := physlibFirstDuhamelBlockZeroCouplingCertificate
      mu m hmUpper0 hmassUpper hbeta hH observed p q hp hq hHamilton homega hT
        hgauge henergy hreferenceRadius hactualMeasurable hreferenceMeasurable
          hreferenceBound
    certificate.failureProbability 0 = 0 ∧
    certificate.delta 0 = physlibFirstDuhamelCouplingRadius
      m mUpper kappa beta g H observed T ∧
    (∀ omega,
      certificate.actual 0 omega =
        physlibFirstDuhamelActualAmplitude m observed p q T omega) ∧
    (∀ omega,
      certificate.reference 0 omega =
        physlibFirstDuhamelReferenceAmplitude m observed p q omega) ∧
    (∀ omega,
      ‖certificate.actual 0 omega - certificate.reference 0 omega‖ ≤
        physlibFirstDuhamelCouplingRadius
          m mUpper kappa beta g H observed T) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [physlibFirstDuhamelBlockZeroCouplingCertificate]
  · simp [physlibFirstDuhamelBlockZeroCouplingCertificate]
  · intro omega
    simp [physlibFirstDuhamelBlockZeroCouplingCertificate]
  · intro omega
    simp [physlibFirstDuhamelBlockZeroCouplingCertificate]
  · intro omega
    simpa [physlibFirstDuhamelBlockZeroCouplingCertificate] using
      physlibFirstDuhamel_uniformApproximation
        m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton homega hT
          hgauge henergy omega

#print axioms uniform_approximation_has_zero_failure_and_moment_cost_contract
#print axioms physlib_hamiltonian_duhamel_builds_block_zero_coupling_contract
#print axioms AmplitudeCouplingRestartCertificate.ofUniformApproximation
#print axioms AmplitudeCouplingRestartCertificate.ofUniformApproximation_second_fourth_moment_errors
#print axioms AmplitudeCouplingRestartCertificate.ofBlockZeroUniformApproximation
#print axioms AmplitudeCouplingRestartCertificate.ofBlockZeroUniformApproximation_second_fourth_moment_errors
#print axioms physlibFirstDuhamel_uniformApproximation
#print axioms physlibFirstDuhamelBlockZeroCouplingCertificate

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTDeterministicCouplingConstructor
