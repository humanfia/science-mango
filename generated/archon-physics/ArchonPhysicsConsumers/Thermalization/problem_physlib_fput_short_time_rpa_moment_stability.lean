import ArchonPhysics.PhyslibFPUTShortTimeRPAMomentStability

/-!
# Consumer: one-block nonlinear RPA moment stability

These contracts expose the deterministic two- and four-product bounds, the exact
canonical Haar initial moments, and the actual short-time Physlib endpoint.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTShortTimeRPAMomentStability

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.Lattice
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTShortTimeRPAMomentStability
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.RandomPhaseMoments

noncomputable section

theorem two_point_product_stability_contract
    {z₁ z₂ w₁ w₂ : Complex} {M epsilon : Real}
    (hM : 0 ≤ M) (hepsilon : 0 ≤ epsilon)
    (hz₁ : ‖z₁‖ ≤ M) (hz₂ : ‖z₂‖ ≤ M)
    (hw₁ : ‖w₁‖ ≤ M) (hw₂ : ‖w₂‖ ≤ M)
    (h₁ : ‖z₁ - w₁‖ ≤ epsilon)
    (h₂ : ‖z₂ - w₂‖ ≤ epsilon) :
    ‖twoPointProduct z₁ z₂ - twoPointProduct w₁ w₂‖ ≤
      2 * M * epsilon :=
  norm_twoPointProduct_sub_le hM hepsilon
    hz₁ hz₂ hw₁ hw₂ h₁ h₂

theorem four_point_product_stability_contract
    {z₁ z₂ z₃ z₄ w₁ w₂ w₃ w₄ : Complex}
    {M epsilon : Real}
    (hM : 0 ≤ M) (hepsilon : 0 ≤ epsilon)
    (hz₁ : ‖z₁‖ ≤ M) (hz₂ : ‖z₂‖ ≤ M)
    (hz₃ : ‖z₃‖ ≤ M) (hz₄ : ‖z₄‖ ≤ M)
    (hw₁ : ‖w₁‖ ≤ M) (hw₂ : ‖w₂‖ ≤ M)
    (hw₃ : ‖w₃‖ ≤ M) (hw₄ : ‖w₄‖ ≤ M)
    (h₁ : ‖z₁ - w₁‖ ≤ epsilon)
    (h₂ : ‖z₂ - w₂‖ ≤ epsilon)
    (h₃ : ‖z₃ - w₃‖ ≤ epsilon)
    (h₄ : ‖z₄ - w₄‖ ≤ epsilon) :
    ‖fourPointProduct z₁ z₂ z₃ z₄ -
        fourPointProduct w₁ w₂ w₃ w₄‖ ≤
      4 * M ^ 3 * epsilon :=
  norm_fourPointProduct_sub_le hM hepsilon
    hz₁ hz₂ hz₃ hz₄ hw₁ hw₂ hw₃ hw₄
      h₁ h₂ h₃ h₄

theorem canonical_Haar_initial_moments_contract
    {N : Nat} [NeZero N]
    (radius frequency : Site N → Real) (observed : Site N) :
    (∫ phase : UnitAddTorus (Site N),
      Complex.normSq
        (canonicalFreeComplexInitialAmplitude radius frequency phase observed)
      ∂finitePhaseHaarLaw (Site N)) =
        canonicalHaarInitialMagnitude radius frequency observed ^ 2 ∧
    (∫ phase : UnitAddTorus (Site N),
      Complex.normSq
          (canonicalFreeComplexInitialAmplitude radius frequency phase observed) ^ 2
      ∂finitePhaseHaarLaw (Site N)) =
        canonicalHaarInitialMagnitude radius frequency observed ^ 4 :=
  ⟨integral_normSq_canonicalFreeComplexInitialAmplitude
      radius frequency observed,
    integral_normSq_sq_canonicalFreeComplexInitialAmplitude
      radius frequency observed⟩

theorem actual_physlib_one_block_approximate_RPA_contract
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N)
    {mUpper kappa beta g H T M : Real}
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
    (hM : 0 ≤ M)
    (hactualBound : ∀ phase,
      ‖actualInteractionPictureHaarAmplitude m observed p q T phase‖ ≤ M)
    (hinitialBound : canonicalHaarInitialMagnitude
      radius (modeFrequency m) observed ≤ M) :
    |∫ phase : UnitAddTorus (Site N),
        Complex.normSq
          (actualInteractionPictureHaarAmplitude m observed p q T phase)
        ∂finitePhaseHaarLaw (Site N) -
      canonicalHaarInitialMagnitude radius (modeFrequency m) observed ^ 2| ≤
        2 * M * shortTimeRPABlockError
          m mUpper kappa beta g H observed T ∧
    |∫ phase : UnitAddTorus (Site N),
        Complex.normSq
            (actualInteractionPictureHaarAmplitude m observed p q T phase) ^ 2
        ∂finitePhaseHaarLaw (Site N) -
      canonicalHaarInitialMagnitude radius (modeFrequency m) observed ^ 4| ≤
        4 * M ^ 3 * shortTimeRPABlockError
          m mUpper kappa beta g H observed T :=
  actual_physlib_shortTime_approximateRPA_moments
    m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton homega hT
      hgauge henergy radius hinitial hactualMeasurable hM hactualBound
        hinitialBound

#print axioms two_point_product_stability_contract
#print axioms four_point_product_stability_contract
#print axioms canonical_Haar_initial_moments_contract
#print axioms actual_physlib_one_block_approximate_RPA_contract
#print axioms ArchonPhysics.PhyslibFPUTShortTimeRPAMomentStability.actual_physlib_shortTime_approximateRPA_moments

end


end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTShortTimeRPAMomentStability
