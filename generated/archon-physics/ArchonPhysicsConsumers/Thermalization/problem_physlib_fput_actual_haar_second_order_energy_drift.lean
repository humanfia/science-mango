import ArchonPhysics.PhyslibFPUTActualHaarSecondOrderEnergyDrift

/-!
# Consumer: exact second-order Haar onset for one actual Physlib block

This consumer exposes the computable finite coefficient masses and the true
expectation-level one-block endpoint.  Haar charge parity removes the entire
first-order Picard energy drift, leaving

`g^2 * (C2 + |g| * C3 + g^2 * C4)`

with `C2 = W^2 + 2 Z U`, `C3 = 2 W U`, and `C4 = U^2`.

The theorem also retains the literal nonlinear correction.  Its currently
available energy-window bound contains an `O(|g| T)` contribution; this
consumer therefore does **not** assert that the complete actual drift is
`O(g^2)`, nor does it assert a restart or kinetic-time result.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTActualHaarSecondOrderEnergyDrift

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTActualHaarSecondOrderEnergyDrift
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- The three displayed constants really are finite sums of absolute values
of the physical `A0`, `A1`, and complete `A2` coefficients. -/
theorem finite_coefficient_mass_constants_contract
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) :
    physlibHaarEnergyDriftC2 m kappa beta radius time observed =
        physlibA1CoefficientAbsMass m kappa radius time observed ^ 2 +
          2 * physlibA0CoefficientAbsMass m radius observed *
            physlibA2CoefficientAbsMass
              m kappa beta radius time observed ∧
    physlibHaarEnergyDriftC3 m kappa beta radius time observed =
        2 * physlibA1CoefficientAbsMass m kappa radius time observed *
          physlibA2CoefficientAbsMass
            m kappa beta radius time observed ∧
    physlibHaarEnergyDriftC4 m kappa beta radius time observed =
        physlibA2CoefficientAbsMass
          m kappa beta radius time observed ^ 2 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Consumer-facing genuine one-block energy-drift theorem.  The comparison
is between the actual modal squared-norm expectations at `T` and at `0`. -/
theorem actual_physlib_one_block_Haar_second_order_energy_drift_contract
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {mUpper kappa beta g H T : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Lattice.Site N)
    (p q : UnitAddTorus (Lattice.Site N) → Time → HilbertConfiguration N)
    (hp : ∀ phase, Differentiable Real (p phase))
    (hq : ∀ phase, Differentiable Real (q phase))
    (hHamilton : ∀ phase,
      SatisfiesHamiltonEquations m kappa beta g (p phase) (q phase))
    (radius : Lattice.Site N → Real)
    (homega : 0 < modeFrequency m observed)
    (hinitial : ∀ phase,
      physlibModeAmplitude m observed (p phase) (q phase) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ phase time, time ∈ Set.Icc 0 T → ∑ i, m.mass i *
      asConfiguration ((realReparametrize (q phase)) time) i = 0)
    (henergy : ∀ phase time, time ∈ Set.Icc 0 T →
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p phase)) time))
        (asConfiguration ((realReparametrize (q phase)) time)) ≤ H)
    (hmeasurable : Measurable
      (actualPostSecondPicardEnergyCorrection
        m kappa beta g observed q radius T)) :
    |(∫ phase : UnitAddTorus (Lattice.Site N),
        actualPhaseModalNormSq m observed p q T phase
        ∂finitePhaseHaarLaw (Lattice.Site N)) -
      ∫ phase : UnitAddTorus (Lattice.Site N),
        actualPhaseModalNormSq m observed p q 0 phase
        ∂finitePhaseHaarLaw (Lattice.Site N)| ≤
      g ^ 2 *
        (physlibHaarEnergyDriftC2 m kappa beta radius T observed +
          |g| * physlibHaarEnergyDriftC3 m kappa beta radius T observed +
          g ^ 2 * physlibHaarEnergyDriftC4
            m kappa beta radius T observed) +
        physlibHaarEnergyCorrectionEnvelope
          m mUpper kappa beta g H radius T observed :=
  abs_integral_actualPhaseModalNormSq_sub_initial_le_energyWindow
    m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton radius homega
      hinitial hT hgauge henergy hmeasurable

#print axioms norm_equalChargeCrossPairSum_le_absMass_mul_absMass
#print axioms abs_sameChargeFamilySquare_le_absMass_sq
#print axioms abs_equalChargeFamilyInterference_le_two_mul_absMass
#print axioms abs_physlibMatchedChargeTwoStepMoment_sub_A0_le
#print axioms integral_actualPhaseModalNormSq_zero_eq_sameChargeFamilySquare
#print axioms abs_integral_actualPhaseModalNormSq_sub_initial_le_energyWindow
#print axioms actual_physlib_one_block_Haar_second_order_energy_drift_contract

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTActualHaarSecondOrderEnergyDrift
