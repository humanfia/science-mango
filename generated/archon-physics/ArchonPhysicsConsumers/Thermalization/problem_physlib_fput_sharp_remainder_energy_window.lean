import ArchonPhysics.PhyslibFPUTSharpRemainderEnergyWindow

/-!
# Consumer: sharpened actual FPUT short-block remainder

This consumer exposes the concrete replacement for the old energy-only
post-second-Picard bound.  The exact first-Duhamel amplitude estimate is
converted to a real modal-history defect of size
`sharpHistoryDefectL1Rate * t`; after subtracting `g A1`, the remaining
history is controlled by `sharpAfterFirstPicardHistoryL1Rate * t`.

Consequently the post-second-Picard coefficient is bounded by the explicit
`sharpAfterSecondPicardSourceWindowEnvelope * T`.  Its direct cubic term
starts at `g^2`, while every quadratic-history term contains either the
first-Duhamel defect or the after-first-Picard remainder.  The former
spurious `O(|g| T)` term from replacing the defect with
`actualBound + radiusL1` is absent.

The zero-frequency translation history remains an explicit matching
condition because the positive-frequency complex amplitude does not encode
that coordinate.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTSharpRemainderEnergyWindow

open MeasureTheory
open UnitAddTorus
open Set
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTActualHaarSecondOrderEnergyDrift
open ArchonPhysics.PhyslibFPUTSharpRemainderEnergyWindow
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.QuadraticTensorHistoryExpansion
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Consumer-facing coefficient-level sharp remainder theorem. -/
theorem actual_physlib_postSecondPicard_remainder_sharp_contract
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {mUpper kappa beta g H T : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (hinitial : ∀ mode,
      physlibModeAmplitude m mode p q 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase mode)
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ s ∈ Icc 0 T, ∑ i, m.mass i *
      asConfiguration ((realReparametrize q) s) i = 0)
    (henergy : ∀ s ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize p) s))
        (asConfiguration ((realReparametrize q) s)) ≤ H)
    (hzeroHistory : ∀ s ∈ Icc 0 T, ∀ mode,
      modeFrequency m mode = 0 →
        physlibModalHistoryDefect m q radius phase s mode = 0) :
    ‖physlibFPUTAfterSecondPicardRemainderCoefficient
        m kappa beta g observed q radius phase T‖ ≤
      sharpAfterSecondPicardCoefficientEnergyWindowEnvelope
        m mUpper kappa beta g H radius T observed :=
  norm_afterSecondPicardRemainderCoefficient_le_sharpEnergyWindow
    m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton radius phase
      hinitial homega hT hgauge henergy hzeroHistory

/-- Consumer-facing Haar expectation endpoint with the sharpened correction. -/
theorem actual_physlib_one_block_Haar_sharp_energy_drift_contract
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
    (hinitial : ∀ phase mode,
      physlibModeAmplitude m mode (p phase) (q phase) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase mode)
    (hT : 0 ≤ T)
    (hgauge : ∀ phase, ∀ s ∈ Icc 0 T, ∑ i, m.mass i *
      asConfiguration ((realReparametrize (q phase)) s) i = 0)
    (henergy : ∀ phase, ∀ s ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p phase)) s))
        (asConfiguration ((realReparametrize (q phase)) s)) ≤ H)
    (hzeroHistory : ∀ phase, ∀ s ∈ Icc 0 T, ∀ mode,
      modeFrequency m mode = 0 →
        physlibModalHistoryDefect
          m (q phase) radius phase s mode = 0)
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
        physlibHaarSharpEnergyCorrectionEnvelope
          m mUpper kappa beta g H radius T observed :=
  abs_integral_actualPhaseModalNormSq_sub_initial_le_sharpEnergyWindow
    m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton radius homega
      hinitial hT hgauge henergy hzeroHistory hmeasurable

#print axioms physlibModalHistoryDefect_apply_eq_interactionPictureCorrectionCoordinate
#print axioms modalAbsSum_physlibModalHistoryDefect_le_sharpRate_mul_time
#print axioms modalAbsSum_afterFirstPicardRemainder_le_sharpRate_mul_time
#print axioms norm_afterSecondPicardRemainderCoefficient_le_sharpEnergyWindow
#print axioms abs_integral_actualPhaseModalNormSq_sub_initial_le_sharpEnergyWindow
#print axioms actual_physlib_one_block_Haar_sharp_energy_drift_contract

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTSharpRemainderEnergyWindow
