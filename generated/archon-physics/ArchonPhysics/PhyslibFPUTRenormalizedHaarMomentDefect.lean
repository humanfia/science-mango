import ArchonPhysics.PhyslibFPUTSharpRemainderEnergyWindow

/-!
# Renormalized one-block Haar moment defect for the actual FPUT flow

The order-`g^2` matched-charge coefficient is the finite-time kinetic signal,
not an RPA error.  This module subtracts that signed coefficient from the
actual one-block Haar energy increment.  What remains is bounded by the
order-`g^3` and order-`g^4` Picard terms plus the literal nonlinear remainder.

This is the moment-level normalization needed before asking whether a
one-block defect is `o(g^2 h)` and hence summable over kinetic block counts.
-/

namespace ArchonPhysics.PhyslibFPUTRenormalizedHaarMomentDefect

open MeasureTheory
open UnitAddTorus
open Set
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.DuhamelSecondMomentAlgebra
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTActualHaarSecondOrderEnergyDrift
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily
open ArchonPhysics.PhyslibFPUTSharpRemainderEnergyWindow
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.RandomPhaseMoments
open ArchonPhysics.QuadraticTensorHistoryExpansion

noncomputable section

/-- The signed finite-time order-two Haar coefficient.  Unlike
`physlibHaarEnergyDriftC2`, this is not an absolute-mass envelope. -/
def physlibHaarFiniteTimeKineticCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) : Real :=
  finiteCharacterFamilySecondOrderCoefficient
    (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
    (freeInitialPhaseCharge observed)
    (physlibQuadraticFirstPicardCharacterCoefficient
      m kappa radius time observed)
    quadraticPhaseCharge
    (completeSecondPicardCoefficient
      m kappa beta radius observed time)
    completeSecondPicardCharge

/-- After subtracting the signed order-`g^2` kinetic signal, the genuine
one-block Haar moment defect contains only the higher Picard orders and the
literal nonlinear correction. -/
theorem abs_actual_Haar_drift_sub_kinetic_signal_le_of_correction_bound
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
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
    (time C : Real)
    (hmeasurable : Measurable
      (actualPostSecondPicardEnergyCorrection
        m kappa beta g observed q radius time))
    (hbound : ∀ phase,
      |actualPostSecondPicardEnergyCorrection
        m kappa beta g observed q radius time phase| ≤ C) :
    |((∫ phase : UnitAddTorus (Lattice.Site N),
          actualPhaseModalNormSq m observed p q time phase
          ∂finitePhaseHaarLaw (Lattice.Site N)) -
        ∫ phase : UnitAddTorus (Lattice.Site N),
          actualPhaseModalNormSq m observed p q 0 phase
          ∂finitePhaseHaarLaw (Lattice.Site N)) -
      g ^ 2 * physlibHaarFiniteTimeKineticCoefficient
        m kappa beta radius time observed| ≤
      g ^ 2 *
        (|g| * physlibHaarEnergyDriftC3
          m kappa beta radius time observed +
        g ^ 2 * physlibHaarEnergyDriftC4
          m kappa beta radius time observed) + C := by
  let Z := sameChargeFamilySquare
    (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
    (freeInitialPhaseCharge observed)
  let S2 := physlibHaarFiniteTimeKineticCoefficient
    m kappa beta radius time observed
  let S3 := equalChargeFamilyInterference
    (physlibQuadraticFirstPicardCharacterCoefficient
      m kappa radius time observed)
    quadraticPhaseCharge
    (completeSecondPicardCoefficient
      m kappa beta radius observed time)
    completeSecondPicardCharge
  let S4 := sameChargeFamilySquare
    (completeSecondPicardCoefficient
      m kappa beta radius observed time)
    completeSecondPicardCharge
  let R := ∫ phase : UnitAddTorus (Lattice.Site N),
    actualPostSecondPicardEnergyCorrection
      m kappa beta g observed q radius time phase
    ∂finitePhaseHaarLaw (Lattice.Site N)
  have hactual :=
    integral_actualPhaseModalNormSq_eq_matchedCharge_add_boundedCorrection
      m kappa beta g observed p q hp hq hHamilton radius homega hinitial
        time hmeasurable hbound
  have hinitialMoment :=
    integral_actualPhaseModalNormSq_zero_eq_sameChargeFamilySquare
      m observed p q radius homega hinitial
  have hmatched := physlibMatchedChargeTwoStepMoment_eq_without_firstOrder
    m kappa beta g radius time observed
  have hactualExpansion :
      (∫ phase : UnitAddTorus (Lattice.Site N),
        actualPhaseModalNormSq m observed p q time phase
        ∂finitePhaseHaarLaw (Lattice.Site N)) =
      Z + g ^ 2 * S2 + g ^ 3 * S3 + g ^ 4 * S4 + R := by
    rw [hactual.1, hmatched]
    rfl
  have hinitialExpansion :
      (∫ phase : UnitAddTorus (Lattice.Site N),
        actualPhaseModalNormSq m observed p q 0 phase
        ∂finitePhaseHaarLaw (Lattice.Site N)) = Z := by
    exact hinitialMoment
  have hS3 : |S3| ≤
      physlibHaarEnergyDriftC3 m kappa beta radius time observed := by
    dsimp only [S3]
    simpa [physlibHaarEnergyDriftC3, physlibA1CoefficientAbsMass,
      physlibA2CoefficientAbsMass] using
      (abs_equalChargeFamilyInterference_le_two_mul_absMass
        (physlibQuadraticFirstPicardCharacterCoefficient
          m kappa radius time observed)
        quadraticPhaseCharge
        (completeSecondPicardCoefficient
          m kappa beta radius observed time)
        completeSecondPicardCharge)
  have hS4 : |S4| ≤
      physlibHaarEnergyDriftC4 m kappa beta radius time observed := by
    dsimp only [S4]
    simpa [physlibHaarEnergyDriftC4, physlibA2CoefficientAbsMass] using
      (abs_sameChargeFamilySquare_le_absMass_sq
        (completeSecondPicardCoefficient
          m kappa beta radius observed time)
        completeSecondPicardCharge)
  have hR : |R| ≤ C := by
    exact hactual.2
  have hg3 : |g ^ 3| = g ^ 2 * |g| := by
    rw [abs_pow]
    rw [show |g| ^ 3 = |g| ^ 2 * |g| by ring, sq_abs]
  have hg4 : |g ^ 4| = g ^ 4 := abs_of_nonneg (by positivity)
  rw [hactualExpansion, hinitialExpansion]
  change |Z + g ^ 2 * S2 + g ^ 3 * S3 + g ^ 4 * S4 + R - Z -
      g ^ 2 * S2| ≤ _
  rw [show Z + g ^ 2 * S2 + g ^ 3 * S3 + g ^ 4 * S4 + R - Z -
      g ^ 2 * S2 = g ^ 3 * S3 + g ^ 4 * S4 + R by ring]
  calc
    |g ^ 3 * S3 + g ^ 4 * S4 + R| ≤
        |g ^ 3 * S3| + |g ^ 4 * S4| + |R| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = (g ^ 2 * |g|) * |S3| + g ^ 4 * |S4| + |R| := by
      rw [abs_mul, abs_mul, hg3, hg4]
    _ ≤ (g ^ 2 * |g|) *
          physlibHaarEnergyDriftC3 m kappa beta radius time observed +
        g ^ 4 * physlibHaarEnergyDriftC4
          m kappa beta radius time observed + C := by
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left hS3
            (mul_nonneg (sq_nonneg g) (abs_nonneg g)))
          (mul_le_mul_of_nonneg_left hS4 (by positivity)))
        hR
    _ = _ := by ring

/-- Concrete actual-FPUT specialization using the sharpened energy-window
correction.  The leading signed `g^2` kinetic signal is no longer counted as
an RPA defect. -/
theorem abs_actual_Haar_drift_sub_kinetic_signal_le_sharpEnergyWindow
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
    |((∫ phase : UnitAddTorus (Lattice.Site N),
          actualPhaseModalNormSq m observed p q T phase
          ∂finitePhaseHaarLaw (Lattice.Site N)) -
        ∫ phase : UnitAddTorus (Lattice.Site N),
          actualPhaseModalNormSq m observed p q 0 phase
          ∂finitePhaseHaarLaw (Lattice.Site N)) -
      g ^ 2 * physlibHaarFiniteTimeKineticCoefficient
        m kappa beta radius T observed| ≤
      g ^ 2 *
        (|g| * physlibHaarEnergyDriftC3
          m kappa beta radius T observed +
        g ^ 2 * physlibHaarEnergyDriftC4
          m kappa beta radius T observed) +
      physlibHaarSharpEnergyCorrectionEnvelope
        m mUpper kappa beta g H radius T observed := by
  apply abs_actual_Haar_drift_sub_kinetic_signal_le_of_correction_bound
    m kappa beta g observed p q hp hq hHamilton radius homega
      (fun phase ↦ hinitial phase observed) T
      (physlibHaarSharpEnergyCorrectionEnvelope
        m mUpper kappa beta g H radius T observed) hmeasurable
  intro phase
  apply abs_actualPostSecondPicardEnergyCorrection_le
    m kappa beta g observed q radius T phase homega
  exact norm_afterSecondPicardRemainderCoefficient_le_sharpEnergyWindow
    m hmUpper0 hmassUpper hbeta observed (p phase) (q phase)
      (hp phase) (hq phase) (hHamilton phase) radius phase (hinitial phase)
      homega hT (hgauge phase) (henergy phase) (hzeroHistory phase)

end

end ArchonPhysics.PhyslibFPUTRenormalizedHaarMomentDefect
