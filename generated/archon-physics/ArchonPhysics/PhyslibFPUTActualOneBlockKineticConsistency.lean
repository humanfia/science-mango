import ArchonPhysics.PhyslibFPUTRenormalizedCollisionSignalBridge

/-!
# Actual one-block FPUT consistency with the finite-time kinetic update

For positive block length `T`, the signed order-two coefficient extracted
from the genuine Hamiltonian Haar drift is `T` times the existing normalized
finite-time collision broadening.  Thus the actual one-block increment is an
Euler kinetic step `g^2 T Q_T` plus an explicit higher-order remainder.
-/

namespace ArchonPhysics.PhyslibFPUTActualOneBlockKineticConsistency

open MeasureTheory
open UnitAddTorus
open Set
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTObservedChildQLevelGainLossClosure
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTActualHaarSecondOrderEnergyDrift
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTRenormalizedCollisionSignalBridge
open ArchonPhysics.PhyslibFPUTRenormalizedHaarMomentDefect
open ArchonPhysics.PhyslibFPUTSecondOrderQLevelUnifiedClosure
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound
open ArchonPhysics.PhyslibFPUTSecondOrderUnifiedDegenerateClosure
open ArchonPhysics.PhyslibFPUTSharpRemainderEnergyWindow
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.QuadraticTensorHistoryExpansion
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Positive-time de-normalization of the finite-time collision signal. -/
theorem physlibHaarFiniteTimeKineticCoefficient_eq_time_mul_broadening
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (homega : 0 < modeFrequency m observed) :
    physlibHaarFiniteTimeKineticCoefficient m kappa beta
        (phaseEnergyRadius energy (modeFrequency m)) time observed =
      time * normalizedSecondOrderHaarBroadening
        m kappa beta energy observed time := by
  have hnormalized :=
    normalized_physlibHaarFiniteTimeKineticCoefficient_eq_broadening
      m kappa beta energy observed time homega
  calc
    physlibHaarFiniteTimeKineticCoefficient m kappa beta
        (phaseEnergyRadius energy (modeFrequency m)) time observed =
      time * ((1 / time) *
        physlibHaarFiniteTimeKineticCoefficient m kappa beta
          (phaseEnergyRadius energy (modeFrequency m)) time observed) := by
        field_simp [htime.ne']
    _ = time * normalizedSecondOrderHaarBroadening
        m kappa beta energy observed time := by rw [hnormalized]

/-- Actual Hamiltonian one-block moment consistency with the finite-time
kinetic Euler increment `g^2 T Q_T`. -/
theorem abs_actual_Haar_drift_sub_finiteTimeKineticStep_le_sharpEnergyWindow
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
    (energy : Lattice.Site N → Real)
    (homega : 0 < modeFrequency m observed)
    (hinitial : ∀ phase mode,
      physlibModeAmplitude m mode (p phase) (q phase) 0 =
        canonicalFreeComplexInitialAmplitude
          (phaseEnergyRadius energy (modeFrequency m))
          (modeFrequency m) phase mode)
    (hT : 0 < T)
    (hgauge : ∀ phase, ∀ s ∈ Icc 0 T, ∑ i, m.mass i *
      asConfiguration ((realReparametrize (q phase)) s) i = 0)
    (henergyWindow : ∀ phase, ∀ s ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p phase)) s))
        (asConfiguration ((realReparametrize (q phase)) s)) ≤ H)
    (hzeroHistory : ∀ phase, ∀ s ∈ Icc 0 T, ∀ mode,
      modeFrequency m mode = 0 →
        physlibModalHistoryDefect m (q phase)
          (phaseEnergyRadius energy (modeFrequency m)) phase s mode = 0)
    (hmeasurable : Measurable
      (actualPostSecondPicardEnergyCorrection m kappa beta g observed q
        (phaseEnergyRadius energy (modeFrequency m)) T)) :
    |((∫ phase : UnitAddTorus (Lattice.Site N),
          actualPhaseModalNormSq m observed p q T phase
          ∂finitePhaseHaarLaw (Lattice.Site N)) -
        ∫ phase : UnitAddTorus (Lattice.Site N),
          actualPhaseModalNormSq m observed p q 0 phase
          ∂finitePhaseHaarLaw (Lattice.Site N)) -
      g ^ 2 * T * normalizedSecondOrderHaarBroadening
        m kappa beta energy observed T| ≤
      g ^ 2 *
        (|g| * physlibHaarEnergyDriftC3 m kappa beta
          (phaseEnergyRadius energy (modeFrequency m)) T observed +
        g ^ 2 * physlibHaarEnergyDriftC4 m kappa beta
          (phaseEnergyRadius energy (modeFrequency m)) T observed) +
      physlibHaarSharpEnergyCorrectionEnvelope m mUpper kappa beta g H
        (phaseEnergyRadius energy (modeFrequency m)) T observed := by
  have hbase :=
    abs_actual_Haar_drift_sub_kinetic_signal_le_sharpEnergyWindow
      m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton
        (phaseEnergyRadius energy (modeFrequency m)) homega hinitial
        hT.le hgauge henergyWindow hzeroHistory hmeasurable
  rw [physlibHaarFiniteTimeKineticCoefficient_eq_time_mul_broadening
    m kappa beta energy observed hT homega] at hbase
  simpa only [mul_assoc] using hbase

/-- The same microscopic one-block theorem with the collision step expanded
into the exact q-level gain, feedback, and finite-volume remainder terms. -/
theorem abs_actual_Haar_drift_sub_qLevelKineticStep_le_sharpEnergyWindow
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
    (energy : Lattice.Site N → Real)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (homega : 0 < modeFrequency m observed)
    (hinitial : ∀ phase mode,
      physlibModeAmplitude m mode (p phase) (q phase) 0 =
        canonicalFreeComplexInitialAmplitude
          (phaseEnergyRadius energy (modeFrequency m))
          (modeFrequency m) phase mode)
    (hT : 0 < T)
    (hgauge : ∀ phase, ∀ s ∈ Icc 0 T, ∑ i, m.mass i *
      asConfiguration ((realReparametrize (q phase)) s) i = 0)
    (henergyWindow : ∀ phase, ∀ s ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p phase)) s))
        (asConfiguration ((realReparametrize (q phase)) s)) ≤ H)
    (hzeroHistory : ∀ phase, ∀ s ∈ Icc 0 T, ∀ mode,
      modeFrequency m mode = 0 →
        physlibModalHistoryDefect m (q phase)
          (phaseEnergyRadius energy (modeFrequency m)) phase s mode = 0)
    (hmeasurable : Measurable
      (actualPostSecondPicardEnergyCorrection m kappa beta g observed q
        (phaseEnergyRadius energy (modeFrequency m)) T)) :
    |((∫ phase : UnitAddTorus (Lattice.Site N),
          actualPhaseModalNormSq m observed p q T phase
          ∂finitePhaseHaarLaw (Lattice.Site N)) -
        ∫ phase : UnitAddTorus (Lattice.Site N),
          actualPhaseModalNormSq m observed p q 0 phase
          ∂finitePhaseHaarLaw (Lattice.Site N)) -
      g ^ 2 * T *
        (qLevelResolvedSecondOrderSignedFluxMain
              m kappa T energy observed +
            allEqualOrbitGainSum m kappa T energy observed +
          repeatedAwayFixedPointCorrection m kappa T energy observed +
          observedChildPlacementCorrection m kappa T energy observed +
          allEqualChannelFiveCorrection m kappa T energy observed +
          secondOrderCounterrotatingRemainder
            m kappa T energy observed +
          secondOrderCrossOrbitRemainder
            m kappa T energy observed)| ≤
      g ^ 2 *
        (|g| * physlibHaarEnergyDriftC3 m kappa beta
          (phaseEnergyRadius energy (modeFrequency m)) T observed +
        g ^ 2 * physlibHaarEnergyDriftC4 m kappa beta
          (phaseEnergyRadius energy (modeFrequency m)) T observed) +
      physlibHaarSharpEnergyCorrectionEnvelope m mUpper kappa beta g H
        (phaseEnergyRadius energy (modeFrequency m)) T observed := by
  have hbase :=
    abs_actual_Haar_drift_sub_finiteTimeKineticStep_le_sharpEnergyWindow
      m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton energy
        homega hinitial hT hgauge henergyWindow hzeroHistory hmeasurable
  rw [normalizedSecondOrderHaarBroadening_eq_qLevelUnifiedClosure
    m kappa beta energy observed hT homega henergy] at hbase
  exact hbase

end

end ArchonPhysics.PhyslibFPUTActualOneBlockKineticConsistency
