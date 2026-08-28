import ArchonPhysics.PhyslibFPUTActualOneBlockKineticConsistency
import ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder

/-!
# Little-o consistency of one finite FPUT block

The cubic-history Lipschitz estimate exposes an exact extra factor `|g|^3`
in the nonlinear correction.  After subtracting the signed finite-time
collision step, the whole actual Haar defect is therefore `o(g^2 T)` at
fixed finite volume and fixed positive block length.

The limiting statement below does not assume boundedness or convergence of
the unit envelope.  Its continuity at zero is proved directly from its
explicit finite-sum formula.
-/

namespace ArchonPhysics.PhyslibFPUTActualOneBlockKineticLittleO

open Filter
open MeasureTheory
open Set
open Topology
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTActualHaarSecondOrderEnergyDrift
open ArchonPhysics.PhyslibFPUTActualOneBlockKineticConsistency
open ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder
open ArchonPhysics.PhyslibFPUTRenormalizedHaarMomentDefect
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibFPUTSharpRemainderEnergyWindow
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.QuadraticTensorHistoryExpansion
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- The explicit upper bound for the renormalized one-block defect. -/
def physlibFPUTKineticLittleORhs
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper kappa beta H : Real)
    (radius : Lattice.Site N → Real) (T : Real)
    (observed : Lattice.Site N) (g : Real) : Real :=
  g ^ 2 *
      (|g| * physlibHaarEnergyDriftC3
          m kappa beta radius T observed +
        g ^ 2 * physlibHaarEnergyDriftC4
          m kappa beta radius T observed) +
    |g| ^ 3 *
      physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
        m mUpper kappa beta g H radius T observed

/-- The actual microscopic Haar increment differs from the finite-time
kinetic Euler step by the explicit little-o candidate above. -/
theorem abs_actual_Haar_drift_sub_finiteTimeKineticStep_le_cubicLittleORhs
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
      physlibFPUTKineticLittleORhs m mUpper kappa beta H
        (phaseEnergyRadius energy (modeFrequency m)) T observed g := by
  let radius := phaseEnergyRadius energy (modeFrequency m)
  have hbase :=
    abs_actual_Haar_drift_sub_kinetic_signal_le_of_correction_bound
      m kappa beta g observed p q hp hq hHamilton radius homega
        (fun phase ↦ hinitial phase observed) T
        (physlibHaarCubicLipschitzEnergyCorrectionEnvelope
          m mUpper kappa beta g H radius T observed) hmeasurable
        (fun phase ↦ by
          apply abs_actualPostSecondPicardEnergyCorrection_le
            m kappa beta g observed q radius T phase homega
          exact
            norm_afterSecondPicardRemainderCoefficient_le_cubicLipschitzEnergyWindow
              m hmUpper0 hmassUpper hbeta observed (p phase) (q phase)
                (hp phase) (hq phase) (hHamilton phase) radius phase
                  (hinitial phase) homega hT.le (hgauge phase)
                    (henergyWindow phase) (hzeroHistory phase))
  rw [physlibHaarFiniteTimeKineticCoefficient_eq_time_mul_broadening
    m kappa beta energy observed hT homega] at hbase
  rw [physlibHaarCubicLipschitzEnergyCorrectionEnvelope_abs_cube_factor]
    at hbase
  simpa only [radius, mul_assoc, physlibFPUTKineticLittleORhs] using hbase

/-- At fixed finite volume and fixed physical parameters, the unit
nonlinear-correction envelope is continuous in the coupling at zero. -/
theorem continuousAt_zero_physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper kappa beta H : Real)
    (radius : Lattice.Site N → Real) (T : Real)
    (observed : Lattice.Site N) :
    ContinuousAt
      (fun g : Real ↦
        physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
          m mUpper kappa beta g H radius T observed) 0 := by
  unfold physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
    cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
    cubicLipschitzAfterSecondPicardSourceUnitEnergyWindowEnvelope
    cubicLipschitzAfterSecondPicardSourceWindowUnitEnvelope
    sharpAfterFirstPicardHistoryL1UnitRate
    sharpFirstPicardRemainderSourceWindowUnitEnvelope
    sharpHistoryDefectL1UnitRate
    firstDuhamelWindowUnitCouplingEnvelope
    finiteCharacterTwoStepAbsMass
  fun_prop

/-- The explicit renormalized defect bound, divided by the kinetic block
scale `g^2 T`, tends to zero through nonzero couplings. -/
theorem physlibFPUTKineticLittleORhs_div_kineticScale_tendsto_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper kappa beta H : Real)
    (radius : Lattice.Site N → Real) {T : Real} (hT : 0 < T)
    (observed : Lattice.Site N) :
    Tendsto
      (fun g : Real ↦
        physlibFPUTKineticLittleORhs m mUpper kappa beta H
            radius T observed g / (g ^ 2 * T))
      (nhdsWithin 0 ({0} : Set Real)ᶜ) (nhds 0) := by
  let U : Real → Real := fun g ↦
    physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
      m mUpper kappa beta g H radius T observed
  let C3 := physlibHaarEnergyDriftC3 m kappa beta radius T observed
  let C4 := physlibHaarEnergyDriftC4 m kappa beta radius T observed
  have hU : ContinuousAt U 0 := by
    exact
      continuousAt_zero_physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
        m mUpper kappa beta H radius T observed
  have hcontinuous : ContinuousAt
      (fun g : Real ↦ (|g| * C3 + g ^ 2 * C4 + |g| * U g) / T) 0 := by
    fun_prop
  have hlimit : Tendsto
      (fun g : Real ↦ (|g| * C3 + g ^ 2 * C4 + |g| * U g) / T)
      (nhdsWithin 0 ({0} : Set Real)ᶜ) (nhds 0) := by
    simpa only [abs_zero, zero_mul, zero_pow (by norm_num : (2 : Nat) ≠ 0),
      add_zero, zero_add, zero_div] using
        hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  apply (tendsto_congr' ?_).mpr hlimit
  filter_upwards [self_mem_nhdsWithin] with g hg
  have hg0 : g ≠ 0 := by simpa using hg
  dsimp only [physlibFPUTKineticLittleORhs, U, C3, C4]
  rw [show |g| ^ 3 = g ^ 2 * |g| by
    rw [← sq_abs]
    ring]
  field_simp [hg0, hT.ne']

/-- Sequential form of the explicit `o(g^2 T)` estimate. -/
theorem physlibFPUTKineticLittleORhs_sequence_div_kineticScale_tendsto_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper kappa beta H : Real)
    (radius : Lattice.Site N → Real) {T : Real} (hT : 0 < T)
    (observed : Lattice.Site N)
    (g : Nat → Real)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : ∀ᶠ n in atTop, g n ≠ 0) :
    Tendsto
      (fun n ↦
        physlibFPUTKineticLittleORhs m mUpper kappa beta H
            radius T observed (g n) / (g n ^ 2 * T))
      atTop (nhds 0) := by
  apply
    (physlibFPUTKineticLittleORhs_div_kineticScale_tendsto_zero
      m mUpper kappa beta H radius hT observed).comp
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨hg, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hg0⟩

/-- Any nonnegative defect bounded by the explicit microscopic right-hand
side has vanishing defect-to-step ratio.  This is the form consumed by the
multiblock kinetic Euler shadowing theorem. -/
theorem defectMax_div_kineticScale_tendsto_zero_of_le_littleORhs
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper kappa beta H : Real)
    (radius : Lattice.Site N → Real) {T : Real} (hT : 0 < T)
    (observed : Lattice.Site N)
    (g defectMax : Nat → Real)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : ∀ᶠ n in atTop, g n ≠ 0)
    (hdefect0 : ∀ᶠ n in atTop, 0 ≤ defectMax n)
    (hdefect : ∀ᶠ n in atTop,
      defectMax n ≤
        physlibFPUTKineticLittleORhs m mUpper kappa beta H
          radius T observed (g n)) :
    Tendsto (fun n ↦ defectMax n / (g n ^ 2 * T)) atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [hdefect0, hg0] with n hn0 hgn
    exact div_nonneg hn0 (mul_nonneg (sq_nonneg _) hT.le)
  · filter_upwards [hdefect, hg0] with n hn hgn
    exact div_le_div_of_nonneg_right hn
      (mul_nonneg (sq_nonneg _) hT.le)
  · exact
      physlibFPUTKineticLittleORhs_sequence_div_kineticScale_tendsto_zero
        m mUpper kappa beta H radius hT observed g hg hg0

end

end ArchonPhysics.PhyslibFPUTActualOneBlockKineticLittleO
