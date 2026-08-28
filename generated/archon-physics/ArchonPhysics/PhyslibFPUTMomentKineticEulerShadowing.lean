import ArchonPhysics.PhyslibFPUTActualOneBlockKineticConsistency
import ArchonPhysics.PhyslibFPUTKineticScaleRPACriteria

/-!
# Moment-level kinetic Euler shadowing

This module closes the deterministic numerical-analysis step between a
microscopic one-block moment law and its kinetic Euler approximation.  The
one-step error recurrence is *derived* from the displayed microscopic
residual and the Lipschitz property of the collision field; it is not an
additional restart assumption.

The final asymptotic theorem is deliberately moment-level.  It does not claim
that the nonlinear FPUT flow regenerates Haar phases between blocks.  Instead,
it states exactly what follows once every actual block supplies the same
residual interface.
-/

namespace ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing

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
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTKineticScaleRPACriteria
open ArchonPhysics.PhyslibFPUTMultiblockRPAMomentPropagation
open ArchonPhysics.PhyslibFPUTRenormalizedHaarMomentDefect
open ArchonPhysics.PhyslibFPUTSharpRemainderEnergyWindow
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.QuadraticTensorHistoryExpansion
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- The scalar interface supplied by a microscopic one-block consistency
theorem: the actual increment differs from one kinetic Euler increment by at
most `defect`. -/
def MomentKineticEulerResidual
    (initial final step collision defect : Real) : Prop :=
  |final - initial - step * collision| ≤ defect

/-- The kinetic Euler trajectory associated with a scalar collision field. -/
def IsKineticEulerTrajectory
    (V : Nat → Real) (step : Real) (Q : Real → Real) : Prop :=
  ∀ j, V (j + 1) = V j + step * Q (V j)

/-- A microscopic residual and a Lipschitz collision field imply the affine
error recurrence.  In particular, the recurrence is a conclusion rather than
a hidden multiblock hypothesis. -/
theorem abs_microscopic_sub_kinetic_next_le
    (E V : Nat → Real) (Q : Real → Real)
    (step L : Real) (defect : Nat → Real)
    (hstep : 0 ≤ step)
    (hkinetic : IsKineticEulerTrajectory V step Q)
    (hresidual : ∀ j,
      MomentKineticEulerResidual
        (E j) (E (j + 1)) step (Q (E j)) (defect j))
    (hQ : ∀ x y, |Q x - Q y| ≤ L * |x - y|)
    (j : Nat) :
    |E (j + 1) - V (j + 1)| ≤
      (1 + L * step) * |E j - V j| + defect j := by
  have hdecomposition :
      E (j + 1) - V (j + 1) =
        (E (j + 1) - E j - step * Q (E j)) +
          ((E j - V j) + step * (Q (E j) - Q (V j))) := by
    rw [hkinetic j]
    ring
  rw [hdecomposition]
  calc
    |(E (j + 1) - E j - step * Q (E j)) +
        ((E j - V j) + step * (Q (E j) - Q (V j)))| ≤
        |E (j + 1) - E j - step * Q (E j)| +
          |(E j - V j) + step * (Q (E j) - Q (V j))| :=
      abs_add_le _ _
    _ ≤ defect j +
          (|E j - V j| + |step * (Q (E j) - Q (V j))|) := by
      gcongr
      · exact hresidual j
      · exact abs_add_le _ _
    _ ≤ defect j +
          (|E j - V j| + step * (L * |E j - V j|)) := by
      gcongr
      rw [abs_mul, abs_of_nonneg hstep]
      exact mul_le_mul_of_nonneg_left (hQ (E j) (V j)) hstep
    _ = (1 + L * step) * |E j - V j| + defect j := by ring

/-- Finite-block shadowing with nonuniform microscopic residuals. -/
theorem moment_kineticEuler_shadowing_exp_bound
    (E V : Nat → Real) (Q : Real → Real)
    (step L : Real) (defect : Nat → Real)
    (hstep : 0 ≤ step) (hL : 0 ≤ L)
    (hdefect : ∀ j, 0 ≤ defect j)
    (hkinetic : IsKineticEulerTrajectory V step Q)
    (hresidual : ∀ j,
      MomentKineticEulerResidual
        (E j) (E (j + 1)) step (Q (E j)) (defect j))
    (hQ : ∀ x y, |Q x - Q y| ≤ L * |x - y|)
    (K : Nat) :
    |E K - V K| ≤
      (|E 0 - V 0| + ∑ j ∈ Finset.range K, defect j) *
        Real.exp (L * step * (K : Real)) := by
  apply discrete_affine_error_exp_bound
      (e := fun j ↦ |E j - V j|) (defect := defect)
      (L := L) (h := step)
  · exact abs_nonneg _
  · exact hL
  · exact hstep
  · exact hdefect
  · exact fun j ↦ abs_microscopic_sub_kinetic_next_le
      E V Q step L defect hstep hkinetic hresidual hQ j

/-- Uniform-residual specialization of moment-level kinetic Euler shadowing. -/
theorem moment_kineticEuler_shadowing_uniform_bound
    (E V : Nat → Real) (Q : Real → Real)
    (step L defectMax : Real) (defect : Nat → Real)
    (hstep : 0 ≤ step) (hL : 0 ≤ L)
    (hdefect : ∀ j, 0 ≤ defect j)
    (hdefectMax : ∀ j, defect j ≤ defectMax)
    (hkinetic : IsKineticEulerTrajectory V step Q)
    (hresidual : ∀ j,
      MomentKineticEulerResidual
        (E j) (E (j + 1)) step (Q (E j)) (defect j))
    (hQ : ∀ x y, |Q x - Q y| ≤ L * |x - y|)
    (K : Nat) :
    |E K - V K| ≤
      (|E 0 - V 0| + (K : Real) * defectMax) *
        Real.exp (L * step * (K : Real)) := by
  apply discrete_affine_error_uniform_defect_bound
      (e := fun j ↦ |E j - V j|) (defect := defect)
      (L := L) (h := step) (defectMax := defectMax)
  · exact abs_nonneg _
  · exact hL
  · exact hstep
  · exact hdefect
  · exact hdefectMax
  · exact fun j ↦ abs_microscopic_sub_kinetic_next_le
      E V Q step L defect hstep hkinetic hresidual hQ j

/-- Kinetic-scale shadowing for a family of microscopic block dynamics.

`step n * K n ≤ tau` bounds the number of kinetic units,
`defectMax n / step n → 0` is the required little-o one-block consistency,
and `L n * step n * K n ≤ exponentBound` controls amplification. -/
theorem moment_kineticEuler_shadowing_tendsto_zero
    (E V : Nat → Nat → Real) (Q : Nat → Real → Real)
    (step L defectMax : Nat → Real) (defect : Nat → Nat → Real)
    (K : Nat → Nat) (tau exponentBound : Real)
    (hstep : ∀ n, 0 < step n)
    (hL : ∀ n, 0 ≤ L n)
    (hdefect : ∀ n j, 0 ≤ defect n j)
    (hdefectMax : ∀ n j, defect n j ≤ defectMax n)
    (hkinetic : ∀ n, IsKineticEulerTrajectory (V n) (step n) (Q n))
    (hresidual : ∀ n j,
      MomentKineticEulerResidual
        (E n j) (E n (j + 1)) (step n) (Q n (E n j)) (defect n j))
    (hQ : ∀ n x y, |Q n x - Q n y| ≤ L n * |x - y|)
    (hkineticBudget : ∀ n,
      step n * (K n : Real) ≤ tau)
    (hexponentBound : ∀ n,
      L n * step n * (K n : Real) ≤ exponentBound)
    (hinitial : Tendsto (fun n ↦ |E n 0 - V n 0|) atTop (nhds 0))
    (hdefectRatio : Tendsto
      (fun n ↦ defectMax n / step n) atTop (nhds 0)) :
    Tendsto (fun n ↦ |E n (K n) - V n (K n)|) atTop (nhds 0) := by
  have hdefectMax0 : ∀ n, 0 ≤ defectMax n := by
    intro n
    exact (hdefect n 0).trans (hdefectMax n 0)
  have hcumulative : Tendsto
      (fun n ↦ (K n : Real) * defectMax n) atTop (nhds 0) :=
    cumulative_block_defect_tendsto_zero
      K step defectMax tau hstep hdefectMax0 hkineticBudget hdefectRatio
  have hprefix : Tendsto
      (fun n ↦ |E n 0 - V n 0| + (K n : Real) * defectMax n)
      atTop (nhds 0) := by
    simpa using hinitial.add hcumulative
  apply squeeze_zero
  · intro n
    exact abs_nonneg _
  · intro n
    have hbase := moment_kineticEuler_shadowing_uniform_bound
      (E n) (V n) (Q n) (step n) (L n) (defectMax n) (defect n)
      (hstep n).le (hL n) (hdefect n) (hdefectMax n)
      (hkinetic n) (hresidual n) (hQ n) (K n)
    have hprefixNonneg :
        0 ≤ |E n 0 - V n 0| + (K n : Real) * defectMax n := by
      exact add_nonneg (abs_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (hdefectMax0 n))
    exact hbase.trans
      (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (hexponentBound n)) hprefixNonneg)
  · simpa using hprefix.mul (tendsto_const_nhds :
      Tendsto (fun _ : Nat ↦ Real.exp exponentBound) atTop
        (nhds (Real.exp exponentBound)))

/-! ## Adapter for the actual one-block FPUT theorem -/

/-- The actual Haar-averaged modal energy used at the two endpoints of one
Hamiltonian block. -/
def actualHaarModalMoment
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (p q : UnitAddTorus (Lattice.Site N) → Time → HilbertConfiguration N)
    (time : Real) : Real :=
  ∫ phase : UnitAddTorus (Lattice.Site N),
    actualPhaseModalNormSq m observed p q time phase
      ∂finitePhaseHaarLaw (Lattice.Site N)

/-- The explicit sharp energy-window defect on the right-hand side of the
actual Hamiltonian one-block consistency theorem. -/
def actualOneBlockSharpKineticDefect
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper kappa beta g H : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (T : Real) : Real :=
  g ^ 2 *
      (|g| * physlibHaarEnergyDriftC3 m kappa beta
          (phaseEnergyRadius energy (modeFrequency m)) T observed +
        g ^ 2 * physlibHaarEnergyDriftC4 m kappa beta
          (phaseEnergyRadius energy (modeFrequency m)) T observed) +
    physlibHaarSharpEnergyCorrectionEnvelope m mUpper kappa beta g H
      (phaseEnergyRadius energy (modeFrequency m)) T observed

/-- The committed actual FPUT one-block theorem has exactly the residual
shape consumed by the shadowing theorem.  This adapter makes no claim that a
later block starts from a fresh Haar law; a multiblock application must supply
the residual separately at every block. -/
theorem actualFPUT_oneBlock_is_momentKineticEulerResidual
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
    MomentKineticEulerResidual
      (actualHaarModalMoment m observed p q 0)
      (actualHaarModalMoment m observed p q T)
      (g ^ 2 * T)
      (normalizedSecondOrderHaarBroadening
        m kappa beta energy observed T)
      (actualOneBlockSharpKineticDefect
        m mUpper kappa beta g H energy observed T) := by
  exact abs_actual_Haar_drift_sub_finiteTimeKineticStep_le_sharpEnergyWindow
    m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton energy
      homega hinitial hT hgauge henergyWindow hzeroHistory hmeasurable

end

end ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing
