import ArchonPhysics.PhyslibFPUTActualOneBlockKineticLittleO
import ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing

/-!
# Closing the fixed-volume FPUT little-o/Euler shadowing chain

This module combines two previously separate results:

* the actual one-block cubic-Lipschitz estimate supplies an explicit
  `o(g^2 T)` residual; and
* moment-level discrete Gronwall shadowing accumulates such residuals over a
  bounded kinetic time interval.

The only deliberately transparent input is
`FPUTAllBlockRestartHaarCertificate`.  It says that every restarted
Hamiltonian block has the Haar one-block residual furnished by the local
theorem.  In particular, the final convergence theorem does **not** assume a
little-o ratio: that ratio is derived below from the explicit microscopic
right-hand side.
-/

namespace ArchonPhysics.PhyslibFPUTKineticLittleOShadowingClosure

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
open ArchonPhysics.PhyslibFPUTActualOneBlockKineticLittleO
open ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing
open ArchonPhysics.PhyslibFPUTRenormalizedHaarMomentDefect
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibFPUTSharpRemainderEnergyWindow
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.QuadraticTensorHistoryExpansion
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-! ## The improved actual one-block adapter -/

/-- The cubic-Lipschitz actual Hamiltonian theorem supplies the same scalar
residual interface used by kinetic Euler shadowing, now with the explicit
little-o right-hand side.  This is the sharp replacement for the older
`actualOneBlockSharpKineticDefect` adapter. -/
theorem actualFPUT_oneBlock_is_momentKineticEulerResidual_cubicLittleO
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
      (physlibFPUTKineticLittleORhs m mUpper kappa beta H
        (phaseEnergyRadius energy (modeFrequency m)) T observed g) := by
  simpa only [MomentKineticEulerResidual, actualHaarModalMoment] using
    abs_actual_Haar_drift_sub_finiteTimeKineticStep_le_cubicLittleORhs
      m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton energy
        homega hinitial hT hgauge henergyWindow hzeroHistory hmeasurable

/-! ## The unique multiblock input -/

/-- The transparent hypothesis still missing from the first-principles
Hamiltonian argument: after every restart, the microscopic modal moment has a
nonnegative residual bounded by the actual Haar one-block little-o envelope.

The one-block adapter above constructs an individual `residual` field.  What
is not constructed here is a coupling/restart theorem that regenerates its
Haar hypotheses simultaneously for all kinetic blocks. -/
structure FPUTAllBlockRestartHaarCertificate
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper kappa beta H : Real)
    (radius : Lattice.Site N → Real) (T : Real)
    (observed : Lattice.Site N)
    (g : Nat → Real) (E : Nat → Nat → Real)
    (Q : Real → Real) where
  defect : Nat → Nat → Real
  defect_nonneg : ∀ n j, 0 ≤ defect n j
  residual : ∀ n j,
    MomentKineticEulerResidual
      (E n j) (E n (j + 1)) (g n ^ 2 * T) (Q (E n j)) (defect n j)
  defect_le_cubicLittleORhs : ∀ n j,
    defect n j ≤
      physlibFPUTKineticLittleORhs m mUpper kappa beta H
        radius T observed (g n)

namespace FPUTAllBlockRestartHaarCertificate

/-- The common explicit one-block envelope used as `defectMax`. -/
def defectMax
    {N : Nat} [NeZero N]
    {m : Lattice.PositiveMassConfig N}
    {mUpper kappa beta H : Real}
    {radius : Lattice.Site N → Real} {T : Real}
    {observed : Lattice.Site N}
    {g : Nat → Real} {E : Nat → Nat → Real}
    {Q : Real → Real}
    (_certificate : FPUTAllBlockRestartHaarCertificate
      m mUpper kappa beta H radius T observed g E Q)
    (n : Nat) : Real :=
  physlibFPUTKineticLittleORhs m mUpper kappa beta H
    radius T observed (g n)

/-- Nonnegativity of the explicit envelope is not separately assumed: it
follows from any certified block residual (use block zero). -/
theorem defectMax_nonneg
    {N : Nat} [NeZero N]
    {m : Lattice.PositiveMassConfig N}
    {mUpper kappa beta H : Real}
    {radius : Lattice.Site N → Real} {T : Real}
    {observed : Lattice.Site N}
    {g : Nat → Real} {E : Nat → Nat → Real}
    {Q : Real → Real}
    (certificate : FPUTAllBlockRestartHaarCertificate
      m mUpper kappa beta H radius T observed g E Q)
    (n : Nat) :
    0 ≤ certificate.defectMax n := by
  exact (certificate.defect_nonneg n 0).trans
    (certificate.defect_le_cubicLittleORhs n 0)

end FPUTAllBlockRestartHaarCertificate

/-! ## Fixed-volume kinetic-time closure -/

/-- At fixed finite volume and fixed positive block length, the actual
cubic-Lipschitz one-block bound and moment Euler shadowing close to a
vanishing kinetic-time error.

Crucially, there is no `defectMax / step → 0` hypothesis.  It is derived
inside the proof from
`physlibFPUTKineticLittleORhs_sequence_div_kineticScale_tendsto_zero`.
Only eventual nonvanishing of `g` is needed; arbitrary finitely many zero
couplings do not affect the limit. -/
theorem actualFPUT_moment_kineticEuler_shadowing_tendsto_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper kappa beta H : Real)
    (radius : Lattice.Site N → Real) {T : Real} (hT : 0 < T)
    (observed : Lattice.Site N)
    (g : Nat → Real) (E V : Nat → Nat → Real)
    (Q : Real → Real) (L : Real) (K : Nat → Nat) (tau : Real)
    (certificate : FPUTAllBlockRestartHaarCertificate
      m mUpper kappa beta H radius T observed g E Q)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : ∀ᶠ n in atTop, g n ≠ 0)
    (hL : 0 ≤ L)
    (hkinetic : ∀ n,
      IsKineticEulerTrajectory (V n) (g n ^ 2 * T) Q)
    (hQ : ∀ x y, |Q x - Q y| ≤ L * |x - y|)
    (hkineticBudget : ∀ n,
      (g n ^ 2 * T) * (K n : Real) ≤ tau)
    (hinitial : Tendsto (fun n ↦ |E n 0 - V n 0|) atTop (nhds 0)) :
    Tendsto (fun n ↦ |E n (K n) - V n (K n)|) atTop (nhds 0) := by
  let step : Nat → Real := fun n ↦ g n ^ 2 * T
  let defectMax : Nat → Real := fun n ↦ certificate.defectMax n
  have hdefectMax0 : ∀ n, 0 ≤ defectMax n := by
    intro n
    exact certificate.defectMax_nonneg n
  have hstepPos : ∀ᶠ n in atTop, 0 < step n := by
    filter_upwards [hg0] with n hgn
    dsimp only [step]
    exact mul_pos (sq_pos_of_ne_zero hgn) hT
  have hdefectRatio : Tendsto
      (fun n ↦ defectMax n / step n) atTop (nhds 0) := by
    simpa only [defectMax, step,
      FPUTAllBlockRestartHaarCertificate.defectMax] using
      defectMax_div_kineticScale_tendsto_zero_of_le_littleORhs
        m mUpper kappa beta H radius hT observed g defectMax hg hg0
          (Filter.Eventually.of_forall hdefectMax0)
          (Filter.Eventually.of_forall (fun _ ↦ le_rfl))
  have hcumulative : Tendsto
      (fun n ↦ (K n : Real) * defectMax n) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall (fun n ↦
        mul_nonneg (Nat.cast_nonneg _) (hdefectMax0 n))
    · filter_upwards [hstepPos] with n hstepn
      have hratio0 : 0 ≤ defectMax n / step n :=
        div_nonneg (hdefectMax0 n) hstepn.le
      calc
        (K n : Real) * defectMax n =
            (step n * (K n : Real)) * (defectMax n / step n) := by
              field_simp [hstepn.ne']
        _ ≤ tau * (defectMax n / step n) :=
          mul_le_mul_of_nonneg_right (by
            simpa only [step] using hkineticBudget n) hratio0
    · simpa using (tendsto_const_nhds.mul hdefectRatio :
        Tendsto (fun n ↦ tau * (defectMax n / step n))
          atTop (nhds (tau * 0)))
  have hprefix : Tendsto
      (fun n ↦ |E n 0 - V n 0| + (K n : Real) * defectMax n)
      atTop (nhds 0) := by
    simpa using hinitial.add hcumulative
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun n ↦ abs_nonneg _)
  · filter_upwards [hstepPos] with n hstepn
    have hbase := moment_kineticEuler_shadowing_uniform_bound
      (E n) (V n) Q (step n) L (defectMax n) (certificate.defect n)
      hstepn.le hL (certificate.defect_nonneg n)
      (certificate.defect_le_cubicLittleORhs n)
      (by simpa only [step] using hkinetic n)
      (by simpa only [step] using certificate.residual n)
      hQ (K n)
    have hprefix0 :
        0 ≤ |E n 0 - V n 0| + (K n : Real) * defectMax n :=
      add_nonneg (abs_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (hdefectMax0 n))
    have hexponent :
        L * step n * (K n : Real) ≤ L * tau := by
      calc
        L * step n * (K n : Real) =
            L * (step n * (K n : Real)) := by ring
        _ ≤ L * tau := mul_le_mul_of_nonneg_left
          (by simpa only [step] using hkineticBudget n) hL
    exact hbase.trans
      (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hexponent) hprefix0)
  · simpa using hprefix.mul (tendsto_const_nhds :
      Tendsto (fun _ : Nat ↦ Real.exp (L * tau)) atTop
        (nhds (Real.exp (L * tau))))

end

end ArchonPhysics.PhyslibFPUTKineticLittleOShadowingClosure
