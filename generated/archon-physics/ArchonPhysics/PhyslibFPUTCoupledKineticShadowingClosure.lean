import ArchonPhysics.PhyslibFPUTCoupledRestartKineticResidual

/-!
# Coupled-restart closure of FPUT kinetic-time moment shadowing

Fix a finite lattice and one observed mode.  This module closes the remaining
deterministic composition between two existing interfaces:

* a reference block has a kinetic Euler residual; and
* an `AmplitudeCouplingRestartCertificate` controls the actual/reference
  amplitudes at every block endpoint.

The actual residual is not assumed.  It is derived block by block from the
reference residual and the two explicit second-moment coupling defects.  If
uniform envelopes for those two inputs are `o(step)`, the resulting actual
second moments shadow the kinetic Euler trajectory for `O(1)` kinetic time.

The transparent probabilistic input is the existence of the common-source
couplings together with the reference-block residuals.  No statement here
constructs those couplings from the nonlinear Hamiltonian flow.
-/

namespace ArchonPhysics.PhyslibFPUTCoupledKineticShadowingClosure

open Filter
open MeasureTheory
open Topology
open ArchonPhysics.PhyslibFPUTCouplingMultiblockRestart
open ArchonPhysics.PhyslibFPUTCoupledRestartKineticResidual
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing

noncomputable section

/-! ## Minimal fixed-volume family certificate -/

/-- The data needed to transfer a family of reference kinetic residuals to
actual second moments.  The asymptotic index `n` changes the weak-coupling
scale, while the physical volume and observed mode have already been fixed.

The two displayed maxima are genuine uniform envelopes over all restart
blocks.  Nonnegativity is intentionally not stored: it follows from the
residual/coupling bounds at block zero. -/
structure CoupledSecondMomentKineticFamilyCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (M : Real)
    (step : Nat → Real) (Q : Real → Real)
    (referenceDefectMax couplingDefectMax : Nat → Real) where
  coupling : Nat → AmplitudeCouplingRestartCertificate mu M
  referenceDefect : Nat → Nat → Real
  reference_residual : ∀ n j,
    MomentKineticEulerResidual
      (coupledReferenceSecondMoment (coupling n) j)
      (coupledReferenceSecondMoment (coupling n) (j + 1))
      (step n) (Q (coupledReferenceSecondMoment (coupling n) j))
      (referenceDefect n j)
  reference_defect_le : ∀ n j,
    referenceDefect n j ≤ referenceDefectMax n
  coupling_endpoint_defect_le : ∀ n j,
    couplingSecondMomentDefect M
      ((coupling n).delta j) ((coupling n).failureProbability j) ≤
        couplingDefectMax n

namespace CoupledSecondMomentKineticFamilyCertificate

variable {Omega : Type*} [MeasurableSpace Omega]
  {mu : Measure Omega} {M : Real}
  {step : Nat → Real} {Q : Real → Real}
  {referenceDefectMax couplingDefectMax : Nat → Real}

/-- Actual modal second moment at block endpoint `j` in family member `n`. -/
def actualSecondMoment
    (family : CoupledSecondMomentKineticFamilyCertificate
      mu M step Q referenceDefectMax couplingDefectMax)
    (n j : Nat) : Real :=
  coupledActualSecondMoment (family.coupling n) j

/-- The blockwise actual residual produced by endpoint coupling stability. -/
def actualResidualDefect
    (family : CoupledSecondMomentKineticFamilyCertificate
      mu M step Q referenceDefectMax couplingDefectMax)
    (L : Real) (n j : Nat) : Real :=
  endpointCoupledKineticResidualDefect
    (step n) L (family.referenceDefect n j)
    (couplingSecondMomentDefect M
      ((family.coupling n).delta j)
      ((family.coupling n).failureProbability j))
    (couplingSecondMomentDefect M
      ((family.coupling n).delta (j + 1))
      ((family.coupling n).failureProbability (j + 1)))

/-- Uniform actual-residual envelope obtained from the two uniform input
envelopes. -/
def actualResidualDefectMax
    (_family : CoupledSecondMomentKineticFamilyCertificate
      mu M step Q referenceDefectMax couplingDefectMax)
    (L : Real) (n : Nat) : Real :=
  endpointCoupledKineticResidualDefect
    (step n) L (referenceDefectMax n)
      (couplingDefectMax n) (couplingDefectMax n)

/-- A certified reference residual is necessarily nonnegative. -/
theorem referenceDefect_nonneg
    (family : CoupledSecondMomentKineticFamilyCertificate
      mu M step Q referenceDefectMax couplingDefectMax)
    (n j : Nat) :
    0 ≤ family.referenceDefect n j := by
  exact (abs_nonneg _).trans (family.reference_residual n j)

/-- The uniform reference envelope is nonnegative without a redundant
certificate field. -/
theorem referenceDefectMax_nonneg
    (family : CoupledSecondMomentKineticFamilyCertificate
      mu M step Q referenceDefectMax couplingDefectMax)
    (n : Nat) :
    0 ≤ referenceDefectMax n :=
  (family.referenceDefect_nonneg n 0).trans
    (family.reference_defect_le n 0)

/-- The uniform second-moment coupling envelope is nonnegative without a
redundant certificate field. -/
theorem couplingDefectMax_nonneg
    (hM : 0 ≤ M)
    (family : CoupledSecondMomentKineticFamilyCertificate
      mu M step Q referenceDefectMax couplingDefectMax)
    (n : Nat) :
    0 ≤ couplingDefectMax n := by
  have hcoupling : 0 ≤ couplingSecondMomentDefect M
      ((family.coupling n).delta 0)
      ((family.coupling n).failureProbability 0) :=
    couplingSecondMomentDefect_nonneg hM
      ((family.coupling n).delta_nonneg 0)
      ((family.coupling n).failureProbability_nonneg 0)
  exact hcoupling.trans (family.coupling_endpoint_defect_le n 0)

/-- The actual residual is derived from the reference residual and the two
endpoint coupling estimates; it is not a field of the family certificate. -/
theorem actualSecondMoment_is_momentKineticEulerResidual
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (hM : 0 ≤ M)
    (family : CoupledSecondMomentKineticFamilyCertificate
      mu M step Q referenceDefectMax couplingDefectMax)
    {L : Real} (hL : 0 ≤ L)
    (hstep : ∀ n, 0 ≤ step n)
    (hQ : ∀ x y, |Q x - Q y| ≤ L * |x - y|)
    (n j : Nat) :
    MomentKineticEulerResidual
      (family.actualSecondMoment n j)
      (family.actualSecondMoment n (j + 1))
      (step n) (Q (family.actualSecondMoment n j))
      (family.actualResidualDefect L n j) := by
  exact coupled_secondMoment_is_momentKineticEulerResidual
    mu hM (family.coupling n) Q (hstep n) hL j
      (family.reference_residual n j) hQ

/-- Every derived actual residual is nonnegative. -/
theorem actualResidualDefect_nonneg
    (hM : 0 ≤ M)
    (family : CoupledSecondMomentKineticFamilyCertificate
      mu M step Q referenceDefectMax couplingDefectMax)
    {L : Real} (hL : 0 ≤ L)
    (hstep : ∀ n, 0 ≤ step n)
    (n j : Nat) :
    0 ≤ family.actualResidualDefect L n j := by
  unfold actualResidualDefect endpointCoupledKineticResidualDefect
  have hreference := family.referenceDefect_nonneg n j
  have hinitial := couplingSecondMomentDefect_nonneg hM
    ((family.coupling n).delta_nonneg j)
    ((family.coupling n).failureProbability_nonneg j)
  have hfinal := couplingSecondMomentDefect_nonneg hM
    ((family.coupling n).delta_nonneg (j + 1))
    ((family.coupling n).failureProbability_nonneg (j + 1))
  have hfactor : 0 ≤ 1 + step n * L :=
    add_nonneg zero_le_one (mul_nonneg (hstep n) hL)
  exact add_nonneg (add_nonneg hreference hfinal)
    (mul_nonneg hfactor hinitial)

/-- The derived residual is bounded by the uniform transferred envelope. -/
theorem actualResidualDefect_le_max
    (family : CoupledSecondMomentKineticFamilyCertificate
      mu M step Q referenceDefectMax couplingDefectMax)
    {L : Real} (hL : 0 ≤ L)
    (hstep : ∀ n, 0 ≤ step n)
    (n j : Nat) :
    family.actualResidualDefect L n j ≤
      family.actualResidualDefectMax L n := by
  unfold actualResidualDefect actualResidualDefectMax
    endpointCoupledKineticResidualDefect
  have hfactor : 0 ≤ 1 + step n * L :=
    add_nonneg zero_le_one (mul_nonneg (hstep n) hL)
  gcongr
  · exact family.reference_defect_le n j
  · exact family.coupling_endpoint_defect_le n (j + 1)
  · exact family.coupling_endpoint_defect_le n j

/-- The uniform transferred envelope is nonnegative. -/
theorem actualResidualDefectMax_nonneg
    (hM : 0 ≤ M)
    (family : CoupledSecondMomentKineticFamilyCertificate
      mu M step Q referenceDefectMax couplingDefectMax)
    {L : Real} (hL : 0 ≤ L)
    (hstep : ∀ n, 0 ≤ step n)
    (n : Nat) :
    0 ≤ family.actualResidualDefectMax L n := by
  exact (family.actualResidualDefect_nonneg hM hL hstep n 0).trans
    (family.actualResidualDefect_le_max hL hstep n 0)

/-! ## Kinetic-time closure -/

/-- At fixed finite volume, uniformly little-o reference residuals and
second-moment endpoint coupling errors imply kinetic-time shadowing of the
actual second moments.

`step n → 0` is the weak-coupling block limit.  It also controls the harmless
factor `1 + step n * L` in the endpoint transfer.  The actual block residual
and its little-o estimate are both conclusions of this theorem's proof. -/
theorem actualSecondMoment_kineticEuler_shadowing_tendsto_zero
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {M : Real} (hM : 0 ≤ M)
    (step : Nat → Real) (Q : Real → Real) (L : Real)
    (referenceDefectMax couplingDefectMax : Nat → Real)
    (family : CoupledSecondMomentKineticFamilyCertificate
      mu M step Q referenceDefectMax couplingDefectMax)
    (V : Nat → Nat → Real) (K : Nat → Nat) (tau : Real)
    (hstep : ∀ n, 0 < step n)
    (hstep0 : Tendsto step atTop (nhds 0))
    (hL : 0 ≤ L)
    (hQ : ∀ x y, |Q x - Q y| ≤ L * |x - y|)
    (hkinetic : ∀ n,
      IsKineticEulerTrajectory (V n) (step n) Q)
    (hkineticBudget : ∀ n,
      step n * (K n : Real) ≤ tau)
    (hinitial : Tendsto
      (fun n ↦ |family.actualSecondMoment n 0 - V n 0|)
      atTop (nhds 0))
    (hreferenceRatio : Tendsto
      (fun n ↦ referenceDefectMax n / step n) atTop (nhds 0))
    (hcouplingRatio : Tendsto
      (fun n ↦ couplingDefectMax n / step n) atTop (nhds 0)) :
    Tendsto
      (fun n ↦ |family.actualSecondMoment n (K n) - V n (K n)|)
      atTop (nhds 0) := by
  have hstepNonneg : ∀ n, 0 ≤ step n := fun n ↦ (hstep n).le
  have hstepL : Tendsto (fun n ↦ step n * L) atTop (nhds 0) := by
    simpa using hstep0.mul_const L
  have hactualRatio : Tendsto
      (fun n ↦ family.actualResidualDefectMax L n / step n)
      atTop (nhds 0) := by
    simpa only [actualResidualDefectMax] using
      endpointCoupledKineticResidualDefect_ratio_tendsto_zero
        step (fun _ ↦ L) referenceDefectMax couplingDefectMax
          couplingDefectMax 0 hstep hreferenceRatio hcouplingRatio
          hcouplingRatio (by simpa using hstepL)
  have hexponent : ∀ n,
      L * step n * (K n : Real) ≤ L * tau := by
    intro n
    calc
      L * step n * (K n : Real) =
          L * (step n * (K n : Real)) := by ring
      _ ≤ L * tau := mul_le_mul_of_nonneg_left
        (hkineticBudget n) hL
  exact moment_kineticEuler_shadowing_tendsto_zero
    family.actualSecondMoment V (fun _ ↦ Q) step (fun _ ↦ L)
      (family.actualResidualDefectMax L) (family.actualResidualDefect L)
      K tau (L * tau) hstep (fun _ ↦ hL)
      (family.actualResidualDefect_nonneg hM hL hstepNonneg)
      (family.actualResidualDefect_le_max hL hstepNonneg)
      hkinetic
      (family.actualSecondMoment_is_momentKineticEulerResidual
        mu hM hL hstepNonneg hQ)
      (fun _ ↦ hQ) hkineticBudget hexponent hinitial hactualRatio

end CoupledSecondMomentKineticFamilyCertificate

end

end ArchonPhysics.PhyslibFPUTCoupledKineticShadowingClosure
