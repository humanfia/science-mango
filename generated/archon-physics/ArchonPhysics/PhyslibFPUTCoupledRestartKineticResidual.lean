import ArchonPhysics.PhyslibFPUTCouplingMultiblockRestart
import ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing

/-!
# Coupled RPA restarts imply kinetic residuals

This module supplies the deterministic bridge from an approximate common-source
RPA coupling to the scalar residual used by kinetic Euler shadowing.  Suppose a
reference block has residual `r`, while the actual and reference moments differ
by at most `eta0` and `eta1` at the two endpoints.  If the collision field is
`L`-Lipschitz, then the actual block has residual

`r + eta1 + (1 + step * L) * eta0`.

For the coupling certificate already used by the multiblock restart theorem,
the endpoint errors are explicitly

`2 * M * delta + 2 * M ^ 2 * failureProbability`

for the second moment, and the analogous fourth-moment expression.  Thus an
exact re-Haarization is not needed for this implication: it is enough that the
displayed coupling defects are little-o of the kinetic step.  The existence of
the coupling certificate and the reference-block kinetic residual remain
transparent hypotheses.
-/

namespace ArchonPhysics.PhyslibFPUTCoupledRestartKineticResidual

open Filter
open MeasureTheory
open Topology
open ArchonPhysics.PhyslibFPUTCouplingMultiblockRestart
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing

noncomputable section

/-! ## Scalar endpoint stability -/

/-- Total kinetic residual obtained from a reference residual and errors at
the initial and final endpoints. -/
def endpointCoupledKineticResidualDefect
    (step L referenceDefect initialEndpointDefect finalEndpointDefect : Real) :
    Real :=
  referenceDefect + finalEndpointDefect +
    (1 + step * L) * initialEndpointDefect

/-- A reference Euler residual is stable under errors at both block endpoints.
The initial error enters twice: directly in the increment and through the
Lipschitz collision field. -/
theorem momentKineticEulerResidual_of_reference_endpoint_control
    (actualInitial actualFinal referenceInitial referenceFinal : Real)
    (Q : Real → Real)
    {step L referenceDefect initialEndpointDefect finalEndpointDefect : Real}
    (hstep : 0 ≤ step) (hL : 0 ≤ L)
    (hreference : MomentKineticEulerResidual
      referenceInitial referenceFinal step (Q referenceInitial)
        referenceDefect)
    (hinitial : |actualInitial - referenceInitial| ≤ initialEndpointDefect)
    (hfinal : |actualFinal - referenceFinal| ≤ finalEndpointDefect)
    (hQ : ∀ x y, |Q x - Q y| ≤ L * |x - y|) :
    MomentKineticEulerResidual
      actualInitial actualFinal step (Q actualInitial)
        (endpointCoupledKineticResidualDefect step L referenceDefect
          initialEndpointDefect finalEndpointDefect) := by
  have hQinitial :
      |Q referenceInitial - Q actualInitial| ≤ L * initialEndpointDefect := by
    calc
      |Q referenceInitial - Q actualInitial| ≤
          L * |referenceInitial - actualInitial| :=
        hQ referenceInitial actualInitial
      _ = L * |actualInitial - referenceInitial| := by
        rw [abs_sub_comm referenceInitial actualInitial]
      _ ≤ L * initialEndpointDefect :=
        mul_le_mul_of_nonneg_left hinitial hL
  have hcollision :
      |step * (Q referenceInitial - Q actualInitial)| ≤
        step * (L * initialEndpointDefect) := by
    rw [abs_mul, abs_of_nonneg hstep]
    exact mul_le_mul_of_nonneg_left hQinitial hstep
  have hidentity :
      actualFinal - actualInitial - step * Q actualInitial =
        (referenceFinal - referenceInitial - step * Q referenceInitial) +
          ((actualFinal - referenceFinal) +
            ((referenceInitial - actualInitial) +
              step * (Q referenceInitial - Q actualInitial))) := by
    ring
  unfold MomentKineticEulerResidual at hreference ⊢
  rw [hidentity]
  calc
    |(referenceFinal - referenceInitial - step * Q referenceInitial) +
        ((actualFinal - referenceFinal) +
          ((referenceInitial - actualInitial) +
            step * (Q referenceInitial - Q actualInitial)))| ≤
        |referenceFinal - referenceInitial - step * Q referenceInitial| +
          |(actualFinal - referenceFinal) +
            ((referenceInitial - actualInitial) +
              step * (Q referenceInitial - Q actualInitial))| :=
      abs_add_le _ _
    _ ≤ |referenceFinal - referenceInitial - step * Q referenceInitial| +
          (|actualFinal - referenceFinal| +
            |(referenceInitial - actualInitial) +
              step * (Q referenceInitial - Q actualInitial)|) := by
      gcongr
      exact abs_add_le _ _
    _ ≤ |referenceFinal - referenceInitial - step * Q referenceInitial| +
          (|actualFinal - referenceFinal| +
            (|referenceInitial - actualInitial| +
              |step * (Q referenceInitial - Q actualInitial)|)) := by
      gcongr
      exact abs_add_le _ _
    _ ≤ referenceDefect +
          (finalEndpointDefect +
            (initialEndpointDefect + step * (L * initialEndpointDefect))) := by
      exact add_le_add hreference
        (add_le_add hfinal
          (add_le_add (by simpa only [abs_sub_comm] using hinitial)
            hcollision))
    _ = endpointCoupledKineticResidualDefect step L referenceDefect
          initialEndpointDefect finalEndpointDefect := by
      unfold endpointCoupledKineticResidualDefect
      ring

/-! ## Moment endpoints supplied by a common-source coupling -/

/-- Actual second moment at restart endpoint `j`. -/
def coupledActualSecondMoment
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {M : Real}
    (certificate : AmplitudeCouplingRestartCertificate mu M) (j : Nat) : Real :=
  ∫ z, Complex.normSq z ∂certificate.actualLaw j

/-- Reference second moment at restart endpoint `j`. -/
def coupledReferenceSecondMoment
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {M : Real}
    (certificate : AmplitudeCouplingRestartCertificate mu M) (j : Nat) : Real :=
  ∫ z, Complex.normSq z ∂certificate.referenceLaw j

/-- Actual fourth moment at restart endpoint `j`. -/
def coupledActualFourthMoment
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {M : Real}
    (certificate : AmplitudeCouplingRestartCertificate mu M) (j : Nat) : Real :=
  ∫ z, Complex.normSq z ^ 2 ∂certificate.actualLaw j

/-- Reference fourth moment at restart endpoint `j`. -/
def coupledReferenceFourthMoment
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {M : Real}
    (certificate : AmplitudeCouplingRestartCertificate mu M) (j : Nat) : Real :=
  ∫ z, Complex.normSq z ^ 2 ∂certificate.referenceLaw j

/-- A reference second-moment block residual and the coupling certificate give
an actual second-moment residual with explicit `delta`, `p`, and `M` costs at
both endpoints. -/
theorem coupled_secondMoment_is_momentKineticEulerResidual
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {M : Real} (hM : 0 ≤ M)
    (certificate : AmplitudeCouplingRestartCertificate mu M)
    (Q : Real → Real) {step L referenceDefect : Real}
    (hstep : 0 ≤ step) (hL : 0 ≤ L)
    (j : Nat)
    (hreference : MomentKineticEulerResidual
      (coupledReferenceSecondMoment certificate j)
      (coupledReferenceSecondMoment certificate (j + 1))
      step (Q (coupledReferenceSecondMoment certificate j)) referenceDefect)
    (hQ : ∀ x y, |Q x - Q y| ≤ L * |x - y|) :
    MomentKineticEulerResidual
      (coupledActualSecondMoment certificate j)
      (coupledActualSecondMoment certificate (j + 1))
      step (Q (coupledActualSecondMoment certificate j))
      (endpointCoupledKineticResidualDefect step L referenceDefect
        (couplingSecondMomentDefect M (certificate.delta j)
          (certificate.failureProbability j))
        (couplingSecondMomentDefect M (certificate.delta (j + 1))
          (certificate.failureProbability (j + 1)))) := by
  have hinitial :=
    (certificate_pushforward_second_fourth_moment_errors
      mu hM certificate j).1
  have hfinal :=
    (certificate_pushforward_second_fourth_moment_errors
      mu hM certificate (j + 1)).1
  exact momentKineticEulerResidual_of_reference_endpoint_control
    (coupledActualSecondMoment certificate j)
    (coupledActualSecondMoment certificate (j + 1))
    (coupledReferenceSecondMoment certificate j)
    (coupledReferenceSecondMoment certificate (j + 1))
    Q hstep hL hreference
    (by simpa [coupledActualSecondMoment, coupledReferenceSecondMoment] using hinitial)
    (by simpa [coupledActualSecondMoment, coupledReferenceSecondMoment] using hfinal)
    hQ

/-- Fourth-moment analogue of
`coupled_secondMoment_is_momentKineticEulerResidual`. -/
theorem coupled_fourthMoment_is_momentKineticEulerResidual
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {M : Real} (hM : 0 ≤ M)
    (certificate : AmplitudeCouplingRestartCertificate mu M)
    (Q : Real → Real) {step L referenceDefect : Real}
    (hstep : 0 ≤ step) (hL : 0 ≤ L)
    (j : Nat)
    (hreference : MomentKineticEulerResidual
      (coupledReferenceFourthMoment certificate j)
      (coupledReferenceFourthMoment certificate (j + 1))
      step (Q (coupledReferenceFourthMoment certificate j)) referenceDefect)
    (hQ : ∀ x y, |Q x - Q y| ≤ L * |x - y|) :
    MomentKineticEulerResidual
      (coupledActualFourthMoment certificate j)
      (coupledActualFourthMoment certificate (j + 1))
      step (Q (coupledActualFourthMoment certificate j))
      (endpointCoupledKineticResidualDefect step L referenceDefect
        (couplingFourthMomentDefect M (certificate.delta j)
          (certificate.failureProbability j))
        (couplingFourthMomentDefect M (certificate.delta (j + 1))
          (certificate.failureProbability (j + 1)))) := by
  have hinitial :=
    (certificate_pushforward_second_fourth_moment_errors
      mu hM certificate j).2
  have hfinal :=
    (certificate_pushforward_second_fourth_moment_errors
      mu hM certificate (j + 1)).2
  exact momentKineticEulerResidual_of_reference_endpoint_control
    (coupledActualFourthMoment certificate j)
    (coupledActualFourthMoment certificate (j + 1))
    (coupledReferenceFourthMoment certificate j)
    (coupledReferenceFourthMoment certificate (j + 1))
    Q hstep hL hreference
    (by simpa [coupledActualFourthMoment, coupledReferenceFourthMoment] using hinitial)
    (by simpa [coupledActualFourthMoment, coupledReferenceFourthMoment] using hfinal)
    hQ

/-! ## Kinetic-scale little-o closure -/

/-- If the reference residual and both endpoint coupling errors are little-o
of the kinetic step, then so is the transferred actual residual.  A finite
limit of `step * L` is enough to control the Lipschitz amplification. -/
theorem endpointCoupledKineticResidualDefect_ratio_tendsto_zero
    (step L referenceDefect initialEndpointDefect finalEndpointDefect :
      Nat → Real)
    (c : Real)
    (hstep : ∀ n, 0 < step n)
    (hreference : Tendsto
      (fun n ↦ referenceDefect n / step n) atTop (nhds 0))
    (hinitial : Tendsto
      (fun n ↦ initialEndpointDefect n / step n) atTop (nhds 0))
    (hfinal : Tendsto
      (fun n ↦ finalEndpointDefect n / step n) atTop (nhds 0))
    (hstepL : Tendsto (fun n ↦ step n * L n) atTop (nhds c)) :
    Tendsto
      (fun n ↦ endpointCoupledKineticResidualDefect
        (step n) (L n) (referenceDefect n)
          (initialEndpointDefect n) (finalEndpointDefect n) / step n)
      atTop (nhds 0) := by
  have hfactor : Tendsto (fun n ↦ 1 + step n * L n)
      atTop (nhds (1 + c)) :=
    tendsto_const_nhds.add hstepL
  have hsum : Tendsto
      (fun n ↦ referenceDefect n / step n +
        finalEndpointDefect n / step n +
        (1 + step n * L n) * (initialEndpointDefect n / step n))
      atTop (nhds 0) := by
    simpa using (hreference.add hfinal).add (hfactor.mul hinitial)
  apply hsum.congr'
  filter_upwards with n
  have hstepNe : step n ≠ 0 := ne_of_gt (hstep n)
  unfold endpointCoupledKineticResidualDefect
  field_simp

/-- Explicit second-moment specialization: the common-source coupling costs
`2 M delta + 2 M^2 p` need only be little-o of the block step. -/
theorem couplingSecondMomentResidualDefect_ratio_tendsto_zero
    (M delta0 p0 delta1 p1 step L referenceDefect : Nat → Real)
    (c : Real)
    (hstep : ∀ n, 0 < step n)
    (hreference : Tendsto
      (fun n ↦ referenceDefect n / step n) atTop (nhds 0))
    (hinitial : Tendsto
      (fun n ↦ couplingSecondMomentDefect (M n) (delta0 n) (p0 n) /
        step n) atTop (nhds 0))
    (hfinal : Tendsto
      (fun n ↦ couplingSecondMomentDefect (M n) (delta1 n) (p1 n) /
        step n) atTop (nhds 0))
    (hstepL : Tendsto (fun n ↦ step n * L n) atTop (nhds c)) :
    Tendsto
      (fun n ↦ endpointCoupledKineticResidualDefect
        (step n) (L n) (referenceDefect n)
          (2 * M n * delta0 n + 2 * (M n) ^ 2 * p0 n)
          (2 * M n * delta1 n + 2 * (M n) ^ 2 * p1 n) / step n)
      atTop (nhds 0) := by
  simpa [couplingSecondMomentDefect] using
    endpointCoupledKineticResidualDefect_ratio_tendsto_zero
      step L referenceDefect
      (fun n ↦ couplingSecondMomentDefect (M n) (delta0 n) (p0 n))
      (fun n ↦ couplingSecondMomentDefect (M n) (delta1 n) (p1 n))
      c hstep hreference hinitial hfinal hstepL

end

end ArchonPhysics.PhyslibFPUTCoupledRestartKineticResidual
