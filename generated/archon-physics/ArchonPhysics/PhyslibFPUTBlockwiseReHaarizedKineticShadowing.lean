import ArchonPhysics.PhyslibFPUTCubicDefectKineticShadowing

/-!
# Blockwise re-Haarized FPUT kinetic shadowing

This module removes an unnecessary coherence requirement from multiblock
restart arguments.  The actual moments form one coherent endpoint chain
`E n j`.  At each block `(n,j)`, however, the reference initial and final
moments are fresh data.  In particular, the final reference moment of block
`j` is not required to equal the initial reference moment of block `j+1`.

The certificate only asks that every independent reference block

* has an `O(|g|^3)` kinetic Euler residual, and
* is `O(|g|^3)`-coupled to the actual moment at each of its two endpoints.

The actual block residual is then a theorem, obtained from endpoint stability;
it is deliberately not a field of the certificate.  Since the kinetic step is
`g^2 T`, the derived residual is little-o of one step at fixed `T > 0`.
Consequently the coherent actual chain shadows the kinetic Euler trajectory
for a bounded kinetic time.

What remains transparent is precisely the probabilistic/dynamical existence
of the independent re-Haarized reference blocks and their endpoint couplings.
-/

namespace ArchonPhysics.PhyslibFPUTBlockwiseReHaarizedKineticShadowing

open Filter
open Topology
open ArchonPhysics.PhyslibFPUTCoupledRestartKineticResidual
open ArchonPhysics.PhyslibFPUTCubicDefectKineticShadowing
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing

noncomputable section

/-! ## Minimal blockwise certificate -/

/-- A family of independently re-Haarized reference blocks coupled to one
coherent actual moment chain.

There is intentionally no equation relating `referenceFinal n j` to
`referenceInitial n (j + 1)`.  Cross-block coherence belongs only to the
single actual chain `E`.  The uniform cubic envelopes are placed directly in
the three estimates, avoiding auxiliary defect fields. -/
structure FPUTBlockwiseReHaarizedMomentCertificate
    (g : Nat → Real) (T : Real)
    (E : Nat → Nat → Real) (Q : Real → Real)
    (Cref Ccoupling : Real) where
  referenceInitial : Nat → Nat → Real
  referenceFinal : Nat → Nat → Real
  reference_residual : ∀ n j,
    MomentKineticEulerResidual
      (referenceInitial n j) (referenceFinal n j)
      (g n ^ 2 * T) (Q (referenceInitial n j))
      (Cref * |g n| ^ 3)
  initial_endpoint_control : ∀ n j,
    |E n j - referenceInitial n j| ≤ Ccoupling * |g n| ^ 3
  final_endpoint_control : ∀ n j,
    |E n (j + 1) - referenceFinal n j| ≤ Ccoupling * |g n| ^ 3

namespace FPUTBlockwiseReHaarizedMomentCertificate

variable {g : Nat → Real} {T : Real}
  {E : Nat → Nat → Real} {Q : Real → Real}
  {Cref Ccoupling : Real}

/-- The uniform actual one-block residual derived from a fresh reference
block and its two endpoint couplings. -/
def actualResidualDefect
    (_certificate : FPUTBlockwiseReHaarizedMomentCertificate
      g T E Q Cref Ccoupling)
    (L : Real) (n : Nat) : Real :=
  endpointCoupledKineticResidualDefect
    (g n ^ 2 * T) L
    (Cref * |g n| ^ 3)
    (Ccoupling * |g n| ^ 3)
    (Ccoupling * |g n| ^ 3)

/-- The actual residual follows block by block from the independently chosen
reference endpoints.  No reference coherence and no assumed actual residual
are used. -/
theorem actual_is_momentKineticEulerResidual
    (certificate : FPUTBlockwiseReHaarizedMomentCertificate
      g T E Q Cref Ccoupling)
    (hT : 0 ≤ T) {L : Real} (hL : 0 ≤ L)
    (hQ : ∀ x y, |Q x - Q y| ≤ L * |x - y|)
    (n j : Nat) :
    MomentKineticEulerResidual
      (E n j) (E n (j + 1)) (g n ^ 2 * T) (Q (E n j))
      (certificate.actualResidualDefect L n) := by
  exact momentKineticEulerResidual_of_reference_endpoint_control
    (E n j) (E n (j + 1))
    (certificate.referenceInitial n j) (certificate.referenceFinal n j)
    Q (mul_nonneg (sq_nonneg _) hT) hL
    (certificate.reference_residual n j)
    (certificate.initial_endpoint_control n j)
    (certificate.final_endpoint_control n j) hQ

/-- The derived uniform actual residual is nonnegative. -/
theorem actualResidualDefect_nonneg
    (certificate : FPUTBlockwiseReHaarizedMomentCertificate
      g T E Q Cref Ccoupling)
    (hT : 0 ≤ T) (hCref : 0 ≤ Cref)
    (hCcoupling : 0 ≤ Ccoupling)
    {L : Real} (hL : 0 ≤ L) (n : Nat) :
    0 ≤ certificate.actualResidualDefect L n := by
  unfold actualResidualDefect endpointCoupledKineticResidualDefect
  have href : 0 ≤ Cref * |g n| ^ 3 :=
    mul_nonneg hCref (pow_nonneg (abs_nonneg _) _)
  have hcoupling : 0 ≤ Ccoupling * |g n| ^ 3 :=
    mul_nonneg hCcoupling (pow_nonneg (abs_nonneg _) _)
  have hfactor : 0 ≤ 1 + (g n ^ 2 * T) * L :=
    add_nonneg zero_le_one
      (mul_nonneg (mul_nonneg (sq_nonneg _) hT) hL)
  exact add_nonneg (add_nonneg href hcoupling)
    (mul_nonneg hfactor hcoupling)

/-! ## Cubic residual divided by the kinetic step -/

/-- The actual residual obtained by endpoint transfer is little-o of
`g^2 T`.  This combines the reusable cubic-ratio theorem for the reference
and endpoint envelopes with the exact endpoint-stability formula. -/
theorem actualResidualDefect_div_kineticStep_tendsto_zero
    (certificate : FPUTBlockwiseReHaarizedMomentCertificate
      g T E Q Cref Ccoupling)
    (hT : 0 < T) (hCref : 0 ≤ Cref)
    (hCcoupling : 0 ≤ Ccoupling)
    (L : Real)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : ∀ᶠ n in atTop, g n ≠ 0) :
    Tendsto
      (fun n ↦ certificate.actualResidualDefect L n /
        (g n ^ 2 * T)) atTop (nhds 0) := by
  let referenceDefect : Nat → Real := fun n ↦ Cref * |g n| ^ 3
  let couplingDefect : Nat → Real := fun n ↦ Ccoupling * |g n| ^ 3
  let step : Nat → Real := fun n ↦ g n ^ 2 * T
  have href0 : ∀ n, 0 ≤ referenceDefect n := fun n ↦
    mul_nonneg hCref (pow_nonneg (abs_nonneg _) _)
  have hcoupling0 : ∀ n, 0 ≤ couplingDefect n := fun n ↦
    mul_nonneg hCcoupling (pow_nonneg (abs_nonneg _) _)
  have hrefRatio : Tendsto
      (fun n ↦ referenceDefect n / step n) atTop (nhds 0) := by
    exact cubicDefect_div_kineticStep_tendsto_zero
      g referenceDefect hT hCref hg hg0 href0 (fun _ ↦ le_rfl)
  have hcouplingRatio : Tendsto
      (fun n ↦ couplingDefect n / step n) atTop (nhds 0) := by
    exact cubicDefect_div_kineticStep_tendsto_zero
      g couplingDefect hT hCcoupling hg hg0 hcoupling0
        (fun _ ↦ le_rfl)
  have hstep0 : Tendsto step atTop (nhds 0) := by
    simpa only [step, zero_pow (by norm_num : (2 : Nat) ≠ 0),
      zero_mul] using (hg.pow 2).mul_const T
  have hfactor : Tendsto (fun n ↦ 1 + step n * L)
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add (hstep0.mul_const L)
  have hsum : Tendsto
      (fun n ↦ referenceDefect n / step n +
        couplingDefect n / step n +
        (1 + step n * L) * (couplingDefect n / step n))
      atTop (nhds 0) := by
    simpa using (hrefRatio.add hcouplingRatio).add
      (hfactor.mul hcouplingRatio)
  apply hsum.congr'
  filter_upwards [hg0] with n hgn
  have hstepNe : step n ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hgn) hT.ne'
  unfold actualResidualDefect endpointCoupledKineticResidualDefect
  dsimp only [referenceDefect, couplingDefect, step] at *
  field_simp [hstepNe]

/-! ## Kinetic-time shadowing -/

/-- Independently re-Haarizing every block is sufficient for kinetic-time
shadowing of the coherent actual moment chain.

The conclusion contains no actual-residual hypothesis and no cross-block
relation between reference endpoints.  The only restart input is
`FPUTBlockwiseReHaarizedMomentCertificate`. -/
theorem actual_blockwiseReHaarized_kineticEuler_shadowing_tendsto_zero
    (certificate : FPUTBlockwiseReHaarizedMomentCertificate
      g T E Q Cref Ccoupling)
    (hT : 0 < T) (hCref : 0 ≤ Cref)
    (hCcoupling : 0 ≤ Ccoupling)
    (L : Real) (hL : 0 ≤ L)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : ∀ᶠ n in atTop, g n ≠ 0)
    (V : Nat → Nat → Real) (K : Nat → Nat) (tau : Real)
    (hQ : ∀ x y, |Q x - Q y| ≤ L * |x - y|)
    (hkinetic : ∀ n,
      IsKineticEulerTrajectory (V n) (g n ^ 2 * T) Q)
    (hkineticBudget : ∀ n,
      (g n ^ 2 * T) * (K n : Real) ≤ tau)
    (hinitial : Tendsto (fun n ↦ |E n 0 - V n 0|)
      atTop (nhds 0)) :
    Tendsto (fun n ↦ |E n (K n) - V n (K n)|)
      atTop (nhds 0) := by
  let step : Nat → Real := fun n ↦ g n ^ 2 * T
  let defectMax : Nat → Real := fun n ↦
    certificate.actualResidualDefect L n
  have hdefect0 : ∀ n, 0 ≤ defectMax n := by
    intro n
    exact certificate.actualResidualDefect_nonneg hT.le hCref
      hCcoupling hL n
  have hratio : Tendsto (fun n ↦ defectMax n / step n)
      atTop (nhds 0) := by
    simpa only [defectMax, step] using
      certificate.actualResidualDefect_div_kineticStep_tendsto_zero
        hT hCref hCcoupling L hg hg0
  have hstepPos : ∀ᶠ n in atTop, 0 < step n := by
    filter_upwards [hg0] with n hgn
    exact mul_pos (sq_pos_of_ne_zero hgn) hT
  have hcumulative : Tendsto
      (fun n ↦ (K n : Real) * defectMax n) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall (fun n ↦
        mul_nonneg (Nat.cast_nonneg _) (hdefect0 n))
    · filter_upwards [hstepPos] with n hstepn
      have hratio0 : 0 ≤ defectMax n / step n :=
        div_nonneg (hdefect0 n) hstepn.le
      calc
        (K n : Real) * defectMax n =
            (step n * (K n : Real)) * (defectMax n / step n) := by
              field_simp [hstepn.ne']
        _ ≤ tau * (defectMax n / step n) :=
          mul_le_mul_of_nonneg_right
            (by simpa only [step] using hkineticBudget n) hratio0
    · simpa using (tendsto_const_nhds.mul hratio :
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
      (E n) (V n) Q (step n) L (defectMax n)
      (fun _ ↦ defectMax n) hstepn.le hL
      (fun _ ↦ hdefect0 n) (fun _ ↦ le_rfl)
      (by simpa only [step] using hkinetic n)
      (fun j ↦ by
        simpa only [step, defectMax] using
          certificate.actual_is_momentKineticEulerResidual
            hT.le hL hQ n j)
      hQ (K n)
    have hprefix0 :
        0 ≤ |E n 0 - V n 0| + (K n : Real) * defectMax n :=
      add_nonneg (abs_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (hdefect0 n))
    have hexponent : L * step n * (K n : Real) ≤ L * tau := by
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
        (nhds (Real.exp (L * tau))) )

end FPUTBlockwiseReHaarizedMomentCertificate

end

end ArchonPhysics.PhyslibFPUTBlockwiseReHaarizedKineticShadowing
