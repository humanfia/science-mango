import ArchonPhysics.PhyslibFPUTMultiblockRPAMomentPropagation

/-!
# Vanishing RPA error at the kinetic block scale

This file isolates the exact asymptotic input needed to turn the finite-block
discrete Grönwall estimate into an RPA statement on a kinetic time interval.
If `scale n` is read as `g_n^2 h_n`, the hypotheses say

* `scale n * K n` stays bounded;
* the defect of one restart block is `o(scale n)`;
* the accumulated Lipschitz exponent stays bounded; and
* the initial RPA error tends to zero.

The conclusion is that the RPA error after `K n` blocks tends to zero.  In
particular, the theorem records why a merely `O(g^2 h)` one-block defect is not
enough at kinetic time: a genuine little-o estimate is required unless one has
an additional cancellation between blocks.

No microscopic claim that the FPUT flow supplies the little-o hypothesis is
made here.
-/

namespace ArchonPhysics.PhyslibFPUTKineticScaleRPACriteria

open Filter
open Topology
open ArchonPhysics.PhyslibFPUTMultiblockRPAMomentPropagation

noncomputable section

/-- A bounded number of kinetic units turns a per-block `o(scale)` defect into
a vanishing cumulative defect. -/
theorem cumulative_block_defect_tendsto_zero
    (K : Nat → Nat) (scale defectMax : Nat → Real) (tau : Real)
    (hscale : ∀ n, 0 < scale n)
    (hdefect : ∀ n, 0 ≤ defectMax n)
    (hkineticBudget : ∀ n,
      scale n * (K n : Real) ≤ tau)
    (hdefectRatio : Tendsto
      (fun n ↦ defectMax n / scale n) atTop (nhds 0)) :
    Tendsto (fun n ↦ (K n : Real) * defectMax n) atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact mul_nonneg (Nat.cast_nonneg _) (hdefect n)
  · intro n
    have hratioNonneg : 0 ≤ defectMax n / scale n :=
      div_nonneg (hdefect n) (hscale n).le
    calc
      (K n : Real) * defectMax n =
          (scale n * (K n : Real)) * (defectMax n / scale n) := by
        field_simp [(hscale n).ne']
      _ ≤ tau * (defectMax n / scale n) :=
        mul_le_mul_of_nonneg_right (hkineticBudget n) hratioNonneg
  · simpa using (tendsto_const_nhds.mul hdefectRatio)

/-- Abstract kinetic-scale RPA closure.

The two-indexed family `error n j` is the RPA error in approximation problem
`n` after `j` restart blocks.  The conclusion follows from the exact affine
recurrence, without replacing a nonuniform microscopic statement by an
unstated uniformity assumption. -/
theorem affine_RPA_error_tendsto_zero_at_kinetic_scale
    (error : Nat → Nat → Real)
    (K : Nat → Nat)
    (L h scale defectMax : Nat → Real)
    (tau exponentBound : Real)
    (herror : ∀ n j, 0 ≤ error n j)
    (hL : ∀ n, 0 ≤ L n)
    (hh : ∀ n, 0 ≤ h n)
    (hscale : ∀ n, 0 < scale n)
    (hdefect : ∀ n, 0 ≤ defectMax n)
    (hstep : ∀ n j,
      error n (j + 1) ≤
        (1 + L n * h n) * error n j + defectMax n)
    (hkineticBudget : ∀ n,
      scale n * (K n : Real) ≤ tau)
    (hexponentBound : ∀ n,
      L n * h n * (K n : Real) ≤ exponentBound)
    (hinitial : Tendsto (fun n ↦ error n 0) atTop (nhds 0))
    (hdefectRatio : Tendsto
      (fun n ↦ defectMax n / scale n) atTop (nhds 0)) :
    Tendsto (fun n ↦ error n (K n)) atTop (nhds 0) := by
  have hcumulative : Tendsto
      (fun n ↦ (K n : Real) * defectMax n) atTop (nhds 0) :=
    cumulative_block_defect_tendsto_zero
      K scale defectMax tau hscale hdefect hkineticBudget hdefectRatio
  have hprefix : Tendsto
      (fun n ↦ error n 0 + (K n : Real) * defectMax n)
      atTop (nhds 0) := by
    simpa using hinitial.add hcumulative
  apply squeeze_zero
  · intro n
    exact herror n (K n)
  · intro n
    have hbase := discrete_affine_error_uniform_defect_bound
      (e := error n) (defect := fun _ ↦ defectMax n)
      (L := L n) (h := h n) (defectMax := defectMax n)
      (herror n 0) (hL n) (hh n)
      (fun _ ↦ hdefect n) (fun _ ↦ le_rfl) (hstep n) (K n)
    have hprefixNonneg :
        0 ≤ error n 0 + (K n : Real) * defectMax n := by
      exact add_nonneg (herror n 0)
        (mul_nonneg (Nat.cast_nonneg _) (hdefect n))
    exact hbase.trans
      (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (hexponentBound n)) hprefixNonneg)
  · simpa using hprefix.mul (tendsto_const_nhds :
      Tendsto (fun _ : Nat ↦ Real.exp exponentBound) atTop
        (nhds (Real.exp exponentBound)))

end

end ArchonPhysics.PhyslibFPUTKineticScaleRPACriteria
