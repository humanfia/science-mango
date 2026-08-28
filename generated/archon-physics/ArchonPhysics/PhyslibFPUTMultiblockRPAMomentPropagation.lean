import ArchonPhysics.PhyslibFPUTShortTimeRPAMomentStability
import Mathlib.Analysis.ODE.DiscreteGronwall

/-!
# Multiblock propagation of the short-time Physlib RPA error

This module separates two logically different ingredients:

* an unconditional discrete Grönwall calculation; and
* a conditional multiblock interface for the second and fourth RPA moments.

At a block restart, the one-block theorem does not by itself prove that the
conditional phase law is again Haar, nor that the moment map is Lipschitz in
the incoming error.  Those two inputs are therefore represented honestly by
the displayed recurrence hypotheses below.  Once those hypotheses hold, the
accumulation and amplification of the one-block defects are exact theorems.

The kinetic-block theorem uses the transparent sufficient conditions
`g^2 * h * K <= tau` and `L <= ell * g^2`.  Thus the Grönwall exponent stays
below `ell * tau`; no claim that the current Hamiltonian analysis establishes
these restart or scaled-Lipschitz hypotheses is made here.
-/

namespace ArchonPhysics.PhyslibFPUTMultiblockRPAMomentPropagation

open Finset
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTShortTimeRPAMomentStability

noncomputable section

/-! ## Reusable discrete Grönwall bounds -/

/-- Exact product/power form of the affine discrete Grönwall iteration.
No sign condition on the defect is needed for this sharper formula; only the
one-step amplification factor must be nonnegative. -/
theorem discrete_affine_error_closedForm
    {e defect : Nat → Real} {L h : Real}
    (hamplification : 0 ≤ 1 + L * h)
    (hstep : ∀ j, e (j + 1) ≤ (1 + L * h) * e j + defect j)
    (K : Nat) :
    e K ≤ e 0 * (1 + L * h) ^ K +
      ∑ j ∈ Finset.range K,
        defect j * (1 + L * h) ^ (K - (j + 1)) := by
  have hgronwall := discrete_gronwall_prod_general
    (u := e) (b := defect) (c := fun _ ↦ 1 + L * h) (n₀ := 0)
    (fun j _ ↦ hstep j) (fun _ _ ↦ hamplification) (Nat.zero_le K)
  simpa [Nat.Ico_zero_eq_range, Finset.prod_const,
    Nat.card_Ico] using hgronwall

/-- Exponential/cumulative-defect form.  This is convenient when the defects
are nonnegative but nonuniform from block to block. -/
theorem discrete_affine_error_exp_bound
    {e defect : Nat → Real} {L h : Real}
    (he0 : 0 ≤ e 0) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hdefect : ∀ j, 0 ≤ defect j)
    (hstep : ∀ j, e (j + 1) ≤ (1 + L * h) * e j + defect j)
    (K : Nat) :
    e K ≤ (e 0 + ∑ j ∈ Finset.range K, defect j) *
      Real.exp (L * h * (K : Real)) := by
  have hgronwall := discrete_gronwall
    (u := e) (b := defect) (c := fun _ ↦ L * h) (n₀ := 0)
    he0 (fun j _ ↦ hstep j)
    (fun _ _ ↦ mul_nonneg hL hh) (fun j _ ↦ hdefect j)
    (Nat.zero_le K)
  rw [Nat.Ico_zero_eq_range] at hgronwall
  have hexponentSum :
      (∑ _i ∈ Finset.range K, L * h) = L * h * (K : Real) := by
    simp
    ring
  rw [hexponentSum] at hgronwall
  exact hgronwall

/-- Uniform per-block defect specialization. -/
theorem discrete_affine_error_uniform_defect_bound
    {e defect : Nat → Real} {L h defectMax : Real}
    (he0 : 0 ≤ e 0) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hdefect0 : ∀ j, 0 ≤ defect j)
    (hdefectMax : ∀ j, defect j ≤ defectMax)
    (hstep : ∀ j, e (j + 1) ≤ (1 + L * h) * e j + defect j)
    (K : Nat) :
    e K ≤ (e 0 + (K : Real) * defectMax) *
      Real.exp (L * h * (K : Real)) := by
  have hbase := discrete_affine_error_exp_bound
    he0 hL hh hdefect0 hstep K
  refine hbase.trans ?_
  have hsum :
      (∑ j ∈ Finset.range K, defect j) ≤ (K : Real) * defectMax := by
    calc
      (∑ j ∈ Finset.range K, defect j) ≤
          ∑ _j ∈ Finset.range K, defectMax := by
        exact Finset.sum_le_sum fun j _ ↦ hdefectMax j
      _ = (K : Real) * defectMax := by simp
  gcongr

/-! ## Kinetic block-count criterion -/

/-- A sufficient scale criterion for maintaining an error tolerance through
`K` blocks.  The block-count budget is written without division so it remains
meaningful at `g = 0` or `h = 0`.  For positive `g,h`, it says
`K <= tau / (g^2 h)`. -/
theorem approximateRPA_at_kinetic_block_count
    {e defect : Nat → Real}
    {L h defectMax g ell tau tolerance : Real}
    (he0 : 0 ≤ e 0) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hell : 0 ≤ ell)
    (hdefect0 : ∀ j, 0 ≤ defect j)
    (hdefectMax : ∀ j, defect j ≤ defectMax)
    (hstep : ∀ j, e (j + 1) ≤ (1 + L * h) * e j + defect j)
    (K : Nat)
    (hscaledLipschitz : L ≤ ell * g ^ 2)
    (hkineticBudget : g ^ 2 * h * (K : Real) ≤ tau)
    (htolerance :
      (e 0 + (K : Real) * defectMax) * Real.exp (ell * tau) ≤
        tolerance) :
    e K ≤ tolerance := by
  have hbase := discrete_affine_error_uniform_defect_bound
    he0 hL hh hdefect0 hdefectMax hstep K
  have hK0 : 0 ≤ (K : Real) := Nat.cast_nonneg K
  have hexponent : L * h * (K : Real) ≤ ell * tau := by
    calc
      L * h * (K : Real) ≤ (ell * g ^ 2) * h * (K : Real) := by
        gcongr
      _ = ell * (g ^ 2 * h * (K : Real)) := by ring
      _ ≤ ell * tau := mul_le_mul_of_nonneg_left hkineticBudget hell
  have hprefix : 0 ≤ e 0 + (K : Real) * defectMax := by
    have hdefectMax0 : 0 ≤ defectMax :=
      (hdefect0 0).trans (hdefectMax 0)
    positivity
  calc
    e K ≤ (e 0 + (K : Real) * defectMax) *
        Real.exp (L * h * (K : Real)) := hbase
    _ ≤ (e 0 + (K : Real) * defectMax) * Real.exp (ell * tau) := by
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hexponent) hprefix
    _ ≤ tolerance := htolerance

/-! ## Moment defects and the actual Physlib one-block envelope -/

/-- The second-moment defect supplied by a pointwise block-amplitude error. -/
def secondMomentBlockDefect (M blockError : Real) : Real :=
  2 * M * blockError

/-- The fourth-moment defect supplied by a pointwise block-amplitude error. -/
def fourthMomentBlockDefect (M blockError : Real) : Real :=
  4 * M ^ 3 * blockError

/-- Physlib's explicit first-Duhamel envelope, packaged as a second-moment
one-block defect. -/
def physlibSecondMomentBlockDefect
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (mUpper kappa beta g H M : Real)
    (observed : Site N) (h : Real) : Real :=
  secondMomentBlockDefect M
    (shortTimeRPABlockError m mUpper kappa beta g H observed h)

/-- Physlib's explicit first-Duhamel envelope, packaged as a fourth-moment
one-block defect. -/
def physlibFourthMomentBlockDefect
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (mUpper kappa beta g H M : Real)
    (observed : Site N) (h : Real) : Real :=
  fourthMomentBlockDefect M
    (shortTimeRPABlockError m mUpper kappa beta g H observed h)

/-- Conditional multiblock propagation for the two RPA moments using one
constant Physlib block envelope.  The two recurrence assumptions are the
precise unresolved restart interface: establishing them requires conditional
Haar/RPA control and Lipschitz stability of the restarted nonlinear flow.

The conclusion itself is unconditional once those displayed assumptions are
provided. -/
theorem physlib_multiblock_second_fourth_moment_bounds
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N)
    {mUpper kappa beta g H M L h : Real}
    (observed : Site N)
    (secondError fourthError : Nat → Real)
    (hsecond0 : 0 ≤ secondError 0)
    (hfourth0 : 0 ≤ fourthError 0)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hblockError : 0 ≤
      shortTimeRPABlockError m mUpper kappa beta g H observed h)
    (hsecondRestart : ∀ j,
      secondError (j + 1) ≤ (1 + L * h) * secondError j +
        physlibSecondMomentBlockDefect
          m mUpper kappa beta g H M observed h)
    (hfourthRestart : ∀ j,
      fourthError (j + 1) ≤ (1 + L * h) * fourthError j +
        physlibFourthMomentBlockDefect
          m mUpper kappa beta g H M observed h)
    (K : Nat) :
    secondError K ≤
        (secondError 0 + (K : Real) *
          physlibSecondMomentBlockDefect
            m mUpper kappa beta g H M observed h) *
          Real.exp (L * h * (K : Real)) ∧
    fourthError K ≤
        (fourthError 0 + (K : Real) *
          physlibFourthMomentBlockDefect
            m mUpper kappa beta g H M observed h) *
          Real.exp (L * h * (K : Real)) := by
  have hsecondDefect0 : 0 ≤ physlibSecondMomentBlockDefect
      m mUpper kappa beta g H M observed h := by
    unfold physlibSecondMomentBlockDefect secondMomentBlockDefect
    positivity
  have hfourthDefect0 : 0 ≤ physlibFourthMomentBlockDefect
      m mUpper kappa beta g H M observed h := by
    unfold physlibFourthMomentBlockDefect fourthMomentBlockDefect
    positivity
  constructor
  · exact discrete_affine_error_uniform_defect_bound
      hsecond0 hL hh (fun _ ↦ hsecondDefect0) (fun _ ↦ le_rfl)
        hsecondRestart K
  · exact discrete_affine_error_uniform_defect_bound
      hfourth0 hL hh (fun _ ↦ hfourthDefect0) (fun _ ↦ le_rfl)
        hfourthRestart K

/-- Kinetic-block tolerance corollary for both Physlib RPA moments.  The
conditions show explicitly what must be proved beyond the current one-block
result: scaled Lipschitz propagation, valid restart recurrences, and small
cumulative one-block defects. -/
theorem physlib_multiblock_moments_at_kinetic_scale
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N)
    {mUpper kappa beta g H M L h ell tau
      secondTolerance fourthTolerance : Real}
    (observed : Site N)
    (secondError fourthError : Nat → Real)
    (hsecond0 : 0 ≤ secondError 0)
    (hfourth0 : 0 ≤ fourthError 0)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hell : 0 ≤ ell)
    (hblockError : 0 ≤
      shortTimeRPABlockError m mUpper kappa beta g H observed h)
    (hsecondRestart : ∀ j,
      secondError (j + 1) ≤ (1 + L * h) * secondError j +
        physlibSecondMomentBlockDefect
          m mUpper kappa beta g H M observed h)
    (hfourthRestart : ∀ j,
      fourthError (j + 1) ≤ (1 + L * h) * fourthError j +
        physlibFourthMomentBlockDefect
          m mUpper kappa beta g H M observed h)
    (K : Nat)
    (hscaledLipschitz : L ≤ ell * g ^ 2)
    (hkineticBudget : g ^ 2 * h * (K : Real) ≤ tau)
    (hsecondTolerance :
      (secondError 0 + (K : Real) *
        physlibSecondMomentBlockDefect
          m mUpper kappa beta g H M observed h) *
          Real.exp (ell * tau) ≤ secondTolerance)
    (hfourthTolerance :
      (fourthError 0 + (K : Real) *
        physlibFourthMomentBlockDefect
          m mUpper kappa beta g H M observed h) *
          Real.exp (ell * tau) ≤ fourthTolerance) :
    secondError K ≤ secondTolerance ∧
      fourthError K ≤ fourthTolerance := by
  have hsecondDefect0 : 0 ≤ physlibSecondMomentBlockDefect
      m mUpper kappa beta g H M observed h := by
    unfold physlibSecondMomentBlockDefect secondMomentBlockDefect
    positivity
  have hfourthDefect0 : 0 ≤ physlibFourthMomentBlockDefect
      m mUpper kappa beta g H M observed h := by
    unfold physlibFourthMomentBlockDefect fourthMomentBlockDefect
    positivity
  constructor
  · exact approximateRPA_at_kinetic_block_count
      hsecond0 hL hh hell (fun _ ↦ hsecondDefect0) (fun _ ↦ le_rfl)
        hsecondRestart K hscaledLipschitz hkineticBudget hsecondTolerance
  · exact approximateRPA_at_kinetic_block_count
      hfourth0 hL hh hell (fun _ ↦ hfourthDefect0) (fun _ ↦ le_rfl)
        hfourthRestart K hscaledLipschitz hkineticBudget hfourthTolerance

end

end ArchonPhysics.PhyslibFPUTMultiblockRPAMomentPropagation
