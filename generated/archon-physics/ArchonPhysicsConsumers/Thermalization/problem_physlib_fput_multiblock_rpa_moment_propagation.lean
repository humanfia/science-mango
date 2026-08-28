import ArchonPhysics.PhyslibFPUTMultiblockRPAMomentPropagation

/-!
# Consumer: multiblock Physlib RPA moment propagation

The contracts below expose the exact discrete Grönwall formula, the kinetic
block-count criterion, and the specialization of the one-block Physlib
Duhamel error to second and fourth moment defects.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTMultiblockRPAMomentPropagation

open Finset
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTMultiblockRPAMomentPropagation
open ArchonPhysics.PhyslibFPUTShortTimeRPAMomentStability

noncomputable section

theorem discrete_multiblock_closed_form_contract
    {e defect : Nat → Real} {L h : Real}
    (hamplification : 0 ≤ 1 + L * h)
    (hstep : ∀ j, e (j + 1) ≤ (1 + L * h) * e j + defect j)
    (K : Nat) :
    e K ≤ e 0 * (1 + L * h) ^ K +
      ∑ j ∈ Finset.range K,
        defect j * (1 + L * h) ^ (K - (j + 1)) :=
  discrete_affine_error_closedForm hamplification hstep K

theorem nonuniform_accumulated_defect_contract
    {e defect : Nat → Real} {L h : Real}
    (he0 : 0 ≤ e 0) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hdefect : ∀ j, 0 ≤ defect j)
    (hstep : ∀ j, e (j + 1) ≤ (1 + L * h) * e j + defect j)
    (K : Nat) :
    e K ≤ (e 0 + ∑ j ∈ Finset.range K, defect j) *
      Real.exp (L * h * (K : Real)) :=
  discrete_affine_error_exp_bound he0 hL hh hdefect hstep K

theorem kinetic_block_count_tolerance_contract
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
    e K ≤ tolerance :=
  approximateRPA_at_kinetic_block_count
    he0 hL hh hell hdefect0 hdefectMax hstep K
      hscaledLipschitz hkineticBudget htolerance

theorem physlib_one_block_defect_identification_contract
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N)
    (mUpper kappa beta g H M : Real)
    (observed : Site N) (h : Real) :
    physlibSecondMomentBlockDefect
        m mUpper kappa beta g H M observed h =
      2 * M * shortTimeRPABlockError
        m mUpper kappa beta g H observed h ∧
    physlibFourthMomentBlockDefect
        m mUpper kappa beta g H M observed h =
      4 * M ^ 3 * shortTimeRPABlockError
        m mUpper kappa beta g H observed h := by
  simp [physlibSecondMomentBlockDefect,
    physlibFourthMomentBlockDefect, secondMomentBlockDefect,
    fourthMomentBlockDefect]

theorem physlib_multiblock_moment_contract
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
          Real.exp (L * h * (K : Real)) :=
  physlib_multiblock_second_fourth_moment_bounds
    m observed secondError fourthError hsecond0 hfourth0 hM hL hh
      hblockError hsecondRestart hfourthRestart K

#print axioms discrete_multiblock_closed_form_contract
#print axioms nonuniform_accumulated_defect_contract
#print axioms kinetic_block_count_tolerance_contract
#print axioms physlib_one_block_defect_identification_contract
#print axioms physlib_multiblock_moment_contract
#print axioms
  ArchonPhysics.PhyslibFPUTMultiblockRPAMomentPropagation.physlib_multiblock_moments_at_kinetic_scale

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTMultiblockRPAMomentPropagation
