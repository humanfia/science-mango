import ArchonPhysics.ActualSixSiteNearResonantFiniteContractionBridge

/-!
# Denominator-cleared polynomial six-site contraction

Multiplying each six-dimensional shifted matrix by `1 - t^2` removes the
two reciprocal path weights.  Its adjugate acquires the fifth power of that
factor, so the three-leg contraction acquires the fifteenth power.  The
literal cleared matrix below has polynomial entries in the path parameter
and spectral energy and is the natural input to a generic quotient or
resultant certificate.
-/

open scoped BigOperators Matrix

namespace ArchonPhysics.ActualSixSiteNearResonantClearedContraction

open ArchonPhysics
open ArchonPhysics.ActualSixSiteNearResonantAdjugateBridge
open ArchonPhysics.ActualSixSiteNearResonantFiniteContractionBridge
open ArchonPhysics.ActualSixSiteNearResonantInteractionAlgebra

noncomputable section

/-- Literal denominator-cleared shifted matrix.  All entries are polynomial
in `t` and `energy`. -/
def sixSiteNearResonantClearedShiftedLiteral (t energy : Real) :
    Matrix (Fin 6) (Fin 6) Real :=
  let d := 1 - t ^ 2
  !![d * energy - 2, 1 - t, 0, 0, 0, 1 + t;
     1 - t, d * energy - (1 - t) - d, d, 0, 0, 0;
     0, d, d * (energy - 2), d, 0, 0;
     0, 0, d, d * (energy - 2), d, 0;
     0, 0, 0, d, d * (energy - 2), d;
     1 + t, 0, 0, 0, d, d * energy - d - (1 + t)]

/-- Away from the reciprocal poles, the literal polynomial matrix is the
scalar-cleared physical shifted matrix. -/
theorem sixSiteNearResonantClearedShiftedLiteral_eq_smul
    {t energy : Real} (hpole : 1 - t ^ 2 ≠ 0) :
    sixSiteNearResonantClearedShiftedLiteral t energy =
      (1 - t ^ 2) • sixSiteNearResonantFinShiftedLiteral t energy := by
  have hprod : (1 - t) * (1 + t) ≠ 0 := by
    rw [show (1 - t) * (1 + t) = 1 - t ^ 2 by ring]
    exact hpole
  have hminus : 1 - t ≠ 0 := (mul_ne_zero_iff.mp hprod).1
  have hplus : 1 + t ≠ 0 := (mul_ne_zero_iff.mp hprod).2
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sixSiteNearResonantClearedShiftedLiteral,
      sixSiteNearResonantFinShiftedLiteral]
  all_goals field_simp [hminus, hplus]
  all_goals ring

/-- Three-leg contraction of the literal polynomial matrices. -/
def sixSiteNearResonantClearedAdjugateInteractionContraction
    (t : Real) (energy : Fin 3 → Real) : Real :=
  adjugateEntryProductContraction
    (fun r ↦ sixSiteNearResonantClearedShiftedLiteral t (energy r))

/-- Clearing the reciprocal denominators multiplies the three-leg
contraction by exactly `(1 - t^2)^15`. -/
theorem sixSiteNearResonantClearedAdjugateInteractionContraction_eq
    {t : Real} (energy : Fin 3 → Real) (hpole : 1 - t ^ 2 ≠ 0) :
    sixSiteNearResonantClearedAdjugateInteractionContraction t energy =
      (1 - t ^ 2) ^ 15 *
        sixSiteNearResonantFiniteAdjugateInteractionContraction t energy := by
  let d : Real := 1 - t ^ 2
  have hmatrix (r : Fin 3) :
      sixSiteNearResonantClearedShiftedLiteral t (energy r) =
        d • sixSiteNearResonantFinShiftedMatrix t energy r := by
    rw [sixSiteNearResonantFinShiftedMatrix_eq_literal]
    exact sixSiteNearResonantClearedShiftedLiteral_eq_smul hpole
  unfold sixSiteNearResonantClearedAdjugateInteractionContraction
  unfold sixSiteNearResonantFiniteAdjugateInteractionContraction
  unfold adjugateEntryProductContraction
  simp_rw [hmatrix, Matrix.adjugate_smul, Matrix.smul_apply, smul_eq_mul]
  simp_rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Fintype.card_fin]
  have hpow :
      (d ^ (6 - 1)) ^ (Finset.univ : Finset (Fin 3)).card = d ^ 15 := by
    norm_num [Finset.card_univ]
    ring
  rw [hpow]
  change (∑ i, ∑ j, d ^ 15 *
      ∏ r, (sixSiteNearResonantFinShiftedMatrix t energy r).adjugate i j) =
    d ^ 15 *
      ∑ i, ∑ j,
        ∏ r, (sixSiteNearResonantFinShiftedMatrix t energy r).adjugate i j
  simp only [Finset.mul_sum]

end

end ArchonPhysics.ActualSixSiteNearResonantClearedContraction
