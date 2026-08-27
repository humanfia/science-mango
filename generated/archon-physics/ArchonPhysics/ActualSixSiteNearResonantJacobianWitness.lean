import ArchonPhysics.ActualSixSiteThreeMassSimpleSpectrum

/-!
# A one-parameter six-site near-resonant Jacobian witness

This module starts the exact algebraic witness along raw masses
`((1 - t, 1 + t), 1)`, with the last three masses frozen at one.
-/

open scoped Matrix

namespace ArchonPhysics.ActualSixSiteNearResonantJacobianWitness

open ArchonPhysics
open ArchonPhysics.PeriodicWeightedCycleBlockGluing

noncomputable section

/-- The symmetric raw-mass path through the clean six-site resonance. -/
def nearResonantMassTriple (t : Real) :
    ThreeParameterSpectralAveragingDensity.MassTriple :=
  (((1 - t : Real), 1 + t), 1)

/-- Inverse masses on the path, including the frozen unit background. -/
def nearResonantInverseWeights (t : Real) : Fin 6 → Real :=
  ![(1 - t)⁻¹, (1 + t)⁻¹, 1, 1, 1, 1]

/-- The reindexed six-cycle matrix with its first two weights free. -/
def explicitSixSiteTwoWeightLaplacian (x y : Real) :
    Matrix (Fin 6) (Fin 6) Real :=
  !![x + y, -y, 0, 0, 0, -x;
     -y, y + 1, -1, 0, 0, 0;
     0, -1, 2, -1, 0, 0;
     0, 0, -1, 2, -1, 0;
     0, 0, 0, -1, 2, -1;
     -x, 0, 0, 0, -1, 1 + x]

/-- The scalar-shifted two-weight Laplacian, written as a literal matrix so
that finite determinant expansion reduces to scalar polynomial algebra. -/
def explicitSixSiteTwoWeightShiftedMatrix (x y energy : Real) :
    Matrix (Fin 6) (Fin 6) Real :=
  !![energy - x - y, y, 0, 0, 0, x;
     y, energy - y - 1, 1, 0, 0, 0;
     0, 1, energy - 2, 1, 0, 0;
     0, 0, 1, energy - 2, 1, 0;
     0, 0, 0, 1, energy - 2, 1;
     x, 0, 0, 0, 1, energy - 1 - x]

theorem scalar_sub_explicitSixSiteTwoWeightLaplacian
    (x y energy : Real) :
    Matrix.scalar (Fin 6) energy - explicitSixSiteTwoWeightLaplacian x y =
      explicitSixSiteTwoWeightShiftedMatrix x y energy := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [explicitSixSiteTwoWeightLaplacian,
      explicitSixSiteTwoWeightShiftedMatrix, Matrix.scalar_apply]
  all_goals ring

/-- The two-weight matrix specialized to the reciprocal raw-mass path. -/
def explicitSixSiteNearResonantLaplacian (t : Real) :
    Matrix (Fin 6) (Fin 6) Real :=
  explicitSixSiteTwoWeightLaplacian (1 - t)⁻¹ (1 + t)⁻¹

/-- Fully expanded determinant formula in dimension four. -/
def detFinFourFormula (M : Matrix (Fin 4) (Fin 4) Real) : Real :=
  M 0 0 *
        (M 1 1 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) -
          M 1 2 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) +
          M 1 3 * (M 2 1 * M 3 2 - M 2 2 * M 3 1)) -
      M 0 1 *
        (M 1 0 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) -
          M 1 2 * (M 2 0 * M 3 3 - M 2 3 * M 3 0) +
          M 1 3 * (M 2 0 * M 3 2 - M 2 2 * M 3 0)) +
      M 0 2 *
        (M 1 0 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) -
          M 1 1 * (M 2 0 * M 3 3 - M 2 3 * M 3 0) +
          M 1 3 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) -
      M 0 3 *
        (M 1 0 * (M 2 1 * M 3 2 - M 2 2 * M 3 1) -
          M 1 1 * (M 2 0 * M 3 2 - M 2 2 * M 3 0) +
          M 1 2 * (M 2 0 * M 3 1 - M 2 1 * M 3 0))

/-- Laplace expansion in dimension five, with four-dimensional minors
replaced by their explicit formula. -/
def detFinFiveFormula (M : Matrix (Fin 5) (Fin 5) Real) : Real :=
  ∑ j : Fin 5, (-1) ^ (j : Nat) * M 0 j *
    detFinFourFormula (M.submatrix Fin.succ j.succAbove)

theorem det_fin_five_real (M : Matrix (Fin 5) (Fin 5) Real) :
    M.det = detFinFiveFormula M := by
  unfold detFinFiveFormula
  rw [Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [ActualThreeMassLiftedJacobianPolynomial.det_fin_four_real]
  rfl

/-- Laplace expansion in dimension six, using the explicit five-dimensional
formula above. -/
def detFinSixFormula (M : Matrix (Fin 6) (Fin 6) Real) : Real :=
  ∑ j : Fin 6, (-1) ^ (j : Nat) * M 0 j *
    detFinFiveFormula (M.submatrix Fin.succ j.succAbove)

theorem det_fin_six_real (M : Matrix (Fin 6) (Fin 6) Real) :
    M.det = detFinSixFormula M := by
  unfold detFinSixFormula
  rw [Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [det_fin_five_real]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Exact characteristic polynomial for the six-cycle with two free
weights.  Separating this polynomial identity from the rational path
specialization keeps kernel normalization small. -/
theorem explicitSixSiteTwoWeightLaplacian_charpoly_eval
    (x y energy : Real) :
    (explicitSixSiteTwoWeightLaplacian x y).charpoly.eval energy =
      energy * (energy ^ 5 -
        2 * (x + y + 4) * energy ^ 4 +
        3 * (x * y + 5 * x + 5 * y + 7) * energy ^ 3 -
        4 * (5 * x * y + 9 * x + 9 * y + 5) * energy ^ 2 +
        5 * (8 * x * y + 6 * x + 6 * y + 1) * energy -
        6 * (4 * x * y + x + y)) := by
  rw [Matrix.eval_charpoly,
    scalar_sub_explicitSixSiteTwoWeightLaplacian]
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ]
  simp [explicitSixSiteTwoWeightShiftedMatrix]
  simp_rw [det_fin_five_real]
  unfold detFinFiveFormula
  simp only [Fin.sum_univ_succ]
  simp [Fin.succAbove]
  unfold detFinFourFormula
  simp [Fin.succAbove]
  set_option maxRecDepth 100000 in
    ring

/-- Exact characteristic polynomial evaluation along the reciprocal-mass
path. -/
theorem explicitSixSiteNearResonantLaplacian_charpoly_eval
    (t energy : Real) (ht : 1 - t ^ 2 ≠ 0) :
    (explicitSixSiteNearResonantLaplacian t).charpoly.eval energy =
      energy / (1 - t ^ 2) *
        ((1 - t ^ 2) * energy ^ 5 +
          (-12 + 8 * t ^ 2) * energy ^ 4 +
          (54 - 21 * t ^ 2) * energy ^ 3 +
          (-112 + 20 * t ^ 2) * energy ^ 2 +
          (105 - 5 * t ^ 2) * energy - 36) := by
  have hprod : (1 - t) * (1 + t) ≠ 0 := by
    rw [show (1 - t) * (1 + t) = 1 - t ^ 2 by ring]
    exact ht
  have hminus : 1 - t ≠ 0 := (mul_ne_zero_iff.mp hprod).1
  have hplus : 1 + t ≠ 0 := (mul_ne_zero_iff.mp hprod).2
  unfold explicitSixSiteNearResonantLaplacian
  rw [explicitSixSiteTwoWeightLaplacian_charpoly_eval]
  field_simp [hminus, hplus, ht]
  ring

end

end ArchonPhysics.ActualSixSiteNearResonantJacobianWitness
