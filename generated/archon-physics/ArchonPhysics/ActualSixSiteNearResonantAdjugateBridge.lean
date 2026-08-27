import ArchonPhysics.ActualSixSiteNearResonantAdjugateFactor
import ArchonPhysics.AdjugateWeightReindex
import ArchonPhysics.ActualProjectorAdjugatePolynomial

/-!
# Actual six-site near-resonant adjugate bridge

This module identifies the three explicit rational columns from
`ActualSixSiteNearResonantAdjugateFactor` with the genuine shifted-adjugate
quadratic weights of the six-site weighted cycle.  The calculation is kept
separate from the one-parameter spectral witness so the exact matrix algebra
can be kernel-checked independently.
-/

open scoped BigOperators Matrix

namespace ArchonPhysics.ActualSixSiteNearResonantAdjugateBridge

open ArchonPhysics
open ArchonPhysics.AdjugateWeightReindex
open ArchonPhysics.ActualProjectorAdjugatePolynomial
open ArchonPhysics.ActualSixSiteNearResonantAdjugateFactor
open ArchonPhysics.ActualThreeMassLiftedJacobianPolynomial
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.PeriodicWeightedCycleBlockGluing

noncomputable section

/-- The inverse-mass coordinates on the symmetric six-site path. -/
def sixSiteNearResonantInverseWeights (t : Real) : Fin 6 → Real :=
  ![(1 - t)⁻¹, (1 + t)⁻¹, 1, 1, 1, 1]

/-- The finite-coordinate two-weight six-cycle matrix. -/
def sixSiteNearResonantFinLaplacian (t : Real) :
    Matrix (Fin 6) (Fin 6) Real :=
  !![(1 - t)⁻¹ + (1 + t)⁻¹, -(1 + t)⁻¹, 0, 0, 0, -(1 - t)⁻¹;
     -(1 + t)⁻¹, (1 + t)⁻¹ + 1, -1, 0, 0, 0;
     0, -1, 2, -1, 0, 0;
     0, 0, -1, 2, -1, 0;
     0, 0, 0, -1, 2, -1;
     -(1 - t)⁻¹, 0, 0, 0, -1, 1 + (1 - t)⁻¹]

/-- The abstract finite weighted-cycle construction is exactly the displayed
six-by-six matrix on the near-resonant path. -/
theorem finWeightedCycleLaplacian_sixSiteNearResonantInverseWeights
    (t : Real) :
    finWeightedCycleLaplacian (sixSiteNearResonantInverseWeights t) =
      sixSiteNearResonantFinLaplacian t := by
  rw [finWeightedCycleLaplacian_eq_sum_rankOne]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, Fin.sum_univ_succ]
  <;> norm_num +decide [sixSiteNearResonantInverseWeights,
    sixSiteNearResonantFinLaplacian, finCycleEdgeVector,
    SingleMassRankOnePerturbation.cycleMassPerturbationVector,
    HarmonicModes.differenceMatrix, siteEquivFin]
  all_goals simp
  all_goals ring

/-- The three genuine cycle directions at sites zero, one, and two, after
canonical transport to finite coordinates. -/
def sixSiteNearResonantFinDirection (s : Fin 3) : Fin 6 → Real :=
  ![(![-1, 0, 0, 0, 0, 1] : Fin 6 → Real),
    (![1, -1, 0, 0, 0, 0] : Fin 6 → Real),
    (![0, 1, -1, 0, 0, 0] : Fin 6 → Real)] s

theorem reindexVector_actualSixSiteCycleDirection (s : Fin 3) :
    reindexVector (siteEquivFin 6)
        (actualThreeMassCycleDirection
          (0 : Lattice.Site 6) (1 : Lattice.Site 6)
          (2 : Lattice.Site 6) s) =
      sixSiteNearResonantFinDirection s := by
  funext i
  fin_cases s <;> fin_cases i <;>
    norm_num +decide [reindexVector, sixSiteNearResonantFinDirection,
      actualThreeMassCycleDirection, actualThreeMassSelectedSite,
      SingleMassRankOnePerturbation.cycleMassPerturbationVector,
      HarmonicModes.differenceMatrix, siteEquivFin]

/-- The finite-coordinate spectral shift. -/
def sixSiteNearResonantFinShiftedMatrix
    (t : Real) (energy : Fin 3 → Real) (r : Fin 3) :
    Matrix (Fin 6) (Fin 6) Real :=
  energy r • 1 - sixSiteNearResonantFinLaplacian t

/-- Literal form of the finite-coordinate spectral shift.  This prevents the
six-dimensional cofactor normalization from unfolding semireducible matrix
constructors under nested submatrices. -/
def sixSiteNearResonantFinShiftedLiteral (t energy : Real) :
    Matrix (Fin 6) (Fin 6) Real :=
  !![energy - (1 - t)⁻¹ - (1 + t)⁻¹, (1 + t)⁻¹, 0, 0, 0, (1 - t)⁻¹;
     (1 + t)⁻¹, energy - (1 + t)⁻¹ - 1, 1, 0, 0, 0;
     0, 1, energy - 2, 1, 0, 0;
     0, 0, 1, energy - 2, 1, 0;
     0, 0, 0, 1, energy - 2, 1;
     (1 - t)⁻¹, 0, 0, 0, 1, energy - 1 - (1 - t)⁻¹]

theorem sixSiteNearResonantFinShiftedMatrix_eq_literal
    (t : Real) (energy : Fin 3 → Real) (r : Fin 3) :
    sixSiteNearResonantFinShiftedMatrix t energy r =
      sixSiteNearResonantFinShiftedLiteral t (energy r) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sixSiteNearResonantFinShiftedMatrix,
      sixSiteNearResonantFinShiftedLiteral,
      sixSiteNearResonantFinLaplacian, Matrix.scalar_apply]
  all_goals ring

/-- The finite-coordinate shifted-adjugate quadratic weights. -/
def sixSiteNearResonantFinAdjugateWeightMatrix
    (t : Real) (energy : Fin 3 → Real) :
    Matrix (Fin 3) (Fin 3) Real :=
  fun r s => sixSiteNearResonantFinDirection s ⬝ᵥ
    ((sixSiteNearResonantFinShiftedMatrix t energy r).adjugate *ᵥ
      sixSiteNearResonantFinDirection s)

/-- The genuine site-indexed spectral shift transports to the displayed
finite-coordinate shift. -/
theorem reindex_sixSiteNearResonant_parameterShiftedMatrix
    (t : Real) (energy : Fin 3 → Real) (r : Fin 3) :
    Matrix.reindex (siteEquivFin 6) (siteEquivFin 6)
        (parameterShiftedMatrix
          (weightedCycleLaplacian
            (weightsOfCoordinates (sixSiteNearResonantInverseWeights t)))
          energy r) =
      sixSiteNearResonantFinShiftedMatrix t energy r := by
  ext i j
  have hentry := congrArg (fun M => M i j)
    (finWeightedCycleLaplacian_sixSiteNearResonantInverseWeights t)
  simp only [finWeightedCycleLaplacian, Matrix.reindex_apply,
    Matrix.submatrix_apply] at hentry
  by_cases hij : i = j
  · subst j
    simp [sixSiteNearResonantFinShiftedMatrix, parameterShiftedMatrix,
      Matrix.reindex_apply, hentry]
  · have hsymm : (siteEquivFin 6).symm i ≠ (siteEquivFin 6).symm j :=
      (siteEquivFin 6).symm.injective.ne hij
    simp [sixSiteNearResonantFinShiftedMatrix, parameterShiftedMatrix,
      Matrix.reindex_apply, hij, hsymm, hentry]

/-- Genuine site-indexed adjugate weights equal the finite-coordinate
quadratic weights after simultaneous transport of matrix and directions. -/
theorem parameterAdjugateWeightMatrix_sixSiteNearResonant_eq_fin
    (t : Real) (energy : Fin 3 → Real) :
    parameterAdjugateWeightMatrix
        (weightedCycleLaplacian
          (weightsOfCoordinates (sixSiteNearResonantInverseWeights t)))
        energy
        (actualThreeMassCycleDirection
          (0 : Lattice.Site 6) (1 : Lattice.Site 6)
          (2 : Lattice.Site 6)) =
      sixSiteNearResonantFinAdjugateWeightMatrix t energy := by
  ext r s
  simp only [parameterAdjugateWeightMatrix,
    sixSiteNearResonantFinAdjugateWeightMatrix]
  have h := reindexVector_dotProduct_adjugate_reindex_mulVec
    (siteEquivFin 6)
    (parameterShiftedMatrix
      (weightedCycleLaplacian
        (weightsOfCoordinates (sixSiteNearResonantInverseWeights t)))
      energy r)
    (actualThreeMassCycleDirection
      (0 : Lattice.Site 6) (1 : Lattice.Site 6)
      (2 : Lattice.Site 6) s)
  rw [reindex_sixSiteNearResonant_parameterShiftedMatrix,
    reindexVector_actualSixSiteCycleDirection] at h
  exact h.symm

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

/-- Five-dimensional Laplace expansion with explicit four-dimensional
minors. -/
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

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- Direct cofactor calculation: the finite-coordinate adjugate quadratic
weights are exactly the three rational columns used by the factor theorem. -/
theorem sixSiteNearResonantFinAdjugateWeightMatrix_eq_displayed
    (t : Real) (energy : Fin 3 → Real)
    (hminus : t - 1 ≠ 0) (hplus : t + 1 ≠ 0) :
    sixSiteNearResonantFinAdjugateWeightMatrix t energy =
      nearResonantAdjugateWeightMatrix t energy := by
  have honeMinus : 1 - t ≠ 0 := by
    intro h
    apply hminus
    linarith
  have honePlus : 1 + t ≠ 0 := by
    simpa [add_comm] using hplus
  have hsquareMinus : 1 - t * 2 + t ^ 2 ≠ 0 := by
    rw [show 1 - t * 2 + t ^ 2 = (1 - t) ^ 2 by ring]
    exact pow_ne_zero 2 honeMinus
  have hsquarePlus : 1 + t * 2 + t ^ 2 ≠ 0 := by
    rw [show 1 + t * 2 + t ^ 2 = (1 + t) ^ 2 by ring]
    exact pow_ne_zero 2 honePlus
  ext r s
  fin_cases s
  all_goals
    simp only [sixSiteNearResonantFinAdjugateWeightMatrix,
      nearResonantAdjugateWeightMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
    simp_rw [sixSiteNearResonantFinShiftedMatrix_eq_literal]
    simp_rw [Matrix.adjugate_fin_succ_eq_det_submatrix,
      det_fin_five_real]
    unfold detFinFiveFormula
    simp only [Fin.sum_univ_succ]
    simp [sixSiteNearResonantFinDirection,
      sixSiteNearResonantFinShiftedLiteral, Fin.succAbove]
    unfold detFinFourFormula
    simp [Fin.succAbove]
    simp [nearResonantAdjugateColumnZero,
      nearResonantAdjugateColumnOne, nearResonantAdjugateColumnTwo]
    field_simp [hminus, hplus, honeMinus, honePlus,
      hsquareMinus, hsquarePlus]
    ring

/-- The full genuine parameter-adjugate weight matrix is the displayed
near-resonant matrix. -/
theorem parameterAdjugateWeightMatrix_sixSiteNearResonant_eq_displayed
    (t : Real) (energy : Fin 3 → Real)
    (hminus : t - 1 ≠ 0) (hplus : t + 1 ≠ 0) :
    parameterAdjugateWeightMatrix
        (weightedCycleLaplacian
          (weightsOfCoordinates (sixSiteNearResonantInverseWeights t)))
        energy
        (actualThreeMassCycleDirection
          (0 : Lattice.Site 6) (1 : Lattice.Site 6)
          (2 : Lattice.Site 6)) =
      nearResonantAdjugateWeightMatrix t energy := by
  rw [parameterAdjugateWeightMatrix_sixSiteNearResonant_eq_fin,
    sixSiteNearResonantFinAdjugateWeightMatrix_eq_displayed
      t energy hminus hplus]

end

end ArchonPhysics.ActualSixSiteNearResonantAdjugateBridge
