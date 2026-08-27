import ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# A single mass is a rank-one perturbation in the dual harmonic matrix

The edge-space weighted cycle Laplacian is the sum, over mass sites, of one
outer product per inverse-mass weight.  Consequently, changing one mass while
holding all other masses fixed changes the dual harmonic matrix by exactly
one scalar multiple of one outer product, and hence by a matrix of rank at
most one.

This finite deterministic fact is the local sensitivity input for later
eigenvalue-counting concentration.  No concentration, IDS limit, localization,
or kinetic theorem is asserted here.
-/

open scoped Matrix

namespace ArchonPhysics.SingleMassRankOnePerturbation

open ArchonPhysics
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedCycleBridge
open ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison

noncomputable section

/-- The column of the periodic difference matrix attached to one mass site. -/
def cycleMassPerturbationVector {N : Nat} [NeZero N]
    (i : Lattice.Site N) : Lattice.Configuration N :=
  fun j ↦ differenceMatrix j i

/-- Exact outer-product decomposition of the weighted cycle Laplacian. -/
theorem weightedCycleLaplacian_eq_sum_rankOne
    {N : Nat} [NeZero N] (w : Lattice.Site N → Real) :
    weightedCycleLaplacian w =
      ∑ i : Lattice.Site N, w i • Matrix.vecMulVec
        (cycleMassPerturbationVector i) (cycleMassPerturbationVector i) := by
  ext j k
  unfold weightedCycleLaplacian
  rw [Matrix.mul_apply, Matrix.sum_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, cycleMassPerturbationVector]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- If two weight fields agree away from one site, their weighted Laplacians
differ by exactly that site's outer product. -/
theorem weightedCycleLaplacian_sub_eq_smul_rankOne_of_eq_off
    {N : Nat} [NeZero N] (w w' : Lattice.Site N → Real)
    (i : Lattice.Site N) (hoff : ∀ j, j ≠ i → w j = w' j) :
    weightedCycleLaplacian w - weightedCycleLaplacian w' =
      (w i - w' i) • Matrix.vecMulVec
        (cycleMassPerturbationVector i) (cycleMassPerturbationVector i) := by
  rw [weightedCycleLaplacian_eq_sum_rankOne,
    weightedCycleLaplacian_eq_sum_rankOne, ← Finset.sum_sub_distrib]
  simp_rw [← sub_smul]
  rw [Finset.sum_eq_single i]
  · intro j _hj hji
    rw [hoff j hji, sub_self, zero_smul]
  · simp

/-- A scalar multiple of a square outer product has matrix rank at most one. -/
theorem rank_smul_vecMulVec_le_one
    {ι : Type*} [Fintype ι]
    (c : Real) (v : ι → Real) :
    (c • Matrix.vecMulVec v v).rank ≤ 1 := by
  classical
  calc
    (c • Matrix.vecMulVec v v).rank =
        ((Matrix.diagonal fun _ : ι ↦ c) * Matrix.vecMulVec v v).rank := by
      rw [← Matrix.smul_eq_diagonal_mul]
    _ ≤ (Matrix.vecMulVec v v).rank := Matrix.rank_mul_le_right _ _
    _ ≤ 1 := Matrix.rank_vecMulVec_le _ _

/-- Exact single-coordinate perturbation formula for the physical dual
random-mass harmonic matrix. -/
theorem dualMassWeightedHarmonicMatrix_sub_eq_smul_rankOne_of_eq_off
    {N : Nat} [NeZero N] (m m' : Lattice.PositiveMassConfig N)
    (i : Lattice.Site N) (hoff : ∀ j, j ≠ i → m.mass j = m'.mass j) :
    dualMassWeightedHarmonicMatrix m -
        dualMassWeightedHarmonicMatrix m' =
      ((m.mass i)⁻¹ - (m'.mass i)⁻¹) • Matrix.vecMulVec
        (cycleMassPerturbationVector i) (cycleMassPerturbationVector i) := by
  rw [dualMassWeightedHarmonicMatrix, dualMassWeightedHarmonicMatrix,
    massWeighted_selfTranspose_eq_weightedCycleLaplacian,
    massWeighted_selfTranspose_eq_weightedCycleLaplacian]
  apply weightedCycleLaplacian_sub_eq_smul_rankOne_of_eq_off
  intro j hji
  rw [hoff j hji]

/-- In particular, changing one mass changes the dual harmonic matrix by rank
at most one. -/
theorem dualMassWeightedHarmonicMatrix_sub_rank_le_one_of_eq_off
    {N : Nat} [NeZero N] (m m' : Lattice.PositiveMassConfig N)
    (i : Lattice.Site N) (hoff : ∀ j, j ≠ i → m.mass j = m'.mass j) :
    (dualMassWeightedHarmonicMatrix m -
      dualMassWeightedHarmonicMatrix m').rank ≤ 1 := by
  rw [dualMassWeightedHarmonicMatrix_sub_eq_smul_rankOne_of_eq_off
    m m' i hoff]
  exact rank_smul_vecMulVec_le_one _ _

end

end ArchonPhysics.SingleMassRankOnePerturbation
