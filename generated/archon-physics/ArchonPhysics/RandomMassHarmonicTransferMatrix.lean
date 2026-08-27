import ArchonPhysics.HarmonicModes

/-!
# Transfer matrices for the periodic random-mass harmonic equation

This module formalizes only the algebraic transfer-matrix starting point used
for one-dimensional disordered harmonic chains.  See Matsuda--Ishii,
`doi:10.1143/PTPS.45.56`, and Ajanki--Huveneers, `arXiv:1003.1076`.

For the existing periodic difference matrix `D`, the physical generalized
eigenvalue equation is

`Dᵀ D q = lambda M q`.

At a site `i` this is the second-order recurrence

`q (i + 1) = (2 - lambda * m_i) q i - q (i - 1)`.

The corresponding matrix sends `(q_i,q_{i-1})` to `(q_{i+1},q_i)` and has
determinant one.  We also record the exact finite forward product.  No
localization, Lyapunov exponent, infinite-volume limit, or probabilistic
spectral conclusion is assumed or proved.
-/

open scoped Matrix

namespace ArchonPhysics.RandomMassHarmonicTransferMatrix

open ArchonPhysics.HarmonicModes

noncomputable section

/-- The physical periodic harmonic matrix `DᵀD`, before mass weighting. -/
def physicalCycleHarmonicMatrix {N : Nat} [NeZero N] :
    Matrix (Lattice.Site N) (Lattice.Site N) Real :=
  let D : Matrix (Lattice.Site N) (Lattice.Site N) Real :=
    differenceMatrix
  (Matrix.transpose D * D : Matrix (Lattice.Site N) (Lattice.Site N) Real)

/-- The physical generalized harmonic eigenvalue equation `DᵀD q = λMq`. -/
def IsGeneralizedHarmonicEigenmode {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (lambda : Real)
    (q : Lattice.Configuration N) : Prop :=
  Matrix.mulVec physicalCycleHarmonicMatrix q =
    lambda • Lattice.massAction m q


/-- A mass-weighted harmonic eigenvector becomes a physical generalized
eigenmode after applying `M⁻¹ᐟ²`.  This is the bridge used to feed the
existing ordered signed eigenframe into the transfer recurrence. -/
theorem massWeightedEigenvector_to_generalizedEigenmode
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (lambda : Real)
    (v : Lattice.Configuration N)
    (hv : Matrix.mulVec (massWeightedHarmonicMatrix m) v = lambda • v) :
    IsGeneralizedHarmonicEigenmode m lambda
      (Lattice.inverseSqrtMassAction m v) := by
  let S : Matrix (Lattice.Site N) (Lattice.Site N) Real :=
    Matrix.diagonal (fun i => (Real.sqrt (m.mass i))⁻¹)
  have hSv : Matrix.mulVec S v = Lattice.inverseSqrtMassAction m v := by
    ext i
    simp [S, Matrix.mulVec_diagonal, Lattice.inverseSqrtMassAction]
  have hvWeighted := hv
  unfold massWeightedHarmonicMatrix massWeightedDifferenceMatrix at hvWeighted
  rw [Matrix.transpose_mul, Matrix.diagonal_transpose] at hvWeighted
  change Matrix.mulVec ((S * Matrix.transpose differenceMatrix) *
      (differenceMatrix * S)) v = lambda • v at hvWeighted
  simp only [← Matrix.mulVec_mulVec, hSv] at hvWeighted
  unfold IsGeneralizedHarmonicEigenmode physicalCycleHarmonicMatrix
  rw [← Matrix.mulVec_mulVec]
  ext i
  have hi := congrFun hvWeighted i
  simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
  simp only [Matrix.mulVec_diagonal, S] at hi
  unfold Lattice.massAction Lattice.inverseSqrtMassAction
  unfold Lattice.inverseSqrtMassAction at hi
  have hs : Real.sqrt (m.mass i) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (m.mass_pos i))
  field_simp [hs] at hi ⊢
  rw [hi]
  ring_nf
  rw [Real.sq_sqrt (le_of_lt (m.mass_pos i))]
  ring

/-- Pointwise action of the transpose periodic difference matrix. -/
theorem transposeDifferenceMatrix_mulVec {N : Nat} [NeZero N]
    (q : Lattice.Configuration N) :
    Matrix.mulVec (Matrix.transpose differenceMatrix) q =
      fun i => q (i - 1) - q i := by
  ext i
  simp only [Matrix.mulVec, dotProduct, differenceMatrix,
    Matrix.transpose_apply, sub_mul]
  rw [Finset.sum_sub_distrib]
  have hshift (j : Lattice.Site N) : i = j + 1 ↔ j = i - 1 := by
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      rw [h]
      simp
  simp_rw [hshift]
  simp

/-- The physical cycle harmonic matrix is the usual nearest-neighbor
Laplacian in periodic coordinates. -/
theorem physicalCycleHarmonicMatrix_mulVec {N : Nat} [NeZero N]
    (q : Lattice.Configuration N) :
    Matrix.mulVec physicalCycleHarmonicMatrix q =
      fun i => 2 * q i - q (i - 1) - q (i + 1) := by
  rw [physicalCycleHarmonicMatrix, ← Matrix.mulVec_mulVec,
    differenceMatrix_mulVec, transposeDifferenceMatrix_mulVec]
  ext i
  simp only [Lattice.forwardDifference]
  ring_nf

/-- Coordinate form of the generalized harmonic eigenvalue equation. -/
theorem generalizedEigenmode_coordinate {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (lambda : Real)
    (q : Lattice.Configuration N)
    (hmode : IsGeneralizedHarmonicEigenmode m lambda q)
    (i : Lattice.Site N) :
    2 * q i - q (i - 1) - q (i + 1) = lambda * m.mass i * q i := by
  have hi := congrFun hmode i
  rw [physicalCycleHarmonicMatrix_mulVec] at hi
  simpa [Lattice.massAction, mul_assoc] using hi

/-- Exact local second-order recurrence. -/
theorem generalizedEigenmode_localRecurrence {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (lambda : Real)
    (q : Lattice.Configuration N)
    (hmode : IsGeneralizedHarmonicEigenmode m lambda q)
    (i : Lattice.Site N) :
    q (i + 1) = (2 - lambda * m.mass i) * q i - q (i - 1) := by
  have hi := generalizedEigenmode_coordinate m lambda q hmode i
  linarith

/-- The one-site `2×2` transfer matrix. -/
def localTransferMatrix {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (lambda : Real)
    (i : Lattice.Site N) : Matrix (Fin 2) (Fin 2) Real :=
  !![2 - lambda * m.mass i, -1;
     1,                         0]

/-- Every local transfer matrix is unimodular. -/
@[simp] theorem det_localTransferMatrix {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (lambda : Real)
    (i : Lattice.Site N) :
    Matrix.det (localTransferMatrix m lambda i) = 1 := by
  simp [localTransferMatrix, Matrix.det_fin_two_of]

/-- Two-component state `(q_i,q_{i-1})`. -/
def transferState {N : Nat} (q : Lattice.Configuration N)
    (i : Lattice.Site N) : Fin 2 → Real :=
  ![q i, q (i - 1)]

/-- One-step propagation identity for the generalized eigenmode. -/
theorem generalizedEigenmode_oneStep {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (lambda : Real)
    (q : Lattice.Configuration N)
    (hmode : IsGeneralizedHarmonicEigenmode m lambda q)
    (i : Lattice.Site N) :
    transferState q (i + 1) =
      Matrix.mulVec (localTransferMatrix m lambda i) (transferState q i) := by
  have hrec := generalizedEigenmode_localRecurrence m lambda q hmode i
  ext r
  fin_cases r
  · simp [transferState, localTransferMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, hrec, sub_eq_add_neg]
  · simp [transferState, localTransferMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

/-- Ordered forward product
`T_{i+n-1} ⋯ T_{i+1} T_i`, totalized at length zero by the identity. -/
def forwardTransferProduct {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (lambda : Real)
    (i : Lattice.Site N) : Nat → Matrix (Fin 2) (Fin 2) Real
  | 0 => 1
  | n + 1 =>
      localTransferMatrix m lambda (i + (n : Lattice.Site N)) *
        forwardTransferProduct m lambda i n

/-- Every finite forward product remains unimodular. -/
@[simp] theorem det_forwardTransferProduct {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (lambda : Real)
    (i : Lattice.Site N) (n : Nat) :
    Matrix.det (forwardTransferProduct m lambda i n) = 1 := by
  induction n with
  | zero => simp [forwardTransferProduct]
  | succ n ih =>
      rw [forwardTransferProduct, Matrix.det_mul,
        det_localTransferMatrix, ih, one_mul]

/-- Exact propagation by the finite ordered transfer product. -/
theorem generalizedEigenmode_forwardPropagation {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (lambda : Real)
    (q : Lattice.Configuration N)
    (hmode : IsGeneralizedHarmonicEigenmode m lambda q)
    (i : Lattice.Site N) (n : Nat) :
    transferState q (i + (n : Lattice.Site N)) =
      Matrix.mulVec (forwardTransferProduct m lambda i n)
        (transferState q i) := by
  induction n with
  | zero => simp [forwardTransferProduct]
  | succ n ih =>
      calc
        transferState q (i + ((n + 1 : Nat) : Lattice.Site N)) =
            transferState q ((i + (n : Lattice.Site N)) + 1) := by
              simp [Nat.cast_add, add_assoc]
        _ = Matrix.mulVec
              (localTransferMatrix m lambda (i + (n : Lattice.Site N)))
              (transferState q (i + (n : Lattice.Site N))) :=
          generalizedEigenmode_oneStep m lambda q hmode _
        _ = Matrix.mulVec
              (localTransferMatrix m lambda (i + (n : Lattice.Site N)))
              (Matrix.mulVec (forwardTransferProduct m lambda i n)
                (transferState q i)) := by rw [ih]
        _ = Matrix.mulVec
              (forwardTransferProduct m lambda i (n + 1))
              (transferState q i) := by
          rw [forwardTransferProduct, Matrix.mulVec_mulVec]

end

end ArchonPhysics.RandomMassHarmonicTransferMatrix
