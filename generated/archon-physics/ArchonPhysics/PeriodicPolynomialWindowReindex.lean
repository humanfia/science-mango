import ArchonPhysics.PolynomialMarkedLegWindowStrongLaw

/-!
# Exact periodic-to-window reindexing for polynomial marked kernels

A cyclic translation first moves an arbitrary finite mass window to the left
block of a `Fin n ⊕ Fin m` decomposition.  The large periodic weighted-cycle
matrix and the block diagonal matrix differ on exactly four cut bonds.  Hence
an entry of a zero-constant polynomial of quotient degree `degree` agrees
exactly with the fixed-window entry whenever all comparison walks of length
strictly less than `degree + 1` avoid those boundary rows.

This is a deterministic finite-volume identity.  It supplies the exact
reindexing bridge required before applying a fixed-window iid strong law; it
does not itself assert that a numerical interval is interior or take an
infinite-volume limit.
-/

open scoped Matrix

namespace ArchonPhysics.PeriodicPolynomialWindowReindex

open ArchonPhysics
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.PolynomialMarkedLegWindowStrongLaw
open ArchonPhysics.RandomMassHarmonicSecondMoment
open ArchonPhysics.RegularizedMarkedLegPolynomialLocality

noncomputable section

/-! ## Cyclic translations and polynomial covariance -/

/-- Translation by `shift` on the periodic lattice. -/
def siteTranslation {N : Nat} [NeZero N] (shift : Lattice.Site N) :
    Equiv.Perm (Lattice.Site N) where
  toFun i := shift + i
  invFun i := i - shift
  left_inv i := by simp [sub_eq_add_neg, add_assoc]
  right_inv i := by simp [sub_eq_add_neg]

/-- Weighted-cycle covariance under a cyclic translation. -/
theorem weightedCycleLaplacian_translate
    {N : Nat} [NeZero N] (w : Lattice.Configuration N)
    (shift i j : Lattice.Site N) :
    weightedCycleLaplacian (fun x ↦ w (siteTranslation shift x)) i j =
      weightedCycleLaplacian w (siteTranslation shift i)
        (siteTranslation shift j) := by
  change weightedCycleLaplacian (fun x ↦ w (shift + x)) i j =
    weightedCycleLaplacian w (shift + i) (shift + j)
  rw [weightedCycleLaplacian_apply, weightedCycleLaplacian_apply]
  have hprev : j = i - 1 ↔ shift + j = shift + i - 1 := by
    constructor <;> intro h
    · rw [h]
      simp [sub_eq_add_neg, add_assoc]
    · apply add_left_cancel (a := shift)
      simpa [sub_eq_add_neg, add_assoc] using h
  simp [hprev, add_assoc]

/-- The induced cyclic translation on `Fin N` coordinates. -/
def finCycleTranslation {N : Nat} [NeZero N] (shift : Fin N) :
    Equiv.Perm (Fin N) :=
  (siteEquivFin N).symm.trans
    ((siteTranslation ((siteEquivFin N).symm shift)).trans (siteEquivFin N))

/-- Pull a finite weight field through a cyclic translation. -/
def translateFinWeights {N : Nat} [NeZero N]
    (w : Fin N → Real) (shift : Fin N) : Fin N → Real :=
  fun i ↦ w (finCycleTranslation shift i)

theorem finWeightedCycleLaplacian_translate
    {N : Nat} [NeZero N] (w : Fin N → Real) (shift i j : Fin N) :
    finWeightedCycleLaplacian (translateFinWeights w shift) i j =
      finWeightedCycleLaplacian w (finCycleTranslation shift i)
        (finCycleTranslation shift j) := by
  unfold finWeightedCycleLaplacian
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  have hweights :
      weightsOfCoordinates (translateFinWeights w shift) =
        fun x ↦ weightsOfCoordinates w
          (siteTranslation ((siteEquivFin N).symm shift) x) := by
    funext x
    simp [weightsOfCoordinates, translateFinWeights, finCycleTranslation]
  rw [hweights, weightedCycleLaplacian_translate]
  simp [finCycleTranslation]

theorem matrix_pow_reindex_apply
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    [DecidableEq iota] [DecidableEq kappa]
    (e : iota ≃ kappa) (M : Matrix iota iota Real)
    (n : Nat) (i j : kappa) :
    (Matrix.reindex e e M ^ n) i j =
      (M ^ n) (e.symm i) (e.symm j) := by
  change ((Matrix.reindexRingEquiv Real e M) ^ n) i j = _
  rw [← map_pow]
  rfl

/-- Zero-constant matrix polynomials commute with a simultaneous row/column
reindexing. -/
theorem zeroConstantMatrixPolynomialUpTo_reindex_apply
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    [DecidableEq iota] [DecidableEq kappa]
    (e : iota ≃ kappa) (M : Matrix iota iota Real)
    (degree : Nat) (coefficient : Nat → Real) (i j : kappa) :
    zeroConstantMatrixPolynomialUpTo degree coefficient
        (Matrix.reindex e e M) i j =
      zeroConstantMatrixPolynomialUpTo degree coefficient M
        (e.symm i) (e.symm j) := by
  unfold zeroConstantMatrixPolynomialUpTo
  simp_rw [Matrix.sum_apply, Matrix.smul_apply,
    matrix_pow_reindex_apply e M]

theorem finWeightedCycleLaplacian_translate_eq_reindex
    {N : Nat} [NeZero N] (w : Fin N → Real) (shift : Fin N) :
    finWeightedCycleLaplacian (translateFinWeights w shift) =
      Matrix.reindex (finCycleTranslation shift).symm
        (finCycleTranslation shift).symm (finWeightedCycleLaplacian w) := by
  ext i j
  rw [finWeightedCycleLaplacian_translate]
  rfl

theorem zeroConstantPolynomial_finWeightedCycle_translate
    {N : Nat} [NeZero N] (w : Fin N → Real) (shift : Fin N)
    (degree : Nat) (coefficient : Nat → Real) (i j : Fin N) :
    zeroConstantMatrixPolynomialUpTo degree coefficient
        (finWeightedCycleLaplacian (translateFinWeights w shift)) i j =
      zeroConstantMatrixPolynomialUpTo degree coefficient
        (finWeightedCycleLaplacian w)
        (finCycleTranslation shift i) (finCycleTranslation shift j) := by
  rw [finWeightedCycleLaplacian_translate_eq_reindex]
  exact zeroConstantMatrixPolynomialUpTo_reindex_apply
    (finCycleTranslation shift).symm (finWeightedCycleLaplacian w)
      degree coefficient i j

/-! ## Exact comparison with a cut block -/

/-- Block diagonal comparison matrix obtained by cutting a periodic cycle. -/
def splitBlockCycleLaplacian {n m : Nat} [NeZero n] [NeZero m]
    (w : Fin (n + m) → Real) :
    Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) Real :=
  Matrix.fromBlocks (finWeightedCycleLaplacian (leftWeights w)) 0 0
    (finWeightedCycleLaplacian (rightWeights w))

/-- A row belongs to the exact boundary perturbation when one of the four
boundary edge vectors is nonzero there. -/
def IsSplitBoundaryRow {n m : Nat} [NeZero n] [NeZero m]
    [NeZero (n + m)] (u : Fin n ⊕ Fin m) : Prop :=
  splitFullEdgeVector (Fin.castAdd m (0 : Fin n)) u ≠ 0 ∨
    splitFullEdgeVector (Fin.natAdd n (0 : Fin m)) u ≠ 0 ∨
    leftBlockEdgeVector (m := m) (0 : Fin n) u ≠ 0 ∨
    rightBlockEdgeVector (n := n) (0 : Fin m) u ≠ 0

/-- The support relation generated jointly by the uncut periodic cycle and
the block-diagonal comparison cycle. -/
def splitComparisonStep {n m : Nat} [NeZero n] [NeZero m]
    [NeZero (n + m)] (w : Fin (n + m) → Real)
    (u v : Fin n ⊕ Fin m) : Prop :=
  splitFinWeightedCycleLaplacian w u v ≠ 0 ∨
    splitBlockCycleLaplacian w u v ≠ 0

/-- A starting row is interior through `radius` when every row reached in
strictly fewer than `radius` comparison steps avoids the four cut bonds. -/
def IsSplitInteriorWithin {n m : Nat} [NeZero n] [NeZero m]
    [NeZero (n + m)] (w : Fin (n + m) → Real)
    (radius : Nat) (start : Fin n ⊕ Fin m) : Prop :=
  ∀ r, r < radius → ∀ u,
    MatrixWalk (splitComparisonStep w) r start u →
      ¬ IsSplitBoundaryRow u

theorem splitFinWeightedCycleLaplacian_apply_eq_block_of_not_boundary
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) → Real) {u : Fin n ⊕ Fin m}
    (hu : ¬ IsSplitBoundaryRow u) (v : Fin n ⊕ Fin m) :
    splitFinWeightedCycleLaplacian w u v =
      splitBlockCycleLaplacian w u v := by
  rw [splitFinWeightedCycleLaplacian_eq_fromBlocks_add_four_boundary]
  unfold splitBlockCycleLaplacian IsSplitBoundaryRow at *
  push Not at hu
  rcases hu with ⟨hfullLeft, hfullRight, hleft, hright⟩
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  rw [hfullLeft, hfullRight, hleft, hright]
  ring

theorem splitFinWeightedCycleLaplacian_supportedOn_comparison
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) → Real) :
    MatrixSupportedOn (splitComparisonStep w)
      (splitFinWeightedCycleLaplacian w) := by
  intro u v huv
  exact Or.inl huv

theorem splitBlockCycleLaplacian_supportedOn_comparison
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) → Real) :
    MatrixSupportedOn (splitComparisonStep w)
      (splitBlockCycleLaplacian w) := by
  intro u v huv
  exact Or.inr huv

theorem zeroConstantMatrixPolynomialUpTo_apply_eq_of_walkLocalAgreement
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {step : iota → iota → Prop} {M M' : Matrix iota iota Real}
    (hM : MatrixSupportedOn step M) (hM' : MatrixSupportedOn step M')
    (degree : Nat) (coefficient : Nat → Real) {i j : iota}
    (hagree : ∀ r, r < degree + 1 → ∀ u v,
      MatrixWalk step r i u → step u v → M u v = M' u v) :
    zeroConstantMatrixPolynomialUpTo degree coefficient M i j =
      zeroConstantMatrixPolynomialUpTo degree coefficient M' i j := by
  unfold zeroConstantMatrixPolynomialUpTo
  rw [Matrix.sum_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  have hnle : n + 1 ≤ degree + 1 :=
    Nat.succ_le_succ (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
  have hpow : (M ^ (n + 1)) i j = (M' ^ (n + 1)) i j :=
    matrix_pow_apply_eq_of_walkLocalAgreement hM hM'
      (fun r hr u v hwalk hstep ↦
        hagree r (lt_of_lt_of_le hr hnle) u v hwalk hstep)
  simp only [Matrix.smul_apply]
  rw [hpow]

theorem fromBlocks_zero_pow_apply_inl_inl
    {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (A : Matrix n n Real) (D : Matrix m m Real)
    (k : Nat) (i j : n) :
    (Matrix.fromBlocks A 0 0 D ^ k) (Sum.inl i) (Sum.inl j) =
      (A ^ k) i j := by
  induction k generalizing j with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
      rw [Fintype.sum_sum_type]
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁,
        Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
      apply Finset.sum_congr rfl
      intro x hx
      rw [ih x]

theorem zeroConstantMatrixPolynomialUpTo_fromBlocks_apply_inl_inl
    {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (A : Matrix n n Real) (D : Matrix m m Real)
    (degree : Nat) (coefficient : Nat → Real) (i j : n) :
    zeroConstantMatrixPolynomialUpTo degree coefficient
        (Matrix.fromBlocks A 0 0 D) (Sum.inl i) (Sum.inl j) =
      zeroConstantMatrixPolynomialUpTo degree coefficient A i j := by
  unfold zeroConstantMatrixPolynomialUpTo
  simp_rw [Matrix.sum_apply, Matrix.smul_apply,
    fromBlocks_zero_pow_apply_inl_inl A D]

/-- Exact fixed-window bridge after the large cycle has been split. -/
theorem splitPeriodicPolynomialKernelEntry_eq_leftWindow
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) → Real)
    (degree : Nat) (coefficient : Nat → Real) (a b : Fin n)
    (hinterior : IsSplitInteriorWithin w (degree + 1) (Sum.inl a)) :
    zeroConstantMatrixPolynomialUpTo degree coefficient
        (splitFinWeightedCycleLaplacian w) (Sum.inl a) (Sum.inl b) =
      zeroConstantMatrixPolynomialUpTo degree coefficient
        (finWeightedCycleLaplacian (leftWeights w)) a b := by
  rw [zeroConstantMatrixPolynomialUpTo_apply_eq_of_walkLocalAgreement
    (splitFinWeightedCycleLaplacian_supportedOn_comparison w)
    (splitBlockCycleLaplacian_supportedOn_comparison w)
    degree coefficient
    (fun r hr u v hwalk _hstep ↦
      splitFinWeightedCycleLaplacian_apply_eq_block_of_not_boundary
        w (hinterior r hr u hwalk) v)]
  exact zeroConstantMatrixPolynomialUpTo_fromBlocks_apply_inl_inl
    (finWeightedCycleLaplacian (leftWeights w))
    (finWeightedCycleLaplacian (rightWeights w))
    degree coefficient a b

/-! ## Arbitrarily translated finite windows -/

/-- The length-`n` cyclic mass window beginning at `shift`. -/
def translatedMassWindow {n m : Nat} [NeZero (n + m)]
    (x : Fin (n + m) → Real) (shift : Fin (n + m)) : Fin n → Real :=
  fun i ↦ x (finCycleTranslation shift (Fin.castAdd m i))

/-- Exact translated fixed-weight-window identity.  The left entry is in the
original large cycle; the right entry is computed only from the translated
length-`n` weight window. -/
theorem periodicPolynomialKernelEntry_eq_translatedWeightWindow
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) → Real) (shift : Fin (n + m))
    (degree : Nat) (coefficient : Nat → Real) (a b : Fin n)
    (hinterior : IsSplitInteriorWithin (translateFinWeights w shift)
      (degree + 1) (Sum.inl a)) :
    zeroConstantMatrixPolynomialUpTo degree coefficient
        (finWeightedCycleLaplacian w)
        (finCycleTranslation shift (Fin.castAdd m a))
        (finCycleTranslation shift (Fin.castAdd m b)) =
      zeroConstantMatrixPolynomialUpTo degree coefficient
        (finWeightedCycleLaplacian
          (leftWeights (translateFinWeights w shift))) a b := by
  symm
  rw [← splitPeriodicPolynomialKernelEntry_eq_leftWindow
    (translateFinWeights w shift) degree coefficient a b hinterior]
  unfold splitFinWeightedCycleLaplacian
  rw [zeroConstantMatrixPolynomialUpTo_reindex_apply
    finSumFinEquiv.symm
    (finWeightedCycleLaplacian (translateFinWeights w shift))]
  simp only [Equiv.symm_symm, finSumFinEquiv_apply_left]
  exact zeroConstantPolynomial_finWeightedCycle_translate
    w shift degree coefficient (Fin.castAdd m a) (Fin.castAdd m b)

/-- Mass-level form used by the fixed-window strong law.  Clipping and taking
reciprocals commute exactly with restriction to the translated window. -/
theorem periodicPolynomialKernelEntry_eq_translatedMassWindow
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (x : Fin (n + m) → Real) (shift : Fin (n + m))
    (degree : Nat) (coefficient : Nat → Real) (a b : Fin n)
    (hinterior : IsSplitInteriorWithin
      (translateFinWeights (inverseClippedWindow x) shift)
      (degree + 1) (Sum.inl a)) :
    zeroConstantMatrixPolynomialUpTo degree coefficient
        (finWeightedCycleLaplacian (inverseClippedWindow x))
        (finCycleTranslation shift (Fin.castAdd m a))
        (finCycleTranslation shift (Fin.castAdd m b)) =
      polynomialWindowKernelEntry degree coefficient a b
        (translatedMassWindow x shift) := by
  have hweights :
      leftWeights (translateFinWeights (inverseClippedWindow x) shift) =
        inverseClippedWindow (translatedMassWindow x shift) := by
    funext i
    rfl
  rw [periodicPolynomialKernelEntry_eq_translatedWeightWindow
    (inverseClippedWindow x) shift degree coefficient a b hinterior]
  unfold polynomialWindowKernelEntry
  rw [hweights]

end
end ArchonPhysics.PeriodicPolynomialWindowReindex
