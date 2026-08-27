import ArchonPhysics.FiniteVolumeSpectralCountGluing
import ArchonPhysics.PathLaplacianResultant
import ArchonPhysics.SingleMassRankOnePerturbation

namespace ArchonPhysics.PeriodicWeightedCycleBlockGluing

open ArchonPhysics
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.FiniteVolumeSpectralCountGluing
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.RandomMassAcousticCountingComparison
open ArchonPhysics.SingleMassRankOnePerturbation

noncomputable section

def finCycleEdgeVector {N : Nat} [NeZero N] (j : Fin N) : Fin N → Real :=
  fun i ↦ cycleMassPerturbationVector ((siteEquivFin N).symm j)
    ((siteEquivFin N).symm i)

theorem val_siteEquivFin_symm {N : Nat} [NeZero N] (i : Fin N) :
    ((siteEquivFin N).symm i).val = i.val := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ N => rfl

theorem finCycle_successor_iff_of_ne_zero {N : Nat} [NeZero N]
    (i j : Fin N) (hj : j ≠ 0) :
    (siteEquivFin N).symm j = (siteEquivFin N).symm i + 1 ↔
      j.val = i.val + 1 := by
  have hN : 1 < N := by
    by_contra hle
    have hjval : j.val = 0 := by omega
    exact hj (Fin.ext hjval)
  have hone : (1 : ZMod N).val = 1 := by
    simpa using (ZMod.val_natCast_of_lt (n := N) (a := 1) hN)
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    rw [val_siteEquivFin_symm, ZMod.val_add,
      val_siteEquivFin_symm, hone] at hv
    by_cases hi : i.val + 1 < N
    · simpa [Nat.mod_eq_of_lt hi] using hv
    · have hi_eq : i.val + 1 = N := by omega
      rw [hi_eq, Nat.mod_self] at hv
      have hjzero : j = 0 := Fin.ext hv
      exact (hj hjzero).elim
  · intro h
    apply ZMod.val_injective N
    rw [val_siteEquivFin_symm, ZMod.val_add,
      val_siteEquivFin_symm, hone]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact h

/-- The actual weighted cycle Laplacian reindexed from `ZMod N` to `Fin N`. -/
def finWeightedCycleLaplacian {N : Nat} [NeZero N] (w : Fin N → Real) :
    Matrix (Fin N) (Fin N) Real :=
  Matrix.reindex (siteEquivFin N) (siteEquivFin N)
    (weightedCycleLaplacian (weightsOfCoordinates w))

/-- Outer-product expansion after the explicit `ZMod`-to-`Fin` reindexing. -/
theorem finWeightedCycleLaplacian_eq_sum_rankOne {N : Nat} [NeZero N]
    (w : Fin N → Real) :
    finWeightedCycleLaplacian w =
      ∑ j : Fin N, w j • Matrix.vecMulVec
        (finCycleEdgeVector j) (finCycleEdgeVector j) := by
  rw [finWeightedCycleLaplacian,
    weightedCycleLaplacian_eq_sum_rankOne]
  ext p q
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
    weightsOfCoordinates]
  symm
  apply Fintype.sum_equiv (siteEquivFin N).symm
  intro j
  simp [finCycleEdgeVector]


theorem finCycleEdgeVector_apply_of_ne_zero {N : Nat} [NeZero N]
    (i j : Fin N) (hj : j ≠ 0) :
    finCycleEdgeVector j i =
      (if j.val = i.val + 1 then 1 else 0) - (if j = i then 1 else 0) := by
  unfold finCycleEdgeVector cycleMassPerturbationVector differenceMatrix
  rw [if_congr (finCycle_successor_iff_of_ne_zero i j hj) rfl rfl]
  simp

/-- A full-chain edge vector after splitting `Fin (n+m)` into two blocks. -/
def splitFullEdgeVector {n m : Nat} [NeZero (n + m)]
    (j : Fin (n + m)) : Fin n ⊕ Fin m → Real :=
  fun x ↦ finCycleEdgeVector j (finSumFinEquiv x)

/-- A left-block cycle edge embedded by zero extension. -/
def leftBlockEdgeVector {n m : Nat} [NeZero n] (j : Fin n) :
    Fin n ⊕ Fin m → Real :=
  Sum.elim (finCycleEdgeVector j) (fun _ ↦ 0)

/-- A right-block cycle edge embedded by zero extension. -/
def rightBlockEdgeVector {n m : Nat} [NeZero m] (j : Fin m) :
    Fin n ⊕ Fin m → Real :=
  Sum.elim (fun _ ↦ 0) (finCycleEdgeVector j)

/-- Every non-wrap left edge is unchanged by splitting the large cycle. -/
theorem splitFullEdgeVector_castAdd_of_ne_zero
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (j : Fin n) (hj : j ≠ 0) :
    splitFullEdgeVector (Fin.castAdd m j) =
      leftBlockEdgeVector (m := m) j := by
  funext x
  have hjbig : Fin.castAdd m j ≠ 0 := by
    intro h
    apply hj
    apply Fin.ext
    simpa using congrArg Fin.val h
  cases x with
  | inl i =>
      rw [splitFullEdgeVector, leftBlockEdgeVector, Sum.elim_inl,
        finSumFinEquiv_apply_left,
        finCycleEdgeVector_apply_of_ne_zero _ _ hjbig,
        finCycleEdgeVector_apply_of_ne_zero _ _ hj]
      simp only [Fin.val_castAdd, Fin.castAdd_inj]
  | inr i =>
      rw [splitFullEdgeVector, leftBlockEdgeVector, Sum.elim_inr,
        finSumFinEquiv_apply_right,
        finCycleEdgeVector_apply_of_ne_zero _ _ hjbig]
      simp only [Fin.val_castAdd, Fin.val_natAdd]
      have hsucc : ¬j.val = n + i.val + 1 := by omega
      have heq : Fin.castAdd m j ≠ Fin.natAdd n i := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
      rw [if_neg hsucc, if_neg heq]
      simp

/-- Every non-wrap right edge is unchanged by splitting the large cycle. -/
theorem splitFullEdgeVector_natAdd_of_ne_zero
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (j : Fin m) (hj : j ≠ 0) :
    splitFullEdgeVector (Fin.natAdd n j) =
      rightBlockEdgeVector (n := n) j := by
  funext x
  have hjbig : Fin.natAdd n j ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_zero] at hv
    have hn : 0 < n := NeZero.pos n
    omega
  cases x with
  | inl i =>
      rw [splitFullEdgeVector, rightBlockEdgeVector, Sum.elim_inl,
        finSumFinEquiv_apply_left,
        finCycleEdgeVector_apply_of_ne_zero _ _ hjbig]
      simp only [Fin.val_castAdd, Fin.val_natAdd]
      have hjval : j.val ≠ 0 := by
        intro h
        apply hj
        exact Fin.ext h
      have hsucc : ¬n + j.val = i.val + 1 := by omega
      have heq : Fin.natAdd n j ≠ Fin.castAdd m i := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
        omega
      rw [if_neg hsucc, if_neg heq]
      simp
  | inr i =>
      rw [splitFullEdgeVector, rightBlockEdgeVector, Sum.elim_inr,
        finSumFinEquiv_apply_right,
        finCycleEdgeVector_apply_of_ne_zero _ _ hjbig,
        finCycleEdgeVector_apply_of_ne_zero _ _ hj]
      simp only [Fin.val_natAdd]
      have hsucc : n + j.val = n + i.val + 1 ↔ j.val = i.val + 1 := by
        omega
      simp only [hsucc, Fin.natAdd_inj]


/-- Restriction of a length-`n+m` weight field to the left block. -/
def leftWeights {n m : Nat} (w : Fin (n + m) → Real) : Fin n → Real :=
  fun i ↦ w (Fin.castAdd m i)

/-- Restriction of a length-`n+m` weight field to the right block. -/
def rightWeights {n m : Nat} (w : Fin (n + m) → Real) : Fin m → Real :=
  fun i ↦ w (Fin.natAdd n i)

/-- The large reindexed cycle, further split into left and right site blocks. -/
def splitFinWeightedCycleLaplacian {n m : Nat} [NeZero (n + m)]
    (w : Fin (n + m) → Real) :
    Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) Real :=
  Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
    (finWeightedCycleLaplacian w)

/-- Outer-product expansion of the large cycle in split coordinates. -/
theorem splitFinWeightedCycleLaplacian_eq_sum_rankOne
    {n m : Nat} [NeZero (n + m)] (w : Fin (n + m) → Real) :
    splitFinWeightedCycleLaplacian w =
      ∑ j : Fin (n + m), w j • Matrix.vecMulVec
        (splitFullEdgeVector j) (splitFullEdgeVector j) := by
  rw [splitFinWeightedCycleLaplacian,
    finWeightedCycleLaplacian_eq_sum_rankOne]
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  rfl

/-- The direct sum of the two small cycles is the sum of their zero-extended
edge outer products. -/
theorem fromBlocks_finWeightedCycleLaplacian_eq_edgeSums
    {n m : Nat} [NeZero n] [NeZero m] (w : Fin (n + m) → Real) :
    Matrix.fromBlocks (finWeightedCycleLaplacian (leftWeights w)) 0 0
        (finWeightedCycleLaplacian (rightWeights w)) =
      (∑ j : Fin n, leftWeights w j • Matrix.vecMulVec
        (leftBlockEdgeVector (m := m) j) (leftBlockEdgeVector (m := m) j)) +
      (∑ j : Fin m, rightWeights w j • Matrix.vecMulVec
        (rightBlockEdgeVector (n := n) j) (rightBlockEdgeVector (n := n) j)) := by
  rw [finWeightedCycleLaplacian_eq_sum_rankOne,
    finWeightedCycleLaplacian_eq_sum_rankOne]
  ext x y
  cases x <;> cases y <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
      Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, leftBlockEdgeVector,
      rightBlockEdgeVector, Sum.elim_inl, Sum.elim_inr, zero_mul, mul_zero,
      Finset.sum_const_zero, add_zero, zero_add]
/-- Splitting a periodic weighted cycle replaces exactly two wrap edges by two
cross-block edges.  Thus the actual length-`n+m` matrix is the block diagonal
of the two actual smaller cycles plus four signed rank-one boundary terms. -/
theorem splitFinWeightedCycleLaplacian_eq_fromBlocks_add_four_boundary
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) → Real) :
    splitFinWeightedCycleLaplacian w =
      Matrix.fromBlocks (finWeightedCycleLaplacian (leftWeights w)) 0 0
        (finWeightedCycleLaplacian (rightWeights w)) +
      w (Fin.castAdd m (0 : Fin n)) • Matrix.vecMulVec
        (splitFullEdgeVector (Fin.castAdd m (0 : Fin n)))
        (splitFullEdgeVector (Fin.castAdd m (0 : Fin n))) +
      w (Fin.natAdd n (0 : Fin m)) • Matrix.vecMulVec
        (splitFullEdgeVector (Fin.natAdd n (0 : Fin m)))
        (splitFullEdgeVector (Fin.natAdd n (0 : Fin m))) -
      leftWeights w 0 • Matrix.vecMulVec
        (leftBlockEdgeVector (m := m) 0) (leftBlockEdgeVector (m := m) 0) -
      rightWeights w 0 • Matrix.vecMulVec
        (rightBlockEdgeVector (n := n) 0) (rightBlockEdgeVector (n := n) 0) := by
  let F : Fin (n + m) → Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) Real :=
    fun j ↦ w j • Matrix.vecMulVec
      (splitFullEdgeVector j) (splitFullEdgeVector j)
  let L : Fin n → Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) Real :=
    fun j ↦ leftWeights w j • Matrix.vecMulVec
      (leftBlockEdgeVector (m := m) j) (leftBlockEdgeVector (m := m) j)
  let R : Fin m → Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) Real :=
    fun j ↦ rightWeights w j • Matrix.vecMulVec
      (rightBlockEdgeVector (n := n) j) (rightBlockEdgeVector (n := n) j)
  have hfullSplit :
      (∑ j, F j) =
        (∑ i : Fin n, F (Fin.castAdd m i)) +
          ∑ i : Fin m, F (Fin.natAdd n i) := by
    calc
      (∑ j, F j) = ∑ x : Fin n ⊕ Fin m, F (finSumFinEquiv x) :=
        (Equiv.sum_comp finSumFinEquiv F).symm
      _ = (∑ i : Fin n, F (finSumFinEquiv (Sum.inl i))) +
          ∑ i : Fin m, F (finSumFinEquiv (Sum.inr i)) :=
        Fintype.sum_sum_type _
      _ = (∑ i : Fin n, F (Fin.castAdd m i)) +
          ∑ i : Fin m, F (Fin.natAdd n i) := by
        simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  have hleftInternal :
      (∑ i : Fin n, F (Fin.castAdd m i)) =
        F (Fin.castAdd m (0 : Fin n)) +
          ∑ i ∈ (Finset.univ.erase (0 : Fin n)), L i := by
    calc
      (∑ i : Fin n, F (Fin.castAdd m i)) =
          ∑ i ∈ Finset.univ, F (Fin.castAdd m i) := rfl
      _ = F (Fin.castAdd m (0 : Fin n)) +
          ∑ i ∈ Finset.univ.erase (0 : Fin n), F (Fin.castAdd m i) :=
        (Finset.add_sum_erase Finset.univ
          (fun i ↦ F (Fin.castAdd m i)) (Finset.mem_univ 0)).symm
      _ = F (Fin.castAdd m (0 : Fin n)) +
          ∑ i ∈ Finset.univ.erase (0 : Fin n), L i := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        have hi0 : i ≠ 0 := Finset.ne_of_mem_erase hi
        dsimp only [F, L, leftWeights]
        rw [splitFullEdgeVector_castAdd_of_ne_zero i hi0]
  have hrightInternal :
      (∑ i : Fin m, F (Fin.natAdd n i)) =
        F (Fin.natAdd n (0 : Fin m)) +
          ∑ i ∈ (Finset.univ.erase (0 : Fin m)), R i := by
    calc
      (∑ i : Fin m, F (Fin.natAdd n i)) =
          ∑ i ∈ Finset.univ, F (Fin.natAdd n i) := rfl
      _ = F (Fin.natAdd n (0 : Fin m)) +
          ∑ i ∈ Finset.univ.erase (0 : Fin m), F (Fin.natAdd n i) :=
        (Finset.add_sum_erase Finset.univ
          (fun i ↦ F (Fin.natAdd n i)) (Finset.mem_univ 0)).symm
      _ = F (Fin.natAdd n (0 : Fin m)) +
          ∑ i ∈ Finset.univ.erase (0 : Fin m), R i := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        have hi0 : i ≠ 0 := Finset.ne_of_mem_erase hi
        dsimp only [F, R, rightWeights]
        rw [splitFullEdgeVector_natAdd_of_ne_zero i hi0]
  have hleftBlock :
      (∑ i : Fin n, L i) = L 0 +
        ∑ i ∈ (Finset.univ.erase (0 : Fin n)), L i := by
    exact (Finset.add_sum_erase Finset.univ L (Finset.mem_univ 0)).symm
  have hrightBlock :
      (∑ i : Fin m, R i) = R 0 +
        ∑ i ∈ (Finset.univ.erase (0 : Fin m)), R i := by
    exact (Finset.add_sum_erase Finset.univ R (Finset.mem_univ 0)).symm
  rw [splitFinWeightedCycleLaplacian_eq_sum_rankOne,
    fromBlocks_finWeightedCycleLaplacian_eq_edgeSums]
  change (∑ j, F j) = (∑ i, L i) + (∑ i, R i) +
    F (Fin.castAdd m 0) + F (Fin.natAdd n 0) - L 0 - R 0
  rw [hfullSplit, hleftInternal, hrightInternal, hleftBlock, hrightBlock]
  abel


/-- Hermitian packaging of the explicitly reindexed weighted cycle. -/
def finWeightedCycleHermitian {N : Nat} [NeZero N] (w : Fin N → Real) :
    HermitianMatrix (Fin N) :=
  ⟨finWeightedCycleLaplacian w,
    (ArchonPhysics.PathLaplacianResultant.weightedCycleLaplacian_isHermitian
      (weightsOfCoordinates w)).reindex (siteEquivFin N)⟩

/-- Hermitian packaging of the large cycle in split coordinates. -/
def splitFinWeightedCycleHermitian {n m : Nat} [NeZero (n + m)]
    (w : Fin (n + m) → Real) : HermitianMatrix (Fin n ⊕ Fin m) :=
  ⟨splitFinWeightedCycleLaplacian w,
    (finWeightedCycleHermitian w).2.reindex finSumFinEquiv.symm⟩

/-- The four signed coefficients: add the two full-chain boundary bonds and
remove the two small-cycle wrap bonds. -/
def boundaryCoefficients {n m : Nat} [NeZero n] [NeZero m]
    (w : Fin (n + m) → Real) : Fin 4 → Real :=
  ![w (Fin.castAdd m (0 : Fin n)), w (Fin.natAdd n (0 : Fin m)),
    -leftWeights w 0, -rightWeights w 0]

/-- The four boundary bond vectors paired with `boundaryCoefficients`. -/
def boundaryVectors {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)] :
    Fin 4 → (Fin n ⊕ Fin m → Real) :=
  ![splitFullEdgeVector (Fin.castAdd m (0 : Fin n)),
    splitFullEdgeVector (Fin.natAdd n (0 : Fin m)),
    leftBlockEdgeVector (m := m) 0, rightBlockEdgeVector (n := n) 0]

/-- The exact four-bond decomposition in the generic finite gluing package. -/
theorem splitFinWeightedCycleHermitian_eq_rankOneUpdated_blockDiagonal
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) → Real) :
    splitFinWeightedCycleHermitian w =
      FiniteVolumeSpectralCountGluing.rankOneUpdatedHermitian
        (FiniteVolumeSpectralCountGluing.blockDiagonalHermitian
          (finWeightedCycleHermitian (leftWeights w))
          (finWeightedCycleHermitian (rightWeights w)))
        Finset.univ (boundaryCoefficients w) boundaryVectors := by
  apply Subtype.ext
  change splitFinWeightedCycleLaplacian w = _
  rw [splitFinWeightedCycleLaplacian_eq_fromBlocks_add_four_boundary]
  ext x y
  simp [FiniteVolumeSpectralCountGluing.rankOneUpdatedHermitian,
    FiniteVolumeSpectralCountGluing.blockDiagonalHermitian,
    FiniteVolumeSpectralCountGluing.rankOneUpdateSum, Fin.sum_univ_four,
    finWeightedCycleHermitian, boundaryCoefficients, boundaryVectors,
    Matrix.vecMulVec_apply] ; ring

/-- Model-specific finite-volume gluing: for every sample and threshold, the
large periodic-chain eigenvalue count differs from the sum of the two smaller
periodic-chain counts by at most four. -/
theorem splitFinWeightedCycle_thresholdCount_defect_le_four
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) → Real) (E : Real) :
    orderedEigenvalueThresholdCount (splitFinWeightedCycleHermitian w) E ≤
        orderedEigenvalueThresholdCount
            (finWeightedCycleHermitian (leftWeights w)) E +
          orderedEigenvalueThresholdCount
            (finWeightedCycleHermitian (rightWeights w)) E + 4 ∧
      orderedEigenvalueThresholdCount
            (finWeightedCycleHermitian (leftWeights w)) E +
          orderedEigenvalueThresholdCount
            (finWeightedCycleHermitian (rightWeights w)) E ≤
        orderedEigenvalueThresholdCount (splitFinWeightedCycleHermitian w) E + 4 := by
  rw [splitFinWeightedCycleHermitian_eq_rankOneUpdated_blockDiagonal]
  simpa using
    (orderedEigenvalueThresholdCount_block_rankOneUpdateSum_sensitivity
        (finWeightedCycleHermitian (leftWeights w))
        (finWeightedCycleHermitian (rightWeights w))
        (Finset.univ : Finset (Fin 4)) (boundaryCoefficients w)
        boundaryVectors E)


end
end ArchonPhysics.PeriodicWeightedCycleBlockGluing
