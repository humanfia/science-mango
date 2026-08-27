import ArchonPhysics.SingleMassThresholdCountSensitivity

/-!
# Finite-volume spectral-count gluing

This module supplies the finite-dimensional gluing layer needed by an
integrated-density-of-states argument.  It proves three deterministic facts.

* The threshold count of a Hermitian block diagonal matrix is the sum of the
  two block counts, including multiplicities.
* A signed real rank-one update changes a threshold count by at most one.
* A finite sum of signed rank-one updates changes a threshold count by at most
  the number of updates.

Consequently, a matrix obtained from two disconnected Hermitian blocks by a
fixed finite list of boundary couplings has a constant spectral-count gluing
defect.  This module does not identify a random periodic chain with such a
block update, split its probability law across the blocks, or prove an IDS
limit; those are separate model-specific and probabilistic steps.
-/

namespace ArchonPhysics.FiniteVolumeSpectralCountGluing

open ArchonPhysics
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.RandomMassAcousticCountingComparison
open ArchonPhysics.SingleMassThresholdCountSensitivity

noncomputable section

/-- The complete ordered Hermitian threshold count equals the cardinality of
the corresponding real characteristic-root submultiset. -/
theorem orderedEigenvalueThresholdCount_eq_card_filter_roots
    {index : Type*} [Fintype index] [DecidableEq index]
    (A : Matrix index index Real) (hA : A.IsHermitian) (E : Real) :
    orderedEigenvalueThresholdCount ⟨A, hA⟩ E =
      (A.charpoly.roots.filter fun x => x ≤ E).card := by
  have hroots : A.charpoly.roots =
      Multiset.map hA.eigenvalues₀ Finset.univ.val := by
    simpa using hA.roots_charpoly_eq_eigenvalues₀
  unfold orderedEigenvalueThresholdCount orderedEigenvalueThresholdIndices
  rw [hroots, Finset.card_def, Finset.filter_val, Multiset.filter_map,
    Multiset.card_map]
  rfl

/-- Threshold counts are exactly additive under a two-block Hermitian direct
sum.  The proof passes through characteristic roots, so multiplicities and
eigenvalues equal to the threshold are retained. -/
theorem orderedEigenvalueThresholdCount_fromBlocks_zero
    {left right : Type*}
    [Fintype left] [DecidableEq left] [Fintype right] [DecidableEq right]
    (A : Matrix left left Real) (B : Matrix right right Real)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (E : Real) :
    orderedEigenvalueThresholdCount
        ⟨Matrix.fromBlocks A 0 0 B, hA.fromBlocks (by simp) hB⟩ E =
      orderedEigenvalueThresholdCount ⟨A, hA⟩ E +
        orderedEigenvalueThresholdCount ⟨B, hB⟩ E := by
  rw [orderedEigenvalueThresholdCount_eq_card_filter_roots,
    orderedEigenvalueThresholdCount_eq_card_filter_roots,
    orderedEigenvalueThresholdCount_eq_card_filter_roots]
  rw [Matrix.charpoly_fromBlocks_zero₁₂,
    Polynomial.roots_mul
      (mul_ne_zero A.charpoly_monic.ne_zero B.charpoly_monic.ne_zero)]
  simp

/-- The Hermitian direct sum of two finite real Hermitian matrices. -/
def blockDiagonalHermitian
    {left right : Type*} [Fintype left] [Fintype right]
    (A : HermitianMatrix left) (B : HermitianMatrix right) :
    HermitianMatrix (left ⊕ right) :=
  ⟨Matrix.fromBlocks A.1 0 0 B.1, A.2.fromBlocks (by simp) B.2⟩

/-- Subtype-packaged form of exact block-diagonal threshold-count
additivity. -/
theorem orderedEigenvalueThresholdCount_blockDiagonal_eq_add
    {left right : Type*}
    [Fintype left] [DecidableEq left] [Fintype right] [DecidableEq right]
    (A : HermitianMatrix left) (B : HermitianMatrix right) (E : Real) :
    orderedEigenvalueThresholdCount (blockDiagonalHermitian A B) E =
      orderedEigenvalueThresholdCount A E +
        orderedEigenvalueThresholdCount B E := by
  exact orderedEigenvalueThresholdCount_fromBlocks_zero
    A.1 B.1 A.2 B.2 E

/-- A signed rank-one Hermitian update changes a complete threshold count by
at most one, without assuming the sign of its coefficient. -/
theorem orderedEigenvalueThresholdCount_signedRankOne_sensitivity
    {index : Type*} [Fintype index] [DecidableEq index]
    (A C : Matrix index index Real)
    (hA : A.IsHermitian) (hC : C.IsHermitian)
    (c : Real) (v : index → Real)
    (hupdate : C = A + c • Matrix.vecMulVec v v) (E : Real) :
    orderedEigenvalueThresholdCount ⟨C, hC⟩ E ≤
        orderedEigenvalueThresholdCount ⟨A, hA⟩ E + 1 ∧
      orderedEigenvalueThresholdCount ⟨A, hA⟩ E ≤
        orderedEigenvalueThresholdCount ⟨C, hC⟩ E + 1 := by
  by_cases hc : 0 ≤ c
  · obtain ⟨hCA, hAC⟩ :=
      orderedEigenvalueThresholdCount_positive_rankOne_update_sandwich
        A C hA hC c hc v hupdate E
    exact ⟨hCA.trans (Nat.le_add_right _ _), hAC⟩
  · have hcneg : 0 ≤ -c := neg_nonneg.mpr (le_of_not_ge hc)
    have hreverse : A = C + (-c) • Matrix.vecMulVec v v := by
      rw [hupdate]
      simp only [neg_smul]
      abel
    obtain ⟨hAC, hCA⟩ :=
      orderedEigenvalueThresholdCount_positive_rankOne_update_sandwich
        C A hC hA (-c) hcneg v hreverse E
    exact ⟨hCA, hAC.trans (Nat.le_add_right _ _)⟩

/-- A real scalar multiple of a square outer product is Hermitian. -/
theorem isHermitian_smul_vecMulVec_self
    {index : Type*} (c : Real) (v : index → Real) :
    (c • Matrix.vecMulVec v v).IsHermitian := by
  rw [Matrix.IsHermitian]
  simp

/-- A finite sum of signed square outer products. -/
def rankOneUpdateSum
    {label index : Type*} [Fintype index]
    (s : Finset label) (c : label → Real) (v : label → index → Real) :
    Matrix index index Real :=
  ∑ i ∈ s, c i • Matrix.vecMulVec (v i) (v i)

/-- Every finite signed square-outer-product sum is Hermitian. -/
theorem rankOneUpdateSum_isHermitian
    {label index : Type*} [Fintype index]
    (s : Finset label) (c : label → Real) (v : label → index → Real) :
    (rankOneUpdateSum s c v).IsHermitian := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rankOneUpdateSum]
  | @insert i s hi ih =>
      rw [rankOneUpdateSum, Finset.sum_insert hi]
      exact (isHermitian_smul_vecMulVec_self (c i) (v i)).add ih

/-- Add a finite signed rank-one sum to a packaged Hermitian matrix. -/
def rankOneUpdatedHermitian
    {label index : Type*} [Fintype index]
    (A : HermitianMatrix index) (s : Finset label)
    (c : label → Real) (v : label → index → Real) :
    HermitianMatrix index :=
  ⟨(fun i j ↦ A.1 i j + rankOneUpdateSum s c v i j),
    A.2.add (rankOneUpdateSum_isHermitian s c v)⟩

/-- A finite list of signed rank-one updates changes a complete threshold
count by at most the number of listed updates. -/
theorem orderedEigenvalueThresholdCount_rankOneUpdateSum_sensitivity
    {label index : Type*} [Fintype index] [DecidableEq index]
    (A : HermitianMatrix index) (s : Finset label)
    (c : label → Real) (v : label → index → Real) (E : Real) :
    orderedEigenvalueThresholdCount (rankOneUpdatedHermitian A s c v) E ≤
        orderedEigenvalueThresholdCount A E + s.card ∧
      orderedEigenvalueThresholdCount A E ≤
        orderedEigenvalueThresholdCount (rankOneUpdatedHermitian A s c v) E + s.card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have heq : rankOneUpdatedHermitian A ∅ c v = A := by
        apply Subtype.ext
        simp [rankOneUpdatedHermitian, rankOneUpdateSum]
      rw [heq]
      simp
  | @insert i s hi ih =>
      have hstep :
          orderedEigenvalueThresholdCount
              (rankOneUpdatedHermitian A (insert i s) c v) E ≤
                orderedEigenvalueThresholdCount
                  (rankOneUpdatedHermitian A s c v) E + 1 ∧
            orderedEigenvalueThresholdCount
                (rankOneUpdatedHermitian A s c v) E ≤
              orderedEigenvalueThresholdCount
                (rankOneUpdatedHermitian A (insert i s) c v) E + 1 := by
        simpa only [Subtype.coe_eta] using
        orderedEigenvalueThresholdCount_signedRankOne_sensitivity
          (rankOneUpdatedHermitian A s c v).1
          (rankOneUpdatedHermitian A (insert i s) c v).1
          (rankOneUpdatedHermitian A s c v).2
          (rankOneUpdatedHermitian A (insert i s) c v).2
          (c i) (v i) (by
            ext p q
            change A.1 p q + rankOneUpdateSum (insert i s) c v p q =
              A.1 p q + rankOneUpdateSum s c v p q +
                (c i • Matrix.vecMulVec (v i) (v i)) p q
            rw [rankOneUpdateSum, Finset.sum_insert hi]
            simp only [Matrix.add_apply]
            abel) E
      rw [Finset.card_insert_of_notMem hi]
      omega

/-- Gluing two exact Hermitian blocks with finitely many signed rank-one
boundary terms has threshold-count defect at most the number of terms. -/
theorem orderedEigenvalueThresholdCount_block_rankOneUpdateSum_sensitivity
    {label left right : Type*}
    [Fintype left] [DecidableEq left] [Fintype right] [DecidableEq right]
    (A : HermitianMatrix left) (B : HermitianMatrix right)
    (s : Finset label) (c : label → Real)
    (v : label → left ⊕ right → Real) (E : Real) :
    orderedEigenvalueThresholdCount
        (rankOneUpdatedHermitian (blockDiagonalHermitian A B) s c v) E ≤
          orderedEigenvalueThresholdCount A E +
            orderedEigenvalueThresholdCount B E + s.card ∧
      orderedEigenvalueThresholdCount A E +
          orderedEigenvalueThresholdCount B E ≤
        orderedEigenvalueThresholdCount
            (rankOneUpdatedHermitian (blockDiagonalHermitian A B) s c v) E +
          s.card := by
  have h := orderedEigenvalueThresholdCount_rankOneUpdateSum_sensitivity
    (blockDiagonalHermitian A B) s c v E
  rw [orderedEigenvalueThresholdCount_blockDiagonal_eq_add] at h
  exact h

end

end ArchonPhysics.FiniteVolumeSpectralCountGluing
