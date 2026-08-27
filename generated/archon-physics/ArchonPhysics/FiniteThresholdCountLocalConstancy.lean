import ArchonPhysics.RandomMassAcousticCountingComparison
import ArchonPhysics.OrderedSingleModeProjector

/-!
# Local constancy of finite spectral threshold counts

A finite Hermitian threshold count is locally constant at every point which
is not an eigenvalue.  This elementary deterministic bridge turns an
almost-sure fixed-energy characteristic-polynomial certificate into the
pointwise continuity input required by dominated convergence.
-/

namespace ArchonPhysics.FiniteThresholdCountLocalConstancy

open ArchonPhysics
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.RandomMassAcousticCountingComparison
open Filter Set Topology

noncomputable section

/-- A nonzero characteristic-polynomial value excludes every ordered
eigenvalue from the specified threshold. -/
theorem orderedEigenvalue_ne_of_charpoly_eval_ne_zero
    {index : Type*} [Fintype index] [DecidableEq index]
    (A : HermitianMatrix index) (E : Real)
    (hEval : (Matrix.charpoly A.1).eval E ≠ 0)
    (k : Fin (Fintype.card index)) :
    orderedEigenvalue A k ≠ E := by
  intro heq
  have hroot :
      orderedEigenvalue A k ∈
        (Matrix.charpoly A.1).roots := by
    rw [A.2.roots_charpoly_eq_eigenvalues₀]
    simp [orderedEigenvalue]
  have hz :
      (Matrix.charpoly A.1).eval
        (orderedEigenvalue A k) = 0 := by
    simpa [Polynomial.IsRoot] using
      (Polynomial.isRoot_of_mem_roots hroot)
  exact hEval (by simpa [heq] using hz)

/-- If no ordered eigenvalue equals `E`, the complete threshold count agrees
with its value at `E` throughout some neighborhood of `E`. -/
theorem eventually_orderedEigenvalueThresholdCount_eq
    {index : Type*} [Fintype index] [DecidableEq index]
    (A : HermitianMatrix index) (E : Real)
    (hne : ∀ k : Fin (Fintype.card index),
      orderedEigenvalue A k ≠ E) :
    ∀ᶠ x in 𝓝 E,
      orderedEigenvalueThresholdCount A x =
        orderedEigenvalueThresholdCount A E := by
  have hleg (k : Fin (Fintype.card index)) :
      ∀ᶠ x in 𝓝 E,
        (orderedEigenvalue A k ≤ x ↔
          orderedEigenvalue A k ≤ E) := by
    rcases lt_or_gt_of_ne (hne k) with hlt | hgt
    · filter_upwards [Ioi_mem_nhds hlt] with x hx
      constructor <;> intro
      · exact hlt.le
      · exact hx.le
    · filter_upwards [Iio_mem_nhds hgt] with x hx
      constructor <;> intro h
      · exact (not_le_of_gt hx h).elim
      · exact (not_le_of_gt hgt h).elim
  have hall : ∀ᶠ x in 𝓝 E, ∀ k : Fin (Fintype.card index),
      (orderedEigenvalue A k ≤ x ↔ orderedEigenvalue A k ≤ E) :=
    Filter.eventually_all.2 hleg
  filter_upwards [hall] with x hx
  unfold orderedEigenvalueThresholdCount orderedEigenvalueThresholdIndices
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hx k

/-- Real-valued finite threshold counts are continuous at every non-spectral
threshold. -/
theorem continuousAt_orderedEigenvalueThresholdCount
    {index : Type*} [Fintype index] [DecidableEq index]
    (A : HermitianMatrix index) (E : Real)
    (hne : ∀ k : Fin (Fintype.card index),
      orderedEigenvalue A k ≠ E) :
    ContinuousAt
      (fun x : Real => (orderedEigenvalueThresholdCount A x : Real)) E := by
  have hlocal := eventually_orderedEigenvalueThresholdCount_eq A E hne
  apply (continuousAt_const :
    ContinuousAt (fun _ : Real =>
      (orderedEigenvalueThresholdCount A E : Real)) E).congr
  filter_upwards [hlocal] with x hx
  exact_mod_cast hx.symm

/-- Characteristic-polynomial form of local threshold-count continuity. -/
theorem continuousAt_orderedEigenvalueThresholdCount_of_charpoly_eval_ne_zero
    {index : Type*} [Fintype index] [DecidableEq index]
    (A : HermitianMatrix index) (E : Real)
    (hEval : (Matrix.charpoly A.1).eval E ≠ 0) :
    ContinuousAt
      (fun x : Real => (orderedEigenvalueThresholdCount A x : Real)) E := by
  exact continuousAt_orderedEigenvalueThresholdCount A E
    (orderedEigenvalue_ne_of_charpoly_eval_ne_zero A E hEval)

end

end ArchonPhysics.FiniteThresholdCountLocalConstancy
