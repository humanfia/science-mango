import ArchonPhysics.MeasurableOrderedSpectrum
import ArchonPhysics.OrderedSpectrumWeylAll

/-!
# Unconditional continuity of the full ordered Hermitian spectrum

The all-index Weyl bound is transported from self-adjoint operators on
Euclidean space to real Hermitian matrices.  It proves the previously
isolated `OrderedSpectrumContinuous` bridge and removes that hypothesis from
the measurable ordered-spectrum consumers provided here.
-/

namespace ArchonPhysics.OrderedSpectrumContinuity

open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSpectrumWeyl
open Module RCLike InnerProductSpace

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix form of Weyl's perturbation bound for every decreasing Hermitian
eigenvalue.  The right side is the operator norm of the matrix difference. -/
theorem abs_orderedEigenvalue_sub_le_clmNorm
    (A B : Matrix ι ι ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (k : Fin (Fintype.card ι)) :
    |orderedEigenvalue ⟨A, hA⟩ k - orderedEigenvalue ⟨B, hB⟩ k| ≤
      ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι)) (A - B)‖ := by
  let TA := Matrix.toEuclideanLin (𝕜 := ℝ) A
  let TB := Matrix.toEuclideanLin (𝕜 := ℝ) B
  have hTA : TA.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hTB : TB.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  have h := abs_ordered_eigenvalue_sub_le_norm hTA hTB
    (Fintype.card ι) finrank_euclideanSpace k
  convert h using 1
  · simp [orderedEigenvalue, Matrix.IsHermitian.eigenvalues₀, TA, TB]
  · apply congrArg norm
    apply ContinuousLinearMap.ext
    intro x
    change (Matrix.toEuclideanLin (𝕜 := ℝ) (A - B)) x =
      (((hTA.sub hTB).toSelfAdjoint :
        EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) x)
    rw [(hTA.sub hTB).coe_toSelfAdjoint]
    simp [TA, TB]

/-- Every decreasing Hermitian eigenvalue is continuous in the entrywise
finite-matrix topology. -/
theorem continuous_orderedEigenvalue (k : Fin (Fintype.card ι)) :
    Continuous fun A : HermitianMatrix ι => orderedEigenvalue A k := by
  let L : Matrix ι ι ℝ →ₗ[ℝ]
      (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :=
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι)).toAlgEquiv.toLinearEquiv.toLinearMap
  have hL : Continuous L := L.continuous_of_finiteDimensional
  have hg : Continuous fun A : HermitianMatrix ι => L A.1 :=
    hL.comp continuous_subtype_val
  rw [Metric.continuous_iff]
  intro B ε hε
  obtain ⟨delta, hdelta, hclose⟩ :=
    (Metric.continuousAt_iff.mp hg.continuousAt) ε hε
  refine ⟨delta, hdelta, fun A hAB => ?_⟩
  apply lt_of_le_of_lt ?_ (hclose hAB)
  rw [Real.dist_eq]
  calc
    |orderedEigenvalue A k - orderedEigenvalue B k| ≤
        ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι)) (A.1 - B.1)‖ :=
      abs_orderedEigenvalue_sub_le_clmNorm A.1 B.1 A.2 B.2 k
    _ = ‖L (A.1 - B.1)‖ := rfl
    _ = ‖L A.1 - L B.1‖ := congrArg norm (L.map_sub A.1 B.1)
    _ = dist (L A.1) (L B.1) := by rw [dist_eq_norm]

/-- The full ordered-spectrum continuity bridge, now proved without an
assumption. -/
theorem orderedSpectrumContinuous : OrderedSpectrumContinuous ι :=
  fun k => continuous_orderedEigenvalue k

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A measurable Hermitian sample has an unconditionally measurable full
ordered eigenvalue vector. -/
theorem measurable_orderedEigenvalues_unconditional
    (sample : Omega → HermitianMatrix ι) (hsample : Measurable sample) :
    Measurable fun omega => orderedEigenvalues (sample omega) :=
  measurable_orderedEigenvalues orderedSpectrumContinuous sample hsample

/-- Ordered square-root frequencies are unconditionally measurable. -/
theorem measurable_orderedModeFrequencies_unconditional
    (sample : Omega → HermitianMatrix ι) (hsample : Measurable sample) :
    Measurable fun omega k => orderedModeFrequency (sample omega) k :=
  measurable_orderedModeFrequencies orderedSpectrumContinuous sample hsample

/-- Positive-mode membership is an unconditionally measurable event. -/
theorem measurableSet_mem_positiveModeIndices_unconditional
    (sample : Omega → HermitianMatrix ι) (hsample : Measurable sample)
    (k : Fin (Fintype.card ι)) :
    MeasurableSet {omega | k ∈ positiveModeIndices (sample omega)} :=
  measurableSet_mem_positiveModeIndices orderedSpectrumContinuous sample hsample k

/-- The complete ordered squared harmonic spectrum is measurable without a
spectral-continuity parameter. -/
theorem measurable_harmonicOrderedEigenvalues_unconditional
    {N : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (hmass : ∀ i, Measurable fun omega => (massSample omega).mass i) :
    Measurable fun omega k => harmonicOrderedEigenvalue massSample omega k :=
  measurable_harmonicOrderedEigenvalues orderedSpectrumContinuous massSample hmass

/-- The complete ordered harmonic frequency vector is measurable without a
spectral-continuity parameter. -/
theorem measurable_harmonicOrderedModeFrequencies_unconditional
    {N : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (hmass : ∀ i, Measurable fun omega => (massSample omega).mass i) :
    Measurable fun omega k => harmonicOrderedModeFrequency massSample omega k :=
  measurable_harmonicOrderedModeFrequencies orderedSpectrumContinuous massSample hmass

end

end ArchonPhysics.OrderedSpectrumContinuity
