import ArchonPhysics.OrderedSpectrumContinuity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection

/-!
# Continuous projectors onto separated Hermitian spectral clusters

For fixed thresholds `a < b`, a continuous ramp is zero on `(-∞, a]` and
one on `[b, ∞)`.  Applying the continuous functional calculus to a finite real
Hermitian matrix gives a globally continuous matrix-valued map.  On the domain
where the spectrum avoids `(a, b)`, this matrix is self-adjoint and idempotent,
hence is the exact orthogonal spectral projector onto the upper cluster.

The construction never chooses eigenvectors.  Degeneracies inside either
cluster are allowed; only separation between the two clusters is required.

The explicit predicate `matrixSelfAdjoint` is important.  Since `Matrix` is a
reducible function type, leaving the star operation implicit can make Lean
select pointwise star instead of conjugate transpose.  The L2-operator scope
uses Mathlib's operator norm while preserving the existing finite-matrix
topology, so the continuity theorem is compatible with entrywise measurable
Hermitian samples.
-/

open scoped ContinuousFunctionalCalculus Matrix Matrix.Norms.L2Operator

namespace ArchonPhysics.SeparatedSpectralClusterProjector

open ArchonPhysics.MeasurableOrderedSpectrum

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Self-adjointness with the square-matrix star explicitly locked to
conjugate transpose. -/
def matrixSelfAdjoint (A : Matrix ι ι Real) : Prop :=
  @IsSelfAdjoint (Matrix ι ι Real) Matrix.instStar A

/-- Continuous ramp used to isolate the upper spectral cluster. -/
def gapCutoff (a b x : Real) : Real :=
  Set.projIcc 0 1 zero_le_one ((x - a) / (b - a))

/-- The ramp is continuous for all thresholds. -/
theorem continuous_gapCutoff (a b : Real) : Continuous (gapCutoff a b) := by
  unfold gapCutoff
  fun_prop

/-- Below the lower threshold the ramp is exactly zero. -/
theorem gapCutoff_eq_zero {a b x : Real} (hab : a < b) (hx : x ≤ a) :
    gapCutoff a b x = 0 := by
  rw [gapCutoff, Set.projIcc_of_le_left]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_nonneg.mpr hab.le)

/-- Above the upper threshold the ramp is exactly one. -/
theorem gapCutoff_eq_one {a b x : Real} (hab : a < b) (hx : b ≤ x) :
    gapCutoff a b x = 1 := by
  rw [gapCutoff, Set.projIcc_of_right_le]
  rw [le_div_iff₀ (sub_pos.mpr hab)]
  linarith

/-- The fixed-threshold upper-cluster functional-calculus matrix. -/
def upperClusterProjector (a b : Real) (A : HermitianMatrix ι) :
    Matrix ι ι Real :=
  cfc (p := matrixSelfAdjoint (ι := ι)) (gapCutoff a b) A.1

/-- Explicit finite-dimensional topology bridge from entrywise Hermitian
matrices to their continuous-linear operator realization. -/
theorem continuous_operatorRealization :
    Continuous fun A : HermitianMatrix ι =>
      Matrix.toEuclideanCLM (𝕜 := Real) A.1 := by
  let L : Matrix ι ι Real →ₗ[Real]
      (EuclideanSpace Real ι →L[Real] EuclideanSpace Real ι) :=
    (Matrix.toEuclideanCLM (𝕜 := Real) (n := ι)).toAlgEquiv.toLinearEquiv.toLinearMap
  exact L.continuous_of_finiteDimensional.comp continuous_subtype_val

/-- The upper-cluster functional-calculus matrix is globally continuous.
Exact projector identities require the spectral-gap premise below, but
continuity does not. -/
theorem continuous_upperClusterProjector (a b : Real) :
    Continuous (upperClusterProjector (ι := ι) a b) := by
  change Continuous fun A : HermitianMatrix ι =>
    cfc (p := matrixSelfAdjoint (ι := ι)) (gapCutoff a b) A.1
  apply continuous_subtype_val.cfc_of_mem_nhdsSet
      (p := matrixSelfAdjoint (ι := ι)) (gapCutoff a b) (s := Set.univ)
      (ha' := by
        intro A
        change A.1ᴴ = A.1
        exact A.2)
      (hf := (continuous_gapCutoff a b).continuousOn)
  simp

/-- Every entry of the upper-cluster matrix is continuous.  This is the
finite-matrix topology bridge in coordinate form. -/
theorem continuous_upperClusterProjector_apply
    (a b : Real) (i j : ι) :
    Continuous fun A : HermitianMatrix ι => upperClusterProjector a b A i j := by
  exact (continuous_apply j).comp
    ((continuous_apply i).comp (continuous_upperClusterProjector a b))

/-- A measurable Hermitian sample has a coordinatewise measurable
upper-cluster matrix. -/
theorem measurable_upperClusterProjector_apply
    {Omega : Type*} [MeasurableSpace Omega]
    (a b : Real) (sample : Omega → HermitianMatrix ι)
    (hsample : Measurable sample) (i j : ι) :
    Measurable fun omega => upperClusterProjector a b (sample omega) i j :=
  (continuous_upperClusterProjector_apply a b i j).measurable.comp hsample

/-- The real spectrum with the square-matrix ring and scalar-algebra
instances explicitly locked. -/
def matrixSpectrum (A : Matrix ι ι Real) : Set Real :=
  @spectrum Real (Matrix ι ι Real) Real.instCommSemiring Matrix.instRing
    Matrix.instAlgebra A

/-- The precise separated-cluster domain.  Degeneracies within the two closed
spectral pieces are unrestricted. -/
def HasSeparatedSpectrum (a b : Real) (A : HermitianMatrix ι) : Prop :=
  matrixSpectrum A.1 ⊆ Set.Iic a ∪ Set.Ici b

/-- The functional-calculus matrix remains self-adjoint without a gap. -/
theorem upperClusterProjector_matrixSelfAdjoint
    (a b : Real) (A : HermitianMatrix ι) :
    matrixSelfAdjoint (upperClusterProjector a b A) := by
  exact cfc_predicate _ _

/-- Conjugate-transpose formulation of self-adjointness. -/
theorem upperClusterProjector_isHermitian
    (a b : Real) (A : HermitianMatrix ι) :
    (upperClusterProjector a b A).IsHermitian := by
  change (upperClusterProjector a b A)ᴴ = upperClusterProjector a b A
  exact upperClusterProjector_matrixSelfAdjoint a b A

/-- Hermitian-subtype packaging of the cluster matrix. -/
def upperClusterHermitianProjector (a b : Real) (A : HermitianMatrix ι) :
    HermitianMatrix ι :=
  ⟨upperClusterProjector a b A, upperClusterProjector_isHermitian a b A⟩

/-- The bundled Hermitian cluster matrix is continuous. -/
theorem continuous_upperClusterHermitianProjector (a b : Real) :
    Continuous (upperClusterHermitianProjector (ι := ι) a b) :=
  Continuous.subtype_mk (continuous_upperClusterProjector a b) _

/-- A measurable Hermitian sample has a bundled measurable Hermitian cluster
matrix, not merely measurable scalar entries. -/
theorem measurable_upperClusterHermitianProjector
    {Omega : Type*} [MeasurableSpace Omega]
    (a b : Real) (sample : Omega → HermitianMatrix ι)
    (hsample : Measurable sample) :
    Measurable fun omega => upperClusterHermitianProjector a b (sample omega) :=
  (continuous_upperClusterHermitianProjector a b).measurable.comp hsample

/-- On a separated spectrum, the cutoff takes values only in `{0, 1}` on the
spectrum. -/
theorem upperClusterProjector_spectrum_subset
    {a b : Real} (hab : a < b) (A : HermitianMatrix ι)
    (hgap : HasSeparatedSpectrum a b A) :
    matrixSpectrum (upperClusterProjector a b A) ⊆ ({0, 1} : Set Real) := by
  unfold matrixSpectrum upperClusterProjector
  rw [cfc_map_spectrum (R := Real) (p := matrixSelfAdjoint (ι := ι))
    (gapCutoff a b) A.1
    (by
      change A.1ᴴ = A.1
      exact A.2)
    ((continuous_gapCutoff a b).continuousOn)]
  rintro y ⟨x, hx, rfl⟩
  rcases hgap hx with hx | hx
  · left
    exact gapCutoff_eq_zero hab hx
  · right
    exact gapCutoff_eq_one hab hx

/-- On a separated spectrum the upper-cluster matrix is idempotent. -/
theorem upperClusterProjector_isIdempotentElem
    {a b : Real} (hab : a < b) (A : HermitianMatrix ι)
    (hgap : HasSeparatedSpectrum a b A) :
    IsIdempotentElem (upperClusterProjector a b A) := by
  rw [isIdempotentElem_iff_spectrum_subset Real _
    (upperClusterProjector_matrixSelfAdjoint a b A)]
  change matrixSpectrum (upperClusterProjector a b A) ⊆ ({0, 1} : Set Real)
  exact upperClusterProjector_spectrum_subset hab A hgap

/-- Exact orthogonal-projector package: Hermitian and idempotent, with no
simplicity assumption inside either spectral cluster. -/
theorem upperClusterProjector_isOrthogonalProjection
    {a b : Real} (hab : a < b) (A : HermitianMatrix ι)
    (hgap : HasSeparatedSpectrum a b A) :
    (upperClusterProjector a b A).IsHermitian ∧
      IsIdempotentElem (upperClusterProjector a b A) :=
  ⟨upperClusterProjector_isHermitian a b A,
    upperClusterProjector_isIdempotentElem hab A hgap⟩

end

end ArchonPhysics.SeparatedSpectralClusterProjector
