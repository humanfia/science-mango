import ArchonPhysics.HarmonicModes

/-!
# Deterministic reduced normal-mode transform

This module turns the already selected orthonormal eigenbasis of the finite
mass-weighted harmonic matrix into modal coordinates.  It proves exact
reconstruction, preservation of the Euclidean norm, and diagonalization of
the mass-weighted harmonic quadratic form.

All statements are pointwise in a supplied positive mass configuration.  No
measurable choice of eigenvectors, measurable ordering of eigenvalues, or
random-basis assertion is made.
-/

namespace ArchonPhysics.ReducedModeTransform

open ArchonPhysics
open HarmonicModes
open scoped InnerProductSpace RealInnerProductSpace

noncomputable section

/-- The mass-weighted finite configuration space carrying its Euclidean norm. -/
abbrev WeightedConfiguration (N : Nat) :=
  EuclideanSpace Real (Lattice.Site N)

/-- Coordinates of a mass-weighted configuration in the selected normal-mode basis. -/
def modalCoordinates {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    WeightedConfiguration N ≃ₗᵢ[Real] WeightedConfiguration N :=
  (normalModeBasis m).repr

/-- Reconstruction from modal coordinates using the inverse basis transform. -/
def reconstruct {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    WeightedConfiguration N ≃ₗᵢ[Real] WeightedConfiguration N :=
  (normalModeBasis m).repr.symm

/-- A modal coordinate is the inner product with the corresponding normal mode. -/
theorem modalCoordinates_apply {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (x : WeightedConfiguration N)
    (k : Lattice.Site N) :
    modalCoordinates m x k = ⟪normalModeBasis m k, x⟫_ℝ := by
  exact (normalModeBasis m).repr_apply_apply x k

/-- Inverse transform after the modal transform reconstructs the configuration. -/
@[simp] theorem reconstruct_modalCoordinates {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (x : WeightedConfiguration N) :
    reconstruct m (modalCoordinates m x) = x := by
  exact (normalModeBasis m).repr.symm_apply_apply x

/-- Modal transform after reconstruction returns the supplied coordinates. -/
@[simp] theorem modalCoordinates_reconstruct {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (a : WeightedConfiguration N) :
    modalCoordinates m (reconstruct m a) = a := by
  exact (normalModeBasis m).repr.apply_symm_apply a

/-- Explicit finite reconstruction as the sum of modal amplitudes times modes. -/
theorem sum_modal_reconstruction {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (x : WeightedConfiguration N) :
    ∑ k, modalCoordinates m x k • normalModeBasis m k = x := by
  exact (normalModeBasis m).sum_repr x

/-- The modal transform preserves the Euclidean norm. -/
theorem norm_modalCoordinates {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (x : WeightedConfiguration N) :
    ‖modalCoordinates m x‖ = ‖x‖ := by
  exact LinearIsometryEquiv.norm_map (modalCoordinates m) x

/-- Parseval in modal coordinates, expressed as a finite real sum of squares. -/
theorem sum_sq_modalCoordinates {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (x : WeightedConfiguration N) :
    ∑ k, (modalCoordinates m x k) ^ 2 = ‖x‖ ^ 2 := by
  calc
    ∑ k, (modalCoordinates m x k) ^ 2 = ‖modalCoordinates m x‖ ^ 2 :=
      (EuclideanSpace.real_norm_sq_eq (modalCoordinates m x)).symm
    _ = ‖x‖ ^ 2 := by rw [norm_modalCoordinates]

/-- The mass-weighted harmonic matrix acting on Euclidean configurations. -/
def harmonicOperator {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) :
    WeightedConfiguration N →ₗ[Real] WeightedConfiguration N :=
  Matrix.toLpLin 2 2 (massWeightedHarmonicMatrix m)

/-- The Euclidean operator is the `PiLp` lift of matrix-vector multiplication. -/
theorem harmonicOperator_apply {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (x : WeightedConfiguration N) :
    harmonicOperator m x =
      WithLp.toLp 2 (Matrix.mulVec (massWeightedHarmonicMatrix m) (WithLp.ofLp x)) := by
  rfl

/-- Each selected normal mode remains an eigenvector of the lifted operator. -/
theorem harmonicOperator_eigenmode {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : Lattice.Site N) :
    harmonicOperator m (normalModeBasis m k) =
      modeFrequencySq m k • normalModeBasis m k := by
  change WithLp.toLp 2
      (Matrix.mulVec (massWeightedHarmonicMatrix m) ⇑(normalModeBasis m k)) =
    modeFrequencySq m k • normalModeBasis m k
  rw [normalMode_eigenvector]
  rfl

/--
An operator with an orthonormal eigenbasis has a diagonal real quadratic
form.  This is the only generic bridge needed between Mathlib's
`OrthonormalBasis.sum_repr` and the selected matrix eigenbasis.
-/
theorem quadraticForm_eq_sum_of_orthonormalEigenbasis
    {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace Real E]
    (b : OrthonormalBasis ι Real E) (T : E →ₗ[Real] E) (eigenvalue : ι → Real)
    (heigen : ∀ i, T (b i) = eigenvalue i • b i) (x : E) :
    ⟪T x, x⟫_ℝ = ∑ i, eigenvalue i * (b.repr x i) ^ 2 := by
  have hTx : T x = ∑ i, (eigenvalue i * b.repr x i) • b i := by
    calc
      T x = T (∑ i, b.repr x i • b i) := by rw [b.sum_repr]
      _ = ∑ i, T (b.repr x i • b i) := by rw [map_sum]
      _ = ∑ i, (eigenvalue i * b.repr x i) • b i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul, heigen, smul_smul]
        congr 1
        ring
  rw [hTx, sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [real_inner_smul_left, b.repr_apply_apply]
  ring

/-- The mass-weighted harmonic quadratic form `⟪H x, x⟫`. -/
def harmonicQuadraticForm {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (x : WeightedConfiguration N) : Real :=
  ⟪harmonicOperator m x, x⟫_ℝ

/-- The quadratic form is the site-coordinate matrix form. -/
theorem harmonicQuadraticForm_eq_site_sum {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (x : WeightedConfiguration N) :
    harmonicQuadraticForm m x =
      ∑ i, Matrix.mulVec (massWeightedHarmonicMatrix m) (WithLp.ofLp x) i * x i := by
  simp [harmonicQuadraticForm, harmonicOperator, Matrix.toLpLin_apply,
    PiLp.inner_apply, mul_comm]

/--
The mass-weighted harmonic quadratic form is the sum of squared modal
amplitudes weighted by the squared mode frequencies.
-/
theorem harmonicQuadraticForm_eq_modal_sum {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (x : WeightedConfiguration N) :
    harmonicQuadraticForm m x =
      ∑ k, modeFrequencySq m k * (modalCoordinates m x k) ^ 2 := by
  exact quadraticForm_eq_sum_of_orthonormalEigenbasis
    (normalModeBasis m) (harmonicOperator m) (modeFrequencySq m)
    (harmonicOperator_eigenmode m) x

end

end ArchonPhysics.ReducedModeTransform
