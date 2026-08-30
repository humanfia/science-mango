import ArchonPhysics.SelfAdjointQuasimodeSpectralWindow
import ArchonPhysics.RandomMassThreeWaveCollisionNetwork

/-!
# Ordered spectral-projector mass of a Hermitian quasimode

This file translates the abstract self-adjoint spectral-window estimate to
the ordered Hermitian spectrum.  If one ordered index is the unique index in
the window, that transparent deterministic isolation premise identifies the
window mass with the quadratic energy of the existing ordered Lagrange
projector.

No random localization or spectral-isolation statement is asserted here.
-/

open scoped Matrix

namespace ArchonPhysics.OrderedQuasimodeSpectralProjectorMass

open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.SelfAdjointQuasimodeSpectralWindow

noncomputable section

variable {iota : Type*} [Fintype iota] [DecidableEq iota]

/-- A specified ordered index is the unique index in the open spectral
window centered at `lambda` with radius `delta`. -/
def UniqueOrderedIndexInWindow
    (A : HermitianMatrix iota) (lambda delta : Real)
    (k₀ : Fin (Fintype.card iota)) : Prop :=
  |orderedEigenvalue A k₀ - lambda| < delta ∧
    ∀ k, |orderedEigenvalue A k - lambda| < delta → k = k₀

/-- Ordered-matrix form of the abstract spectral-window mass estimate. -/
theorem orderedEigenbasis_window_mass_ge
    (A : HermitianMatrix iota) (v : EuclideanSpace Real iota)
    {lambda epsilon delta : Real}
    (hdelta : 0 < delta) (hv : ‖v‖ = 1)
    (hresidual :
      ‖Matrix.toEuclideanLin A.1 v - lambda • v‖ ≤ epsilon) :
    1 - epsilon ^ 2 / delta ^ 2 ≤
      ∑ k ∈ Finset.univ.filter
        (fun k : Fin (Fintype.card iota) =>
          |orderedEigenvalue A k - lambda| < delta),
        ((v : iota → Real) ⬝ᵥ
          ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k))) ^ 2 := by
  let T : EuclideanSpace Real iota →ₗ[Real] EuclideanSpace Real iota :=
    Matrix.toEuclideanLin A.1
  let hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr A.2
  have h := inside_window_eigenbasis_mass_ge
    T hT (Fintype.card iota) finrank_euclideanSpace
    v hdelta hv hresidual
  have heigen (k : Fin (Fintype.card iota)) :
      hT.eigenvalues finrank_euclideanSpace k =
        orderedEigenvalue A k := by
    simp [orderedEigenvalue, Matrix.IsHermitian.eigenvalues₀, T]
  have hbasis (k : Fin (Fintype.card iota)) :
      hT.eigenvectorBasis finrank_euclideanSpace k =
        A.2.eigenvectorBasis (orderedIndexEquiv k) := by
    simp [Matrix.IsHermitian.eigenvectorBasis, orderedIndexEquiv, T]
  simp_rw [heigen, OrthonormalBasis.repr_apply_apply, hbasis] at h
  simpa [EuclideanSpace.inner_eq_star_dotProduct] using h

/-- Uniqueness in a positive-radius window isolates the selected ordered
eigenvalue from every other ordered index. -/
theorem isolatedOrderedMode_of_uniqueWindow
    (A : HermitianMatrix iota) {lambda delta : Real}
    {k₀ : Fin (Fintype.card iota)}
    (hunique : UniqueOrderedIndexInWindow A lambda delta k₀) :
    IsolatedOrderedMode A k₀ := by
  intro j hj hequal
  apply hj
  apply hunique.2 j
  rw [hequal]
  exact hunique.1

/-- Under a unique-window premise, the full ordered eigenbasis mass in that
window is exactly the squared coefficient of its unique mode. -/
theorem orderedEigenbasis_window_mass_eq_single
    (A : HermitianMatrix iota) (v : EuclideanSpace Real iota)
    {lambda delta : Real} {k₀ : Fin (Fintype.card iota)}
    (hunique : UniqueOrderedIndexInWindow A lambda delta k₀) :
    (∑ k ∈ Finset.univ.filter
        (fun k : Fin (Fintype.card iota) =>
          |orderedEigenvalue A k - lambda| < delta),
        ((v : iota → Real) ⬝ᵥ
          ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k))) ^ 2) =
      ((v : iota → Real) ⬝ᵥ
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k₀))) ^ 2 := by
  apply Finset.sum_eq_single k₀
  · intro k hk hne
    have hwindow : |orderedEigenvalue A k - lambda| < delta := by
      simpa using hk
    exact (hne (hunique.2 k hwindow)).elim
  · simp [hunique.1]

/-- If the spectral window contains exactly one ordered index, the ordered
rank-one projector captures at least `1 - epsilon² / delta²` of the unit
quasimode's quadratic energy.  Isolation is only a displayed premise. -/
theorem orderedModeProjector_quadraticEnergy_ge_of_uniqueWindow
    (A : HermitianMatrix iota) (v : EuclideanSpace Real iota)
    {lambda epsilon delta : Real} {k₀ : Fin (Fintype.card iota)}
    (hdelta : 0 < delta) (hv : ‖v‖ = 1)
    (hresidual :
      ‖Matrix.toEuclideanLin A.1 v - lambda • v‖ ≤ epsilon)
    (hunique : UniqueOrderedIndexInWindow A lambda delta k₀) :
    1 - epsilon ^ 2 / delta ^ 2 ≤
      (v : iota → Real) ⬝ᵥ
        (orderedModeProjector A k₀ *ᵥ (v : iota → Real)) := by
  have hmass := orderedEigenbasis_window_mass_ge
    A v hdelta hv hresidual
  have hcoefficient :
      1 - epsilon ^ 2 / delta ^ 2 ≤
        ((v : iota → Real) ⬝ᵥ
          ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k₀))) ^ 2 := by
    rw [orderedEigenbasis_window_mass_eq_single A v hunique] at hmass
    exact hmass
  rw [orderedModeProjector_eq_vecMulVec_of_isolated A
    (isolatedOrderedMode_of_uniqueWindow A hunique),
    Matrix.vecMulVec_mulVec]
  simp only [dotProduct_smul, op_smul_eq_smul, smul_eq_mul]
  rw [dotProduct_comm
    (⇑(A.2.eigenvectorBasis (orderedIndexEquiv k₀))) (v : iota → Real)]
  simpa [pow_two] using hcoefficient

/-- At an isolated ordered mode, the squared norm of the projected vector is
exactly the squared ordered eigenbasis coefficient. -/
theorem norm_sq_orderedModeProjector_mulVec_eq_coefficient_sq_of_isolated
    (A : HermitianMatrix iota) (v : EuclideanSpace Real iota)
    (k : Fin (Fintype.card iota)) (hisolated : IsolatedOrderedMode A k) :
    ‖WithLp.toLp 2
        (orderedModeProjector A k *ᵥ (v : iota → Real))‖ ^ 2 =
      ((v : iota → Real) ⬝ᵥ
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k))) ^ 2 := by
  rw [orderedModeProjector_eq_vecMulVec_of_isolated A hisolated,
    Matrix.vecMulVec_mulVec]
  simp only [op_smul_eq_smul, WithLp.toLp_smul, norm_smul,
    Real.norm_eq_abs]
  rw [A.2.eigenvectorBasis.norm_eq_one, mul_one, sq_abs]
  rw [dotProduct_comm
    (⇑(A.2.eigenvectorBasis (orderedIndexEquiv k))) (v : iota → Real)]

/-- For an isolated ordered mode, its projector quadratic form and the
squared norm of the projected vector use the same normalization. -/
theorem orderedModeProjector_quadraticEnergy_eq_projectedNormSq_of_isolated
    (A : HermitianMatrix iota) (v : EuclideanSpace Real iota)
    (k : Fin (Fintype.card iota)) (hisolated : IsolatedOrderedMode A k) :
    (v : iota → Real) ⬝ᵥ
        (orderedModeProjector A k *ᵥ (v : iota → Real)) =
      ‖WithLp.toLp 2
        (orderedModeProjector A k *ᵥ (v : iota → Real))‖ ^ 2 := by
  calc
    _ = ((v : iota → Real) ⬝ᵥ
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k))) ^ 2 := by
      rw [orderedModeProjector_eq_vecMulVec_of_isolated A hisolated,
        Matrix.vecMulVec_mulVec]
      simp only [dotProduct_smul, op_smul_eq_smul, smul_eq_mul]
      rw [dotProduct_comm
        (⇑(A.2.eigenvectorBasis (orderedIndexEquiv k)))
        (v : iota → Real)]
      ring
    _ = _ :=
      (norm_sq_orderedModeProjector_mulVec_eq_coefficient_sq_of_isolated
        A v k hisolated).symm

/-- Unique-window form of the projector-mass estimate stated as a squared
projected-norm lower bound. -/
theorem orderedModeProjector_projectedNormSq_ge_of_uniqueWindow
    (A : HermitianMatrix iota) (v : EuclideanSpace Real iota)
    {lambda epsilon delta : Real} {k₀ : Fin (Fintype.card iota)}
    (hdelta : 0 < delta) (hv : ‖v‖ = 1)
    (hresidual :
      ‖Matrix.toEuclideanLin A.1 v - lambda • v‖ ≤ epsilon)
    (hunique : UniqueOrderedIndexInWindow A lambda delta k₀) :
    1 - epsilon ^ 2 / delta ^ 2 ≤
      ‖WithLp.toLp 2
        (orderedModeProjector A k₀ *ᵥ (v : iota → Real))‖ ^ 2 := by
  calc
    _ ≤ (v : iota → Real) ⬝ᵥ
        (orderedModeProjector A k₀ *ᵥ (v : iota → Real)) :=
      orderedModeProjector_quadraticEnergy_ge_of_uniqueWindow
        A v hdelta hv hresidual hunique
    _ = _ :=
      orderedModeProjector_quadraticEnergy_eq_projectedNormSq_of_isolated
        A v k₀ (isolatedOrderedMode_of_uniqueWindow A hunique)

end

end ArchonPhysics.OrderedQuasimodeSpectralProjectorMass
