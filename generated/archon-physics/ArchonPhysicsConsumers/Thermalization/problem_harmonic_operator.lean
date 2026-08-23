import Mathlib
import ArchonPhysics
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
import Physlib.CondensedMatter.LatticeModels.Basic

/-! Finite-dimensional harmonic dynamical operators and modal energies. -/

namespace ArchonPhysics.Generated.HarmonicOperator

noncomputable section

abbrev Field (N : ℕ) := Fin N → ℝ

/-- The diagonal factor `M^(-1/2)` associated to strictly positive masses. -/
def inverseSqrtMass {N : ℕ} (mass : Field N) : Field N :=
  fun i => (Real.sqrt (mass i))⁻¹

/-- The mass-weighted dynamical matrix `M^(-1/2) Dᵀ D M^(-1/2)`. -/
def dynamicalMatrix {N : ℕ} (mass : Field N) (D : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (inverseSqrtMass mass) * D.transpose * D *
    Matrix.diagonal (inverseSqrtMass mass)

/-- Real self-adjointness of a finite matrix. -/
def IsSelfAdjoint {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  A.transpose = A

/-- Nonnegativity of a real finite-dimensional quadratic form. -/
def IsPositiveSemidefinite {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ x : Field N, 0 ≤ dotProduct x (A.mulVec x)

/-- A normal-mode interface that keeps the translation zero mode explicit. -/
structure NormalModeDiagonalization (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) where
  frequencySquared : Fin N → ℝ
  mode : Fin N → Field N
  translationMode : Field N
  translation_zero : A.mulVec translationMode = 0

/-- A harmonic trajectory satisfying the stated linear flow equation. -/
structure HarmonicFlow (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) where
  position : ℝ → Field N
  momentum : ℝ → Field N
  equation : ∀ t, HasDerivAt position (momentum t) t ∧
    HasDerivAt momentum (-(A.mulVec (position t))) t

/-- The harmonic energy assigned to one real normal coordinate. -/
def modalEnergy (ωSquared q p : ℝ) : ℝ :=
  (p ^ 2 + ωSquared * q ^ 2) / 2

/-- Self-adjointness and nonnegativity of the finite mass-weighted operator. -/
theorem harmonic_operator_physics_formalization_target
    {N : ℕ} (mass : Field N) (D : Matrix (Fin N) (Fin N) ℝ)
    (hmass : ∀ i, 0 < mass i) :
    IsSelfAdjoint (dynamicalMatrix mass D) ∧
      IsPositiveSemidefinite (dynamicalMatrix mass D) := by
  constructor
  · unfold IsSelfAdjoint dynamicalMatrix
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  · unfold IsPositiveSemidefinite
    have hpos : Matrix.PosSemidef
        ((D * Matrix.diagonal (inverseSqrtMass mass)).transpose *
          (D * Matrix.diagonal (inverseSqrtMass mass))) := by
      simpa using
        (Matrix.posSemidef_conjTranspose_mul_self
          (D * Matrix.diagonal (inverseSqrtMass mass)))
    intro x
    simpa [dynamicalMatrix, Matrix.transpose_mul, Matrix.mul_assoc] using
      hpos.dotProduct_mulVec_nonneg x

end

end ArchonPhysics.Generated.HarmonicOperator
