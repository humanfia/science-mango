import Mathlib
import ArchonPhysics
import Physlib.CondensedMatter.LatticeModels.Basic

/-! Diagonal mass operators for a finite random-mass lattice. -/

namespace ArchonPhysics.Generated.MassMatrix

noncomputable section

/-- A positive real mass attached to each site of a finite lattice. -/
structure PositiveMasses (N : ℕ) where
  mass : Fin N → ℝ
  mass_pos : ∀ i, 0 < mass i

/-- The diagonal mass operator. -/
def massOperator {N : ℕ} (m : PositiveMasses N) (x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => m.mass i * x i

/-- The diagonal inverse-mass operator. -/
def inverseMassOperator {N : ℕ} (m : PositiveMasses N) (x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => (m.mass i)⁻¹ * x i

/-- The kinetic quadratic form associated to positive site masses. -/
def kineticQuadraticForm {N : ℕ} (m : PositiveMasses N) (p : Fin N → ℝ) : ℝ :=
  ∑ i, p i ^ 2 / (2 * m.mass i)

/-- The mass-weighted coordinate used to pass to unit-mass variables. -/
def massWeightedCoordinate {N : ℕ} (m : PositiveMasses N) (q : Fin N → ℝ) : Fin N → ℝ :=
  fun i => Real.sqrt (m.mass i) * q i

/-- The target inverse-mass identities and positivity fact for the finite model. -/
theorem mass_matrix_physics_formalization_target
    {N : ℕ} (m : PositiveMasses N) (p q : Fin N → ℝ) :
    (∀ i, inverseMassOperator m (massOperator m q) i = q i) ∧
      0 ≤ kineticQuadraticForm m p := by
  constructor
  · intro i
    simp [inverseMassOperator, massOperator, ne_of_gt (m.mass_pos i)]
  · unfold kineticQuadraticForm
    apply Finset.sum_nonneg
    intro i _
    exact div_nonneg (sq_nonneg (p i))
      (mul_nonneg (by norm_num) (le_of_lt (m.mass_pos i)))

end

end ArchonPhysics.Generated.MassMatrix
