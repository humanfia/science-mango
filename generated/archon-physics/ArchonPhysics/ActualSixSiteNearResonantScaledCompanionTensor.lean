import ArchonPhysics.ActualSixSiteNearResonantScaledCompanion

/-!
# Threefold scaled-companion quotient

This file isolates the tensor-eigenvector calculation needed by the finite
collision elimination polynomial.  It is independent of any subsequently
computed determinant certificate.
-/

open scoped BigOperators Matrix Kronecker

namespace ArchonPhysics.ActualSixSiteNearResonantScaledCompanionTensor

open ArchonPhysics.ActualSixSiteNearResonantPathSeparable
open ArchonPhysics.ActualSixSiteNearResonantScaledCompanion

noncomputable section

/-- Tensor product of two row vectors, in the same indexing convention as
`Matrix.kronecker`. -/
def rowKronecker {m n : Type*} (v : m → Real) (w : n → Real) :
    m × n → Real :=
  fun i => v i.1 * w i.2

/-- Left multiplication by a Kronecker matrix separates into the two left
multiplications. -/
theorem rowKronecker_vecMul_kronecker
    {l m n p : Type*}
    [Fintype l] [Fintype n]
    (v : l → Real) (w : n → Real)
    (A : Matrix l m Real) (B : Matrix n p Real) :
    rowKronecker v w ᵥ* (A ⊗ₖ B) =
      rowKronecker (v ᵥ* A) (w ᵥ* B) := by
  funext ⟨j, k⟩
  simp only [Matrix.vecMul, dotProduct, rowKronecker,
    Matrix.kroneckerMap_apply]
  rw [← Finset.univ_product_univ, Finset.sum_product,
    Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro i' hi'
  ring

abbrev TripleQuinticIndex := Fin 5 × (Fin 5 × Fin 5)

/-- Simultaneous evaluation at three roots of the characteristic quintic. -/
def tripleQuinticEvaluationRow (energy₀ energy₁ energy₂ : Real) :
    TripleQuinticIndex → Real :=
  rowKronecker (quinticEvaluationRow energy₀)
    (rowKronecker (quinticEvaluationRow energy₁)
      (quinticEvaluationRow energy₂))

theorem tripleQuinticEvaluationRow_origin
    (energy₀ energy₁ energy₂ : Real) :
    tripleQuinticEvaluationRow energy₀ energy₁ energy₂
        (0, (0, 0)) = 1 := by
  norm_num [tripleQuinticEvaluationRow, rowKronecker,
    quinticEvaluationRow]

theorem tripleQuinticEvaluationRow_ne_zero
    (energy₀ energy₁ energy₂ : Real) :
    tripleQuinticEvaluationRow energy₀ energy₁ energy₂ ≠ 0 := by
  intro h
  have := congrFun h (0, (0, 0))
  rw [tripleQuinticEvaluationRow_origin] at this
  norm_num at this

/-- A triple evaluation row is a left eigenvector of every pure tensor of
powers of the scaled companion matrix. -/
theorem tripleQuinticEvaluationRow_vecMul_tensorPowers
    {t energy₀ energy₁ energy₂ : Real}
    (hroot₀ : (nearResonantPathQuintic (t ^ 2)).eval energy₀ = 0)
    (hroot₁ : (nearResonantPathQuintic (t ^ 2)).eval energy₁ = 0)
    (hroot₂ : (nearResonantPathQuintic (t ^ 2)).eval energy₂ = 0)
    (n₀ n₁ n₂ : Nat) :
    tripleQuinticEvaluationRow energy₀ energy₁ energy₂ ᵥ*
        ((nearResonantScaledCompanion t ^ n₀) ⊗ₖ
          ((nearResonantScaledCompanion t ^ n₁) ⊗ₖ
            (nearResonantScaledCompanion t ^ n₂))) =
      ((((1 - t ^ 2) * energy₀) ^ n₀) *
          (((1 - t ^ 2) * energy₁) ^ n₁) *
          (((1 - t ^ 2) * energy₂) ^ n₂)) •
        tripleQuinticEvaluationRow energy₀ energy₁ energy₂ := by
  rw [tripleQuinticEvaluationRow, rowKronecker_vecMul_kronecker,
    rowKronecker_vecMul_kronecker,
    quinticEvaluationRow_vecMul_scaledCompanion_pow hroot₀,
    quinticEvaluationRow_vecMul_scaledCompanion_pow hroot₁,
    quinticEvaluationRow_vecMul_scaledCompanion_pow hroot₂]
  funext ⟨i, j, k⟩
  simp [rowKronecker, Pi.smul_apply]
  ring

end


end ArchonPhysics.ActualSixSiteNearResonantScaledCompanionTensor
