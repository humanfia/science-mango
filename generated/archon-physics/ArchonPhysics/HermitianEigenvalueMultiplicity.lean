import ArchonPhysics.GenericSpectrumResultant

/-!
# Repeated Hermitian eigenvalues give geometric multiplicity two

Mathlib supplies an orthonormal eigenbasis for every finite Hermitian matrix.
This file packages the elementary bridge from a duplicate in either of its
eigenvalue enumerations to the basis-free multiplicity witness used by the
generic resultant certificate.
-/

namespace ArchonPhysics.HermitianEigenvalueMultiplicity

open ArchonPhysics.GenericSpectrumResultant

noncomputable section

/-- Equal Hermitian eigenvalues at two distinct matrix indices provide two
linearly independent eigenvectors for the common eigenvalue. -/
theorem hasGeometricMultiplicityTwo_of_eigenvalues_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n Real} (hA : A.IsHermitian)
    {i j : n} (hij : hA.eigenvalues i = hA.eigenvalues j) (hne : i ≠ j) :
    HasGeometricMultiplicityTwo A := by
  let f : Fin 2 → n := ![i, j]
  have hf : Function.Injective f := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [f, hne, Ne.symm hne]
  let v : Fin 2 → (n → Real) :=
    fun k ↦ ⇑(hA.eigenvectorBasis (f k))
  have hv : LinearIndependent Real v := by
    have hb := hA.eigenvectorBasis.toBasis.linearIndependent.comp f hf
    rw [Fintype.linearIndependent_iff] at hb ⊢
    intro g hg
    apply hb g
    ext x
    have hx := congrFun hg x
    simpa [v, Function.comp_def] using hx
  refine ⟨hA.eigenvalues i, v, hv, ?_⟩
  intro k
  fin_cases k
  · simpa [v, f] using hA.mulVec_eigenvectorBasis i
  · simpa [v, f, hij] using hA.mulVec_eigenvectorBasis j

/-- Equal entries in Mathlib's decreasing ordered eigenvalue list at distinct
positions imply geometric multiplicity two. -/
theorem hasGeometricMultiplicityTwo_of_eigenvalues₀_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n Real} (hA : A.IsHermitian)
    {i j : Fin (Fintype.card n)}
    (hij : hA.eigenvalues₀ i = hA.eigenvalues₀ j) (hne : i ≠ j) :
    HasGeometricMultiplicityTwo A := by
  let e : Fin (Fintype.card n) ≃ n :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  apply hasGeometricMultiplicityTwo_of_eigenvalues_eq hA
      (i := e i) (j := e j)
  · simpa [Matrix.IsHermitian.eigenvalues, e] using hij
  · exact e.injective.ne hne

/-- Strong form retaining the common ordered eigenvalue in the witness. -/
theorem exists_linearIndependent_eigenvectors_of_eigenvalues₀_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n Real} (hA : A.IsHermitian)
    {i j : Fin (Fintype.card n)}
    (hij : hA.eigenvalues₀ i = hA.eigenvalues₀ j) (hne : i ≠ j) :
    ∃ v : Fin 2 → (n → Real), LinearIndependent Real v ∧
      ∀ k, Matrix.mulVec A (v k) = hA.eigenvalues₀ i • (v k) := by
  let e : Fin (Fintype.card n) ≃ n :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let f : Fin 2 → n := ![e i, e j]
  have hf : Function.Injective f := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [f, hne, Ne.symm hne]
  let v : Fin 2 → (n → Real) :=
    fun k ↦ ⇑(hA.eigenvectorBasis (f k))
  have hv : LinearIndependent Real v := by
    have hb := hA.eigenvectorBasis.toBasis.linearIndependent.comp f hf
    rw [Fintype.linearIndependent_iff] at hb ⊢
    intro g hg
    apply hb g
    ext x
    have hx := congrFun hg x
    simpa [v, Function.comp_def] using hx
  refine ⟨v, hv, ?_⟩
  intro k
  fin_cases k
  · simpa [v, f, Matrix.IsHermitian.eigenvalues, e] using
      hA.mulVec_eigenvectorBasis (e i)
  · simpa [v, f, Matrix.IsHermitian.eigenvalues, e, hij] using
      hA.mulVec_eigenvectorBasis (e j)

end

end ArchonPhysics.HermitianEigenvalueMultiplicity
