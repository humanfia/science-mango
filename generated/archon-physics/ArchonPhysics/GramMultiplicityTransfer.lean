import ArchonPhysics.GenericSpectrumResultant

/-!
# Positive-spectrum multiplicity transfer between Gram matrices

For a nonzero eigenvalue, multiplication by `D` transfers a linearly
independent eigenfamily of `DᵀD` to one of `DDᵀ`.  This is the exact
algebraic bridge from the mass-weighted harmonic matrix to the weighted cycle
Laplacian used by the polynomial resultant certificate.
-/

namespace ArchonPhysics.GramMultiplicityTransfer

open ArchonPhysics.GenericSpectrumResultant

noncomputable section

/-- On a nonzero Gram eigenspace, multiplication by `D` preserves a
two-vector linearly independent family. -/
theorem mulVec_family_linearIndependent_of_gram_eigen
    {n : Type*} [Fintype n]
    (D : Matrix n n Real) {lambda : Real} (hlambda : lambda ≠ 0)
    (v : Fin 2 → (n → Real)) (hv : LinearIndependent Real v)
    (heigen : ∀ j,
      Matrix.mulVec (Matrix.transpose D * D) (v j) = lambda • (v j)) :
    LinearIndependent Real (fun j ↦ Matrix.mulVec D (v j)) := by
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro g hsum
  have hafter := congrArg (fun x ↦ Matrix.mulVecLin (Matrix.transpose D) x) hsum
  simp only [map_sum, map_smul, map_zero, Matrix.mulVecLin_apply] at hafter
  have hscaled : lambda • (∑ j, g j • v j) = 0 := by
    simpa [Matrix.mulVec_mulVec, heigen, Finset.smul_sum,
      smul_smul, mul_comm] using hafter
  have hzero : (∑ j, g j • v j) = 0 :=
    (smul_eq_zero.mp hscaled).resolve_left hlambda
  exact hv g hzero

/-- A multiplicity-two witness at a nonzero eigenvalue transfers from `DᵀD`
to `DDᵀ`. -/
theorem selfTranspose_geometricMultiplicityTwo_of_transposeSelf
    {n : Type*} [Fintype n]
    (D : Matrix n n Real) {lambda : Real} (hlambda : lambda ≠ 0)
    (v : Fin 2 → (n → Real)) (hv : LinearIndependent Real v)
    (heigen : ∀ j,
      Matrix.mulVec (Matrix.transpose D * D) (v j) = lambda • (v j)) :
    HasGeometricMultiplicityTwo (D * Matrix.transpose D) := by
  refine ⟨lambda, (fun j ↦ Matrix.mulVec D (v j)),
    mulVec_family_linearIndependent_of_gram_eigen D hlambda v hv heigen, ?_⟩
  intro j
  calc
    Matrix.mulVec (D * Matrix.transpose D) (Matrix.mulVec D (v j)) =
        Matrix.mulVec D
          (Matrix.mulVec (Matrix.transpose D * D) (v j)) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = Matrix.mulVec D (lambda • v j) := by rw [heigen]
    _ = lambda • Matrix.mulVec D (v j) := Matrix.mulVec_smul D lambda (v j)

end

end ArchonPhysics.GramMultiplicityTransfer
