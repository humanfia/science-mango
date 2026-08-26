import ArchonPhysics.PathLaplacianSimplicity

/-!
# Simple spectrum and nonzero resultant for the broken-cycle path

For `N ≥ 2`, the specialization with one zero weight and all other weights
equal to one has simple full spectrum.  This supplies the concrete point at
which the generic characteristic resultant is nonzero.
-/

namespace ArchonPhysics.PathLaplacianResultant

open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.PathLaplacianSpecialization
open ArchonPhysics.PathLaplacianSimplicity

noncomputable section

theorem weightedCycleLaplacian_isHermitian {N : Nat} [NeZero N]
    (w : Lattice.Configuration N) :
    (weightedCycleLaplacian w).IsHermitian := by
  unfold weightedCycleLaplacian Matrix.IsHermitian
  simp [Matrix.mul_assoc]

/-- The path recurrence excludes a two-dimensional eigenspace at every real
eigenvalue. -/
theorem not_hasGeometricMultiplicityTwo_path
    {N : Nat} [NeZero N] (hN : 2 ≤ N) :
    ¬ HasGeometricMultiplicityTwo
      (weightedCycleLaplacian (pathWeight (N := N))) := by
  rintro ⟨lambda, v, hv, heigen⟩
  have hv_ne (j : Fin 2) : v j ≠ 0 := hv.ne_zero j
  have hfirst_ne (j : Fin 2) : v j 0 ≠ 0 := by
    intro hzero
    apply hv_ne j
    exact path_eigenvector_zero_of_zero_first hN (v j) lambda (heigen j) hzero
  let q : Lattice.Configuration N :=
    v 1 0 • v 0 - v 0 0 • v 1
  have hqEigen :
      Matrix.mulVec (weightedCycleLaplacian pathWeight) q = lambda • q := by
    unfold q
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
      heigen 0, heigen 1]
    simp [smul_sub, smul_smul, mul_comm]
  have hq0 : q 0 = 0 := by
    simp [q]
    ring
  have hq : q = 0 :=
    path_eigenvector_zero_of_zero_first hN q lambda hqEigen hq0
  have hsum :
      (∑ j : Fin 2, ![v 1 0, -v 0 0] j • v j) = 0 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    simpa [q, sub_eq_add_neg, neg_smul] using hq
  have hcoeff := (Fintype.linearIndependent_iff.mp hv)
    ![v 1 0, -v 0 0] hsum (0 : Fin 2)
  exact hfirst_ne 1 (by simpa using hcoeff)

/-- The Hermitian eigenvalue enumeration is injective for the broken-cycle
path specialization. -/
theorem path_eigenvalues_injective
    {N : Nat} [NeZero N] (hN : 2 ≤ N) :
    Function.Injective
      (weightedCycleLaplacian_isHermitian (pathWeight (N := N))).eigenvalues := by
  let hA := weightedCycleLaplacian_isHermitian (pathWeight (N := N))
  intro i j hij
  by_contra hne
  apply not_hasGeometricMultiplicityTwo_path hN
  let f : Fin 2 → Lattice.Site N := ![i, j]
  have hf : Function.Injective f := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [f, hne, Ne.symm hne]
  let v : Fin 2 → Lattice.Configuration N :=
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
  · simpa [v, f, hA] using hA.mulVec_eigenvectorBasis i
  · simpa [v, f, hA, hij] using hA.mulVec_eigenvectorBasis j

theorem path_charpoly_separable
    {N : Nat} [NeZero N] (hN : 2 ≤ N) :
    (weightedCycleLaplacian (pathWeight (N := N))).charpoly.Separable := by
  let hA := weightedCycleLaplacian_isHermitian (pathWeight (N := N))
  rw [hA.charpoly_eq]
  exact Polynomial.separable_prod_X_sub_C_iff.mpr
    (path_eigenvalues_injective hN)

/-- The fixed-size Sylvester resultant is nonzero at the path
specialization. -/
theorem path_fixedResultant_ne_zero
    {N : Nat} [NeZero N] (hN : 2 ≤ N) :
    let A := weightedCycleLaplacian (pathWeight (N := N))
    Polynomial.resultant A.charpoly A.charpoly.derivative
      (Fintype.card (Lattice.Site N))
      (Fintype.card (Lattice.Site N) - 1) ≠ 0 := by
  dsimp only
  let A := weightedCycleLaplacian (pathWeight (N := N))
  have hsep : A.charpoly.Separable := path_charpoly_separable hN
  have hunit : IsUnit (Polynomial.resultant A.charpoly A.charpoly.derivative) :=
    (Polynomial.isUnit_resultant_iff_isCoprime (Matrix.charpoly_monic A)).mpr hsep
  have hne : Polynomial.resultant A.charpoly A.charpoly.derivative ≠ 0 :=
    IsUnit.ne_zero hunit
  simpa [Matrix.charpoly_natDegree_eq_dim,
    Polynomial.natDegree_derivative] using hne

theorem path_specialization_fixedResultant_ne_zero
    {N : Nat} [NeZero N] (hN : 2 ≤ N) :
    let A := weightedCycleLaplacian
      (weightsOfCoordinates (pathWeightCoordinates N))
    Polynomial.resultant A.charpoly A.charpoly.derivative
      (Fintype.card (Lattice.Site N))
      (Fintype.card (Lattice.Site N) - 1) ≠ 0 := by
  rw [weightsOfCoordinates_pathWeightCoordinates]
  exact path_fixedResultant_ne_zero hN

/-- The symbolic characteristic resultant is genuinely nonzero for every
chain size `N ≥ 2`. -/
theorem symbolicRepeatedRootCertificate_ne_zero
    {N : Nat} [NeZero N] (hN : 2 ≤ N) :
    symbolicRepeatedRootCertificate (N := N) ≠ 0 :=
  symbolicRepeatedRootCertificate_ne_zero_of_specialization
    (pathWeightCoordinates N) (path_specialization_fixedResultant_ne_zero hN)

/-- Hence the geometric multiplicity-two event is unconditionally
Lebesgue-null for `N ≥ 2`. -/
theorem volume_geometricMultiplicityTwo_eq_zero
    {N : Nat} [NeZero N] (hN : 2 ≤ N) :
    MeasureTheory.volume
        {x : Fin N → Real |
          HasGeometricMultiplicityTwo
            (weightedCycleLaplacian (weightsOfCoordinates x))} = 0 :=
  volume_geometricMultiplicityTwo_eq_zero_of_specialization
    (pathWeightCoordinates N) (path_specialization_fixedResultant_ne_zero hN)

end

end ArchonPhysics.PathLaplacianResultant
