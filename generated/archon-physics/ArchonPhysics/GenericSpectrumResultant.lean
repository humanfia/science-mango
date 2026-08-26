import ArchonPhysics.HarmonicModes
import ArchonPhysics.PolynomialZeroSetNull

/-!
# A resultant certificate for generic simplicity of the weighted cycle Laplacian

This file isolates the algebraic part of the almost-sure simple-spectrum route.
The edge weights are coordinates in `Fin N`, while the matrix acts on the
periodic sites `ZMod N`.  Its entries are linear multivariate polynomials.
The fixed-size Sylvester resultant of the characteristic polynomial and its
derivative is therefore a multivariate polynomial in the edge weights.

The proved chain is

`geometric multiplicity at least two -> repeated characteristic root
  -> evaluated resultant = 0`.

Consequently, once one concrete weight specialization has nonzero resultant,
the bad geometric-multiplicity event is Lebesgue-null.  The remaining
specialization theorem is deliberately exposed as a hypothesis; no axiom is
introduced here.
-/

namespace ArchonPhysics.GenericSpectrumResultant

open ArchonPhysics.HarmonicModes

noncomputable section

/-- A fixed enumeration of the periodic sites by `Fin N`. -/
def siteEquivFin (N : Nat) [NeZero N] : Lattice.Site N ≃ Fin N :=
  (ZMod.finEquiv N).symm.toEquiv

/-- Interpret `Fin N` coordinates as weights on the periodic sites. -/
def weightsOfCoordinates {N : Nat} [NeZero N] (x : Fin N → Real) :
    Lattice.Site N → Real :=
  fun i ↦ x (siteEquivFin N i)

/-- The edge-space Gram matrix `D diag(w) Dᵀ`. -/
def weightedCycleLaplacian {N : Nat} [NeZero N]
    (w : Lattice.Site N → Real) :
    Matrix (Lattice.Site N) (Lattice.Site N) Real :=
  differenceMatrix * Matrix.diagonal w * Matrix.transpose differenceMatrix

/-- The same weighted cycle Laplacian with one polynomial variable per edge. -/
def symbolicWeightedCycleLaplacian {N : Nat} [NeZero N] :
    Matrix (Lattice.Site N) (Lattice.Site N) (MvPolynomial (Fin N) Real) :=
  differenceMatrix.map MvPolynomial.C *
    Matrix.diagonal (fun i ↦ MvPolynomial.X (siteEquivFin N i)) *
      (Matrix.transpose differenceMatrix).map MvPolynomial.C


/-- Evaluation of the symbolic matrix is exactly the concrete matrix. -/
theorem evaluate_symbolicWeightedCycleLaplacian {N : Nat} [NeZero N]
    (x : Fin N → Real) :
    (symbolicWeightedCycleLaplacian (N := N)).map (MvPolynomial.eval x) =
      weightedCycleLaplacian (weightsOfCoordinates x) := by
  unfold symbolicWeightedCycleLaplacian weightedCycleLaplacian
  rw [Matrix.map_mul, Matrix.map_mul]
  simp only [Matrix.diagonal_map, map_zero]
  congr 2
  · ext i j
    simp
  · ext i j
    simp only [MvPolynomial.eval_X]
    unfold weightsOfCoordinates
    rfl
  · ext i j
    simp

/-- Fixed-dimension resultant of the symbolic characteristic polynomial and
its derivative.  Fixed dimensions make specialization functorial without any
degree-drop side condition. -/
def symbolicRepeatedRootCertificate {N : Nat} [NeZero N] :
    MvPolynomial (Fin N) Real :=
  let p := (symbolicWeightedCycleLaplacian (N := N)).charpoly
  Polynomial.resultant p p.derivative (Fintype.card (Lattice.Site N))
    (Fintype.card (Lattice.Site N) - 1)

/-- The symbolic resultant specializes to the concrete fixed-size
characteristic resultant. -/
theorem evaluate_symbolicRepeatedRootCertificate {N : Nat} [NeZero N]
    (x : Fin N → Real) :
    MvPolynomial.eval x (symbolicRepeatedRootCertificate (N := N)) =
      let p := (weightedCycleLaplacian (weightsOfCoordinates x)).charpoly
      Polynomial.resultant p p.derivative (Fintype.card (Lattice.Site N))
        (Fintype.card (Lattice.Site N) - 1) := by
  simp only [symbolicRepeatedRootCertificate]
  rw [← Polynomial.resultant_map_map]
  rw [← Polynomial.derivative_map]
  rw [← Matrix.charpoly_map]
  rw [evaluate_symbolicWeightedCycleLaplacian]

/-- A basis-free geometric multiplicity-two witness. -/
def HasGeometricMultiplicityTwo {n : Type*} [Fintype n]
    (A : Matrix n n Real) : Prop :=
  ∃ lambda : Real, ∃ v : Fin 2 → (n → Real),
    LinearIndependent Real v ∧
      ∀ j, Matrix.mulVec A (v j) = lambda • (v j)

/-- Two independent eigenvectors force root multiplicity at least two in the
characteristic polynomial. -/
theorem rootMultiplicity_charpoly_gt_one_of_geometricMultiplicityTwo
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n Real} (hA : HasGeometricMultiplicityTwo A) :
    ∃ lambda : Real, 1 < A.charpoly.rootMultiplicity lambda := by
  rcases hA with ⟨lambda, v, hv, heigen⟩
  let T : Module.End Real (n → Real) := A.toLin'
  let u : Fin 2 → (T.eigenspace lambda) := fun j ↦
    ⟨v j, by
      rw [Module.End.mem_eigenspace_iff]
      simpa [T, Matrix.toLin'_apply'] using heigen j⟩
  have hu : LinearIndependent Real u := by
    apply LinearIndependent.of_comp (T.eigenspace lambda).subtype
    simpa [u, Function.comp_def] using hv
  have htwo : 2 ≤ Module.finrank Real (T.eigenspace lambda) := by
    simpa using hu.fintype_card_le_finrank
  have hle := LinearMap.finrank_eigenspace_le T lambda
  have hle' : Module.finrank Real (T.eigenspace lambda) ≤
      A.charpoly.rootMultiplicity lambda := by
    simpa [T, Matrix.charpoly_toLin'] using hle
  exact ⟨lambda, by omega⟩

/-- Geometric multiplicity two forces the fixed-size characteristic
resultant to vanish. -/
theorem fixedResultant_eq_zero_of_geometricMultiplicityTwo
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n Real} (hA : HasGeometricMultiplicityTwo A) :
    Polynomial.resultant A.charpoly A.charpoly.derivative (Fintype.card n)
        (Fintype.card n - 1) = 0 := by
  rcases rootMultiplicity_charpoly_gt_one_of_geometricMultiplicityTwo hA with
    ⟨lambda, hlambda⟩
  have hpne : A.charpoly ≠ 0 := (Matrix.charpoly_monic A).ne_zero
  have hroots :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hpne).mp hlambda
  have hnotCoprime : ¬ IsCoprime A.charpoly A.charpoly.derivative := by
    intro hcoprime
    rcases hcoprime with ⟨a, b, hab⟩
    have heval := congrArg (Polynomial.eval lambda) hab
    simp only [Polynomial.IsRoot.def] at hroots
    simp [hroots.1, hroots.2] at heval
  have hresultant :
      Polynomial.resultant A.charpoly A.charpoly.derivative = 0 :=
    Polynomial.resultant_eq_zero_iff.mpr
      ⟨Or.inl hpne, hnotCoprime⟩
  simpa [Matrix.charpoly_natDegree_eq_dim,
    Polynomial.natDegree_derivative] using hresultant

/-- Every multiplicity-two specialization belongs to the zero set of the
symbolic certificate. -/
theorem certificate_vanishes_of_geometricMultiplicityTwo
    {N : Nat} [NeZero N] (x : Fin N → Real)
    (h : HasGeometricMultiplicityTwo
      (weightedCycleLaplacian (weightsOfCoordinates x))) :
    MvPolynomial.eval x (symbolicRepeatedRootCertificate (N := N)) = 0 := by
  rw [evaluate_symbolicRepeatedRootCertificate]
  exact fixedResultant_eq_zero_of_geometricMultiplicityTwo h

/-- One nonsingular concrete specialization proves that the symbolic
certificate is not the zero polynomial. -/
theorem symbolicRepeatedRootCertificate_ne_zero_of_specialization
    {N : Nat} [NeZero N] (x₀ : Fin N → Real)
    (hx₀ :
      let p := (weightedCycleLaplacian (weightsOfCoordinates x₀)).charpoly
      Polynomial.resultant p p.derivative (Fintype.card (Lattice.Site N))
        (Fintype.card (Lattice.Site N) - 1) ≠ 0) :
    symbolicRepeatedRootCertificate (N := N) ≠ 0 := by
  intro hzero
  have heval := evaluate_symbolicRepeatedRootCertificate x₀
  rw [hzero] at heval
  simp only [map_zero] at heval
  exact hx₀ heval.symm

/-- Once a nonsingular specialization is supplied, the geometric
multiplicity-two event is Lebesgue-null. -/
theorem volume_geometricMultiplicityTwo_eq_zero_of_specialization
    {N : Nat} [NeZero N] (x₀ : Fin N → Real)
    (hx₀ :
      let p := (weightedCycleLaplacian (weightsOfCoordinates x₀)).charpoly
      Polynomial.resultant p p.derivative (Fintype.card (Lattice.Site N))
        (Fintype.card (Lattice.Site N) - 1) ≠ 0) :
    MeasureTheory.volume
        {x : Fin N → Real |
          HasGeometricMultiplicityTwo
            (weightedCycleLaplacian (weightsOfCoordinates x))} = 0 := by
  apply MeasureTheory.measure_mono_null (t :=
    {x : Fin N → Real |
      MvPolynomial.eval x (symbolicRepeatedRootCertificate (N := N)) = 0})
  · intro x hx
    exact certificate_vanishes_of_geometricMultiplicityTwo x hx
  · exact ArchonPhysics.volume_zeroSet_mvPolynomial_eval
      (symbolicRepeatedRootCertificate (N := N))
      (symbolicRepeatedRootCertificate_ne_zero_of_specialization x₀ hx₀)

end

end ArchonPhysics.GenericSpectrumResultant
