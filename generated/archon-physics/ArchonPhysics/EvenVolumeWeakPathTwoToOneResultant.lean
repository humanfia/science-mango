import ArchonPhysics.OddVolumePathTwoToOneResultant
import ArchonPhysics.OrderedSpectrumContinuity
import ArchonPhysics.PathLaplacianResultant

/-!
# Even-volume weak-path two-to-one resultant witness

For an even volume `2k+2`, break the periodic cycle at one edge and give the
last edge of the remaining path weight `t^2`, leaving all earlier path edges
at unit weight.  At `t = 0` the edge Gram matrix is the direct sum of the
odd-volume unit-path positive matrix and one zero eigenvalue.  The already
proved odd-volume resultant excludes fourfold ratios among the nonzero
eigenvalues.  Continuity of the finite ordered Hermitian spectrum then gives
a sufficiently small `t > 0` for which every off-diagonal fourfold ratio is
still absent; positive definiteness excludes the diagonal ratio.

The selected weak parameter is existential and volume-dependent.  This is an
algebraic specialization witness, not a uniform acoustic gap or a quantitative
lower bound on the mismatch.
-/

namespace ArchonPhysics.EvenVolumeWeakPathTwoToOneResultant

open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OddVolumePathTwoToOneResultant
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.FiniteExactDecayResonanceObstruction
open ArchonPhysics.FixedEnergySpectrumAvoidance
open ArchonPhysics.PathLaplacianResultant
open ArchonPhysics.PathLaplacianSpecialization

noncomputable section

/-- All path edges are unit-scaled except the last, weak edge. -/
def weakLastEdgeScale (n : Nat) (t : Real) : Fin (n + 1) → Real :=
  Fin.lastCases t (fun _ ↦ 1)

@[simp] theorem weakLastEdgeScale_last (n : Nat) (t : Real) :
    weakLastEdgeScale n t (Fin.last n) = t := by
  simp [weakLastEdgeScale]

@[simp] theorem weakLastEdgeScale_castSucc (n : Nat) (t : Real) (j : Fin n) :
    weakLastEdgeScale n t j.castSucc = 1 := by
  simp [weakLastEdgeScale]

@[simp] theorem weakLastEdgeScale_castAdd_one
    (n : Nat) (t : Real) (j : Fin n) :
    weakLastEdgeScale n t (Fin.castAdd 1 j) = 1 := by
  exact weakLastEdgeScale_castSucc n t j

@[simp] theorem weakLastEdgeScale_natAdd_one
    (n : Nat) (t : Real) (j : Fin 1) :
    weakLastEdgeScale n t (Fin.natAdd n j) = t := by
  rw [show Fin.natAdd n j = Fin.last n by
    ext
    simp]
  exact weakLastEdgeScale_last n t

/-- Coordinates with one broken cycle edge, `n` strong path edges, and one
last path edge of weight `t^2`. -/
def evenWeakPathCoordinates (n : Nat) (t : Real) : Fin (n + 2) → Real :=
  Fin.cases 0 (fun j ↦ (weakLastEdgeScale n t j) ^ 2)

@[simp] theorem evenWeakPathCoordinates_zero (n : Nat) (t : Real) :
    evenWeakPathCoordinates n t 0 = 0 := by
  simp [evenWeakPathCoordinates]

@[simp] theorem evenWeakPathCoordinates_succ
    (n : Nat) (t : Real) (j : Fin (n + 1)) :
    evenWeakPathCoordinates n t j.succ = (weakLastEdgeScale n t j) ^ 2 := by
  simp [evenWeakPathCoordinates]

/-- Incidence matrix whose last column is scaled by `t`. -/
def evenWeakPathEdgeMatrix (n : Nat) (t : Real) :
    Matrix (Fin (n + 2)) (Fin (n + 1)) Real :=
  unitPathEdgeMatrix (n + 1) * Matrix.diagonal (weakLastEdgeScale n t)

@[simp] theorem evenWeakPathEdgeMatrix_apply
    (n : Nat) (t : Real) (i : Fin (n + 2)) (j : Fin (n + 1)) :
    evenWeakPathEdgeMatrix n t i j =
      unitPathEdgeMatrix (n + 1) i j * weakLastEdgeScale n t j := by
  simp [evenWeakPathEdgeMatrix, Matrix.mul_diagonal]

/-- The positive-mode edge Gram matrix. -/
def evenWeakPathPositiveMatrix (n : Nat) (t : Real) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) Real :=
  (evenWeakPathEdgeMatrix n t).transpose * evenWeakPathEdgeMatrix n t

theorem evenWeakPathPositiveMatrix_isHermitian (n : Nat) (t : Real) :
    (evenWeakPathPositiveMatrix n t).IsHermitian :=
  by
    let B := evenWeakPathEdgeMatrix n t
    have hconj : Matrix.conjTranspose B = B.transpose := by
      ext i j
      change star (B j i) = B j i
      exact star_trivial _
    change (B.transpose * B).IsHermitian
    rw [← hconj]
    exact Matrix.isHermitian_conjTranspose_mul_self B

theorem evenWeakPathPositiveMatrix_posSemidef (n : Nat) (t : Real) :
    (evenWeakPathPositiveMatrix n t).PosSemidef :=
  by
    let B := evenWeakPathEdgeMatrix n t
    have hconj : Matrix.conjTranspose B = B.transpose := by
      ext i j
      change star (B j i) = B j i
      exact star_trivial _
    change (B.transpose * B).PosSemidef
    rw [← hconj]
    exact Matrix.posSemidef_conjTranspose_mul_self B

theorem evenWeakPathPositiveMatrix_eq_diagonal_cartan_diagonal
    (n : Nat) (t : Real) :
    evenWeakPathPositiveMatrix n t =
      Matrix.diagonal (weakLastEdgeScale n t) *
        ((CartanMatrix.A (n + 1)).map (Int.castRingHom Real)) *
        Matrix.diagonal (weakLastEdgeScale n t) := by
  simp only [evenWeakPathPositiveMatrix, evenWeakPathEdgeMatrix,
    Matrix.transpose_mul, Matrix.diagonal_transpose]
  rw [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (unitPathEdgeMatrix (n + 1)).transpose
    (unitPathEdgeMatrix (n + 1))]
  rw [unitPathEdgeMatrix_transpose_mul_eq_cartan]
  simp [Matrix.mul_assoc]

/-- The physical weak path is the corresponding incidence Gram matrix. -/
theorem finWeightedCycleLaplacian_evenWeakPath_eq_mul_transpose
    (n : Nat) (t : Real) :
    finWeightedCycleLaplacian (evenWeakPathCoordinates n t) =
      evenWeakPathEdgeMatrix n t * (evenWeakPathEdgeMatrix n t).transpose := by
  rw [finWeightedCycleLaplacian_eq_sum_rankOne]
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply,
    evenWeakPathEdgeMatrix_apply]
  rw [Fin.sum_univ_succ]
  simp only [evenWeakPathCoordinates_zero, zero_mul, zero_add,
    evenWeakPathCoordinates_succ]
  apply Finset.sum_congr rfl
  intro q _
  rw [unitPathEdgeMatrix_apply_eq_finCycleEdgeVector,
    unitPathEdgeMatrix_apply_eq_finCycleEdgeVector]
  ring

/-- The full weak-path characteristic polynomial has exactly the translation
factor `X`; its quotient is the edge-Gram characteristic polynomial. -/
theorem finWeightedCycleLaplacian_evenWeakPath_charpoly_divX_eq
    (n : Nat) (t : Real) :
    (finWeightedCycleLaplacian (evenWeakPathCoordinates n t)).charpoly.divX =
      (evenWeakPathPositiveMatrix n t).charpoly := by
  rw [finWeightedCycleLaplacian_evenWeakPath_eq_mul_transpose]
  rw [Matrix.charpoly_mul_comm_of_le]
  · ext q
    simp [evenWeakPathPositiveMatrix, Polynomial.coeff_divX]
  · simp

/-- At zero weak coupling the edge Gram matrix is the direct sum of the old
Cartan matrix and a scalar zero block. -/
theorem evenWeakPathPositiveMatrix_zero_reindex (n : Nat) :
    Matrix.reindex (finSumFinEquiv (m := n) (n := 1)).symm
        (finSumFinEquiv (m := n) (n := 1)).symm
        (evenWeakPathPositiveMatrix n 0) =
      Matrix.fromBlocks
        ((CartanMatrix.A n).map (Int.castRingHom Real)) 0 0 0 := by
  rw [evenWeakPathPositiveMatrix_eq_diagonal_cartan_diagonal]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, finSumFinEquiv_apply_left,
      Matrix.fromBlocks_apply₁₁, Matrix.map_apply,
      Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp [CartanMatrix.A]
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₁₂,
      Matrix.mul_diagonal, Matrix.diagonal_mul]
    fin_cases j
    simp
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, finSumFinEquiv_apply_right,
      finSumFinEquiv_apply_left, Matrix.fromBlocks_apply₂₁,
      Matrix.mul_diagonal, Matrix.diagonal_mul]
    fin_cases i
    simp
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, finSumFinEquiv_apply_right,
      Matrix.fromBlocks_apply₂₂, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
    fin_cases i
    fin_cases j
    simp

theorem evenWeakPathPositiveMatrix_zero_charpoly (n : Nat) :
    (evenWeakPathPositiveMatrix n 0).charpoly =
      Polynomial.X *
        (unitPathIntegerPositiveCharacteristic n).map (Int.castRingHom Real) := by
  have h := congrArg Matrix.charpoly
    (evenWeakPathPositiveMatrix_zero_reindex n)
  rw [Matrix.charpoly_reindex] at h
  simp only [Matrix.charpoly_fromBlocks_zero₁₂, Matrix.charpoly_zero,
    Fintype.card_fin, pow_one] at h
  calc
    (evenWeakPathPositiveMatrix n 0).charpoly =
        ((CartanMatrix.A n).map (Int.castRingHom Real)).charpoly *
          Polynomial.X := h
    _ = (unitPathIntegerPositiveCharacteristic n).map
          (Int.castRingHom Real) * Polynomial.X := by
      rw [Matrix.charpoly_map]
      rfl
    _ = Polynomial.X *
          (unitPathIntegerPositiveCharacteristic n).map
            (Int.castRingHom Real) := mul_comm _ _

/-- Entrywise continuity of the weak edge Gram family. -/
theorem continuous_evenWeakPathPositiveMatrix (n : Nat) :
    Continuous fun t : Real ↦ evenWeakPathPositiveMatrix n t := by
  rw [show (fun t : Real ↦ evenWeakPathPositiveMatrix n t) =
      fun t ↦ Matrix.diagonal (weakLastEdgeScale n t) *
        ((CartanMatrix.A (n + 1)).map (Int.castRingHom Real)) *
        Matrix.diagonal (weakLastEdgeScale n t) by
    funext t
    exact evenWeakPathPositiveMatrix_eq_diagonal_cartan_diagonal n t]
  have hscale : Continuous fun t : Real ↦ weakLastEdgeScale n t := by
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [weakLastEdgeScale_last] using
        (continuous_id' : Continuous fun t : Real ↦ t)
    · simpa using (continuous_const : Continuous fun _ : Real ↦ (1 : Real))
  exact (hscale.matrix_diagonal.matrix_mul continuous_const).matrix_mul
    hscale.matrix_diagonal

/-- Hermitian-subtype packaging of the weak edge Gram family. -/
def evenWeakPathHermitianMatrix (n : Nat) (t : Real) :
    HermitianMatrix (Fin (n + 1)) :=
  ⟨evenWeakPathPositiveMatrix n t,
    evenWeakPathPositiveMatrix_isHermitian n t⟩

theorem continuous_evenWeakPathHermitianMatrix (n : Nat) :
    Continuous (evenWeakPathHermitianMatrix n) := by
  apply Continuous.subtype_mk
  exact continuous_evenWeakPathPositiveMatrix n

/-- A separable Hermitian characteristic polynomial makes its decreasing
ordered eigenvalue enumeration injective. -/
theorem orderedEigenvalue_injective_of_charpoly_separable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) (hseparable : (Matrix.charpoly A.1).Separable) :
    Function.Injective (orderedEigenvalue A) := by
  intro i j hij
  have hroots := Polynomial.nodup_roots hseparable
  rw [A.2.roots_charpoly_eq_eigenvalues₀] at hroots
  apply Multiset.inj_on_of_nodup_map hroots i (by simp) j (by simp)
  simpa [orderedEigenvalue, Function.comp_def] using hij

/-- At `t=0`, the weak-path edge Gram has simple spectrum: it is the full
unit-path spectrum on the preceding odd volume. -/
theorem evenWeakPath_zero_orderedEigenvalue_injective (k : Nat) :
    Function.Injective
      (orderedEigenvalue (evenWeakPathHermitianMatrix (2 * k) 0)) := by
  by_cases hk : k = 0
  · subst k
    intro i j _
    fin_cases i
    fin_cases j
    rfl
  · apply orderedEigenvalue_injective_of_charpoly_separable
    have hN : 2 ≤ 2 * k + 1 := by omega
    have hsep := path_charpoly_separable (N := 2 * k + 1) hN
    have hfinChar :
        (finWeightedCycleLaplacian
          (pathWeightCoordinates (2 * k + 1))).charpoly =
        (weightedCycleLaplacian
          (pathWeight (N := 2 * k + 1))).charpoly := by
      unfold finWeightedCycleLaplacian
      rw [weightsOfCoordinates_pathWeightCoordinates]
      exact Matrix.charpoly_reindex (siteEquivFin (2 * k + 1)) _
    rw [evenWeakPathHermitianMatrix,
      evenWeakPathPositiveMatrix_zero_charpoly,
      ← finWeightedCycleLaplacian_path_charpoly_eq (2 * k), hfinChar]
    exact hsep

/-- At the degenerate endpoint, distinct ordered eigenvalues cannot be in a
fourfold ratio.  The only new endpoint root is zero; simplicity prevents it
from being paired with a second zero, while the old nonzero roots are covered
by the odd-volume resultant. -/
theorem evenWeakPath_zero_offDiagonal_fourfold_ne
    (k : Nat) (i j : Fin (Fintype.card (Fin (2 * k + 1)))) (hij : i ≠ j) :
    orderedEigenvalue (evenWeakPathHermitianMatrix (2 * k) 0) i ≠
      4 * orderedEigenvalue (evenWeakPathHermitianMatrix (2 * k) 0) j := by
  let A₀ := evenWeakPathHermitianMatrix (2 * k) 0
  let p := (unitPathIntegerPositiveCharacteristic (2 * k)).map
    (Int.castRingHom Real)
  intro hratio
  have hsimple : Function.Injective (orderedEigenvalue A₀) :=
    evenWeakPath_zero_orderedEigenvalue_injective k
  have hjne : orderedEigenvalue A₀ j ≠ 0 := by
    intro hjzero
    have hizero : orderedEigenvalue A₀ i = 0 := by
      rw [hratio, hjzero]
      norm_num
    exact hij (hsimple (by rw [hizero, hjzero]))
  have hine : orderedEigenvalue A₀ i ≠ 0 := by
    rw [hratio]
    exact mul_ne_zero (by norm_num) hjne
  have hiFull := charpoly_eval_orderedEigenvalue_eq_zero A₀ i
  have hjFull := charpoly_eval_orderedEigenvalue_eq_zero A₀ j
  have hchar : (Matrix.charpoly A₀.1) = Polynomial.X * p := by
    exact evenWeakPathPositiveMatrix_zero_charpoly (2 * k)
  rw [hchar, Polynomial.eval_mul, Polynomial.eval_X] at hiFull hjFull
  have hiRoot : p.eval (orderedEigenvalue A₀ i) = 0 :=
    (mul_eq_zero.mp hiFull).resolve_left hine
  have hjRoot : p.eval (orderedEigenvalue A₀ j) = 0 :=
    (mul_eq_zero.mp hjFull).resolve_left hjne
  have hscaleRoot :
      (p.scaleRoots 4).eval (orderedEigenvalue A₀ i) = 0 := by
    rw [hratio, Polynomial.scaleRoots_eval_mul, hjRoot, mul_zero]
  have hpMonic : p.Monic :=
    (unitPathIntegerPositiveCharacteristic_monic (2 * k)).map _
  have hzero :
      Polynomial.resultant p (p.scaleRoots 4)
        p.natDegree p.natDegree = 0 := by
    apply resultant_eq_zero_of_common_root_of_right_degree_le hpMonic
    · rw [Polynomial.natDegree_scaleRoots]
    · exact hiRoot
    · exact hscaleRoot
  exact unitPathRealPositiveCharacteristic_resultant_ne_zero k hzero

/-- Product of all off-diagonal fourfold mismatch factors in a finite
vector.  Keeping it as a literal finite product avoids any uniform-gap claim. -/
def offDiagonalFourfoldMismatchProduct
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → Real) : Real :=
  ∏ i, ∏ j ∈ Finset.univ.erase i, (v i - 4 * v j)

/-- A continuous finite vector whose off-diagonal fourfold mismatches are all
nonzero at zero retains that property at some strictly positive parameter. -/
theorem exists_pos_offDiagonal_fourfold_ne_of_continuous
    {ι : Type*} [Finite ι]
    (f : Real → ι → Real)
    (hf : ∀ i, Continuous fun t ↦ f t i)
    (hzero : ∀ i j, i ≠ j → f 0 i ≠ 4 * f 0 j) :
    ∃ t : Real, 0 < t ∧ ∀ i j, i ≠ j → f t i ≠ 4 * f t j := by
  classical
  let _ := Fintype.ofFinite ι
  let g : Real → Real := fun t ↦
    offDiagonalFourfoldMismatchProduct (fun i ↦ f t i)
  have hg : Continuous g := by
    apply continuous_finsetProd
    intro i _
    apply continuous_finsetProd
    intro j _
    exact (hf i).sub (continuous_const.mul (hf j))
  have hgzero : g 0 ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    rw [Finset.mem_erase] at hj
    exact sub_ne_zero.mpr (hzero i j hj.1.symm)
  have hnear : {t : Real | g t ≠ 0} ∈ nhds (0 : Real) :=
    hg.continuousAt.eventually_ne hgzero
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let t : Real := ε / 2
  have ht : 0 < t := by exact half_pos hε
  have htball : t ∈ Metric.ball (0 : Real) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp only [t]
    rw [sub_zero, abs_of_pos (half_pos hε)]
    linarith
  have hgt : g t ≠ 0 := hball htball
  refine ⟨t, ht, fun i j hij ↦ ?_⟩
  have hi := Finset.prod_ne_zero_iff.mp hgt i (Finset.mem_univ i)
  have hj := Finset.prod_ne_zero_iff.mp hi j
    (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
  exact sub_ne_zero.mp hj

/-- Every strictly positive weak parameter makes the edge Gram positive
definite.  The proof keeps the volume dependence explicit through the Cartan
determinant `n+2`; it does not produce a uniform lower eigenvalue bound. -/
theorem evenWeakPathPositiveMatrix_posDef
    (n : Nat) {t : Real} (ht : 0 < t) :
    (evenWeakPathPositiveMatrix n t).PosDef := by
  have hscaleDet :
      Matrix.det (Matrix.diagonal (weakLastEdgeScale n t)) ≠ 0 := by
    rw [Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa using ht.ne'
    · simp
  have hcartanDet :
      Matrix.det ((CartanMatrix.A (n + 1)).map
        (Int.castRingHom Real)) ≠ 0 := by
    change Matrix.det ((Int.castRingHom Real).mapMatrix
      (CartanMatrix.A (n + 1))) ≠ 0
    rw [← (Int.castRingHom Real).map_det (CartanMatrix.A (n + 1)),
      cartanMatrix_A_det]
    norm_num
    positivity
  apply (evenWeakPathPositiveMatrix_posSemidef n t).posDef_iff_det_ne_zero.mpr
  rw [evenWeakPathPositiveMatrix_eq_diagonal_cartan_diagonal,
    Matrix.det_mul, Matrix.det_mul]
  exact mul_ne_zero (mul_ne_zero hscaleDet hcartanDet) hscaleDet

theorem evenWeakPath_orderedEigenvalue_pos
    (n : Nat) {t : Real} (ht : 0 < t)
    (i : Fin (Fintype.card (Fin (n + 1)))) :
    0 < orderedEigenvalue (evenWeakPathHermitianMatrix n t) i := by
  let A := evenWeakPathHermitianMatrix n t
  let e : Fin (Fintype.card (Fin (n + 1))) ≃ Fin (n + 1) :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  have hi := (evenWeakPathPositiveMatrix_posDef n ht).eigenvalues_pos (e i)
  simpa [A, e, evenWeakPathHermitianMatrix, orderedEigenvalue,
    Matrix.IsHermitian.eigenvalues] using hi

/-- For every even volume `2k+2`, some strictly positive weak edge excludes
all fourfold ratios in the full positive edge spectrum. -/
theorem exists_pos_evenWeakPath_all_fourfold_ne (k : Nat) :
    ∃ t : Real, 0 < t ∧
      ∀ i j : Fin (Fintype.card (Fin (2 * k + 1))),
        orderedEigenvalue (evenWeakPathHermitianMatrix (2 * k) t) i ≠
          4 * orderedEigenvalue
            (evenWeakPathHermitianMatrix (2 * k) t) j := by
  let f : Real → Fin (Fintype.card (Fin (2 * k + 1))) → Real :=
    fun t i ↦ orderedEigenvalue
      (evenWeakPathHermitianMatrix (2 * k) t) i
  have hf (i : Fin (Fintype.card (Fin (2 * k + 1)))) :
      Continuous fun t ↦ f t i :=
    (continuous_orderedEigenvalue i).comp
      (continuous_evenWeakPathHermitianMatrix (2 * k))
  obtain ⟨t, ht, hoff⟩ :=
    exists_pos_offDiagonal_fourfold_ne_of_continuous f hf
      (evenWeakPath_zero_offDiagonal_fourfold_ne k)
  refine ⟨t, ht, fun i j ↦ ?_⟩
  by_cases hij : i = j
  · subst j
    have hpos := evenWeakPath_orderedEigenvalue_pos (2 * k) ht i
    intro hratio
    linarith
  · exact hoff i j hij

/-- A finite Hermitian matrix with no fourfold ratio among ordered
eigenvalues has nonzero fixed-size scale-roots resultant. -/
theorem charpoly_scaleRoots_four_resultant_ne_zero_of_ordered
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι)
    (havoid : ∀ i j : Fin (Fintype.card ι),
      orderedEigenvalue A i ≠ 4 * orderedEigenvalue A j) :
    let p := (Matrix.charpoly A.1)
    Polynomial.resultant p (p.scaleRoots 4)
      p.natDegree p.natDegree ≠ 0 := by
  dsimp only
  let p := Matrix.charpoly A.1
  let q := p.scaleRoots 4
  have hpMonic : p.Monic := Matrix.charpoly_monic A.1
  have hqMonic : q.Monic :=
    (Polynomial.monic_scaleRoots_iff (p := p) 4).mpr hpMonic
  rw [Polynomial.resultant_eq_prod_eval p q p.natDegree
    (by simp [q]) A.2.splits_charpoly]
  simp only [hpMonic.leadingCoeff, one_pow, one_mul]
  rw [A.2.roots_charpoly_eq_eigenvalues₀]
  apply Multiset.prod_ne_zero
  intro hzeroMem
  rcases Multiset.mem_map.mp hzeroMem with ⟨r₀, hr₀, hqroot⟩
  rcases Multiset.mem_map.mp hr₀ with ⟨i, hi, hri₀⟩
  have hr₀eq : r₀ = orderedEigenvalue A i := by
    simpa [orderedEigenvalue, Function.comp_def] using hri₀.symm
  have hqroot' : q.eval (orderedEigenvalue A i) = 0 := by
    rw [← hr₀eq]
    exact hqroot
  have hmemq : orderedEigenvalue A i ∈ q.roots :=
    (Polynomial.mem_roots hqMonic.ne_zero).mpr hqroot'
  rw [show q = p.scaleRoots 4 by rfl,
    Polynomial.roots_scaleRoots p (by norm_num)] at hmemq
  rcases Multiset.mem_map.mp hmemq with ⟨r, hr, hri⟩
  rw [A.2.roots_charpoly_eq_eigenvalues₀] at hr
  rcases Multiset.mem_map.mp hr with ⟨j, hj, hrj⟩
  apply havoid i j
  simpa [orderedEigenvalue, Function.comp_def] using hri.symm.trans
    (congrArg (fun x : Real ↦ 4 * x) hrj).symm

/-- The positive edge-Gram polynomial has a nonzero fourfold resultant at a
strictly positive weak-path specialization for every even volume. -/
theorem exists_pos_evenWeakPathPositive_resultant_ne_zero (k : Nat) :
    ∃ t : Real, 0 < t ∧
      let p := (evenWeakPathPositiveMatrix (2 * k) t).charpoly
      Polynomial.resultant p (p.scaleRoots 4)
        p.natDegree p.natDegree ≠ 0 := by
  obtain ⟨t, ht, havoid⟩ := exists_pos_evenWeakPath_all_fourfold_ne k
  refine ⟨t, ht, ?_⟩
  exact charpoly_scaleRoots_four_resultant_ne_zero_of_ordered
    (evenWeakPathHermitianMatrix (2 * k) t) havoid

/-- Reinsert the translation factor: the zero-mode-reduced physical Fin-path
polynomial has the same nonzero resultant. -/
theorem exists_pos_finWeightedCycle_evenWeakPath_reduced_resultant_ne_zero
    (k : Nat) :
    ∃ t : Real, 0 < t ∧
      let p := (finWeightedCycleLaplacian
        (evenWeakPathCoordinates (2 * k) t)).charpoly.divX
      Polynomial.resultant p (p.scaleRoots 4)
        p.natDegree p.natDegree ≠ 0 := by
  obtain ⟨t, ht, hresultant⟩ :=
    exists_pos_evenWeakPathPositive_resultant_ne_zero k
  refine ⟨t, ht, ?_⟩
  rw [finWeightedCycleLaplacian_evenWeakPath_charpoly_divX_eq]
  exact hresultant

/-- The same even-volume witness in the physical `ZMod` cycle indexing. -/
theorem exists_pos_weightedCycle_evenWeakPath_reduced_resultant_ne_zero
    (k : Nat) :
    ∃ t : Real, 0 < t ∧
      let p := (weightedCycleLaplacian
        (weightsOfCoordinates
          (evenWeakPathCoordinates (2 * k) t))).charpoly.divX
      Polynomial.resultant p (p.scaleRoots 4)
        p.natDegree p.natDegree ≠ 0 := by
  obtain ⟨t, ht, hresultant⟩ :=
    exists_pos_finWeightedCycle_evenWeakPath_reduced_resultant_ne_zero k
  refine ⟨t, ht, ?_⟩
  have hchar :
      (finWeightedCycleLaplacian
        (evenWeakPathCoordinates (2 * k) t)).charpoly =
      (weightedCycleLaplacian
        (weightsOfCoordinates
          (evenWeakPathCoordinates (2 * k) t))).charpoly := by
    exact Matrix.charpoly_reindex (siteEquivFin (2 * k + 2)) _
  rw [← hchar]
  exact hresultant

/-- Unconditional nonvanishing of the symbolic two-to-one resonance
certificate at every even volume.  The proof uses the volume-dependent,
strictly positive weak edge selected above; no certificate premise remains. -/
theorem symbolicTwoToOneResultantCertificate_ne_zero_evenSize (k : Nat) :
    symbolicTwoToOneResultantCertificate (N := 2 * k + 2) ≠ 0 := by
  obtain ⟨t, ht, hresultant⟩ :=
    exists_pos_weightedCycle_evenWeakPath_reduced_resultant_ne_zero k
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval (evenWeakPathCoordinates (2 * k) t)) hzero
  rw [eval_symbolicTwoToOneResultantCertificate] at heval
  exact hresultant (by simpa using heval)

end
end ArchonPhysics.EvenVolumeWeakPathTwoToOneResultant
