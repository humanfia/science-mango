import ArchonPhysics.PeriodicWeightedCycleBlockGluing
import ArchonPhysics.OddConstantScaleRootsResultant
import ArchonPhysics.FiniteExactDecayResonanceObstruction
import Mathlib.LinearAlgebra.Matrix.Cartan

/-!
# Odd-volume broken-path two-to-one resultant witness

For every odd volume `N = 2k+1`, the unit open path obtained by breaking one
edge of the periodic weighted cycle supplies an unconditional specialization
where the zero-mode-reduced characteristic polynomial has no fourfold root
ratio.  The proof factors the path Laplacian as `E Eᵀ`, identifies `Eᵀ E`
with the type-A Cartan matrix, and proves the variable-rank continuant formula
`det (A n) = n+1`.  At even rank the reduced integer characteristic
polynomial therefore has odd constant coefficient, so reduction modulo two
forces its fourfold scale-roots resultant to be nonzero.

The broken path is an algebraic witness for nonvanishing of the symbolic
inverse-mass polynomial.  Its zero edge is not asserted to be a realization
of a strictly positive random-mass ensemble.  The result covers odd volumes
only; no even-volume claim is made.
-/

namespace ArchonPhysics.OddVolumePathTwoToOneResultant

open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.PathLaplacianSpecialization
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.FiniteExactDecayResonanceObstruction

noncomputable section

theorem cartanMatrix_A_det (n : Nat) :
    (CartanMatrix.A n).det = (n + 1 : Int) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [CartanMatrix.A]
  | one => norm_num [CartanMatrix.A, Matrix.det_fin_two]
  | more n hn hn1 =>
      have hminor0 :
          (CartanMatrix.A (n + 2)).submatrix Fin.succ Fin.succ =
            CartanMatrix.A (n + 1) := by
        ext i j
        simp only [CartanMatrix.A, Matrix.submatrix_apply, Matrix.of_apply,
          Fin.val_succ]
        grind
      let B : Matrix (Fin (n + 1)) (Fin (n + 1)) Int :=
        (CartanMatrix.A (n + 2)).submatrix Fin.succ (Fin.succAbove 1)
      have hBminor : B.submatrix Fin.succ Fin.succ = CartanMatrix.A n := by
        ext i j
        simp only [B, CartanMatrix.A, Matrix.submatrix_apply, Matrix.of_apply,
          Fin.val_succ, Fin.one_succAbove_succ]
        grind
      have hBdet : B.det = -(CartanMatrix.A n).det := by
        rw [Matrix.det_succ_column_zero]
        simp only [Fin.sum_univ_succ, Fin.succAbove_zero]
        rw [hBminor]
        simp [B, CartanMatrix.A]
      have hdiag : CartanMatrix.A (n + 2) 0 0 = 2 := by
        simp [CartanMatrix.A]
      have hoff : CartanMatrix.A (n + 2) 0 (Fin.succ 0) = -1 := by
        simp [CartanMatrix.A, Fin.ext_iff]
      have hfar (i : Fin n) : CartanMatrix.A (n + 2) 0 i.succ.succ = 0 := by
        simp [CartanMatrix.A, Fin.ext_iff]
      rw [Matrix.det_succ_row_zero]
      simp only [Fin.sum_univ_succ, Fin.succAbove_zero]
      rw [hminor0]
      have hminor1 :
          (CartanMatrix.A (n + 2)).submatrix Fin.succ
            (Fin.succ 0).succAbove = B := by
        rfl
      rw [hminor1, hBdet, hdiag, hoff]
      simp_rw [hfar]
      simp only [mul_zero]
      norm_num
      rw [hn, hn1]
      omega

def unitPathEdgeMatrix (n : Nat) : Matrix (Fin (n + 1)) (Fin n) Real :=
  fun i j => (if i = j.castSucc then 1 else 0) -
    (if i = j.succ then 1 else 0)

theorem unitPathEdgeMatrix_apply_eq_finCycleEdgeVector
    (n : Nat) (i : Fin (n + 1)) (j : Fin n) :
    unitPathEdgeMatrix n i j =
      finCycleEdgeVector (N := n + 1) j.succ i := by
  rw [finCycleEdgeVector_apply_of_ne_zero _ _ (by simp)]
  simp only [unitPathEdgeMatrix, Fin.val_succ]
  have hfirst : j.val + 1 = i.val + 1 ↔ i = j.castSucc := by
    simp only [Fin.ext_iff, Fin.val_castSucc]
    omega
  rw [if_congr hfirst rfl rfl]
  rw [if_congr (eq_comm : j.succ = i ↔ i = j.succ) rfl rfl]

theorem finWeightedCycleLaplacian_path_eq_mul_transpose (n : Nat) :
    finWeightedCycleLaplacian (pathWeightCoordinates (n + 1)) =
      unitPathEdgeMatrix n * (unitPathEdgeMatrix n).transpose := by
  rw [finWeightedCycleLaplacian_eq_sum_rankOne]
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Fin.sum_univ_succ]
  have hzero : (siteEquivFin (n + 1)).symm 0 = 0 := by
    apply ZMod.val_injective
    rw [val_siteEquivFin_symm]
    rfl
  have hsucc (k : Fin n) : (siteEquivFin (n + 1)).symm k.succ ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    rw [val_siteEquivFin_symm] at hv
    simp at hv
  simp only [pathWeightCoordinates, pathWeight, hzero, if_pos, hsucc, if_false,
    zero_mul, zero_add]
  apply Finset.sum_congr rfl
  intro k _
  rw [unitPathEdgeMatrix_apply_eq_finCycleEdgeVector,
    unitPathEdgeMatrix_apply_eq_finCycleEdgeVector]
  simp

theorem unitPathEdgeMatrix_transpose_mul_eq_cartan (n : Nat) :
    (unitPathEdgeMatrix n).transpose * unitPathEdgeMatrix n =
      (CartanMatrix.A n).map (Int.castRingHom Real) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, unitPathEdgeMatrix,
    Matrix.map_apply, CartanMatrix.A, Matrix.of_apply]
  simp_rw [sub_mul, mul_sub]
  simp only [Finset.sum_sub_distrib]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Fin.castSucc_inj, Fin.succ_inj,
    Int.reduceNeg, eq_intCast, Int.cast_ite, Int.cast_ofNat,
    Int.cast_neg, Int.cast_one, Int.cast_zero]
  have hi := i.isLt
  have hj := j.isLt
  have heq : j = i ↔ i = j := eq_comm
  have hprev : j.succ = i.castSucc ↔ j.val + 1 = i.val := by
    rw [Fin.ext_iff]
    simp only [Fin.val_succ, Fin.val_castSucc]
  have hnext : j.castSucc = i.succ ↔ i.val + 1 = j.val := by
    rw [Fin.ext_iff]
    simp only [Fin.val_castSucc, Fin.val_succ]
    exact eq_comm
  rw [if_congr heq rfl rfl, if_congr hprev rfl rfl,
    if_congr hnext rfl rfl]
  split_ifs <;> try norm_num <;> try omega

def unitPathIntegerPositiveCharacteristic (n : Nat) : Polynomial Int :=
  (CartanMatrix.A n).charpoly

theorem finWeightedCycleLaplacian_path_charpoly_eq (n : Nat) :
    (finWeightedCycleLaplacian (pathWeightCoordinates (n + 1))).charpoly =
      Polynomial.X *
        (unitPathIntegerPositiveCharacteristic n).map (Int.castRingHom Real) := by
  rw [show finWeightedCycleLaplacian (pathWeightCoordinates (n + 1)) =
      unitPathEdgeMatrix n * (unitPathEdgeMatrix n).transpose by
      exact finWeightedCycleLaplacian_path_eq_mul_transpose n]
  rw [Matrix.charpoly_mul_comm_of_le]
  · rw [unitPathEdgeMatrix_transpose_mul_eq_cartan]
    simp only [unitPathIntegerPositiveCharacteristic]
    rw [Matrix.charpoly_map]
    simp
  · simp

theorem finWeightedCycleLaplacian_path_charpoly_divX_eq (n : Nat) :
    (finWeightedCycleLaplacian
      (pathWeightCoordinates (n + 1))).charpoly.divX =
      (unitPathIntegerPositiveCharacteristic n).map (Int.castRingHom Real) := by
  rw [finWeightedCycleLaplacian_path_charpoly_eq]
  ext k
  simp [Polynomial.coeff_divX]

theorem unitPathIntegerPositiveCharacteristic_monic (n : Nat) :
    (unitPathIntegerPositiveCharacteristic n).Monic :=
  Matrix.charpoly_monic (CartanMatrix.A n)

theorem unitPathIntegerPositiveCharacteristic_coeff_zero_even (k : Nat) :
    (unitPathIntegerPositiveCharacteristic (2 * k)).coeff 0 =
      (2 * k + 1 : Int) := by
  have hdet := Matrix.det_eq_sign_charpoly_coeff (CartanMatrix.A (2 * k))
  rw [cartanMatrix_A_det] at hdet
  have hsign : (-1 : Int) ^ (2 * k) = 1 := by
    rw [pow_mul]
    norm_num
  rw [Fintype.card_fin] at hdet
  rw [hsign, one_mul] at hdet
  norm_num at hdet ⊢
  exact hdet.symm

theorem unitPathIntegerPositiveCharacteristic_coeff_zero_odd (k : Nat) :
    Odd ((unitPathIntegerPositiveCharacteristic (2 * k)).coeff 0) := by
  rw [unitPathIntegerPositiveCharacteristic_coeff_zero_even]
  refine ⟨(k : Int), ?_⟩
  ring

theorem unitPathIntegerPositiveCharacteristic_resultant_ne_zero (k : Nat) :
    let p := unitPathIntegerPositiveCharacteristic (2 * k)
    Polynomial.resultant p (p.scaleRoots 4) p.natDegree p.natDegree ≠ 0 := by
  dsimp only
  exact
    OddConstantScaleRootsResultant.int_resultant_scaleRoots_four_ne_zero_of_odd_constant
      _ (unitPathIntegerPositiveCharacteristic_monic _)
      (unitPathIntegerPositiveCharacteristic_coeff_zero_odd k)

theorem unitPathRealPositiveCharacteristic_resultant_ne_zero (k : Nat) :
    let pInt := unitPathIntegerPositiveCharacteristic (2 * k)
    let pReal := pInt.map (Int.castRingHom Real)
    Polynomial.resultant pReal (pReal.scaleRoots 4)
      pReal.natDegree pReal.natDegree ≠ 0 := by
  dsimp only
  let pInt := unitPathIntegerPositiveCharacteristic (2 * k)
  let phi : Int →+* Real := Int.castRingHom Real
  have hpMonic : pInt.Monic := unitPathIntegerPositiveCharacteristic_monic _
  have hlead : phi pInt.leadingCoeff ≠ 0 := by
    rw [hpMonic.leadingCoeff]
    norm_num
  have hdegree : (pInt.map phi).natDegree = pInt.natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero phi hlead
  have hscale :
      (pInt.scaleRoots 4).map phi =
        (pInt.map phi).scaleRoots (phi 4) :=
    Polynomial.map_scaleRoots pInt 4 phi hlead
  have hInt :
      Polynomial.resultant pInt (pInt.scaleRoots 4)
        pInt.natDegree pInt.natDegree ≠ 0 :=
    unitPathIntegerPositiveCharacteristic_resultant_ne_zero k
  have hcast :
      phi (Polynomial.resultant pInt (pInt.scaleRoots 4)
        pInt.natDegree pInt.natDegree) ≠ 0 := by
    change ((Polynomial.resultant pInt (pInt.scaleRoots 4)
      pInt.natDegree pInt.natDegree : Int) : Real) ≠ 0
    exact_mod_cast hInt
  rw [← Polynomial.resultant_map_map, hscale] at hcast
  have hfour : phi 4 = (4 : Real) := by norm_num
  rw [hfour] at hcast
  change
    Polynomial.resultant (pInt.map phi) ((pInt.map phi).scaleRoots 4)
      (pInt.map phi).natDegree (pInt.map phi).natDegree ≠ 0
  simpa [hdegree] using hcast

theorem finWeightedCycleLaplacian_path_reduced_resultant_ne_zero (k : Nat) :
    let p := (finWeightedCycleLaplacian
      (pathWeightCoordinates (2 * k + 1))).charpoly.divX
    Polynomial.resultant p (p.scaleRoots 4) p.natDegree p.natDegree ≠ 0 := by
  dsimp only
  rw [finWeightedCycleLaplacian_path_charpoly_divX_eq (2 * k)]
  exact unitPathRealPositiveCharacteristic_resultant_ne_zero k

theorem weightedCycleLaplacian_unitPath_reduced_resultant_ne_zero (k : Nat) :
    let p := (weightedCycleLaplacian
      (pathWeight (N := 2 * k + 1))).charpoly.divX
    Polynomial.resultant p (p.scaleRoots 4) p.natDegree p.natDegree ≠ 0 := by
  dsimp only
  have hchar :
      (finWeightedCycleLaplacian
        (pathWeightCoordinates (2 * k + 1))).charpoly =
      (weightedCycleLaplacian
        (pathWeight (N := 2 * k + 1))).charpoly := by
    unfold finWeightedCycleLaplacian
    rw [weightsOfCoordinates_pathWeightCoordinates]
    exact Matrix.charpoly_reindex (siteEquivFin (2 * k + 1)) _
  rw [← hchar]
  exact finWeightedCycleLaplacian_path_reduced_resultant_ne_zero k

/-- Resultant certificate for an exact fourfold ratio between two roots of
the zero-mode-reduced symbolic characteristic polynomial. -/
def symbolicTwoToOneResultantCertificate {N : Nat} [NeZero N] :
    MvPolynomial (Fin N) Real :=
  let p := symbolicPositiveCharacteristic (N := N)
  Polynomial.resultant p (p.scaleRoots 4) p.natDegree p.natDegree

theorem eval_symbolicTwoToOneResultantCertificate
    {N : Nat} [NeZero N] (x : Fin N → Real) :
    MvPolynomial.eval x (symbolicTwoToOneResultantCertificate (N := N)) =
      let p := (weightedCycleLaplacian
        (weightsOfCoordinates x)).charpoly.divX
      Polynomial.resultant p (p.scaleRoots 4) p.natDegree p.natDegree := by
  let p := symbolicPositiveCharacteristic (N := N)
  let phi : MvPolynomial (Fin N) Real →+* Real := MvPolynomial.eval x
  have hpMonic : p.Monic := symbolicPositiveCharacteristic_monic
  have hlead : phi p.leadingCoeff ≠ 0 := by
    rw [hpMonic.leadingCoeff]
    simp
  have hdegree : (p.map phi).natDegree = p.natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero phi hlead
  have hscale :
      (p.scaleRoots 4).map phi =
        (p.map phi).scaleRoots (phi 4) :=
    Polynomial.map_scaleRoots p 4 phi hlead
  change phi (Polynomial.resultant p (p.scaleRoots 4)
      p.natDegree p.natDegree) = _
  rw [← Polynomial.resultant_map_map, hscale]
  rw [← hdegree]
  have hfour : phi 4 = (4 : Real) := by
    exact map_ofNat phi 4
  rw [hfour]
  simp only [p]
  rw [map_symbolicPositiveCharacteristic]

theorem symbolicTwoToOneResultantCertificate_ne_zero_oddSize (k : Nat) :
    symbolicTwoToOneResultantCertificate (N := 2 * k + 1) ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval (pathWeightCoordinates (2 * k + 1))) hzero
  rw [eval_symbolicTwoToOneResultantCertificate,
    weightsOfCoordinates_pathWeightCoordinates] at heval
  exact weightedCycleLaplacian_unitPath_reduced_resultant_ne_zero k
    (by simpa using heval)

end
end ArchonPhysics.OddVolumePathTwoToOneResultant
