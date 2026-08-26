import ArchonPhysics.OrderedSpectrumContinuity
import ArchonPhysics.SpectralBandEnergyObservable

/-!
# Measurable ordered single-mode spectral projectors

For ordered eigenvalue index `k`, this module defines the Lagrange matrix
`Pₖ(A) = ∏_{j ≠ k} (λₖ(A) - λⱼ(A))⁻¹ (A - λⱼ(A) I)`.

The inverse is totalized, so the formula is defined and coordinatewise
measurable on every Hermitian matrix. Exact projector identities are asserted
only on `SimpleOrderedSpectrum`: degeneracies are never hidden, and the
construction itself makes no measurable eigenvector choice. Mathlib’s
noncomputable Hermitian eigenbasis is used only inside deterministic proofs.
-/

open scoped Matrix

namespace ArchonPhysics.OrderedSingleModeProjector

open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSpectrumContinuity

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixVal (A : HermitianMatrix ι) : Matrix ι ι Real :=
  fun i j => A.1 i j

def orderedModeFactor (A : HermitianMatrix ι)
    (k j : Fin (Fintype.card ι)) : Matrix ι ι Real :=
  (orderedEigenvalue A k - orderedEigenvalue A j)⁻¹ •
    (matrixVal A -
      orderedEigenvalue A j • (1 : Matrix ι ι Real))

def orderedModeRatio (A : HermitianMatrix ι)
    (k r j : Fin (Fintype.card ι)) : Real :=
  (orderedEigenvalue A r - orderedEigenvalue A j) /
    (orderedEigenvalue A k - orderedEigenvalue A j)

def orderedModeProjector (A : HermitianMatrix ι)
    (k : Fin (Fintype.card ι)) : Matrix ι ι Real :=
  ((Finset.univ.erase k).toList.map (orderedModeFactor A k)).prod

def orderedIndexEquiv : Fin (Fintype.card ι) ≃ ι :=
  Fintype.equivOfCardEq (Fintype.card_fin _)

theorem orderedEigenvalue_equiv (A : HermitianMatrix ι)
    (j : Fin (Fintype.card ι)) :
    A.2.eigenvalues (orderedIndexEquiv j) = orderedEigenvalue A j := by
  simp [orderedIndexEquiv, Matrix.IsHermitian.eigenvalues, orderedEigenvalue]

theorem orderedModeFactor_mulVec_eigenvectorBasis
    (A : HermitianMatrix ι) (k j r : Fin (Fintype.card ι)) :
    orderedModeFactor A k j *ᵥ
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) =
      (orderedModeRatio A k r j) •
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) := by
  have heigen : matrixVal A *ᵥ
      ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) =
        orderedEigenvalue A r •
          ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) := by
    have hval : matrixVal A = (fun i j => A.1 i j) := rfl
    rw [hval]
    simpa [orderedEigenvalue_equiv] using
      A.2.mulVec_eigenvectorBasis (orderedIndexEquiv r)
  rw [orderedModeFactor, Matrix.smul_mulVec, Matrix.sub_mulVec, heigen,
    Matrix.smul_mulVec, Matrix.one_mulVec]
  ext i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  unfold orderedModeRatio
  ring

theorem listProduct_mulVec_eigenvectorBasis
    (A : HermitianMatrix ι) (k r : Fin (Fintype.card ι)) :
    ∀ L : List (Fin (Fintype.card ι)),
      (L.map (orderedModeFactor A k)).prod *ᵥ
          ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) =
        (L.map (orderedModeRatio A k r)).prod •
          ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r))
  | [] => by simp
  | j :: L => by
      rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec,
        listProduct_mulVec_eigenvectorBasis A k r L, Matrix.mulVec_smul,
        orderedModeFactor_mulVec_eigenvectorBasis, List.map_cons,
        List.prod_cons, smul_smul]
      simp only [mul_comm]

def SimpleOrderedSpectrum (A : HermitianMatrix ι) : Prop :=
  Function.Injective (orderedEigenvalue A)

theorem orderedModeProjector_mulVec_eigenvectorBasis
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (k r : Fin (Fintype.card ι)) :
    orderedModeProjector A k *ᵥ
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) =
      if r = k then ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) else 0 := by
  rw [orderedModeProjector, listProduct_mulVec_eigenvectorBasis]
  split_ifs with hrk
  · subst r
    have hprod :
        (((Finset.univ.erase k).toList.map
          (orderedModeRatio A k k))).prod = 1 := by
      apply List.prod_eq_one
      intro z hz
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
      have hjk : j ≠ k := by simpa using hj
      have hne : orderedEigenvalue A k - orderedEigenvalue A j ≠ 0 :=
        sub_ne_zero.mpr (hsimple.ne hjk.symm)
      exact div_self hne
    rw [hprod, one_smul]
  · have hrmem : r ∈ (Finset.univ.erase k).toList := by
      simp [hrk]
    have hzero : orderedModeRatio A k r r = 0 := by
      simp [orderedModeRatio]
    have hzmem :
        (0 : Real) ∈ ((Finset.univ.erase k).toList.map
          (orderedModeRatio A k r)) :=
      List.mem_map.mpr ⟨r, hrmem, hzero⟩
    rw [List.prod_eq_zero hzmem, zero_smul]

theorem matrix_eq_of_mulVec_eigenvectorBasis_eq
    (A : HermitianMatrix ι) (M N : Matrix ι ι Real)
    (h : ∀ r : Fin (Fintype.card ι),
      M *ᵥ ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) =
        N *ᵥ ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r))) :
    M = N := by
  apply Matrix.toEuclideanLin.injective
  apply A.2.eigenvectorBasis.toBasis.ext
  intro i
  simp only [Matrix.toLpLin_apply]
  apply congrArg (WithLp.toLp 2)
  simpa using h (orderedIndexEquiv.symm i)

theorem orderedModeProjector_isIdempotentElem
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (k : Fin (Fintype.card ι)) :
    IsIdempotentElem (orderedModeProjector A k) := by
  apply matrix_eq_of_mulVec_eigenvectorBasis_eq A
  intro r
  rw [← Matrix.mulVec_mulVec]
  by_cases hr : r = k
  · simp [orderedModeProjector_mulVec_eigenvectorBasis A hsimple, hr]
  · simp [orderedModeProjector_mulVec_eigenvectorBasis A hsimple, hr]

theorem orderedModeProjector_mul_eq_zero
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    {k l : Fin (Fintype.card ι)} (hkl : k ≠ l) :
    orderedModeProjector A k * orderedModeProjector A l = 0 := by
  apply matrix_eq_of_mulVec_eigenvectorBasis_eq A
  intro r
  rw [← Matrix.mulVec_mulVec]
  by_cases hrl : r = l
  · subst r
    simp [orderedModeProjector_mulVec_eigenvectorBasis A hsimple, Ne.symm hkl]
  · simp [orderedModeProjector_mulVec_eigenvectorBasis A hsimple, hrl]

theorem orderedModeProjector_sum_eq_one
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A) :
    ∑ k : Fin (Fintype.card ι), orderedModeProjector A k = 1 := by
  apply matrix_eq_of_mulVec_eigenvectorBasis_eq A
  intro r
  rw [Matrix.sum_mulVec, Matrix.one_mulVec]
  simp [orderedModeProjector_mulVec_eigenvectorBasis A hsimple]

theorem orderedModeFactor_isHermitian
    (A : HermitianMatrix ι) (k j : Fin (Fintype.card ι)) :
    (orderedModeFactor A k j).IsHermitian := by
  have hA : (matrixVal A).IsHermitian := by
    have hval : matrixVal A = (fun i j => A.1 i j) := rfl
    rw [hval]
    exact A.2
  exact (hA.sub (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _))).smul
    (IsSelfAdjoint.all _)

theorem orderedModeFactor_commute
    (A : HermitianMatrix ι) (k j l : Fin (Fintype.card ι)) :
    Commute (orderedModeFactor A k j) (orderedModeFactor A k l) := by
  let X := matrixVal A
  let sj := orderedEigenvalue A j
  let sl := orderedEigenvalue A l
  have hXright : Commute X (sl • (1 : Matrix ι ι Real)) :=
    (Commute.one_right X).smul_right sl
  have hjX : Commute (sj • (1 : Matrix ι ι Real)) X :=
    (Commute.one_left X).smul_left sj
  have hjl : Commute (sj • (1 : Matrix ι ι Real))
      (sl • (1 : Matrix ι ι Real)) :=
    ((Commute.refl (1 : Matrix ι ι Real)).smul_left sj).smul_right sl
  have hbase : Commute (X - sj • (1 : Matrix ι ι Real))
      (X - sl • (1 : Matrix ι ι Real)) :=
    ((Commute.refl X).sub_right hXright).sub_left
      (hjX.sub_right hjl)
  exact (hbase.smul_left
    (orderedEigenvalue A k - orderedEigenvalue A j)⁻¹).smul_right
      (orderedEigenvalue A k - orderedEigenvalue A l)⁻¹

theorem orderedModeFactor_commute_listProduct
    (A : HermitianMatrix ι) (k j : Fin (Fintype.card ι)) :
    ∀ L : List (Fin (Fintype.card ι)),
      Commute (orderedModeFactor A k j)
        (L.map (orderedModeFactor A k)).prod
  | [] => Commute.one_right _
  | l :: L =>
      (orderedModeFactor_commute A k j l).mul_right
        (orderedModeFactor_commute_listProduct A k j L)

theorem listProduct_isHermitian
    (A : HermitianMatrix ι) (k : Fin (Fintype.card ι)) :
    ∀ L : List (Fin (Fintype.card ι)),
      ((L.map (orderedModeFactor A k)).prod).IsHermitian
  | [] => Matrix.isHermitian_one
  | j :: L => by
      rw [List.map_cons, List.prod_cons]
      have hj := orderedModeFactor_isHermitian A k j
      have hL := listProduct_isHermitian A k L
      change IsSelfAdjoint (orderedModeFactor A k j) at hj
      change IsSelfAdjoint ((L.map (orderedModeFactor A k)).prod) at hL
      exact (IsSelfAdjoint.commute_iff hj hL).mp
        (orderedModeFactor_commute_listProduct A k j L)

theorem orderedModeProjector_isHermitian
    (A : HermitianMatrix ι) (k : Fin (Fintype.card ι)) :
    (orderedModeProjector A k).IsHermitian := by
  exact listProduct_isHermitian A k (Finset.univ.erase k).toList

theorem matrixVal_mulVec_eigenvectorBasis
    (A : HermitianMatrix ι) (r : Fin (Fintype.card ι)) :
    matrixVal A *ᵥ ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) =
      orderedEigenvalue A r •
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) := by
  have hval : matrixVal A = (fun i j => A.1 i j) := rfl
  rw [hval]
  simpa [orderedEigenvalue_equiv] using
    A.2.mulVec_eigenvectorBasis (orderedIndexEquiv r)

theorem matrixVal_mul_orderedModeProjector
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (k : Fin (Fintype.card ι)) :
    matrixVal A * orderedModeProjector A k =
      orderedEigenvalue A k • orderedModeProjector A k := by
  apply matrix_eq_of_mulVec_eigenvectorBasis_eq A
  intro r
  rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec]
  by_cases hr : r = k
  · subst r
    rw [orderedModeProjector_mulVec_eigenvectorBasis A hsimple]
    simp only [if_pos, matrixVal_mulVec_eigenvectorBasis]
  · rw [orderedModeProjector_mulVec_eigenvectorBasis A hsimple]
    simp [hr]

def orderedModeProjectedState (A : HermitianMatrix ι)
    (k : Fin (Fintype.card ι)) (x : ι → Real) : ι → Real :=
  orderedModeProjector A k *ᵥ x

def orderedModeEnergy (A : HermitianMatrix ι)
    (k : Fin (Fintype.card ι)) (x : ι → Real) : Real :=
  ArchonPhysics.SpectralBandEnergyObservable.coordinateEnergy
    (orderedModeProjectedState A k x)

theorem orderedModeEnergy_nonneg (A : HermitianMatrix ι)
    (k : Fin (Fintype.card ι)) (x : ι → Real) :
    0 ≤ orderedModeEnergy A k x :=
  ArchonPhysics.SpectralBandEnergyObservable.coordinateEnergy_nonneg _

theorem orderedModeProjectedState_orthogonal
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    {k l : Fin (Fintype.card ι)} (hkl : k ≠ l) (x : ι → Real) :
    orderedModeProjectedState A k x ⬝ᵥ orderedModeProjectedState A l x = 0 := by
  unfold orderedModeProjectedState
  have htranspose : (orderedModeProjector A k)ᵀ =
      orderedModeProjector A k := by
    have hH := orderedModeProjector_isHermitian A k
    ext i j
    have hij := congrArg
      (fun M : Matrix ι ι Real => M i j) hH
    simpa [Matrix.IsHermitian, Matrix.conjTranspose] using hij
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, htranspose,
    orderedModeProjector_mul_eq_zero A hsimple hkl, Matrix.vecMul_zero,
    zero_dotProduct]

theorem orderedModeEnergy_eq_quadraticForm
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (k : Fin (Fintype.card ι)) (x : ι → Real) :
    orderedModeEnergy A k x =
      x ⬝ᵥ orderedModeProjectedState A k x := by
  unfold orderedModeEnergy orderedModeProjectedState
  unfold ArchonPhysics.SpectralBandEnergyObservable.coordinateEnergy
  have htranspose : (orderedModeProjector A k)ᵀ =
      orderedModeProjector A k := by
    have hH := orderedModeProjector_isHermitian A k
    ext i j
    have hij := congrArg
      (fun M : Matrix ι ι Real => M i j) hH
    simpa [Matrix.IsHermitian, Matrix.conjTranspose] using hij
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, htranspose,
    orderedModeProjector_isIdempotentElem A hsimple k]
  rw [← Matrix.mulVec_transpose, htranspose, dotProduct_comm]

theorem orderedModeEnergy_sum_eq_coordinateEnergy
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (x : ι → Real) :
    ∑ k : Fin (Fintype.card ι), orderedModeEnergy A k x =
      ArchonPhysics.SpectralBandEnergyObservable.coordinateEnergy x := by
  simp_rw [orderedModeEnergy_eq_quadraticForm A hsimple]
  unfold orderedModeProjectedState
  unfold ArchonPhysics.SpectralBandEnergyObservable.coordinateEnergy
  have hdot :
      (∑ k : Fin (Fintype.card ι),
        x ⬝ᵥ orderedModeProjector A k *ᵥ x) =
      x ⬝ᵥ (∑ k : Fin (Fintype.card ι),
        orderedModeProjector A k *ᵥ x) := by
    unfold dotProduct
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [Finset.sum_apply]
    rw [Finset.mul_sum]
  have hmul :
      (∑ k : Fin (Fintype.card ι), orderedModeProjector A k) *ᵥ x =
        ∑ k : Fin (Fintype.card ι), orderedModeProjector A k *ᵥ x := by
    simpa using Matrix.sum_mulVec Finset.univ
      (fun k => orderedModeProjector A k) x
  rw [hdot]
  rw [← hmul, orderedModeProjector_sum_eq_one A hsimple,
    Matrix.one_mulVec]

omit [DecidableEq ι] in
theorem measurable_matrixVal_apply (u v : ι) :
    Measurable fun A : HermitianMatrix ι => matrixVal A u v := by
  change Measurable fun A : HermitianMatrix ι => A.1 u v
  exact (measurable_pi_apply v).comp
    ((measurable_pi_apply u).comp measurable_subtype_coe)

theorem measurable_orderedModeFactor_apply (k j : Fin (Fintype.card ι)) (u v : ι) :
    Measurable fun A : HermitianMatrix ι => orderedModeFactor A k j u v := by
  change Measurable fun A : HermitianMatrix ι =>
    (orderedEigenvalue A k - orderedEigenvalue A j)⁻¹ *
      (matrixVal A u v - orderedEigenvalue A j * (1 : Matrix ι ι Real) u v)
  exact (((continuous_orderedEigenvalue k).measurable.sub
      (continuous_orderedEigenvalue j).measurable).inv).mul
    ((measurable_matrixVal_apply u v).sub
      ((continuous_orderedEigenvalue j).measurable.mul measurable_const))

theorem measurable_listProduct_apply
    (k : Fin (Fintype.card ι)) :
    ∀ (L : List (Fin (Fintype.card ι))) (u v : ι),
      Measurable fun A : HermitianMatrix ι =>
        (L.map (orderedModeFactor A k)).prod u v
  | [], u, v => by simp
  | j :: L, u, v => by
      simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
      apply Finset.measurable_sum
      intro w _hw
      exact (measurable_orderedModeFactor_apply k j u w).mul
        (measurable_listProduct_apply k L w v)

theorem measurable_orderedModeProjector_apply (k : Fin (Fintype.card ι)) (u v : ι) :
    Measurable fun A : HermitianMatrix ι => orderedModeProjector A k u v := by
  exact measurable_listProduct_apply k (Finset.univ.erase k).toList u v


theorem measurable_orderedModeProjectedState_apply
    {Omega : Type*} [MeasurableSpace Omega]
    (sample : Omega → HermitianMatrix ι) (hsample : Measurable sample)
    (state : Omega → ι → Real) (hstate : Measurable state)
    (k : Fin (Fintype.card ι)) (u : ι) :
    Measurable fun omega =>
      orderedModeProjectedState (sample omega) k (state omega) u := by
  unfold orderedModeProjectedState Matrix.mulVec dotProduct
  apply Finset.measurable_sum
  intro v _hv
  exact ((measurable_orderedModeProjector_apply k u v).comp hsample).mul
    hstate.eval

theorem measurable_orderedModeEnergy
    {Omega : Type*} [MeasurableSpace Omega]
    (sample : Omega → HermitianMatrix ι) (hsample : Measurable sample)
    (state : Omega → ι → Real) (hstate : Measurable state)
    (k : Fin (Fintype.card ι)) :
    Measurable fun omega => orderedModeEnergy (sample omega) k (state omega) := by
  unfold orderedModeEnergy
  unfold ArchonPhysics.SpectralBandEnergyObservable.coordinateEnergy dotProduct
  apply Finset.measurable_sum
  intro u _hu
  exact (measurable_orderedModeProjectedState_apply
    sample hsample state hstate k u).mul
      (measurable_orderedModeProjectedState_apply
        sample hsample state hstate k u)

end
end ArchonPhysics.OrderedSingleModeProjector
