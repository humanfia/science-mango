import ArchonPhysics.MeasurableOrderedModeCoupling

/-!
# Explicit globally measurable signed ordered eigenvectors

For each totalized ordered Lagrange projector, this module scans the finite
site enumeration `orderedIndexEquiv` and chooses the first strictly positive
diagonal entry.  The corresponding column is divided by the square root of
that entry.  Rather than hiding this finite scan behind a measurable-choice
interface, the globally defined vector is written as a finite sum over the
mutually exclusive first-pivot events.  If no positive diagonal exists, that
sum is zero.

On simple spectrum the ordered projector is rank one, so a positive pivot
exists.  The resulting vector has positive pivot coordinate, Euclidean norm
one, rank-one outer product equal to the ordered projector, and is an
eigenvector for the matching ordered eigenvalue.  No phase law, collision
asymptotic, or thermalization statement is made here.
-/

open scoped Matrix

namespace ArchonPhysics.MeasurableOrderedEigenframe

open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Site attached to the finite canonical enumeration used by the ordered
spectral API. -/
def pivotSite (r : Fin (Fintype.card ι)) : ι :=
  orderedIndexEquiv r

/-- The candidate pivots with strictly positive projector diagonal. -/
def positiveDiagonalIndices (A : HermitianMatrix ι)
    (k : Fin (Fintype.card ι)) : Finset (Fin (Fintype.card ι)) :=
  Finset.univ.filter fun r =>
    0 < orderedModeProjector A k (pivotSite r) (pivotSite r)

/-- `r` is the first positive diagonal coordinate in the finite enumeration. -/
def IsFirstPositiveDiagonal (A : HermitianMatrix ι)
    (k r : Fin (Fintype.card ι)) : Prop :=
  0 < orderedModeProjector A k (pivotSite r) (pivotSite r) ∧
    ∀ s, s < r →
      orderedModeProjector A k (pivotSite s) (pivotSite s) ≤ 0

/-- Totalized pivot index.  The fallback is irrelevant on simple spectrum. -/
def orderedModePivotIndex (A : HermitianMatrix ι)
    (k : Fin (Fintype.card ι)) : Fin (Fintype.card ι) :=
  if h : (positiveDiagonalIndices A k).Nonempty then
    (positiveDiagonalIndices A k).min' h
  else k

/-- Totalized pivot site. -/
def orderedModePivotSite (A : HermitianMatrix ι)
    (k : Fin (Fintype.card ι)) : ι :=
  pivotSite (orderedModePivotIndex A k)

/-- Explicit signed vector.  Exactly one term survives when a positive
diagonal exists; if there is none, the vector is totalized to zero. -/
def signedOrderedEigenvector (A : HermitianMatrix ι)
    (k : Fin (Fintype.card ι)) : ι → Real := by
  classical
  exact fun i =>
    ∑ r : Fin (Fintype.card ι),
      if IsFirstPositiveDiagonal A k r then
        orderedModeProjector A k i (pivotSite r) /
          Real.sqrt (orderedModeProjector A k (pivotSite r) (pivotSite r))
      else 0

/-- The same vector in the Euclidean `L²` wrapper, for an actual norm-one
statement rather than only a coordinate-square identity. -/
def signedOrderedEigenvectorLp (A : HermitianMatrix ι)
    (k : Fin (Fintype.card ι)) : EuclideanSpace Real ι :=
  WithLp.toLp 2 (signedOrderedEigenvector A k)

theorem isFirstPositiveDiagonal_unique
    (A : HermitianMatrix ι) (k : Fin (Fintype.card ι))
    {r s : Fin (Fintype.card ι)}
    (hr : IsFirstPositiveDiagonal A k r)
    (hs : IsFirstPositiveDiagonal A k s) : r = s := by
  apply le_antisymm
  · apply not_lt.mp
    intro hsr
    exact (not_lt_of_ge (hr.2 s hsr)) hs.1
  · apply not_lt.mp
    intro hrs
    exact (not_lt_of_ge (hs.2 r hrs)) hr.1

theorem isFirstPositiveDiagonal_min'
    (A : HermitianMatrix ι) (k : Fin (Fintype.card ι))
    (h : (positiveDiagonalIndices A k).Nonempty) :
    IsFirstPositiveDiagonal A k ((positiveDiagonalIndices A k).min' h) := by
  let r := (positiveDiagonalIndices A k).min' h
  have hrmem : r ∈ positiveDiagonalIndices A k :=
    Finset.min'_mem _ h
  refine ⟨?_, ?_⟩
  · simpa [positiveDiagonalIndices, r] using hrmem
  · intro s hsr
    by_contra hs
    have hspos : 0 <
        orderedModeProjector A k (pivotSite s) (pivotSite s) :=
      lt_of_not_ge hs
    have hsmem : s ∈ positiveDiagonalIndices A k := by
      simp [positiveDiagonalIndices, hspos]
    exact (not_lt_of_ge (Finset.min'_le _ _ hsmem)) hsr

theorem orderedModePivotIndex_eq_min'
    (A : HermitianMatrix ι) (k : Fin (Fintype.card ι))
    (h : (positiveDiagonalIndices A k).Nonempty) :
    orderedModePivotIndex A k = (positiveDiagonalIndices A k).min' h := by
  simp [orderedModePivotIndex, h]

theorem isFirstPositiveDiagonal_orderedModePivotIndex
    (A : HermitianMatrix ι) (k : Fin (Fintype.card ι))
    (h : (positiveDiagonalIndices A k).Nonempty) :
    IsFirstPositiveDiagonal A k (orderedModePivotIndex A k) := by
  rw [orderedModePivotIndex_eq_min' A k h]
  exact isFirstPositiveDiagonal_min' A k h

theorem signedOrderedEigenvector_apply_of_isFirst
    (A : HermitianMatrix ι) (k r : Fin (Fintype.card ι))
    (hr : IsFirstPositiveDiagonal A k r) (i : ι) :
    signedOrderedEigenvector A k i =
      orderedModeProjector A k i (pivotSite r) /
        Real.sqrt (orderedModeProjector A k (pivotSite r) (pivotSite r)) := by
  classical
  let f : Fin (Fintype.card ι) → Real := fun s =>
    if IsFirstPositiveDiagonal A k s then
      orderedModeProjector A k i (pivotSite s) /
        Real.sqrt (orderedModeProjector A k (pivotSite s) (pivotSite s))
    else 0
  change (∑ s, f s) = _
  calc
    (∑ s, f s) = f r := by
      apply Finset.sum_eq_single r
      · intro s _hs hsr
        have hsnot : ¬ IsFirstPositiveDiagonal A k s := by
          intro hs
          exact hsr (isFirstPositiveDiagonal_unique A k hs hr)
        simp [f, hsnot]
      · simp
    _ = _ := by simp [f, hr]

theorem signedOrderedEigenvector_pivot_pos_of_isFirst
    (A : HermitianMatrix ι) (k r : Fin (Fintype.card ι))
    (hr : IsFirstPositiveDiagonal A k r) :
    0 < signedOrderedEigenvector A k (pivotSite r) := by
  rw [signedOrderedEigenvector_apply_of_isFirst A k r hr]
  exact div_pos hr.1 (Real.sqrt_pos.2 hr.1)

theorem positiveDiagonalIndices_nonempty_of_simple
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (k : Fin (Fintype.card ι)) :
    (positiveDiagonalIndices A k).Nonempty := by
  let e : ι → Real :=
    ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k))
  have hdot : e ⬝ᵥ e = 1 := by
    change ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k)) ⬝ᵥ
      ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k)) = 1
    have hinner := A.2.eigenvectorBasis.inner_eq_one (orderedIndexEquiv k)
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hinner
  have hene : e ≠ 0 := by
    intro he
    rw [he] at hdot
    simp at hdot
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hene
  have hi' : e i ≠ 0 := by simpa using hi
  let r : Fin (Fintype.card ι) := orderedIndexEquiv.symm i
  refine ⟨r, ?_⟩
  have hdiag : 0 < orderedModeProjector A k i i := by
    rw [orderedModeProjector_eq_vecMulVec A hsimple k]
    simpa [Matrix.vecMulVec_apply, e] using (mul_self_pos.mpr hi')
  simp only [positiveDiagonalIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  simpa [pivotSite, r] using hdiag

theorem signedOrderedEigenvector_outerProduct_of_isFirst
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (k r : Fin (Fintype.card ι))
    (hr : IsFirstPositiveDiagonal A k r) :
    Matrix.vecMulVec (signedOrderedEigenvector A k)
        (signedOrderedEigenvector A k) = orderedModeProjector A k := by
  let p := pivotSite (ι := ι) r
  let d := orderedModeProjector A k p p
  have hd : 0 < d := hr.1
  have hsqrt : Real.sqrt d ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hd)
  have hprojector := orderedModeProjector_eq_vecMulVec A hsimple k
  have hcross (i j : ι) :
      orderedModeProjector A k i p * orderedModeProjector A k j p =
        orderedModeProjector A k i j * d := by
    dsimp [d, p]
    rw [hprojector]
    simp only [Matrix.vecMulVec_apply]
    ring
  ext i j
  rw [Matrix.vecMulVec_apply,
    signedOrderedEigenvector_apply_of_isFirst A k r hr i,
    signedOrderedEigenvector_apply_of_isFirst A k r hr j]
  change (_ / Real.sqrt d) * (_ / Real.sqrt d) = _
  field_simp [hsqrt]
  change orderedModeProjector A k i p * orderedModeProjector A k j p =
    Real.sqrt d ^ 2 * orderedModeProjector A k i j
  rw [Real.sq_sqrt hd.le, hcross]
  ring

theorem signedOrderedEigenvector_outerProduct
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (k : Fin (Fintype.card ι)) :
    Matrix.vecMulVec (signedOrderedEigenvector A k)
        (signedOrderedEigenvector A k) = orderedModeProjector A k := by
  let h := positiveDiagonalIndices_nonempty_of_simple A hsimple k
  exact signedOrderedEigenvector_outerProduct_of_isFirst A hsimple k
    (orderedModePivotIndex A k)
    (isFirstPositiveDiagonal_orderedModePivotIndex A k h)

theorem signedOrderedEigenvector_dot_self
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (k : Fin (Fintype.card ι)) :
    signedOrderedEigenvector A k ⬝ᵥ signedOrderedEigenvector A k = 1 := by
  let e : ι → Real :=
    ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k))
  calc
    signedOrderedEigenvector A k ⬝ᵥ signedOrderedEigenvector A k =
        Matrix.trace (Matrix.vecMulVec (signedOrderedEigenvector A k)
          (signedOrderedEigenvector A k)) :=
      (Matrix.trace_vecMulVec _ _).symm
    _ = Matrix.trace (orderedModeProjector A k) := by
      rw [signedOrderedEigenvector_outerProduct A hsimple k]
    _ = Matrix.trace (Matrix.vecMulVec e e) := by
      rw [orderedModeProjector_eq_vecMulVec A hsimple k]
    _ = e ⬝ᵥ e := Matrix.trace_vecMulVec _ _
    _ = 1 := by
      change ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k)) ⬝ᵥ
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k)) = 1
      have hinner := A.2.eigenvectorBasis.inner_eq_one (orderedIndexEquiv k)
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hinner

theorem signedOrderedEigenvectorLp_norm
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (k : Fin (Fintype.card ι)) :
    ‖signedOrderedEigenvectorLp A k‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one]
  rw [one_pow, EuclideanSpace.real_norm_sq_eq]
  simpa [signedOrderedEigenvectorLp, dotProduct, pow_two] using
    signedOrderedEigenvector_dot_self A hsimple k

theorem signedOrderedEigenvector_eigenvector
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (k : Fin (Fintype.card ι)) :
    matrixVal A *ᵥ signedOrderedEigenvector A k =
      orderedEigenvalue A k • signedOrderedEigenvector A k := by
  let v := signedOrderedEigenvector A k
  have houter : Matrix.vecMulVec v v = orderedModeProjector A k :=
    signedOrderedEigenvector_outerProduct A hsimple k
  have hdot : v ⬝ᵥ v = 1 :=
    signedOrderedEigenvector_dot_self A hsimple k
  have hAP := matrixVal_mul_orderedModeProjector A hsimple k
  rw [← houter] at hAP
  have happ := congrArg (fun M : Matrix ι ι Real => M *ᵥ v) hAP
  simpa [← Matrix.mulVec_mulVec, Matrix.vecMulVec_mulVec,
    Matrix.smul_mulVec, hdot] using happ

theorem measurableSet_isFirstPositiveDiagonal
    {Omega : Type*} [MeasurableSpace Omega]
    (sample : Omega → HermitianMatrix ι) (hsample : Measurable sample)
    (k r : Fin (Fintype.card ι)) :
    MeasurableSet {omega | IsFirstPositiveDiagonal (sample omega) k r} := by
  have hdiag (s : Fin (Fintype.card ι)) :
      Measurable fun omega =>
        orderedModeProjector (sample omega) k (pivotSite s) (pivotSite s) :=
    (measurable_orderedModeProjector_apply k (pivotSite s) (pivotSite s)).comp hsample
  have hpos : MeasurableSet {omega |
      0 < orderedModeProjector (sample omega) k (pivotSite r) (pivotSite r)} :=
    measurableSet_Ioi.preimage (hdiag r)
  have hnonpos (s : Fin (Fintype.card ι)) : MeasurableSet {omega |
      orderedModeProjector (sample omega) k (pivotSite s) (pivotSite s) ≤ 0} :=
    measurableSet_Iic.preimage (hdiag s)
  have hall : MeasurableSet {omega |
      ∀ s, s < r →
        orderedModeProjector (sample omega) k (pivotSite s) (pivotSite s) ≤ 0} := by
    have hinter : MeasurableSet
        (⋂ s : Fin (Fintype.card ι), ⋂ (_h : s < r),
          {omega | orderedModeProjector (sample omega) k
            (pivotSite s) (pivotSite s) ≤ 0}) :=
      MeasurableSet.iInter fun s => MeasurableSet.iInter fun _h => hnonpos s
    have heq : {omega |
        ∀ s, s < r →
          orderedModeProjector (sample omega) k (pivotSite s) (pivotSite s) ≤ 0} =
        ⋂ s : Fin (Fintype.card ι), ⋂ (_h : s < r),
          {omega | orderedModeProjector (sample omega) k
            (pivotSite s) (pivotSite s) ≤ 0} := by
      ext omega
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rw [heq]
    exact hinter
  exact hpos.inter hall

/-- Every coordinate of the explicitly signed vector is globally measurable,
including at degenerate matrices where it is totalized by the finite sum. -/
theorem measurable_signedOrderedEigenvector_apply
    {Omega : Type*} [MeasurableSpace Omega]
    (sample : Omega → HermitianMatrix ι) (hsample : Measurable sample)
    (k : Fin (Fintype.card ι)) (i : ι) :
    Measurable fun omega => signedOrderedEigenvector (sample omega) k i := by
  unfold signedOrderedEigenvector
  apply Finset.measurable_sum
  intro r _hr
  apply Measurable.ite
    (measurableSet_isFirstPositiveDiagonal sample hsample k r)
  · exact ((measurable_orderedModeProjector_apply k i (pivotSite r)).comp hsample).div
      (((measurable_orderedModeProjector_apply k (pivotSite r) (pivotSite r)).comp
        hsample).sqrt)
  · exact measurable_const

/-- The entire signed frame vector is globally measurable in the product
coordinate space. -/
theorem measurable_signedOrderedEigenvector
    {Omega : Type*} [MeasurableSpace Omega]
    (sample : Omega → HermitianMatrix ι) (hsample : Measurable sample)
    (k : Fin (Fintype.card ι)) :
    Measurable fun omega => signedOrderedEigenvector (sample omega) k := by
  exact measurable_pi_lambda _ fun i =>
    measurable_signedOrderedEigenvector_apply sample hsample k i

/-- The Euclidean wrapper of the signed vector is globally measurable. -/
theorem measurable_signedOrderedEigenvectorLp
    {Omega : Type*} [MeasurableSpace Omega]
    (sample : Omega → HermitianMatrix ι) (hsample : Measurable sample)
    (k : Fin (Fintype.card ι)) :
    Measurable fun omega => signedOrderedEigenvectorLp (sample omega) k := by
  apply (WithLp.measurable_toLp 2 _).comp
  exact measurable_signedOrderedEigenvector sample hsample k

end

end ArchonPhysics.MeasurableOrderedEigenframe
