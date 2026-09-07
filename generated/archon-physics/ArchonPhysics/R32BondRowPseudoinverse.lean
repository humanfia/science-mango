import ArchonPhysics.HarmonicNormalizedEdgeFrame

/-!
# R32 bond-row pseudoinverse identity

Let `C` be the periodic mass-weighted difference matrix and let
`A = Cᵀ C` be the harmonic matrix.  If `v_k` is an ordered unit eigenvector,
write `b_{ik} = (C v_k)_i` and `omega_k²` for its eigenvalue.  On simple
spectrum, the positive-mode part of the bond-space pseudoinverse has diagonal

`sum_{omega_k > 0} b_{ik}² / omega_k²`.

The normalized positive bond modes, together with the normalized constant
bond vector, are a square orthonormal frame.  Finite-dimensional Parseval
therefore identifies the displayed sum with the diagonal of the orthogonal
projector onto the mean-zero bond subspace.  In particular it is exactly
`1 - 1 / N`, and hence at most one.  No lower spectral-gap estimate enters.
-/

open scoped BigOperators Matrix

namespace ArchonPhysics.R32BondRowPseudoinverse

open ArchonPhysics
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.ThreeLegKernelApproximationAlgebra

noncomputable section

/-- The orthogonal projector in bond space onto the complement of the
normalized constant edge vector.  This is the range projector of the
periodic incidence matrix. -/
def meanZeroBondProjector {N : Nat} [NeZero N] :
    Matrix (Lattice.Site N) (Lattice.Site N) Real :=
  1 - Matrix.vecMulVec
    (constantEdgeMode (N := N)) (constantEdgeMode (N := N))

/-- The diagonal entry of `C (Cᵀ C)⁺ Cᵀ`, written directly in its positive
ordered spectral expansion. -/
def bondRowPseudoinverseDiagonal {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (i : Lattice.Site N) : Real :=
  ∑ k ∈ positiveModeIndices (harmonicHermitian m),
    orderedRawEdgeMode m k i ^ 2 /
      orderedModeFrequency (harmonicHermitian m) k ^ 2

/-- The square of the normalized constant edge coordinate is exactly
`1 / N`. -/
theorem constantEdgeMode_sq_eq_inv_card
    {N : Nat} [NeZero N] (i : Lattice.Site N) :
    constantEdgeMode (N := N) i ^ 2 = ((N : Real))⁻¹ := by
  simp only [constantEdgeMode]
  rw [inv_pow, Real.sq_sqrt]
  positivity

/-- Exact row-pseudoinverse identity: the positive spectral sum is the
corresponding diagonal of the mean-zero bond-space range projector. -/
theorem bondRowPseudoinverseDiagonal_eq_meanZeroBondProjector_diag
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (i : Lattice.Site N) :
    bondRowPseudoinverseDiagonal m i = meanZeroBondProjector i i := by
  let z : HarmonicOrderedModeIndex N :=
    lastOrderedIndex (ι := Lattice.Site N)
  have hfull :
      (∑ k : HarmonicOrderedModeIndex N,
        harmonicNormalizedEdgeFrame m k i ^ 2) = 1 := by
    simpa [rowEnergy] using
      (rowEnergy_eq_one_of_orthonormal_of_card_eq
        (harmonicNormalizedEdgeFrame m)
        (by simp [HarmonicOrderedModeIndex])
        (harmonicNormalizedEdgeFrame_orthonormal m hsimple) i)
  have hsplit :
      (∑ k ∈ (Finset.univ.erase z),
          harmonicNormalizedEdgeFrame m k i ^ 2) +
        harmonicNormalizedEdgeFrame m z i ^ 2 = 1 := by
    rw [Finset.sum_erase_add Finset.univ _ (Finset.mem_univ z)]
    exact hfull
  have hpositive :
      (∑ k ∈ positiveModeIndices (harmonicHermitian m),
          orderedRawEdgeMode m k i ^ 2 /
            orderedModeFrequency (harmonicHermitian m) k ^ 2) =
        ∑ k ∈ (Finset.univ.erase z),
          harmonicNormalizedEdgeFrame m k i ^ 2 := by
    rw [positiveModeIndices_eq_univ_erase_last m hsimple]
    apply Finset.sum_congr rfl
    intro k hk
    have hkne : k ≠ lastOrderedIndex (ι := Lattice.Site N) :=
      (Finset.mem_erase.mp hk).1
    simp only [harmonicNormalizedEdgeFrame, if_neg hkne, div_pow]
  unfold bondRowPseudoinverseDiagonal
  rw [hpositive]
  have hzframe : harmonicNormalizedEdgeFrame m z i =
      constantEdgeMode (N := N) i := by
    simp [harmonicNormalizedEdgeFrame, z]
  rw [hzframe] at hsplit
  simp only [meanZeroBondProjector, Matrix.sub_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply, if_pos, pow_two]
  simpa only [pow_two] using (eq_sub_of_add_eq hsplit)

/-- Scalar closed form of the projector diagonal. -/
theorem bondRowPseudoinverseDiagonal_eq_one_sub_inv_card
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (i : Lattice.Site N) :
    bondRowPseudoinverseDiagonal m i = 1 - ((N : Real))⁻¹ := by
  rw [bondRowPseudoinverseDiagonal_eq_meanZeroBondProjector_diag m hsimple i]
  simp only [meanZeroBondProjector, Matrix.sub_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply, if_pos]
  rw [← pow_two, constantEdgeMode_sq_eq_inv_card i]

/-- The requested uniform row bound, in the literal notation
`sum b_{ik}² / omega_k² <= 1`. -/
theorem sum_positive_orderedRawEdgeMode_sq_div_frequency_sq_le_one
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (i : Lattice.Site N) :
    (∑ k ∈ positiveModeIndices (harmonicHermitian m),
      orderedRawEdgeMode m k i ^ 2 /
        orderedModeFrequency (harmonicHermitian m) k ^ 2) ≤ 1 := by
  change bondRowPseudoinverseDiagonal m i ≤ 1
  rw [bondRowPseudoinverseDiagonal_eq_one_sub_inv_card m hsimple i]
  exact sub_le_self 1 (by positivity)

end

end ArchonPhysics.R32BondRowPseudoinverse
