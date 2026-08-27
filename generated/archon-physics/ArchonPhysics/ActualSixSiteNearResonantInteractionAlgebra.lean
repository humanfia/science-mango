import ArchonPhysics.ActualSixSiteNearResonantPathSimpleSpectrum
import ArchonPhysics.DecayChannelModeEqualityPartition
import ArchonPhysics.FrozenCollisionMassPositivity
import ArchonPhysics.OrderedProjectorShiftedAdjugate
import ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison

open scoped Matrix BigOperators

/-!
# Interaction algebra for the six-site near-resonant channel

This module isolates the basis-free algebra needed by a collision-weight
witness.  It records that the selected ordered labels are all distinct and
reduces strict positivity of the normalized interaction weight to strict
positivity of the projector-defined tensor square.  On simple spectrum this
is equivalently nonvanishing of the usual cubic interaction tensor.

No numerical or spectral nonvanishing assertion is made here.
-/

namespace ArchonPhysics.ActualSixSiteNearResonantInteractionAlgebra

open ArchonPhysics
open ArchonPhysics.ActualSixSiteCleanDecayResonancePatch
open ArchonPhysics.ActualSixSiteThreeMassSimpleSpectrum
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.FrozenCollisionMassPositivity
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModeCoupling
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedProjectorLagrangeNumerator
open ArchonPhysics.OrderedProjectorShiftedAdjugate
open ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork

noncomputable section

/-- A harmonic numerator factor intertwines the site and bond Gram
presentations through the transposed mass-weighted difference matrix. -/
theorem harmonic_orderedModeNumeratorFactor_mul_transpose_eq_dual
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (j : Fin (Fintype.card (Lattice.Site N))) :
    orderedModeNumeratorFactor (harmonicHermitian mass) j *
        (massWeightedDifferenceMatrix mass).transpose =
      (massWeightedDifferenceMatrix mass).transpose *
        orderedModeNumeratorFactor
          (dualMassWeightedHarmonicHermitian mass) j := by
  unfold orderedModeNumeratorFactor
  rw [orderedEigenvalue_harmonic_eq_dual mass j]
  let B : Matrix (Lattice.Site N) (Lattice.Site N) Real :=
    massWeightedDifferenceMatrix mass
  let eigenvalue :=
    orderedEigenvalue (dualMassWeightedHarmonicHermitian mass) j
  change (B.transpose * B - eigenvalue • 1) * B.transpose =
    B.transpose * (B * B.transpose - eigenvalue • 1)
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_assoc]

/-- The factor intertwining survives every finite product. -/
theorem listProduct_harmonic_orderedModeNumeratorFactor_mul_transpose_eq_dual
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N) :
    ∀ indices : List (Fin (Fintype.card (Lattice.Site N))),
      (indices.map
          (orderedModeNumeratorFactor (harmonicHermitian mass))).prod *
          (massWeightedDifferenceMatrix mass).transpose =
        (massWeightedDifferenceMatrix mass).transpose *
          (indices.map (orderedModeNumeratorFactor
            (dualMassWeightedHarmonicHermitian mass))).prod
  | [] => by simp
  | j :: indices => by
      simp only [List.map_cons, List.prod_cons]
      rw [Matrix.mul_assoc,
        listProduct_harmonic_orderedModeNumeratorFactor_mul_transpose_eq_dual
          mass indices,
        ← Matrix.mul_assoc,
        harmonic_orderedModeNumeratorFactor_mul_transpose_eq_dual mass j,
        Matrix.mul_assoc]

/-- The complete denominator-free harmonic numerator intertwines the two
Gram presentations. -/
theorem harmonic_orderedModeProjectorNumerator_mul_transpose_eq_dual
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (k : Fin (Fintype.card (Lattice.Site N))) :
    orderedModeProjectorNumerator (harmonicHermitian mass) k *
        (massWeightedDifferenceMatrix mass).transpose =
      (massWeightedDifferenceMatrix mass).transpose *
        orderedModeProjectorNumerator
          (dualMassWeightedHarmonicHermitian mass) k := by
  unfold orderedModeProjectorNumerator
  exact
    listProduct_harmonic_orderedModeNumeratorFactor_mul_transpose_eq_dual
      mass _

/-- The Lagrange numerator is an eigenmatrix for left multiplication by its
selected Hermitian matrix.  No simplicity hypothesis is needed. -/
theorem matrixVal_mul_orderedModeProjectorNumerator
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) (k : Fin (Fintype.card ι)) :
    matrixVal A * orderedModeProjectorNumerator A k =
      orderedEigenvalue A k • orderedModeProjectorNumerator A k := by
  apply matrix_eq_of_mulVec_eigenvectorBasis_eq A
  intro r
  rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec]
  by_cases hr : r = k
  · subst r
    rw [orderedModeProjectorNumerator_mulVec_eigenvectorBasis]
    simp only [if_pos, Matrix.mulVec_smul,
      matrixVal_mulVec_eigenvectorBasis, smul_smul]
    rw [mul_comm]
  · rw [orderedModeProjectorNumerator_mulVec_eigenvectorBasis]
    simp [hr]

/-- Clearing the site-space spectral-gap denominator turns the projected
bond kernel into the selected eigenvalue times the edge-space shifted
adjugate. -/
theorem harmonic_orderedModeGapProduct_smul_projectedBondKernel_eq_dualAdjugate
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian mass))
    (k : Fin (Fintype.card (Lattice.Site N))) :
    orderedModeGapProduct (harmonicHermitian mass) k •
        projectedBondKernel (massWeightedDifferenceMatrix mass)
          (harmonicHermitian mass) k =
      orderedEigenvalue (harmonicHermitian mass) k •
        (orderedEigenvalueShiftedMatrix
          (dualMassWeightedHarmonicHermitian mass) k).adjugate := by
  let B : Matrix (Lattice.Site N) (Lattice.Site N) Real :=
    massWeightedDifferenceMatrix mass
  let A : HermitianMatrix (Lattice.Site N) := harmonicHermitian mass
  let D : HermitianMatrix (Lattice.Site N) :=
    dualMassWeightedHarmonicHermitian mass
  have hnumerator :
      orderedModeProjectorNumerator A k * B.transpose =
        B.transpose * orderedModeProjectorNumerator D k := by
    simpa [A, B, D] using
      harmonic_orderedModeProjectorNumerator_mul_transpose_eq_dual mass k
  have hDval : matrixVal D = B * B.transpose := by
    ext i j
    rfl
  have heigenvalue :
      orderedEigenvalue A k = orderedEigenvalue D k := by
    simpa [A, D] using orderedEigenvalue_harmonic_eq_dual mass k
  change orderedModeGapProduct A k • projectedBondKernel B A k =
    orderedEigenvalue A k •
      (orderedEigenvalueShiftedMatrix D k).adjugate
  calc
    orderedModeGapProduct A k • projectedBondKernel B A k =
        B * (orderedModeGapProduct A k • orderedModeProjector A k) *
          B.transpose := by
      rw [projectedBondKernel, Matrix.mul_smul, Matrix.smul_mul]
    _ = B * orderedModeProjectorNumerator A k * B.transpose := by
      rw [orderedModeGapProduct_smul_projector_eq_numerator A hsimple k]
    _ = B * (orderedModeProjectorNumerator A k * B.transpose) :=
      Matrix.mul_assoc _ _ _
    _ = B * (B.transpose * orderedModeProjectorNumerator D k) := by
      rw [hnumerator]
    _ = (B * B.transpose) * orderedModeProjectorNumerator D k :=
      (Matrix.mul_assoc _ _ _).symm
    _ = matrixVal D * orderedModeProjectorNumerator D k := by
      rw [hDval]
    _ = orderedEigenvalue D k • orderedModeProjectorNumerator D k :=
      matrixVal_mul_orderedModeProjectorNumerator D k
    _ = orderedEigenvalue A k • orderedModeProjectorNumerator D k := by
      rw [heigenvalue]
    _ = orderedEigenvalue A k •
        (orderedEigenvalueShiftedMatrix D k).adjugate := by
      rw [orderedModeProjectorNumerator_eq_shiftedAdjugate]

/-- Double coordinate sum of entrywise products of a finite family of
adjugates. -/
def adjugateEntryProductContraction
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    {n : Nat} (family : Fin n → Matrix ι ι R) : R :=
  ∑ i, ∑ j, ∏ r, (family r).adjugate i j

/-- The full double-sum adjugate contraction is invariant under simultaneous
reindexing of every matrix in the family. -/
theorem adjugateEntryProductContraction_reindex
    {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [CommRing R]
    (e : ι ≃ κ) {n : Nat} (family : Fin n → Matrix ι ι R) :
    adjugateEntryProductContraction
        (fun r => Matrix.reindex e e (family r)) =
      adjugateEntryProductContraction family := by
  unfold adjugateEntryProductContraction
  simp_rw [Matrix.adjugate_reindex, Matrix.reindex_apply]
  calc
    (∑ i : κ, ∑ j : κ,
        ∏ r, (family r).adjugate (e.symm i) (e.symm j)) =
        ∑ i : κ, ∑ j : ι,
          ∏ r, (family r).adjugate (e.symm i) j := by
      apply Fintype.sum_congr
      intro i
      exact e.symm.sum_comp
        (fun j => ∏ r, (family r).adjugate (e.symm i) j)
    _ = ∑ i : ι, ∑ j : ι, ∏ r, (family r).adjugate i j := by
      exact e.symm.sum_comp
        (fun i => ∑ j : ι, ∏ r, (family r).adjugate i j)

/-- Raw edge-space contraction of shifted adjugates.  This is the polynomial
quantity targeted by a resultant certificate. -/
def harmonicDualOrderedAdjugateInteractionContraction
    {N n : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (modes : Fin n → Fin (Fintype.card (Lattice.Site N))) : Real :=
  ∑ j, ∑ l, ∏ r,
    (orderedEigenvalueShiftedMatrix
      (dualMassWeightedHarmonicHermitian mass) (modes r)).adjugate j l

/-- Product-cleared exact bridge from the basis-free interaction weight to
the raw dual-adjugate contraction. -/
theorem harmonic_gapProduct_mul_interactionWeightSq_eq_eigenvalueProduct_mul_dualAdjugateContraction
    {N n : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian mass))
    (modes : Fin n → Fin (Fintype.card (Lattice.Site N))) :
    (∏ r, orderedModeGapProduct (harmonicHermitian mass) (modes r)) *
        harmonicOrderedInteractionWeightSq mass modes =
      (∏ r, orderedEigenvalue (harmonicHermitian mass) (modes r)) *
        harmonicDualOrderedAdjugateInteractionContraction mass modes := by
  let gap : Fin n → Real := fun r =>
    orderedModeGapProduct (harmonicHermitian mass) (modes r)
  let eigenvalue : Fin n → Real := fun r =>
    orderedEigenvalue (harmonicHermitian mass) (modes r)
  let kernel : Fin n →
      Matrix (Lattice.Site N) (Lattice.Site N) Real := fun r =>
    projectedBondKernel (massWeightedDifferenceMatrix mass)
      (harmonicHermitian mass) (modes r)
  let dualAdjugate : Fin n →
      Matrix (Lattice.Site N) (Lattice.Site N) Real := fun r =>
    (orderedEigenvalueShiftedMatrix
      (dualMassWeightedHarmonicHermitian mass) (modes r)).adjugate
  have hkernel (r : Fin n) (j l : Lattice.Site N) :
      gap r * kernel r j l = eigenvalue r * dualAdjugate r j l := by
    have hmatrix : gap r • kernel r = eigenvalue r • dualAdjugate r := by
      simpa [gap, eigenvalue, kernel, dualAdjugate] using
        harmonic_orderedModeGapProduct_smul_projectedBondKernel_eq_dualAdjugate
          mass hsimple (modes r)
    have hentry := congrArg (fun M => M j l) hmatrix
    simpa using hentry
  change (∏ r, gap r) * (∑ j, ∑ l, ∏ r, kernel r j l) =
    (∏ r, eigenvalue r) * (∑ j, ∑ l, ∏ r, dualAdjugate r j l)
  calc
    (∏ r, gap r) * (∑ j, ∑ l, ∏ r, kernel r j l) =
        ∑ j, ∑ l, (∏ r, gap r) * (∏ r, kernel r j l) := by
      simp only [Finset.mul_sum]
    _ = ∑ j, ∑ l, ∏ r, gap r * kernel r j l := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro l _hl
      rw [Finset.prod_mul_distrib]
    _ = ∑ j, ∑ l, ∏ r, eigenvalue r * dualAdjugate r j l := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro l _hl
      apply Finset.prod_congr rfl
      intro r _hr
      exact hkernel r j l
    _ = ∑ j, ∑ l,
        (∏ r, eigenvalue r) * (∏ r, dualAdjugate r j l) := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro l _hl
      rw [Finset.prod_mul_distrib]
    _ = (∏ r, eigenvalue r) *
        (∑ j, ∑ l, ∏ r, dualAdjugate r j l) := by
      simp only [Finset.mul_sum]

/-- A nonzero dual-adjugate contraction forces strictly positive
basis-free interaction weight whenever the selected energies are nonzero. -/
theorem harmonicOrderedInteractionWeightSq_pos_of_dualAdjugateContraction_ne_zero
    {N n : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian mass))
    (modes : Fin n → Fin (Fintype.card (Lattice.Site N)))
    (henergy : ∀ r,
      orderedEigenvalue (harmonicHermitian mass) (modes r) ≠ 0)
    (hcontraction :
      harmonicDualOrderedAdjugateInteractionContraction mass modes ≠ 0) :
    0 < harmonicOrderedInteractionWeightSq mass modes := by
  have henergyProduct :
      (∏ r, orderedEigenvalue
        (harmonicHermitian mass) (modes r)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro r _hr
    exact henergy r
  have hclearedNe :
      (∏ r, orderedModeGapProduct
        (harmonicHermitian mass) (modes r)) *
          harmonicOrderedInteractionWeightSq mass modes ≠ 0 := by
    rw [harmonic_gapProduct_mul_interactionWeightSq_eq_eigenvalueProduct_mul_dualAdjugateContraction
      mass hsimple modes]
    exact mul_ne_zero henergyProduct hcontraction
  have hweightNe : harmonicOrderedInteractionWeightSq mass modes ≠ 0 := by
    intro hzero
    apply hclearedNe
    rw [hzero, mul_zero]
  have hweightNonneg :
      0 ≤ harmonicOrderedInteractionWeightSq mass modes := by
    exact orderedInteractionWeightSq_nonneg
      (massWeightedDifferenceMatrix mass) (harmonicHermitian mass) modes
  exact lt_of_le_of_ne hweightNonneg (Ne.symm hweightNe)

/-- The ordered six-site decay labels `0`, `3`, and `4` are pairwise
distinct, so this channel belongs to the all-distinct sector. -/
theorem cleanSixSiteDecayModes_allDistinct :
    AllDistinctModes cleanSixSiteDecayModes := by
  change (3 : Fin 6) ≠ 4 ∧ (0 : Fin 6) ≠ 3 ∧ (0 : Fin 6) ≠ 4
  decide

/-- If all selected ordered frequencies are positive, normalization by their
inverse product neither creates nor destroys strict positivity of the
basis-free interaction square. -/
theorem harmonicOrderedNormalizedInteractionWeight_pos_iff_weightSq_pos
    {N n : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (modes : Fin n → Fin (Fintype.card (Lattice.Site N)))
    (hpositive : ∀ r, 0 < orderedModeFrequency
      (harmonicHermitian mass) (modes r)) :
    0 < harmonicOrderedNormalizedInteractionWeight mass modes ↔
      0 < harmonicOrderedInteractionWeightSq mass modes := by
  have hproduct : 0 <
      (∏ r, (2 * orderedModeFrequency
        (harmonicHermitian mass) (modes r))⁻¹) := by
    apply Finset.prod_pos
    intro r _hr
    exact inv_pos.mpr (mul_pos zero_lt_two (hpositive r))
  constructor
  · intro hweight
    have hsquareNonneg :
        0 ≤ harmonicOrderedInteractionWeightSq mass modes := by
      exact orderedInteractionWeightSq_nonneg
        (massWeightedDifferenceMatrix mass) (harmonicHermitian mass) modes
    have hsquareNe : harmonicOrderedInteractionWeightSq mass modes ≠ 0 := by
      intro hsquare
      unfold harmonicOrderedNormalizedInteractionWeight at hweight
      rw [hsquare, zero_mul] at hweight
      exact (lt_irrefl 0) hweight
    exact lt_of_le_of_ne hsquareNonneg (Ne.symm hsquareNe)
  · intro hsquare
    unfold harmonicOrderedNormalizedInteractionWeight
    exact mul_pos hsquare hproduct

/-- The same resultant-style nonvanishing certificate yields positivity of
the frequency-normalized collision weight. -/
theorem harmonicOrderedNormalizedInteractionWeight_pos_of_dualAdjugateContraction_ne_zero
    {N n : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian mass))
    (modes : Fin n → Fin (Fintype.card (Lattice.Site N)))
    (hfrequency : ∀ r, 0 < orderedModeFrequency
      (harmonicHermitian mass) (modes r))
    (hcontraction :
      harmonicDualOrderedAdjugateInteractionContraction mass modes ≠ 0) :
    0 < harmonicOrderedNormalizedInteractionWeight mass modes := by
  apply (harmonicOrderedNormalizedInteractionWeight_pos_iff_weightSq_pos
    mass modes hfrequency).2
  apply harmonicOrderedInteractionWeightSq_pos_of_dualAdjugateContraction_ne_zero
    mass hsimple modes
  · intro r
    apply ne_of_gt
    exact Real.sqrt_pos.1 (by
      simpa [orderedModeFrequency] using hfrequency r)
  · exact hcontraction

/-- For the genuine six-site slice, simple spectrum makes normalized
collision-weight positivity exactly the nonvanishing of the ordinary cubic
interaction tensor in the selected ordered modes. -/
theorem actualSixSite_normalizedInteractionWeight_pos_iff_tensor_ne_zero
    (triple : ThreeParameterSpectralAveragingDensity.MassTriple)
    (hsimple : SimpleOrderedSpectrum
      (actualSixSiteThreeMassHarmonic triple)) :
    0 < harmonicOrderedNormalizedInteractionWeight
        (actualSixSiteThreeMassConfig triple) cleanSixSiteDecayModes ↔
      interactionTensor (actualSixSiteThreeMassConfig triple) 3
        (fun r ↦ orderedIndexEquiv (cleanSixSiteDecayModes r)) ≠ 0 := by
  have hsimple' : SimpleOrderedSpectrum
      (harmonicHermitian (actualSixSiteThreeMassConfig triple)) := by
    simpa [actualSixSiteThreeMassHarmonic, actualSixSiteThreeMassConfig,
      ActualThreeMassLiftedSpectralChart.threeMassHarmonicHermitian] using
        hsimple
  have hpositive : ∀ r, 0 < orderedModeFrequency
      (harmonicHermitian (actualSixSiteThreeMassConfig triple))
      (cleanSixSiteDecayModes r) := by
    intro r
    rw [orderedModeFrequency]
    exact Real.sqrt_pos.2 (by
      simpa [actualSixSiteThreeMassHarmonic, actualSixSiteThreeMassConfig,
        ActualThreeMassLiftedSpectralChart.threeMassHarmonicHermitian] using
          actualSixSiteDecayModes_energy_pos_of_simple triple hsimple r)
  rw [harmonicOrderedNormalizedInteractionWeight_pos_iff_weightSq_pos
    (actualSixSiteThreeMassConfig triple) cleanSixSiteDecayModes hpositive]
  rw [harmonicOrderedInteractionWeightSq_eq
    (actualSixSiteThreeMassConfig triple) hsimple' cleanSixSiteDecayModes]
  exact sq_pos_iff

end

end ArchonPhysics.ActualSixSiteNearResonantInteractionAlgebra
