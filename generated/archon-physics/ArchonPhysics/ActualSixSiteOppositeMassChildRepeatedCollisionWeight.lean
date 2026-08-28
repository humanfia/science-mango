import ArchonPhysics.ActualSixSiteExactChildRepeatedLinearSmallBall
import ArchonPhysics.ActualSixSiteNearResonantInteractionAlgebra

/-!
# Vanishing collision weight on the opposite-mass child-repeated resonance

The opposite-site six-cycle used by the exact child-repeated small-ball
witness has an exact reflection selection rule.  Every non-structural
edge-space eigendirection is odd under bond reversal.  Thus the cubic product
with one parent leg and two copies of the child leg is odd, and its finite
bond sum vanishes.

The proof is stated through shifted adjugates and the basis-free ordered
projector weight.  Consequently it does not depend on the sign convention of
any chosen eigenvector frame.
-/

open scoped BigOperators Matrix

namespace ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedCollisionWeight

open ArchonPhysics
open ArchonPhysics.ActualSixSiteExactChildRepeatedLinearSmallBall
open ArchonPhysics.ActualSixSiteNearResonantInteractionAlgebra
open ArchonPhysics.ActualSixSiteNearResonantJacobianWitness
open ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedExactResonance
open ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedJacobian
open ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedSimpleSpectrum
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedCycleBridge
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedProjectorLagrangeNumerator
open ArchonPhysics.OrderedProjectorShiftedAdjugate
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.RandomMassResultantBridge
open ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison
open ArchonPhysics.TwoParameterSpectralAveragingAtlas

noncomputable section

/-- The ordered parent-child-child tuple used by the exact resonance. -/
def oppositeChildRepeatedModes : Fin 3 → Fin 6 := ![0, 3, 3]

/-- Reversal of the six bond coordinates. -/
def reverseFinSix (i : Fin 6) : Fin 6 := ![5, 4, 3, 2, 1, 0] i

/-- Bond reversal as a finite equivalence. -/
def reverseFinSixEquiv : Fin 6 ≃ Fin 6 where
  toFun := reverseFinSix
  invFun := reverseFinSix
  left_inv i := by fin_cases i <;> decide
  right_inv i := by fin_cases i <;> decide

/-- At a non-structural eigenvalue, every column of the shifted
adjugate is odd under bond reversal. -/
theorem explicitSixSiteOppositeWeightShiftedMatrix_adjugate_reverse_row
    (x y energy : Real)
    (hroot : oppositeSixSiteCubic x y energy = 0)
    (hstruct : energy * (energy - 1) * (energy - 3) ≠ 0)
    (i j : Fin 6) :
    (explicitSixSiteOppositeWeightShiftedMatrix x y energy).adjugate
        (reverseFinSix i) j =
      -(explicitSixSiteOppositeWeightShiftedMatrix x y energy).adjugate i j := by
  let S := explicitSixSiteOppositeWeightShiftedMatrix x y energy
  let u : Fin 6 → Real := fun q ↦ S.adjugate q j
  have hdet : S.det = 0 := by
    dsimp [S]
    rw [← scalar_sub_explicitSixSiteOppositeWeightLaplacian,
      ← Matrix.eval_charpoly,
      explicitSixSiteOppositeWeightLaplacian_charpoly_eval, hroot, mul_zero]
  have hkernel (k : Fin 6) : ∑ q, S k q * u q = 0 := by
    have hmul := congrArg (fun M : Matrix (Fin 6) (Fin 6) Real ↦ M k j)
      (Matrix.mul_adjugate S)
    simp only [Matrix.mul_apply] at hmul
    simpa [hdet] using hmul
  have h0 := hkernel (0 : Fin 6)
  have h1 := hkernel (Fin.succ (0 : Fin 5))
  have h2 := hkernel (Fin.succ (Fin.succ (0 : Fin 4)))
  have h3 := hkernel (Fin.succ (Fin.succ (Fin.succ (0 : Fin 3))))
  have h4 := hkernel (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 2)))))
  have h5 := hkernel
    (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1))))))
  simp only [S, explicitSixSiteOppositeWeightShiftedMatrix,
    Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5
  simp at h0 h1 h2 h3 h4 h5
  let a := u 0 + u 5
  let b := u 1 + u 4
  let c := u 2 + u 3
  have haeq : (energy - 1) * a + b = 0 := by
    dsimp [a, b]
    linarith [h0, h5]
  have hbeq : a + (energy - 2) * b + c = 0 := by
    dsimp [a, b, c]
    linarith [h1, h4]
  have hceq : b + (energy - 1) * c = 0 := by
    dsimp [b, c]
    linarith [h2, h3]
  have hdetA : energy * (energy - 1) * (energy - 3) * a = 0 := by
    linear_combination
      ((energy - 2) * (energy - 1) - 1) * haeq -
        (energy - 1) * hbeq + hceq
  have ha : a = 0 := (mul_eq_zero.mp hdetA).resolve_left hstruct
  have hb : b = 0 := by
    rw [ha, mul_zero, zero_add] at haeq
    exact haeq
  have hc : c = 0 := by
    have heone : energy - 1 ≠ 0 := by
      intro he
      apply hstruct
      have : energy = 1 := sub_eq_zero.mp he
      simp [this]
    rw [hb, zero_add] at hceq
    exact (mul_eq_zero.mp hceq).resolve_left heone
  fin_cases i
  · change u 5 = -u 0
    linarith [ha]
  · change u 4 = -u 1
    linarith [hb]
  · change u 3 = -u 2
    linarith [hc]
  · change u 2 = -u 3
    linarith [hc]
  · change u 1 = -u 4
    linarith [hb]
  · change u 0 = -u 5
    linarith [ha]

/-- Spectral parameters for one parent leg followed by two identical child
legs. -/
def oppositeChildRepeatedEnergy (parent child : Real) : Fin 3 → Real :=
  ![parent, child, child]

/-- Literal finite-coordinate shifted-adjugate contraction for the
parent-child-child channel. -/
def oppositeChildRepeatedFiniteAdjugateInteractionContraction
    (x y parent child : Real) : Real :=
  adjugateEntryProductContraction (fun r ↦
    explicitSixSiteOppositeWeightShiftedMatrix x y
      (oppositeChildRepeatedEnergy parent child r))

/-- If both selected energies belong to the non-structural cubic factor,
the parent-child-child adjugate contraction vanishes by bond reflection. -/
theorem oppositeChildRepeatedFiniteAdjugateInteractionContraction_eq_zero
    (x y parent child : Real)
    (hparent : oppositeSixSiteCubic x y parent = 0)
    (hchild : oppositeSixSiteCubic x y child = 0)
    (hparentStruct : parent * (parent - 1) * (parent - 3) ≠ 0)
    (hchildStruct : child * (child - 1) * (child - 3) ≠ 0) :
    oppositeChildRepeatedFiniteAdjugateInteractionContraction
        x y parent child = 0 := by
  let A := fun energy ↦
    (explicitSixSiteOppositeWeightShiftedMatrix x y energy).adjugate
  have hparentOdd (i j : Fin 6) :
      A parent (reverseFinSix i) j = -A parent i j :=
    explicitSixSiteOppositeWeightShiftedMatrix_adjugate_reverse_row
      x y parent hparent hparentStruct i j
  have hchildOdd (i j : Fin 6) :
      A child (reverseFinSix i) j = -A child i j :=
    explicitSixSiteOppositeWeightShiftedMatrix_adjugate_reverse_row
      x y child hchild hchildStruct i j
  unfold oppositeChildRepeatedFiniteAdjugateInteractionContraction
    adjugateEntryProductContraction
  simp only [Fin.prod_univ_succ]
  simp [oppositeChildRepeatedEnergy]
  change ∑ i : Fin 6, ∑ j : Fin 6,
    A parent i j * (A child i j * A child i j) = 0
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _hj
  let f : Fin 6 → Real := fun i ↦
    A parent i j * (A child i j * A child i j)
  have hfodd (i : Fin 6) : f (reverseFinSix i) = -f i := by
    dsimp [f]
    rw [hparentOdd i j, hchildOdd i j]
    ring
  have hreindex := reverseFinSixEquiv.sum_comp f
  have hneg : (∑ i, f i) = -(∑ i, f i) := by
    calc
      (∑ i, f i) = ∑ i, f (reverseFinSixEquiv i) := hreindex.symm
      _ = ∑ i, -f i := by
        apply Fintype.sum_congr
        intro i
        exact hfodd i
      _ = -(∑ i, f i) := by simp
  change (∑ i, f i) = 0
  linarith

/-- The physical opposite-site dual-adjugate contraction is exactly the
literal finite-coordinate parent-child-child contraction. -/
theorem harmonicDualOrderedAdjugateInteractionContraction_opposite_eq_finite
    {s : Real} (hs : s ∈ Set.Icc ((5 : Real) / 6) (7 / 6)) :
    harmonicDualOrderedAdjugateInteractionContraction
        (oppositeSixSiteMassConfig s) oppositeChildRepeatedModes =
      oppositeChildRepeatedFiniteAdjugateInteractionContraction
        (6 / 5) s⁻¹
        (orderedEigenvalue (oppositeSixSiteHarmonic s) 0)
        (orderedEigenvalue (oppositeSixSiteHarmonic s) 3) := by
  let mass := oppositeSixSiteMassConfig s
  let dual := dualMassWeightedHarmonicHermitian mass
  let parent := orderedEigenvalue (oppositeSixSiteHarmonic s) 0
  let child := orderedEigenvalue (oppositeSixSiteHarmonic s) 3
  let family : Fin 3 → Matrix (Lattice.Site 6) (Lattice.Site 6) Real :=
    fun r ↦ orderedEigenvalueShiftedMatrix dual (oppositeChildRepeatedModes r)
  have hbase :
      Matrix.reindex (siteEquivFin 6) (siteEquivFin 6) (matrixVal dual) =
        explicitSixSiteOppositeWeightLaplacian (6 / 5) s⁻¹ := by
    have hdual :
        matrixVal dual =
          weightedCycleLaplacian (fun i ↦ (mass.mass i)⁻¹) := by
      change massWeightedDifferenceMatrix mass *
          (massWeightedDifferenceMatrix mass).transpose = _
      exact massWeighted_selfTranspose_eq_weightedCycleLaplacian mass
    calc
      Matrix.reindex (siteEquivFin 6) (siteEquivFin 6) (matrixVal dual) =
          finWeightedCycleLaplacian (inverseMassCoordinates mass) := by
        rw [hdual, ← weightsOfCoordinates_inverseMassCoordinates]
        rfl
      _ = finWeightedCycleLaplacian
          (oppositeSixSiteInverseWeights (6 / 5) s⁻¹) := by
        rw [show inverseMassCoordinates mass =
          oppositeSixSiteInverseWeights (6 / 5) s⁻¹ by
            simpa [mass] using inverseMassCoordinates_oppositeSixSiteMassConfig hs]
      _ = explicitSixSiteOppositeWeightLaplacian (6 / 5) s⁻¹ :=
        finWeightedCycleLaplacian_oppositeSixSiteInverseWeights _ _
  have hphysical :
      harmonicHermitian mass = oppositeSixSiteHarmonic s := rfl
  have hspec (k : Fin 6) :
      orderedEigenvalue dual k =
        orderedEigenvalue (oppositeSixSiteHarmonic s) k := by
    rw [← hphysical]
    exact (orderedEigenvalue_harmonic_eq_dual mass k).symm
  have hfamily (r : Fin 3) :
      Matrix.reindex (siteEquivFin 6) (siteEquivFin 6) (family r) =
        explicitSixSiteOppositeWeightShiftedMatrix (6 / 5) s⁻¹
          (oppositeChildRepeatedEnergy parent child r) := by
    have henergy :
        orderedEigenvalue dual (oppositeChildRepeatedModes r) =
          oppositeChildRepeatedEnergy parent child r := by
      fin_cases r
      · change orderedEigenvalue dual 0 =
          orderedEigenvalue (oppositeSixSiteHarmonic s) 0
        exact hspec 0
      · change orderedEigenvalue dual 3 =
          orderedEigenvalue (oppositeSixSiteHarmonic s) 3
        exact hspec 3
      · change orderedEigenvalue dual 3 =
          orderedEigenvalue (oppositeSixSiteHarmonic s) 3
        exact hspec 3
    ext i j
    simp only [family, orderedEigenvalueShiftedMatrix, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply]
    rw [henergy]
    have hbaseEntry := congrArg (fun M ↦ M i j) hbase
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply] at hbaseEntry
    rw [hbaseEntry]
    fin_cases i <;> fin_cases j <;>
      norm_num +decide [explicitSixSiteOppositeWeightLaplacian,
        explicitSixSiteOppositeWeightShiftedMatrix, Matrix.one_apply, siteEquivFin] <;>
      ring
  unfold harmonicDualOrderedAdjugateInteractionContraction
    oppositeChildRepeatedFiniteAdjugateInteractionContraction
  change adjugateEntryProductContraction family =
    adjugateEntryProductContraction (fun r ↦
      explicitSixSiteOppositeWeightShiftedMatrix (6 / 5) s⁻¹
        (oppositeChildRepeatedEnergy parent child r))
  rw [← adjugateEntryProductContraction_reindex (siteEquivFin 6) family]
  congr 1
  funext r
  exact hfamily r

/-- On every interior exact resonance of the opposite-mass slice, the
basis-free physical dual-adjugate contraction vanishes. -/
theorem harmonicDualOrderedAdjugateInteractionContraction_opposite_eq_zero
    {s : Real} (hs : s ∈ Set.Ioo ((5 : Real) / 6) (7 / 6))
    (hres : oppositeChildRepeatedMismatch s = 0) :
    harmonicDualOrderedAdjugateInteractionContraction
        (oppositeSixSiteMassConfig s) oppositeChildRepeatedModes = 0 := by
  let pair := oppositeMassPair s
  let parent := orderedEigenvalue (oppositeTwoMassHarmonic pair) 0
  let child := orderedEigenvalue (oppositeTwoMassHarmonic pair) 3
  have hsupport : pair ∈ iidMassPairSupport :=
    oppositeMassPair_mem_iidMassPairSupport
      ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  have hregular := exactResonance_structural_and_recovery_regular hs hres
  have hparentRoot :
      oppositeSixSiteCubic pair.1⁻¹ pair.2⁻¹ parent = 0 :=
    opposite_orderedEnergy_cubic_root_of_structural_ne
      hsupport (0 : Fin 6) hregular.1
  have hchildRoot :
      oppositeSixSiteCubic pair.1⁻¹ pair.2⁻¹ child = 0 :=
    opposite_orderedEnergy_cubic_root_of_structural_ne
      hsupport (3 : Fin 6) hregular.2.1
  rw [harmonicDualOrderedAdjugateInteractionContraction_opposite_eq_finite
    ⟨le_of_lt hs.1, le_of_lt hs.2⟩]
  apply oppositeChildRepeatedFiniteAdjugateInteractionContraction_eq_zero
  · have h := hparentRoot
    simp only [pair, parent, oppositeTwoMassHarmonic_oppositeMassPair] at h
    simpa [oppositeMassPair] using h
  · have h := hchildRoot
    simp only [pair, child, oppositeTwoMassHarmonic_oppositeMassPair] at h
    simpa [oppositeMassPair] using h
  · simpa [pair, parent, oppositeSelectedEnergy,
      oppositeTwoMassHarmonic_oppositeMassPair] using hregular.1
  · simpa [pair, child, oppositeSelectedEnergy,
      oppositeTwoMassHarmonic_oppositeMassPair] using hregular.2.1

/-- The projector-defined squared cubic interaction weight of the exact
parent-child-child channel is zero. -/
theorem harmonicOrderedInteractionWeightSq_oppositeChildRepeated_eq_zero
    {s : Real} (hs : s ∈ Set.Ioo ((5 : Real) / 6) (7 / 6))
    (hres : oppositeChildRepeatedMismatch s = 0) :
    harmonicOrderedInteractionWeightSq
        (oppositeSixSiteMassConfig s) oppositeChildRepeatedModes = 0 := by
  have hsimpleOpposite :
      SimpleOrderedSpectrum (oppositeSixSiteHarmonic s) :=
    oppositeSixSiteHarmonic_simpleOrderedSpectrum hs
  have hsimple :
      SimpleOrderedSpectrum
        (harmonicHermitian (oppositeSixSiteMassConfig s)) := by
    exact hsimpleOpposite
  have hcleared :=
    harmonic_gapProduct_mul_interactionWeightSq_eq_eigenvalueProduct_mul_dualAdjugateContraction
      (oppositeSixSiteMassConfig s) hsimple oppositeChildRepeatedModes
  rw [harmonicDualOrderedAdjugateInteractionContraction_opposite_eq_zero
    hs hres, mul_zero] at hcleared
  have hgap :
      (∏ r, orderedModeGapProduct
        (harmonicHermitian (oppositeSixSiteMassConfig s))
        (oppositeChildRepeatedModes r)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro r _hr
    exact orderedModeGapProduct_ne_zero _ hsimple _
  exact (mul_eq_zero.mp hcleared).resolve_left hgap

/-- Consequently the genuine positive-frequency normalized collision weight
at the exact child-repeated resonance is exactly zero. -/
theorem harmonicOrderedNormalizedInteractionWeight_oppositeChildRepeated_eq_zero
    {s : Real} (hs : s ∈ Set.Ioo ((5 : Real) / 6) (7 / 6))
    (hres : oppositeChildRepeatedMismatch s = 0) :
    harmonicOrderedNormalizedInteractionWeight
        (oppositeSixSiteMassConfig s) oppositeChildRepeatedModes = 0 := by
  unfold harmonicOrderedNormalizedInteractionWeight
  rw [harmonicOrderedInteractionWeightSq_oppositeChildRepeated_eq_zero hs hres,
    zero_mul]

/-- The unconditional exact small-ball seed can be chosen only with zero
physical cubic collision weight in its corresponding child-repeated channel. -/
theorem exists_oppositeSixSite_exactChildRepeated_resonance_weight_eq_zero :
    ∃ s ∈ Set.Ioo ((5 : Real) / 6) (7 / 6),
      oppositeChildRepeatedMismatch s = 0 ∧
      SimpleOrderedSpectrum (oppositeSixSiteHarmonic s) ∧
      0 < orderedModeFrequency (oppositeSixSiteHarmonic s) 0 ∧
      0 < orderedModeFrequency (oppositeSixSiteHarmonic s) 3 ∧
      harmonicOrderedNormalizedInteractionWeight
        (oppositeSixSiteMassConfig s) oppositeChildRepeatedModes = 0 := by
  obtain ⟨s, hs, hres, hsimple, hparent, hchild, _hJacobian⟩ :=
    exists_interior_simple_positive_jacobian_oppositeChildRepeated_exactResonance
  exact ⟨s, hs, hres, hsimple, hparent, hchild,
    harmonicOrderedNormalizedInteractionWeight_oppositeChildRepeated_eq_zero
      hs hres⟩

end

end ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedCollisionWeight
