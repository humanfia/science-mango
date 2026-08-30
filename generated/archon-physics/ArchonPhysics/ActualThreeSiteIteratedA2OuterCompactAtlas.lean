import ArchonPhysics.ActualThreeSiteIteratedA2OuterInverseMassStrip
import ArchonPhysics.QuantitativeJacobianGoodBadPushforward

/-!
# Compact augmented atlases for the actual three-site outer mismatch

The scalar outer mismatch is augmented by the unchanged first and third
masses.  Its determinant is exactly the negative derivative in the middle
mass direction.  The quantitative bridges therefore make this square chart
locally invertible at every interior point off the inverse-mass diagonal.

This module first exposes the pointwise calculus and local-chart API.  The
compact determinant lower bound and finite-subcover estimate are kept here,
independently of the inverse-strip probability calculation.
-/

open scoped Matrix ENNReal

namespace ArchonPhysics.ActualThreeSiteIteratedA2OuterCompactAtlas

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeBridges
open ArchonPhysics.QuantitativeJacobianGoodBadPushforward
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterProjectorWeightJacobian
open ArchonPhysics.LocalCollisionMarkContinuity
open ArchonPhysics.QuantitativeJacobianPushforward
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Filter Function MeasureTheory Set

noncomputable section

local instance tripleVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure MassTriple) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- Square augmented chart retaining the first and third raw masses. -/
def threeSiteOuterAugmentedChart (triple : MassTriple) : MassTriple :=
  ((threeSiteOuterTripleMismatch triple, triple.1.1), triple.2)

/-- Explicit derivative of the augmented chart. -/
def threeSiteOuterAugmentedDerivative (triple : MassTriple) :
    MassTriple →L[Real] MassTriple :=
  ((threeSiteOuterTripleMismatchDerivative triple).prod
    massTripleCoordinateZero).prod massTripleCoordinateTwo

theorem continuous_threeSiteOuterTripleMismatch :
    Continuous threeSiteOuterTripleMismatch := by
  unfold threeSiteOuterTripleMismatch threeSiteOuterTripleHarmonic
  exact ((continuous_orderedModeFrequency 1).comp
    (continuous_threeMassHarmonicHermitian threeSiteOuterTripleBackground
      (0 : Lattice.Site 3) (1 : Lattice.Site 3)
      (2 : Lattice.Site 3))).neg

theorem continuous_threeSiteOuterAugmentedChart :
    Continuous threeSiteOuterAugmentedChart := by
  unfold threeSiteOuterAugmentedChart
  exact (continuous_threeSiteOuterTripleMismatch.prodMk
    (continuous_fst.comp continuous_fst)).prodMk continuous_snd

theorem measurable_threeSiteOuterAugmentedChart :
    Measurable threeSiteOuterAugmentedChart :=
  continuous_threeSiteOuterAugmentedChart.measurable

/-- The true strict derivative of the mismatch assembles into the strict
derivative of the parameter-retaining square chart. -/
theorem hasStrictFDerivAt_threeSiteOuterAugmentedChart
    {triple : MassTriple} (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeSiteOuterTripleHarmonic triple)) :
    HasStrictFDerivAt threeSiteOuterAugmentedChart
      (threeSiteOuterAugmentedDerivative triple) triple := by
  change HasStrictFDerivAt
    (fun nearby : MassTriple =>
      ((threeSiteOuterTripleMismatch nearby, nearby.1.1), nearby.2))
    (threeSiteOuterAugmentedDerivative triple) triple
  have hassembled :=
    ((hasStrictFDerivAt_threeSiteOuterTripleMismatch htriple hsimple).prodMk
      massTripleCoordinateZero.hasStrictFDerivAt).prodMk
        massTripleCoordinateTwo.hasStrictFDerivAt
  convert hassembled using 1 <;>
    ext <;>
    simp [threeSiteOuterAugmentedDerivative, massTripleCoordinateZero,
      massTripleCoordinateTwo]

/-- Coordinate matrix of the augmented derivative. -/
theorem toMatrix_threeSiteOuterAugmentedDerivative (triple : MassTriple) :
    LinearMap.toMatrix massTripleBasis massTripleBasis
      (threeSiteOuterAugmentedDerivative triple).toLinearMap =
        !![threeSiteOuterTripleMismatchDerivative triple (massTripleBasis 0),
            threeSiteOuterTripleMismatchDerivative triple (massTripleBasis 1),
            threeSiteOuterTripleMismatchDerivative triple (massTripleBasis 2);
           1, 0, 0;
           0, 0, 1] := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [threeSiteOuterAugmentedDerivative, massTripleCoordinateZero,
      massTripleCoordinateTwo]

/-- The augmented determinant is precisely the negative middle-mass
derivative detected by the explicit eliminant. -/
theorem det_threeSiteOuterAugmentedDerivative (triple : MassTriple) :
    (threeSiteOuterAugmentedDerivative triple).det =
      -threeSiteOuterTripleMismatchDerivative triple (massTripleBasis 1) := by
  rw [ContinuousLinearMap.det]
  rw [← LinearMap.det_toMatrix massTripleBasis
    (threeSiteOuterAugmentedDerivative triple).toLinearMap]
  rw [toMatrix_threeSiteOuterAugmentedDerivative]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two]

theorem continuousAt_threeSiteOuterAugmentedDerivative_det
    {triple : MassTriple} (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeSiteOuterTripleHarmonic triple)) :
    ContinuousAt (fun nearby =>
      (threeSiteOuterAugmentedDerivative nearby).det) triple := by
  simp_rw [det_threeSiteOuterAugmentedDerivative]
  exact ((continuousAt_threeSiteOuterTripleMismatchDerivative
    htriple hsimple).clm_apply continuousAt_const).neg

/-- Off the inverse-mass diagonal, the actual augmented derivative is
nonsingular.  Spectral simplicity is supplied by the arbitrary-third-mass
degeneracy bridge. -/
theorem threeSiteOuterAugmentedDerivative_det_ne_zero_of_inverse_separated
    {triple : MassTriple} (htriple : triple ∈ interior iidMassTripleSupport)
    (hne : triple.1.1⁻¹ ≠ triple.2⁻¹) :
    (threeSiteOuterAugmentedDerivative triple).det ≠ 0 := by
  have hsimple := threeSiteOuterTripleHarmonic_simple_of_inverse_separated
    (interior_subset htriple) hne
  have hmiddle : threeSiteOuterTripleMismatchDerivative triple
      (massTripleBasis 1) ≠ 0 := by
    intro hzero
    exact hne (threeSiteOuterTripleMismatchDerivative_second_zero_forces_inverse_eq
      htriple hsimple hzero)
  rw [det_threeSiteOuterAugmentedDerivative]
  exact neg_ne_zero.mpr hmiddle

/-- Every interior inverse-separated point has an open patch on which the
augmented chart is injective. -/
theorem exists_open_injective_threeSiteOuterAugmentedPatch
    {triple : MassTriple} (htriple : triple ∈ interior iidMassTripleSupport)
    (hne : triple.1.1⁻¹ ≠ triple.2⁻¹) :
    ∃ patch : Set MassTriple,
      IsOpen patch ∧ triple ∈ patch ∧
        InjOn threeSiteOuterAugmentedChart patch := by
  have hsimple := threeSiteOuterTripleHarmonic_simple_of_inverse_separated
    (interior_subset htriple) hne
  have hdet :=
    threeSiteOuterAugmentedDerivative_det_ne_zero_of_inverse_separated
      htriple hne
  let derivativeEquiv :=
    (threeSiteOuterAugmentedDerivative triple).toContinuousLinearEquivOfDetNeZero
      hdet
  have hderivativeEquiv :
      (derivativeEquiv : MassTriple →L[Real] MassTriple) =
        threeSiteOuterAugmentedDerivative triple :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ hdet
  have hstrictEquiv : HasStrictFDerivAt threeSiteOuterAugmentedChart
      (derivativeEquiv : MassTriple →L[Real] MassTriple) triple := by
    rw [hderivativeEquiv]
    exact hasStrictFDerivAt_threeSiteOuterAugmentedChart htriple hsimple
  let localChart : OpenPartialHomeomorph MassTriple MassTriple :=
    hstrictEquiv.toOpenPartialHomeomorph threeSiteOuterAugmentedChart
  refine ⟨localChart.source, localChart.open_source,
    hstrictEquiv.mem_toOpenPartialHomeomorph_source, ?_⟩
  change InjOn (localChart : MassTriple → MassTriple) localChart.source
  exact localChart.injOn

/-! ## Uniform determinant lower bounds and finite atlases -/

/-- Compactness upgrades pointwise inverse separation to a positive lower
bound for the actual augmented determinant. -/
theorem exists_positive_threeSiteOuterAugmented_detLower_on_compact
    (K : Set MassTriple) (hK : IsCompact K)
    (hKInterior : K ⊆ interior iidMassTripleSupport)
    (hKSeparated : ∀ triple ∈ K, triple.1.1⁻¹ ≠ triple.2⁻¹) :
    ∃ detLower : Real, 0 < detLower ∧ ∀ triple ∈ K,
      detLower ≤ |(threeSiteOuterAugmentedDerivative triple).det| := by
  let jacobianDet : MassTriple → Real := fun triple =>
    (threeSiteOuterAugmentedDerivative triple).det
  have hcontinuous : ContinuousOn (fun triple => |jacobianDet triple|) K := by
    intro triple htriple
    have hinterior := hKInterior htriple
    have hsimple := threeSiteOuterTripleHarmonic_simple_of_inverse_separated
      (interior_subset hinterior) (hKSeparated triple htriple)
    exact (continuousAt_threeSiteOuterAugmentedDerivative_det
      hinterior hsimple).abs.continuousWithinAt
  have hnonzero : ∀ triple ∈ K, jacobianDet triple ≠ 0 := by
    intro triple htriple
    exact threeSiteOuterAugmentedDerivative_det_ne_zero_of_inverse_separated
      (hKInterior htriple) (hKSeparated triple htriple)
  by_cases hKnonempty : K.Nonempty
  · obtain ⟨triple, htriple, hminimum⟩ :=
      hK.exists_isMinOn hKnonempty hcontinuous
    refine ⟨|jacobianDet triple|,
      abs_pos.mpr (hnonzero triple htriple), ?_⟩
    intro nearby hnearby
    exact hminimum hnearby
  · refine ⟨1, one_pos, ?_⟩
    intro triple htriple
    exact (hKnonempty ⟨triple, htriple⟩).elim

/-- A compact interior inverse-separated set admits a finite quantitative
atlas for the augmented mismatch chart. -/
theorem exists_detLower_atlasCard_threeSiteOuterAugmented_map_restrict_le
    (K : Set MassTriple) (hK : IsCompact K)
    (hKInterior : K ⊆ interior iidMassTripleSupport)
    (hKSeparated : ∀ triple ∈ K, triple.1.1⁻¹ ≠ triple.2⁻¹) :
    ∃ detLower : Real, ∃ atlasCard : Nat,
      0 < detLower ∧
      Measure.map threeSiteOuterAugmentedChart
          (iidMassTripleLaw.restrict K) ≤
        ((atlasCard : ENNReal) *
          (27 * (ENNReal.ofReal detLower)⁻¹)) •
            (volume : Measure MassTriple) := by
  classical
  obtain ⟨detLower, hdetLower, hdet⟩ :=
    exists_positive_threeSiteOuterAugmented_detLower_on_compact
      K hK hKInterior hKSeparated
  have hKmeasurable : MeasurableSet K := hK.isClosed.measurableSet
  have hlocalPatch : ∀ point : K, ∃ patch : Set MassTriple,
      IsOpen patch ∧ point.1 ∈ patch ∧
        InjOn threeSiteOuterAugmentedChart patch := by
    intro point
    exact exists_open_injective_threeSiteOuterAugmentedPatch
      (hKInterior point.2) (hKSeparated point.1 point.2)
  choose localPatch hopen hmem hinjective using hlocalPatch
  obtain ⟨atlas, hcover⟩ := hK.elim_finite_subcover localPatch hopen (by
    intro point hpoint
    rw [mem_iUnion]
    exact ⟨⟨point, hpoint⟩, hmem ⟨point, hpoint⟩⟩)
  let AtlasIndex := {point : K // point ∈ atlas}
  let patch : AtlasIndex → Set MassTriple := fun index =>
    K ∩ localPatch index.1
  have hpatchMeasurable : ∀ index : AtlasIndex,
      MeasurableSet (patch index) := by
    intro index
    exact hKmeasurable.inter (hopen index.1).measurableSet
  have hK_eq : K = ⋃ index : AtlasIndex, patch index := by
    apply Subset.antisymm
    · intro point hpoint
      rcases mem_iUnion₂.mp (hcover hpoint) with
        ⟨center, hcenter, hpointPatch⟩
      rw [mem_iUnion]
      exact ⟨⟨center, hcenter⟩, hpoint, hpointPatch⟩
    · intro point hpoint
      rcases mem_iUnion.mp hpoint with ⟨index, hindex⟩
      exact hindex.1
  have hderivative : ∀ index : AtlasIndex, ∀ point ∈ patch index,
      HasFDerivWithinAt threeSiteOuterAugmentedChart
        (threeSiteOuterAugmentedDerivative point) (patch index) point := by
    intro index point hpoint
    have hinterior := hKInterior hpoint.1
    have hsimple := threeSiteOuterTripleHarmonic_simple_of_inverse_separated
      (interior_subset hinterior) (hKSeparated point hpoint.1)
    exact (hasStrictFDerivAt_threeSiteOuterAugmentedChart
      hinterior hsimple).hasFDerivAt.hasFDerivWithinAt
  have hsource : ∀ index : AtlasIndex,
      iidMassTripleLaw.restrict (patch index) ≤
        (27 : ENNReal) •
          (volume : Measure MassTriple).restrict (patch index) := by
    intro index
    calc
      iidMassTripleLaw.restrict (patch index) ≤
          ((27 : ENNReal) •
            (volume : Measure MassTriple)).restrict (patch index) :=
        Measure.restrict_mono_measure
          iidMassTripleLaw_le_twentySeven_smul_volume _
      _ = (27 : ENNReal) •
          (volume : Measure MassTriple).restrict (patch index) := by
        rw [Measure.restrict_smul]
  have hlocalMap : ∀ index : AtlasIndex,
      Measure.map threeSiteOuterAugmentedChart
          (iidMassTripleLaw.restrict (patch index)) ≤
        (27 * (ENNReal.ofReal detLower)⁻¹) •
          (volume : Measure MassTriple) := by
    intro index
    exact map_le_smul_volume_of_le_volume_restrict_of_det_lower
      (volume : Measure MassTriple) (hpatchMeasurable index)
      threeSiteOuterAugmentedChart measurable_threeSiteOuterAugmentedChart
      threeSiteOuterAugmentedDerivative (hderivative index)
      ((hinjective index.1).mono inter_subset_right)
      hdetLower (fun point hpoint => hdet point hpoint.1)
      (iidMassTripleLaw.restrict (patch index)) 27 (hsource index)
  have hrestrictK : iidMassTripleLaw.restrict K ≤
      Measure.sum fun index : AtlasIndex =>
        iidMassTripleLaw.restrict (patch index) := by
    rw [hK_eq]
    exact Measure.restrict_iUnion_le
  have hmapK : Measure.map threeSiteOuterAugmentedChart
        (iidMassTripleLaw.restrict K) ≤
      Measure.sum fun index : AtlasIndex =>
        Measure.map threeSiteOuterAugmentedChart
          (iidMassTripleLaw.restrict (patch index)) := by
    calc
      Measure.map threeSiteOuterAugmentedChart
          (iidMassTripleLaw.restrict K) ≤
        Measure.map threeSiteOuterAugmentedChart
          (Measure.sum fun index : AtlasIndex =>
            iidMassTripleLaw.restrict (patch index)) :=
        Measure.map_mono hrestrictK measurable_threeSiteOuterAugmentedChart
      _ = Measure.sum fun index : AtlasIndex =>
          Measure.map threeSiteOuterAugmentedChart
            (iidMassTripleLaw.restrict (patch index)) := by
        rw [Measure.map_sum
          measurable_threeSiteOuterAugmentedChart.aemeasurable]
  have hsum :
      (Measure.sum fun index : AtlasIndex =>
        Measure.map threeSiteOuterAugmentedChart
          (iidMassTripleLaw.restrict (patch index))) ≤
      ((Fintype.card AtlasIndex : ENNReal) *
        (27 * (ENNReal.ofReal detLower)⁻¹)) •
          (volume : Measure MassTriple) := by
    rw [Measure.le_iff]
    intro target htarget
    rw [Measure.sum_apply _ htarget, Measure.smul_apply]
    simp only [tsum_fintype, smul_eq_mul]
    calc
      (∑ index : AtlasIndex,
          Measure.map threeSiteOuterAugmentedChart
            (iidMassTripleLaw.restrict (patch index)) target) ≤
        ∑ _index : AtlasIndex,
          (27 * (ENNReal.ofReal detLower)⁻¹) *
            (volume : Measure MassTriple) target :=
        Finset.sum_le_sum fun index _hindex => hlocalMap index target
      _ = (Fintype.card AtlasIndex : ENNReal) *
          (27 * (ENNReal.ofReal detLower)⁻¹) *
            (volume : Measure MassTriple) target := by
        simp [mul_assoc]
  refine ⟨detLower, atlas.card, hdetLower, ?_⟩
  simpa [AtlasIndex] using hmapK.trans hsum

end

end ArchonPhysics.ActualThreeSiteIteratedA2OuterCompactAtlas
