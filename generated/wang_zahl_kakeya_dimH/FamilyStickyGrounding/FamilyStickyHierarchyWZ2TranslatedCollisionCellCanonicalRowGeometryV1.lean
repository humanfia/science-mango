import FamilyStickyGrounding.FamilyStickyHierarchyWZ2TranslatedCollisionCellUnionMassV1
import Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyHierarchyWZ2TranslatedCollisionCellCanonicalRowGeometryV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.Uniformity
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomWZCommonNeighbourPackingV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
open FamilyStickyHierarchyWZ2CollisionCellSourceAdapterV1
open FamilyStickyWZ2CinematicTranslationV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyWZ2TranslatedActualShadingInstantiationV1
open FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1
open FamilyStickyWZ2TranslatedShadingUnionCopyLossV1
open FamilyStickyKatzTaoAtEveryScaleOverlapMultiplicityConsumerV1
open FamilyStickyWZ2ShearParameterPackingV1
open FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1
open FamilyStickyWZ2SharedHundredSourceConstantEndpointV1
open FamilyStickyHierarchyWZ2FixedGridConstantEndpointV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellKatzTaoV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellUnionMassV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Canonical overlap-row geometry for translated collision cells

For any finite actual shading, define the majorant to be the literal pairwise
intersection volume.  In row `i`, retain exactly those `j` for which that
volume is nonzero, and take the closed convex hull of their full convex
bodies.  Every retained body is then contained in the row hull, while every
discarded majorant is zero.  This automatically supplies the `support` field
of `KatzTaoOverlapRowGeometry`.

The canonical scale factor is the supremum of the row-hull-volume to
row-shading-volume ratios.  A zero-volume row causes no division loophole:
all its intersections have zero volume, its active set is empty, and its
canonical hull is the zero-volume singleton.  Consequently the complete row
geometry is produced without a majorant, support, container, container-
volume, second-moment, mass, or union-bound callback.

For quantitative use, all remaining WZ2 geometry is isolated in the single
scalar statement that this explicit canonical scale factor is at most `A`.
-/

/-- The exact pairwise-intersection majorant. -/
noncomputable def exactPairwiseOverlapBound
    {iota : Type*} {F : ConvexFamily iota} (Y : Shading F) :
    PairwiseOverlapBound Y where
  majorant i j := volume (Y.carrier i ∩ Y.carrier j)
  pairwise_le _ _ := le_rfl

/-- Indices whose shaded pieces meet row `i` in positive ambient measure. -/
noncomputable def positiveVolumeOverlapIndices
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    (Y : Shading F) (i : iota) : Finset iota := by
  classical
  exact Finset.univ.filter fun j =>
    volume (Y.carrier i ∩ Y.carrier j) ≠ 0

@[simp]
theorem mem_positiveVolumeOverlapIndices
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    (Y : Shading F) (i j : iota) :
    j ∈ positiveVolumeOverlapIndices Y i ↔
      volume (Y.carrier i ∩ Y.carrier j) ≠ 0 := by
  classical
  simp [positiveVolumeOverlapIndices]

/-- The closed convex hull of all full bodies with positive-measure overlap
with row `i`; an empty row uses the canonical singleton body. -/
noncomputable def positiveOverlapHullContainer
    {iota : Type*} [Fintype iota] (F : ConvexFamily iota)
    (Y : Shading F) (i : iota) : ConvexBody Space :=
  hullContainer F (positiveVolumeOverlapIndices Y i)

/-- A positive-overlap body's full convex body lies in the canonical row
hull. -/
theorem body_subset_positiveOverlapHullContainer
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    (Y : Shading F) {i j : iota}
    (hvolume : volume (Y.carrier i ∩ Y.carrier j) ≠ 0) :
    (F j : Set Space) ⊆ (positiveOverlapHullContainer F Y i : Set Space) := by
  classical
  have hj : j ∈ positiveVolumeOverlapIndices Y i :=
    (mem_positiveVolumeOverlapIndices Y i j).2 hvolume
  exact body_subset_hullContainer F hj ⟨j, hj⟩

/-- The exact majorant is automatically supported by active full bodies
contained in the canonical row hull. -/
theorem exactPairwiseOverlapBound_le_activeContainedVolume
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    (Y : Shading F) (i j : iota) :
    (exactPairwiseOverlapBound Y).majorant i j ≤
      PairwiseOverlapBound.activeContainedVolume F
        (positiveVolumeOverlapIndices Y i)
        (positiveOverlapHullContainer F Y i) j := by
  classical
  change volume (Y.carrier i ∩ Y.carrier j) ≤ _
  by_cases hvolume : volume (Y.carrier i ∩ Y.carrier j) = 0
  · simp [hvolume]
  · have hjActive : j ∈ positiveVolumeOverlapIndices Y i :=
      (mem_positiveVolumeOverlapIndices Y i j).2 hvolume
    have hjContained :
        j ∈ containedIndices F (positiveOverlapHullContainer F Y i) :=
      (mem_containedIndices F (positiveOverlapHullContainer F Y i) j).2
        (body_subset_positiveOverlapHullContainer Y hvolume)
    have hinter :
        volume (Y.carrier i ∩ Y.carrier j) ≤ volume (F j : Set Space) :=
      measure_mono (inter_subset_right.trans (Y.carrier_subset j))
    simpa [PairwiseOverlapBound.activeContainedVolume, hjActive,
      hjContained] using hinter

/-- A zero-volume row has no positive-volume interactions. -/
theorem positiveVolumeOverlapIndices_eq_empty_of_carrier_volume_eq_zero
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    (Y : Shading F) (i : iota) (hzero : volume (Y.carrier i) = 0) :
    positiveVolumeOverlapIndices Y i = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have hnonzero := (mem_positiveVolumeOverlapIndices Y i j).1 hj
  apply hnonzero
  apply le_antisymm
  · exact (measure_mono inter_subset_left).trans_eq hzero
  · exact bot_le

/-- Hence the canonical hull of a zero-volume row is itself zero-volume. -/
theorem volume_positiveOverlapHullContainer_eq_zero_of_carrier_volume_eq_zero
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    (Y : Shading F) (i : iota) (hzero : volume (Y.carrier i) = 0) :
    volume (positiveOverlapHullContainer F Y i : Set Space) = 0 := by
  have hempty :=
    positiveVolumeOverlapIndices_eq_empty_of_carrier_volume_eq_zero Y i hzero
  simp [positiveOverlapHullContainer, hempty]

/-- The explicit uniform row scale: the supremum of canonical row-hull
volume divided by the corresponding shaded-row volume. -/
noncomputable def canonicalOverlapScaleFactor
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    (Y : Shading F) : ENNReal :=
  ⨆ i : iota,
    volume (positiveOverlapHullContainer F Y i : Set Space) /
      volume (Y.carrier i)

theorem rowRatio_le_canonicalOverlapScaleFactor
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    (Y : Shading F) (i : iota) :
    volume (positiveOverlapHullContainer F Y i : Set Space) /
        volume (Y.carrier i) ≤
      canonicalOverlapScaleFactor Y := by
  exact le_iSup (fun j : iota =>
    volume (positiveOverlapHullContainer F Y j : Set Space) /
      volume (Y.carrier j)) i

/-- The canonical scale factor automatically gives every required row
container-volume comparison, including zero-volume rows. -/
theorem positiveOverlapHullContainer_volume_le
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    (Y : Shading F) (i : iota) :
    volume (positiveOverlapHullContainer F Y i : Set Space) ≤
      canonicalOverlapScaleFactor Y * volume (Y.carrier i) := by
  by_cases hzero : volume (Y.carrier i) = 0
  · rw [hzero,
      volume_positiveOverlapHullContainer_eq_zero_of_carrier_volume_eq_zero
        Y i hzero]
    simp
  · have htop : volume (Y.carrier i) ≠ ∞ :=
      ((measure_mono (Y.carrier_subset i)).trans_lt
        (F i).isCompact.measure_lt_top).ne
    calc
      volume (positiveOverlapHullContainer F Y i : Set Space) =
          (volume (positiveOverlapHullContainer F Y i : Set Space) /
            volume (Y.carrier i)) * volume (Y.carrier i) :=
        (ENNReal.div_mul_cancel hzero htop).symm
      _ ≤ canonicalOverlapScaleFactor Y * volume (Y.carrier i) :=
        mul_le_mul'
          (rowRatio_le_canonicalOverlapScaleFactor Y i) le_rfl

/-- Bounding the canonical scale is exactly the remaining row-hull volume
estimate; all other overlap-row fields have already been produced. -/
theorem canonicalOverlapScaleFactor_le_iff
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    (Y : Shading F) (A : ENNReal) :
    canonicalOverlapScaleFactor Y ≤ A ↔
      ∀ i, volume (positiveOverlapHullContainer F Y i : Set Space) ≤
        A * volume (Y.carrier i) := by
  constructor
  · intro hscale i
    exact (positiveOverlapHullContainer_volume_le Y i).trans
      (mul_le_mul' hscale le_rfl)
  · intro hrow
    unfold canonicalOverlapScaleFactor
    apply iSup_le
    intro i
    by_cases hzero : volume (Y.carrier i) = 0
    · rw [hzero,
        volume_positiveOverlapHullContainer_eq_zero_of_carrier_volume_eq_zero
          Y i hzero]
      simp
    · have htop : volume (Y.carrier i) ≠ ∞ :=
        ((measure_mono (Y.carrier_subset i)).trans_lt
          (F i).isCompact.measure_lt_top).ne
      exact (ENNReal.div_le_iff hzero htop).2 (hrow i)

/-- Complete, callback-free overlap-row geometry for any finite actual
shading. -/
noncomputable def canonicalKatzTaoOverlapRowGeometry
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    (Y : Shading F) : KatzTaoOverlapRowGeometry Y where
  overlap := exactPairwiseOverlapBound Y
  active := positiveVolumeOverlapIndices Y
  container := positiveOverlapHullContainer F Y
  scaleFactor := canonicalOverlapScaleFactor Y
  support := exactPairwiseOverlapBound_le_activeContainedVolume Y
  container_volume_le := positiveOverlapHullContainer_volume_le Y

/-- If the one remaining scalar geometric estimate bounds the canonical
factor by `A`, the same canonical fields give row geometry with scale `A`. -/
noncomputable def canonicalKatzTaoOverlapRowGeometryOfScaleCap
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    (Y : Shading F) (A : ENNReal)
    (hscale : canonicalOverlapScaleFactor Y ≤ A) :
    KatzTaoOverlapRowGeometry Y where
  overlap := exactPairwiseOverlapBound Y
  active := positiveVolumeOverlapIndices Y
  container := positiveOverlapHullContainer F Y
  scaleFactor := A
  support := exactPairwiseOverlapBound_le_activeContainedVolume Y
  container_volume_le i :=
    (positiveOverlapHullContainer_volume_le Y i).trans
      (mul_le_mul' hscale le_rfl)

/-- The generic translated-copy union-mass theorem with the complete
canonical row geometry filled automatically. -/
theorem source_shadingMass_le_canonicalRowFactor_mul_copyAverage
    {tau kappa : Type*} {delta : NNReal}
    [Fintype tau] [Fintype kappa] [DecidableEq kappa]
    (htau : Nonempty tau)
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (Y : Shading (tubeBodyFamily fine.tubes))
    {C : ENNReal}
    (hKT : IsKatzTao C
      (indexedTranslatedBodyFamily shift (tubeBodyFamily fine.tubes))) :
    Y.shadingMass ≤
      (C * canonicalOverlapScaleFactor
        (indexedTranslatedActualShading shift fine Y)) *
        (volume (indexedTranslatedActualShadingUnion shift fine Y) /
          (Fintype.card tau : ENNReal)) := by
  simpa [canonicalKatzTaoOverlapRowGeometry] using
    (source_shadingMass_le_katzTaoRowFactor_mul_copyAverage
      htau shift fine Y hKT
      (canonicalKatzTaoOverlapRowGeometry
        (indexedTranslatedActualShading shift fine Y)))

/-- A single explicit bound on the canonical row scale is the complete
remaining geometric input for the quantitative translated-copy estimate. -/
theorem source_shadingMass_le_of_canonicalRowScaleFactor_le
    {tau kappa : Type*} {delta : NNReal}
    [Fintype tau] [Fintype kappa] [DecidableEq kappa]
    (htau : Nonempty tau)
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (Y : Shading (tubeBodyFamily fine.tubes))
    {C A : ENNReal}
    (hKT : IsKatzTao C
      (indexedTranslatedBodyFamily shift (tubeBodyFamily fine.tubes)))
    (hscale : canonicalOverlapScaleFactor
      (indexedTranslatedActualShading shift fine Y) ≤ A) :
    Y.shadingMass ≤
      (C * A) *
        (volume (indexedTranslatedActualShadingUnion shift fine Y) /
          (Fintype.card tau : ENNReal)) := by
  simpa [canonicalKatzTaoOverlapRowGeometryOfScaleCap] using
    (source_shadingMass_le_katzTaoRowFactor_mul_copyAverage
      htau shift fine Y hKT
      (canonicalKatzTaoOverlapRowGeometryOfScaleCap
        (indexedTranslatedActualShading shift fine Y) A hscale))

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  {spacing : Real} {siteCount gridConstant : Nat}

/-- The literal product-indexed translated collision-cell shading has a
fully produced canonical row-geometry instance. -/
noncomputable def selectedHierarchyCollisionCellCanonicalRowGeometry
    (joint : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (p : Index (k.1 + 1))
    (a : ModelCandidate (hierarchyCollisionGrid H G joint k p))
    (r : Fin (repetitions G.toDependentSource k))
    (Y : Shading
      (tubeBodyFamily
        (selectedHierarchyCollisionCellFamily H G joint k p a r).tubes)) :
    KatzTaoOverlapRowGeometry
      (indexedTranslatedActualShading
        (shearReducedShift spacing (siteCount := siteCount))
        (selectedHierarchyCollisionCellFamily H G joint k p a r) Y) :=
  canonicalKatzTaoOverlapRowGeometry
    (indexedTranslatedActualShading
      (shearReducedShift spacing (siteCount := siteCount))
      (selectedHierarchyCollisionCellFamily H G joint k p a r) Y)

/-- End-to-end collision-cell union-mass estimate with no row-geometry
structure premise.  Its explicit canonical scale is the sole remaining
quantity to estimate geometrically. -/
theorem selectedHierarchyCollisionCell_shadingMass_le_canonicalRowFactor_mul_copyAverage
    (grid : FixedShearCopyGridCertificate siteCount gridConstant)
    (joint : HierarchyJointRandomMotionCertificate H G)
    (wz : HierarchyLevelWZSeparationData H)
    (k : Fin depth) (p : Index (k.1 + 1))
    (hp : p ∈ (G.toDependentSource.layer k).activeParents)
    (a : ModelCandidate (hierarchyCollisionGrid H G joint k p))
    (r : Fin (repetitions G.toDependentSource k))
    (baseD rho : Real) (hspacing : 0 < spacing) (hrho : 0 <= rho)
    (source : Finset
      (SelectedHierarchyCollisionCellIndex H G joint k p a r))
    (hselected :
      (Finset.univ : Finset
        (SelectedHierarchyCollisionCellIndex H G joint k p a r)) <=
      fixedVerticalChartIndices
        (selectedHierarchyCollisionCellFamily H G joint k p a r) source)
    (hcluster : forall l,
      |tubeGraphD
          ((selectedHierarchyCollisionCellFamily H G joint k p a r).tubes l) -
        baseD| <= rho)
    (hsiteCount : 0 < siteCount)
    (Y : Shading
      (tubeBodyFamily
        (selectedHierarchyCollisionCellFamily H G joint k p a r).tubes)) :
    Y.shadingMass ≤
      ((16 *
          ((gridConstant * commonHundredNeighbourPackingConstant : Nat) :
            ENNReal)) *
        canonicalOverlapScaleFactor
          (indexedTranslatedActualShading
            (shearReducedShift spacing (siteCount := siteCount))
            (selectedHierarchyCollisionCellFamily H G joint k p a r) Y)) *
        (volume
            (indexedTranslatedActualShadingUnion
              (shearReducedShift spacing (siteCount := siteCount))
              (selectedHierarchyCollisionCellFamily H G joint k p a r) Y) /
          (siteCount : ENNReal)) := by
  have hKT :=
    selectedHierarchyCollisionCell_fullTranslatedFamily_isKatzTao
      grid joint wz k p hp a r baseD rho hspacing hrho source hselected
        hcluster
  simpa using
    (source_shadingMass_le_canonicalRowFactor_mul_copyAverage
      (htau := ⟨⟨0, hsiteCount⟩⟩)
      (shift := shearReducedShift spacing (siteCount := siteCount))
      (fine := selectedHierarchyCollisionCellFamily H G joint k p a r)
      (Y := Y) hKT)

/-- Quantitative collision-cell endpoint: after all majorant/support/container
fields have been produced, only one scalar bound on their explicit canonical
row factor remains. -/
theorem selectedHierarchyCollisionCell_shadingMass_le_of_canonicalRowScaleFactor_le
    (grid : FixedShearCopyGridCertificate siteCount gridConstant)
    (joint : HierarchyJointRandomMotionCertificate H G)
    (wz : HierarchyLevelWZSeparationData H)
    (k : Fin depth) (p : Index (k.1 + 1))
    (hp : p ∈ (G.toDependentSource.layer k).activeParents)
    (a : ModelCandidate (hierarchyCollisionGrid H G joint k p))
    (r : Fin (repetitions G.toDependentSource k))
    (baseD rho : Real) (hspacing : 0 < spacing) (hrho : 0 <= rho)
    (source : Finset
      (SelectedHierarchyCollisionCellIndex H G joint k p a r))
    (hselected :
      (Finset.univ : Finset
        (SelectedHierarchyCollisionCellIndex H G joint k p a r)) <=
      fixedVerticalChartIndices
        (selectedHierarchyCollisionCellFamily H G joint k p a r) source)
    (hcluster : forall l,
      |tubeGraphD
          ((selectedHierarchyCollisionCellFamily H G joint k p a r).tubes l) -
        baseD| <= rho)
    (hsiteCount : 0 < siteCount)
    (Y : Shading
      (tubeBodyFamily
        (selectedHierarchyCollisionCellFamily H G joint k p a r).tubes))
    (A : ENNReal)
    (hscale : canonicalOverlapScaleFactor
      (indexedTranslatedActualShading
        (shearReducedShift spacing (siteCount := siteCount))
        (selectedHierarchyCollisionCellFamily H G joint k p a r) Y) ≤ A) :
    Y.shadingMass ≤
      ((16 *
          ((gridConstant * commonHundredNeighbourPackingConstant : Nat) :
            ENNReal)) * A) *
        (volume
            (indexedTranslatedActualShadingUnion
              (shearReducedShift spacing (siteCount := siteCount))
              (selectedHierarchyCollisionCellFamily H G joint k p a r) Y) /
          (siteCount : ENNReal)) := by
  have hKT :=
    selectedHierarchyCollisionCell_fullTranslatedFamily_isKatzTao
      grid joint wz k p hp a r baseD rho hspacing hrho source hselected
        hcluster
  simpa using
    (source_shadingMass_le_of_canonicalRowScaleFactor_le
      (htau := ⟨⟨0, hsiteCount⟩⟩)
      (shift := shearReducedShift spacing (siteCount := siteCount))
      (fine := selectedHierarchyCollisionCellFamily H G joint k p a r)
      (Y := Y) hKT hscale)

#print axioms exactPairwiseOverlapBound_le_activeContainedVolume
#print axioms positiveOverlapHullContainer_volume_le
#print axioms canonicalOverlapScaleFactor_le_iff
#print axioms canonicalKatzTaoOverlapRowGeometry
#print axioms source_shadingMass_le_canonicalRowFactor_mul_copyAverage
#print axioms source_shadingMass_le_of_canonicalRowScaleFactor_le
#print axioms selectedHierarchyCollisionCellCanonicalRowGeometry
#print axioms selectedHierarchyCollisionCell_shadingMass_le_canonicalRowFactor_mul_copyAverage
#print axioms selectedHierarchyCollisionCell_shadingMass_le_of_canonicalRowScaleFactor_le

end
end FamilyStickyHierarchyWZ2TranslatedCollisionCellCanonicalRowGeometryV1
