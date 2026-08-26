import FamilyStickyGrounding.FamilyStickyHierarchyWZ2TranslatedCollisionCellCanonicalRowGeometryV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyHierarchyWZ2TranslatedCollisionCellCanonicalRowScaleFloorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
open FamilyStickyHierarchyWZ2CollisionCellSourceAdapterV1
open FamilyStickyWZ2CinematicTranslationV1
open FamilyStickyWZ2TranslatedShadingUnionCovarianceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyWZ2TranslatedActualShadingInstantiationV1
open FamilyStickyWZ2AmbientCinematicTranslationVolumeV1
open FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1
open FamilyStickyWZ2TranslatedShadingUnionCopyLossV1
open FamilyStickyWZ2ShearParameterPackingV1
open FamilyStickyWZ2SharedHundredSourceConstantEndpointV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellCanonicalRowGeometryV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# A density-floor producer for the canonical WZ2 row scale

The exact canonical row hull contains the full body of its own row whenever
that row has positive shading volume.  Consequently, no uniform bound for
the canonical scale can follow from Katz--Tao, John-box, fixed-grid, or
packing data alone: such a bound necessarily implies a pointwise lower
density estimate comparing every nonzero shaded piece with its full body.

This module formalizes that obstruction and the strongest direct producer
available from the present collision-cell certificates.  A common global
convex container for the full family, together with a positive finite lower
floor for every nonzero shaded row, bounds the canonical scale by the
container volume divided by that floor.

For a selected hierarchy collision cell, the existing
`SharedHundredSourceContainer` automatically supplies a global container:
take the closed convex hull of the affine images, over all shear copies, of
the one literal source `100T`.  Thus no hull bound, scale-factor bound,
union-mass bound, or row-container callback remains.  The sole quantitative
input is the per-carrier shading floor, precisely the datum that a later
popular-restriction adapter must produce.
-/

/-- Closed convex hull of every member of a finite convex family. -/
noncomputable def fullFamilyHullContainer
    {iota : Type*} [Fintype iota] (F : ConvexFamily iota) :
    ConvexBody Space :=
  hullContainer F Finset.univ

/-- Every member lies in the full-family hull. -/
theorem body_subset_fullFamilyHullContainer
    {iota : Type*} [Fintype iota] (F : ConvexFamily iota) (i : iota) :
    (F i : Set Space) ⊆ (fullFamilyHullContainer F : Set Space) := by
  classical
  exact body_subset_hullContainer F (Finset.mem_univ i)
    ⟨i, Finset.mem_univ i⟩

/-- A positive-volume row interacts with itself and hence retains its own
full body in the canonical row hull. -/
theorem body_subset_own_positiveOverlapHullContainer
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    (Y : Shading F) (i : iota) (hvolume : volume (Y.carrier i) ≠ 0) :
    (F i : Set Space) ⊆ (positiveOverlapHullContainer F Y i : Set Space) := by
  apply body_subset_positiveOverlapHullContainer Y
  simpa only [inter_self] using hvolume

/-- Formal obstruction: any bound on the canonical row scale forces a
pointwise full-body-to-shading density bound on every nonzero row. -/
theorem body_volume_le_of_canonicalOverlapScaleFactor_le
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    (Y : Shading F) (A : ENNReal)
    (hscale : canonicalOverlapScaleFactor Y ≤ A)
    (i : iota) (hvolume : volume (Y.carrier i) ≠ 0) :
    volume (F i : Set Space) ≤ A * volume (Y.carrier i) := by
  calc
    volume (F i : Set Space) ≤
        volume (positiveOverlapHullContainer F Y i : Set Space) :=
      measure_mono
        (body_subset_own_positiveOverlapHullContainer Y i hvolume)
    _ ≤ canonicalOverlapScaleFactor Y * volume (Y.carrier i) :=
      positiveOverlapHullContainer_volume_le Y i
    _ ≤ A * volume (Y.carrier i) := mul_le_mul' hscale le_rfl

/-- If all full bodies lie in `K`, then the canonical positive-overlap hull
of every nonzero row lies in `K`. -/
theorem positiveOverlapHullContainer_subset_globalContainer
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    (Y : Shading F) (K : ConvexBody Space)
    (hcontains : ∀ j, (F j : Set Space) ⊆ (K : Set Space))
    (i : iota) (hvolume : volume (Y.carrier i) ≠ 0) :
    (positiveOverlapHullContainer F Y i : Set Space) ⊆ (K : Set Space) := by
  classical
  have hi : i ∈ positiveVolumeOverlapIndices Y i :=
    (mem_positiveVolumeOverlapIndices Y i i).2 (by
      simpa only [inter_self] using hvolume)
  apply hullContainer_subset F ⟨i, hi⟩
  intro j _hj
  exact hcontains j

/-- A genuine global container plus a nonzero finite shading floor produces
the entire canonical row-scale bound.  This is not a reformulation of the
target: `K` contains the full family independently of pairwise overlaps, and
the only row datum is a lower bound for each nonzero carrier. -/
theorem canonicalOverlapScaleFactor_le_globalContainerVolume_div_floor
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    (Y : Shading F) (K : ConvexBody Space)
    (hcontains : ∀ j, (F j : Set Space) ⊆ (K : Set Space))
    (lower : ENNReal) (hlower0 : lower ≠ 0) (hlowerTop : lower ≠ ∞)
    (hfloor : ∀ i, volume (Y.carrier i) ≠ 0 →
      lower ≤ volume (Y.carrier i)) :
    canonicalOverlapScaleFactor Y ≤ volume (K : Set Space) / lower := by
  rw [canonicalOverlapScaleFactor_le_iff]
  intro i
  by_cases hvolume : volume (Y.carrier i) = 0
  · rw [hvolume,
      volume_positiveOverlapHullContainer_eq_zero_of_carrier_volume_eq_zero
        Y i hvolume]
    simp
  · calc
      volume (positiveOverlapHullContainer F Y i : Set Space) ≤
          volume (K : Set Space) :=
        measure_mono
          (positiveOverlapHullContainer_subset_globalContainer
            Y K hcontains i hvolume)
      _ = (volume (K : Set Space) / lower) * lower :=
        (ENNReal.div_mul_cancel hlower0 hlowerTop).symm
      _ ≤ (volume (K : Set Space) / lower) * volume (Y.carrier i) :=
        mul_le_mul' le_rfl (hfloor i hvolume)

/-- Canonical full-family version: only a per-nonzero-carrier floor remains. -/
theorem canonicalOverlapScaleFactor_le_fullFamilyHullVolume_div_floor
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    (Y : Shading F)
    (lower : ENNReal) (hlower0 : lower ≠ 0) (hlowerTop : lower ≠ ∞)
    (hfloor : ∀ i, volume (Y.carrier i) ≠ 0 →
      lower ≤ volume (Y.carrier i)) :
    canonicalOverlapScaleFactor Y ≤
      volume (fullFamilyHullContainer F : Set Space) / lower := by
  exact canonicalOverlapScaleFactor_le_globalContainerVolume_div_floor
    Y (fullFamilyHullContainer F) (body_subset_fullFamilyHullContainer F)
      lower hlower0 hlowerTop hfloor

/-! ## Automatic carrier-floor restriction -/

/-- Retain exactly the shading carriers whose full carrier mass is at least
`lower`; discarded indices receive the empty carrier. -/
noncomputable def retainCarrierFloor
    {iota : Type*} {F : ConvexFamily iota}
    (Y : Shading F) (lower : ENNReal) : Shading F := by
  classical
  exact
    { carrier := fun i =>
        if lower ≤ volume (Y.carrier i) then Y.carrier i else ∅
      measurable_carrier := by
        intro i
        split_ifs
        · exact Y.measurable_carrier i
        · exact MeasurableSet.empty
      carrier_subset := by
        intro i
        split_ifs
        · exact Y.carrier_subset i
        · exact empty_subset _ }

@[simp]
theorem retainCarrierFloor_carrier
    {iota : Type*} {F : ConvexFamily iota}
    (Y : Shading F) (lower : ENNReal) (i : iota) :
    (retainCarrierFloor Y lower).carrier i =
      if lower ≤ volume (Y.carrier i) then Y.carrier i else ∅ := by
  classical
  rfl

/-- Every nonzero retained carrier satisfies the declared floor by
construction. -/
theorem lower_le_volume_retainCarrierFloor_of_ne_zero
    {iota : Type*} {F : ConvexFamily iota}
    (Y : Shading F) (lower : ENNReal) (i : iota)
    (hvolume : volume ((retainCarrierFloor Y lower).carrier i) ≠ 0) :
    lower ≤ volume ((retainCarrierFloor Y lower).carrier i) := by
  classical
  by_cases hfloor : lower ≤ volume (Y.carrier i)
  · simp [retainCarrierFloor, hfloor]
  · simp [retainCarrierFloor, hfloor] at hvolume

/-- Hence floor restriction automatically supplies a quantitative canonical
scale bound, without a lower-density callback. -/
theorem canonicalOverlapScaleFactor_retainCarrierFloor_le
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    (Y : Shading F)
    (lower : ENNReal) (hlower0 : lower ≠ 0) (hlowerTop : lower ≠ ∞) :
    canonicalOverlapScaleFactor (retainCarrierFloor Y lower) ≤
      volume (fullFamilyHullContainer F : Set Space) / lower := by
  exact canonicalOverlapScaleFactor_le_fullFamilyHullVolume_div_floor
    (retainCarrierFloor Y lower) lower hlower0 hlowerTop
      (lower_le_volume_retainCarrierFloor_of_ne_zero Y lower)

/-! ## The existing shared `100T` certificate produces the global container -/

/-- One affine image of the shared source `100T` for each translation copy. -/
noncomputable def translatedSharedHundredBodyFamily
    {tau kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    (shift : tau → ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (shared : SharedHundredSourceContainer fine) : ConvexFamily tau :=
  fun j => affineImageConvexBody
    (ambientCinematicAffineEquiv
      (shift j).1 (shift j).2.1 (shift j).2.2)
    (hundredTube shared.container).body

@[simp]
theorem coe_translatedSharedHundredBodyFamily
    {tau kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    (shift : tau → ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (shared : SharedHundredSourceContainer fine) (j : tau) :
    (translatedSharedHundredBodyFamily shift fine shared j : Set Space) =
      ambientCinematicTranslation
          (shift j).1 (shift j).2.1 (shift j).2.2 ''
        (hundredTube shared.container).carrier := by
  rfl

/-- Closed convex hull of all affine images of the shared `100T`. -/
noncomputable def translatedSharedHundredHullContainer
    {tau kappa : Type*} [Fintype tau]
    {delta : NNReal} [DecidableEq kappa]
    (shift : tau → ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (shared : SharedHundredSourceContainer fine) : ConvexBody Space :=
  fullFamilyHullContainer (translatedSharedHundredBodyFamily shift fine shared)

/-- Every product-indexed translated source body lies in the corresponding
affine shared `100T`. -/
theorem indexedTranslatedBody_subset_translatedSharedHundredBody
    {tau kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    (shift : tau → ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (shared : SharedHundredSourceContainer fine) (ji : tau × kappa) :
    (indexedTranslatedBodyFamily shift (tubeBodyFamily fine.tubes) ji :
        Set Space) ⊆
      (translatedSharedHundredBodyFamily shift fine shared ji.1 :
        Set Space) := by
  rw [coe_indexedTranslatedBodyFamily,
    coe_translatedSharedHundredBodyFamily]
  exact image_mono (shared.carrier_subset ji.2)

/-- Therefore the existing shared-source certificate automatically contains
the entire product-indexed translated family in one explicit convex hull. -/
theorem indexedTranslatedBody_subset_translatedSharedHundredHull
    {tau kappa : Type*} [Fintype tau]
    {delta : NNReal} [DecidableEq kappa]
    (shift : tau → ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (shared : SharedHundredSourceContainer fine) (ji : tau × kappa) :
    (indexedTranslatedBodyFamily shift (tubeBodyFamily fine.tubes) ji :
        Set Space) ⊆
      (translatedSharedHundredHullContainer shift fine shared : Set Space) :=
  (indexedTranslatedBody_subset_translatedSharedHundredBody
    shift fine shared ji).trans
      (body_subset_fullFamilyHullContainer
        (translatedSharedHundredBodyFamily shift fine shared) ji.1)

/-- Translation preserves the source shading floor, and the shared `100T`
hull then bounds the complete canonical scale of the product family. -/
theorem canonicalOverlapScaleFactor_indexedTranslatedActualShading_le
    {tau kappa : Type*} [Fintype tau] [Fintype kappa]
    {delta : NNReal} [DecidableEq kappa]
    (shift : tau → ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (shared : SharedHundredSourceContainer fine)
    (Y : Shading (tubeBodyFamily fine.tubes))
    (lower : ENNReal) (hlower0 : lower ≠ 0) (hlowerTop : lower ≠ ∞)
    (hfloor : ∀ i, volume (Y.carrier i) ≠ 0 →
      lower ≤ volume (Y.carrier i)) :
    canonicalOverlapScaleFactor
        (indexedTranslatedActualShading shift fine Y) ≤
      volume (translatedSharedHundredHullContainer shift fine shared :
        Set Space) / lower := by
  apply canonicalOverlapScaleFactor_le_globalContainerVolume_div_floor
    (indexedTranslatedActualShading shift fine Y)
    (translatedSharedHundredHullContainer shift fine shared)
    (indexedTranslatedBody_subset_translatedSharedHundredHull
      shift fine shared) lower hlower0 hlowerTop
  intro ji hvolume
  have hvolumeEq :
      volume ((indexedTranslatedActualShading shift fine Y).carrier ji) =
        volume (Y.carrier ji.2) := by
    rw [indexedTranslatedActualShading_carrier]
    exact volume_translatedShadingCarrier
      (shift ji.1).1 (shift ji.1).2.1 (shift ji.1).2.2 Y.carrier ji.2
  rw [hvolumeEq]
  apply hfloor ji.2
  intro hzero
  apply hvolume
  rw [hvolumeEq, hzero]

/-- Direct analytic consequence: the shared source certificate and the
carrier floor close the translated-copy union-mass estimate. -/
theorem source_shadingMass_le_sharedHundredHull_div_floor_mul_copyAverage
    {tau kappa : Type*} [Fintype tau] [Fintype kappa]
    {delta : NNReal} [DecidableEq kappa]
    (htau : Nonempty tau)
    (shift : tau → ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (shared : SharedHundredSourceContainer fine)
    (Y : Shading (tubeBodyFamily fine.tubes))
    (lower : ENNReal) (hlower0 : lower ≠ 0) (hlowerTop : lower ≠ ∞)
    (hfloor : ∀ i, volume (Y.carrier i) ≠ 0 →
      lower ≤ volume (Y.carrier i))
    {C : ENNReal}
    (hKT : IsKatzTao C
      (indexedTranslatedBodyFamily shift (tubeBodyFamily fine.tubes))) :
    Y.shadingMass ≤
      (C *
        (volume (translatedSharedHundredHullContainer shift fine shared :
          Set Space) / lower)) *
        (volume (indexedTranslatedActualShadingUnion shift fine Y) /
          (Fintype.card tau : ENNReal)) := by
  apply source_shadingMass_le_of_canonicalRowScaleFactor_le
    htau shift fine Y hKT
  exact canonicalOverlapScaleFactor_indexedTranslatedActualShading_le
    shift fine shared Y lower hlower0 hlowerTop hfloor

variable {depth : Nat} {nominalRadius : Nat → NNReal}
  {Index : Nat → Type*}
  [∀ l, Fintype (Index l)] [∀ l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  {spacing : Real} {siteCount : Nat}

/-- Selected hierarchy collision cells already carry the shared `100T`
certificate, so their canonical scale needs only the source shading floor. -/
theorem selectedHierarchyCollisionCell_canonicalOverlapScaleFactor_le
    (joint : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (p : Index (k.1 + 1))
    (a : ModelCandidate (hierarchyCollisionGrid H G joint k p))
    (r : Fin (repetitions G.toDependentSource k))
    (Y : Shading
      (tubeBodyFamily
        (selectedHierarchyCollisionCellFamily H G joint k p a r).tubes))
    (lower : ENNReal) (hlower0 : lower ≠ 0) (hlowerTop : lower ≠ ∞)
    (hfloor : ∀ i, volume (Y.carrier i) ≠ 0 →
      lower ≤ volume (Y.carrier i)) :
    canonicalOverlapScaleFactor
        (indexedTranslatedActualShading
          (shearReducedShift spacing (siteCount := siteCount))
          (selectedHierarchyCollisionCellFamily H G joint k p a r) Y) ≤
      volume
          (translatedSharedHundredHullContainer
            (shearReducedShift spacing (siteCount := siteCount))
            (selectedHierarchyCollisionCellFamily H G joint k p a r)
            (selectedHierarchyCollisionCell_sharedHundredSourceContainer
              H G joint k p a r) : Set Space) /
        lower := by
  exact canonicalOverlapScaleFactor_indexedTranslatedActualShading_le
    (shearReducedShift spacing (siteCount := siteCount))
    (selectedHierarchyCollisionCellFamily H G joint k p a r)
    (selectedHierarchyCollisionCell_sharedHundredSourceContainer
      H G joint k p a r)
    Y lower hlower0 hlowerTop hfloor

#print axioms body_volume_le_of_canonicalOverlapScaleFactor_le
#print axioms canonicalOverlapScaleFactor_le_globalContainerVolume_div_floor
#print axioms canonicalOverlapScaleFactor_le_fullFamilyHullVolume_div_floor
#print axioms canonicalOverlapScaleFactor_retainCarrierFloor_le
#print axioms indexedTranslatedBody_subset_translatedSharedHundredHull
#print axioms canonicalOverlapScaleFactor_indexedTranslatedActualShading_le
#print axioms source_shadingMass_le_sharedHundredHull_div_floor_mul_copyAverage
#print axioms selectedHierarchyCollisionCell_canonicalOverlapScaleFactor_le

end
end FamilyStickyHierarchyWZ2TranslatedCollisionCellCanonicalRowScaleFloorV1
