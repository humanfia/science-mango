import FamilyStickyGrounding.FamilyStickyHierarchyWZ2TranslatedCollisionCellCanonicalRowScaleFloorV1
import FamilyStickyGrounding.FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyHierarchyWZ2TranslatedCollisionCellPopularFloorUnionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2PopularFibersV1
open FamilyStickyWZ2ShadingPopularityV2
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
open FamilyStickyWZ2CinematicTranslationV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyWZ2TranslatedActualShadingInstantiationV1
open FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1
open FamilyStickyWZ2TranslatedShadingUnionCopyLossV1
open FamilyStickyWZ2ShearParameterPackingV1
open FamilyStickyWZ2SharedHundredSourceConstantEndpointV1
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomWZCommonNeighbourPackingV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
open FamilyStickyHierarchyWZ2CollisionCellSourceAdapterV1
open FamilyStickyHierarchyWZ2FixedGridConstantEndpointV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellKatzTaoV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellCanonicalRowScaleFloorV1
open FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Popular restricted mass to the canonical WZ2 carrier floor

The existing WZ2 popularity adapter selects indices whose mass inside a
literal restricted set is at least `(alpha / 2) * cap`.  Since restricted
mass is bounded by the full carrier mass, every such index survives
`retainCarrierFloor` at the corresponding `ENNReal` threshold.

This module proves the stronger mass statement behind the usual cardinality
popularity lemma.  The total restricted mass lost on unpopular indices is at
most `active.card * threshold`; therefore the retained shading contains the
total restricted mass minus exactly this explicit budget.  A projected-slice
integral lower bound consequently produces literal retained shading mass.

Finally that mass is fed through the canonical-row scale producer, the
shared source `100T` hull, and Katz--Tao.  Monotonicity returns the resulting
lower bound from the floor-restricted translated union to the original
translated union.  No shading-mass target, row-scale bound, hull-volume
bound, or union lower bound is supplied as a premise.
-/

/-- The literal carrier floor selected by the WZ2 half-threshold. -/
noncomputable def popularCarrierFloor (alpha cap : Real) : ENNReal :=
  ENNReal.ofReal (alpha / 2 * cap)

/-- Every popular restricted index has enough full carrier mass to meet the
literal popular carrier floor. -/
theorem popularCarrierFloor_le_carrierMass_of_mem
    {iota : Type*} {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota) (X : Set Space)
    (alpha cap : Real) {i : iota}
    (hi : i ∈ popularRestrictedIndices Y active X alpha cap) :
    popularCarrierFloor alpha cap ≤ volume (Y.carrier i) := by
  have hiThreshold :
      alpha / 2 * cap ≤ restrictedMassReal Y X i := by
    exact (Finset.mem_filter.mp hi).2
  have hrestricted :
      popularCarrierFloor alpha cap ≤ restrictedMass Y X i := by
    rw [popularCarrierFloor]
    exact (ENNReal.ofReal_le_iff_le_toReal
      (restrictedMass_lt_top Y X i).ne).2 hiThreshold
  exact hrestricted.trans (restrictedMass_le_carrierMass Y X i)

/-- A popular restricted index is retained with its whole original carrier,
not merely with its intersection with the restricted set. -/
theorem retainCarrierFloor_carrier_eq_of_mem_popularRestrictedIndices
    {iota : Type*} {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota) (X : Set Space)
    (alpha cap : Real) {i : iota}
    (hi : i ∈ popularRestrictedIndices Y active X alpha cap) :
    (retainCarrierFloor Y (popularCarrierFloor alpha cap)).carrier i =
      Y.carrier i := by
  classical
  simp [retainCarrierFloor,
    popularCarrierFloor_le_carrierMass_of_mem Y active X alpha cap hi]

/-- The floor-restricted shading mass dominates the exact restricted mass
of all popular indices. -/
theorem sum_popularRestrictedMass_le_retainCarrierFloor_shadingMass
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota) (X : Set Space)
    (alpha cap : Real) :
    (∑ i ∈ popularRestrictedIndices Y active X alpha cap,
        restrictedMass Y X i) ≤
      (retainCarrierFloor Y
        (popularCarrierFloor alpha cap)).shadingMass := by
  classical
  unfold Shading.shadingMass
  calc
    (∑ i ∈ popularRestrictedIndices Y active X alpha cap,
        restrictedMass Y X i) ≤
        ∑ i ∈ popularRestrictedIndices Y active X alpha cap,
          volume
            ((retainCarrierFloor Y
              (popularCarrierFloor alpha cap)).carrier i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [retainCarrierFloor_carrier_eq_of_mem_popularRestrictedIndices
        Y active X alpha cap hi]
      exact restrictedMass_le_carrierMass Y X i
    _ ≤ ∑ i,
          volume
            ((retainCarrierFloor Y
              (popularCarrierFloor alpha cap)).carrier i) := by
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- The real restricted mass on unpopular indices is at most their cardinality
times the half-threshold. -/
theorem sum_unpopularRestrictedMassReal_le_budget
    {iota : Type*} {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota) (X : Set Space)
    (alpha cap : Real) :
    (∑ i ∈ unpopularIndices active (restrictedMassReal Y X)
          (alpha / 2 * cap),
        restrictedMassReal Y X i) ≤
      (unpopularIndices active (restrictedMassReal Y X)
        (alpha / 2 * cap)).card * (alpha / 2 * cap) := by
  calc
    (∑ i ∈ unpopularIndices active (restrictedMassReal Y X)
          (alpha / 2 * cap),
        restrictedMassReal Y X i) ≤
        ∑ _i ∈ unpopularIndices active (restrictedMassReal Y X)
            (alpha / 2 * cap),
          alpha / 2 * cap := by
      apply Finset.sum_le_sum
      intro i hi
      exact le_of_not_ge (Finset.mem_filter.mp hi).2
    _ = (unpopularIndices active (restrictedMassReal Y X)
          (alpha / 2 * cap)).card * (alpha / 2 * cap) := by
      simp

/-- Strongest direct popularity budget: the popular restricted mass is at
least the total active restricted mass minus one threshold per active index. -/
theorem restrictedMassReal_sub_budget_le_sum_popularRestrictedMassReal
    {iota : Type*} {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota) (X : Set Space)
    (alpha cap : Real) (halpha0 : 0 ≤ alpha) (hcap0 : 0 ≤ cap) :
    (∑ i ∈ active, restrictedMassReal Y X i) -
        active.card * (alpha / 2 * cap) ≤
      ∑ i ∈ popularRestrictedIndices Y active X alpha cap,
        restrictedMassReal Y X i := by
  have hthreshold0 : 0 ≤ alpha / 2 * cap :=
    mul_nonneg (div_nonneg halpha0 (by norm_num)) hcap0
  have hcardNat :
      (unpopularIndices active (restrictedMassReal Y X)
        (alpha / 2 * cap)).card ≤ active.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hcardReal :
      ((unpopularIndices active (restrictedMassReal Y X)
        (alpha / 2 * cap)).card : Real) ≤ active.card := by
    exact_mod_cast hcardNat
  have hunpopular :
      (∑ i ∈ unpopularIndices active (restrictedMassReal Y X)
            (alpha / 2 * cap),
          restrictedMassReal Y X i) ≤
        active.card * (alpha / 2 * cap) :=
    (sum_unpopularRestrictedMassReal_le_budget
      Y active X alpha cap).trans
        (mul_le_mul_of_nonneg_right hcardReal hthreshold0)
  have hsplit := sum_eq_popular_add_unpopular active
    (restrictedMassReal Y X) (alpha / 2 * cap)
  change (∑ i ∈ active, restrictedMassReal Y X i) -
      active.card * (alpha / 2 * cap) ≤
    ∑ i ∈ popularIndices active (restrictedMassReal Y X)
      (alpha / 2 * cap), restrictedMassReal Y X i
  rw [hsplit]
  linarith

/-- ENNReal form of the exact loss budget.  It is a literal lower bound for
the mass of the constructed floor-restricted shading. -/
theorem popularRestricted_exactBudget_le_retainCarrierFloor_shadingMass
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota) (X : Set Space)
    (alpha cap : Real) (halpha0 : 0 ≤ alpha) (hcap0 : 0 ≤ cap) :
    ENNReal.ofReal
        ((∑ i ∈ active, restrictedMassReal Y X i) -
          active.card * (alpha / 2 * cap)) ≤
      (retainCarrierFloor Y
        (popularCarrierFloor alpha cap)).shadingMass := by
  calc
    ENNReal.ofReal
        ((∑ i ∈ active, restrictedMassReal Y X i) -
          active.card * (alpha / 2 * cap)) ≤
        ENNReal.ofReal
          (∑ i ∈ popularRestrictedIndices Y active X alpha cap,
            restrictedMassReal Y X i) :=
      ENNReal.ofReal_le_ofReal
        (restrictedMassReal_sub_budget_le_sum_popularRestrictedMassReal
          Y active X alpha cap halpha0 hcap0)
    _ = ∑ i ∈ popularRestrictedIndices Y active X alpha cap,
          restrictedMass Y X i := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro i _hi
        exact ENNReal.ofReal_toReal (restrictedMass_lt_top Y X i).ne
      · intro i _hi
        exact ENNReal.toReal_nonneg
    _ ≤ (retainCarrierFloor Y
          (popularCarrierFloor alpha cap)).shadingMass :=
      sum_popularRestrictedMass_le_retainCarrierFloor_shadingMass
        Y active X alpha cap

/-- If the existing restricted double count has the standard
`alpha * card * cap` lower bound, at least the displayed half-scale is
literal mass in the floor-restricted shading. -/
theorem popularRestricted_halfMass_le_retainCarrierFloor_shadingMass
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota) (X : Set Space)
    (alpha cap : Real) (halpha0 : 0 ≤ alpha) (hcap0 : 0 ≤ cap)
    (hmass : alpha * active.card * cap ≤
      ∑ i ∈ active, restrictedMassReal Y X i) :
    ENNReal.ofReal (alpha / 2 * active.card * cap) ≤
      (retainCarrierFloor Y
        (popularCarrierFloor alpha cap)).shadingMass := by
  have hhalf :
      alpha / 2 * active.card * cap ≤
        (∑ i ∈ active, restrictedMassReal Y X i) -
          active.card * (alpha / 2 * cap) := by
    have hidentity :
        alpha * active.card * cap =
          alpha / 2 * active.card * cap +
            active.card * (alpha / 2 * cap) := by
      ring
    linarith
  exact (ENNReal.ofReal_le_ofReal hhalf).trans
    (popularRestricted_exactBudget_le_retainCarrierFloor_shadingMass
      Y active X alpha cap halpha0 hcap0)

/-- Projected-slice form: the existing exact ambient change of variables
directly supplies the mass premise above. -/
theorem projectedSlice_halfMass_le_retainCarrierFloor_shadingMass
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f) (X : Set ProjectionSpace)
    (alpha cap : Real) (halpha0 : 0 ≤ alpha) (hcap0 : 0 ≤ cap)
    (hmass : alpha * active.card * cap ≤
      (∫⁻ u in X, projectedActiveMultiplicity Y active f u
        ∂(volume : Measure ProjectionSpace)).toReal) :
    ENNReal.ofReal (alpha / 2 * active.card * cap) ≤
      (retainCarrierFloor Y
        (popularCarrierFloor alpha cap)).shadingMass := by
  apply popularRestricted_halfMass_le_retainCarrierFloor_shadingMass
    Y active (twistedProjection f ⁻¹' X) alpha cap halpha0 hcap0
  rw [sum_restrictedMassReal_eq_projectedActiveMultiplicity_toReal
    Y active f hf X]
  exact hmass

/-! ## Returning the floor-restricted union estimate to the original union -/

/-- Floor restriction is a literal subshading. -/
theorem retainCarrierFloor_carrier_subset
    {iota : Type*} {F : ConvexFamily iota}
    (Y : Shading F) (lower : ENNReal) (i : iota) :
    (retainCarrierFloor Y lower).carrier i ⊆ Y.carrier i := by
  classical
  by_cases hfloor : lower ≤ volume (Y.carrier i)
  · simp [retainCarrierFloor, hfloor]
  · simp [retainCarrierFloor, hfloor]

/-- Every translated carrier of the floor restriction lies in the
corresponding translated carrier of the original shading. -/
theorem indexedTranslatedActualShadingUnion_retainCarrierFloor_subset
    {tau kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    (shift : tau → ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (Y : Shading (tubeBodyFamily fine.tubes)) (lower : ENNReal) :
    indexedTranslatedActualShadingUnion shift fine
        (retainCarrierFloor Y lower) ⊆
      indexedTranslatedActualShadingUnion shift fine Y := by
  intro p hp
  rcases Set.mem_iUnion.mp hp with ⟨ji, hji⟩
  apply Set.mem_iUnion.mpr
  refine ⟨ji, ?_⟩
  exact Set.image_mono
    (retainCarrierFloor_carrier_subset Y lower ji.2) hji

/-- Hence the floor-restricted translated union has no larger volume. -/
theorem volume_indexedTranslatedActualShadingUnion_retainCarrierFloor_le
    {tau kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    (shift : tau → ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (Y : Shading (tubeBodyFamily fine.tubes)) (lower : ENNReal) :
    volume
        (indexedTranslatedActualShadingUnion shift fine
          (retainCarrierFloor Y lower)) ≤
      volume (indexedTranslatedActualShadingUnion shift fine Y) :=
  measure_mono
    (indexedTranslatedActualShadingUnion_retainCarrierFloor_subset
      shift fine Y lower)

/-- Complete generic endpoint.  Popular restricted mass is converted into a
carrier floor; shared-`100T` containment and Katz--Tao produce the translated
union lower bound, which is then enlarged to the original translated union. -/
theorem popularRestricted_halfMass_le_sharedHundredHull_originalUnion
    {tau kappa : Type*} [Fintype tau] [Fintype kappa]
    {delta : NNReal} [DecidableEq kappa]
    (htau : Nonempty tau)
    (shift : tau → ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (shared : SharedHundredSourceContainer fine)
    (Y : Shading (tubeBodyFamily fine.tubes))
    (active : Finset kappa) (X : Set Space)
    (alpha cap : Real) (halphaPos : 0 < alpha) (hcapPos : 0 < cap)
    (hmass : alpha * active.card * cap ≤
      ∑ i ∈ active, restrictedMassReal Y X i)
    {C : ENNReal}
    (hKT : IsKatzTao C
      (indexedTranslatedBodyFamily shift (tubeBodyFamily fine.tubes))) :
    ENNReal.ofReal (alpha / 2 * active.card * cap) ≤
      (C *
        (volume (translatedSharedHundredHullContainer shift fine shared :
          Set Space) / popularCarrierFloor alpha cap)) *
        (volume (indexedTranslatedActualShadingUnion shift fine Y) /
          (Fintype.card tau : ENNReal)) := by
  have hfloorPos : 0 < popularCarrierFloor alpha cap := by
    rw [popularCarrierFloor, ENNReal.ofReal_pos]
    exact mul_pos (div_pos halphaPos (by norm_num)) hcapPos
  have hretained :
      ENNReal.ofReal (alpha / 2 * active.card * cap) ≤
        (retainCarrierFloor Y
          (popularCarrierFloor alpha cap)).shadingMass :=
    popularRestricted_halfMass_le_retainCarrierFloor_shadingMass
      Y active X alpha cap halphaPos.le hcapPos.le hmass
  have hWZ :=
    source_shadingMass_le_sharedHundredHull_div_floor_mul_copyAverage
      htau shift fine shared
      (retainCarrierFloor Y (popularCarrierFloor alpha cap))
      (popularCarrierFloor alpha cap) (ne_of_gt hfloorPos)
      ENNReal.ofReal_ne_top
      (lower_le_volume_retainCarrierFloor_of_ne_zero
        Y (popularCarrierFloor alpha cap)) hKT
  calc
    ENNReal.ofReal (alpha / 2 * active.card * cap) ≤
        (retainCarrierFloor Y
          (popularCarrierFloor alpha cap)).shadingMass := hretained
    _ ≤ (C *
          (volume
            (translatedSharedHundredHullContainer shift fine shared :
              Set Space) / popularCarrierFloor alpha cap)) *
          (volume
              (indexedTranslatedActualShadingUnion shift fine
                (retainCarrierFloor Y (popularCarrierFloor alpha cap))) /
            (Fintype.card tau : ENNReal)) := hWZ
    _ ≤ (C *
          (volume
            (translatedSharedHundredHullContainer shift fine shared :
              Set Space) / popularCarrierFloor alpha cap)) *
          (volume (indexedTranslatedActualShadingUnion shift fine Y) /
            (Fintype.card tau : ENNReal)) := by
      gcongr
      exact indexedTranslatedActualShadingUnion_retainCarrierFloor_subset
        shift fine Y (popularCarrierFloor alpha cap)

/-- Projected-slice version of the complete generic endpoint. -/
theorem projectedSlice_halfMass_le_sharedHundredHull_originalUnion
    {tau kappa : Type*} [Fintype tau] [Fintype kappa]
    {delta : NNReal} [DecidableEq kappa]
    (htau : Nonempty tau)
    (shift : tau → ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (shared : SharedHundredSourceContainer fine)
    (Y : Shading (tubeBodyFamily fine.tubes))
    (active : Finset kappa)
    (f : Real → Real) (hf : Measurable f) (X : Set ProjectionSpace)
    (alpha cap : Real) (halphaPos : 0 < alpha) (hcapPos : 0 < cap)
    (hmass : alpha * active.card * cap ≤
      (∫⁻ u in X, projectedActiveMultiplicity Y active f u
        ∂(volume : Measure ProjectionSpace)).toReal)
    {C : ENNReal}
    (hKT : IsKatzTao C
      (indexedTranslatedBodyFamily shift (tubeBodyFamily fine.tubes))) :
    ENNReal.ofReal (alpha / 2 * active.card * cap) ≤
      (C *
        (volume (translatedSharedHundredHullContainer shift fine shared :
          Set Space) / popularCarrierFloor alpha cap)) *
        (volume (indexedTranslatedActualShadingUnion shift fine Y) /
          (Fintype.card tau : ENNReal)) := by
  apply popularRestricted_halfMass_le_sharedHundredHull_originalUnion
    htau shift fine shared Y active (twistedProjection f ⁻¹' X)
      alpha cap halphaPos hcapPos
  · rw [sum_restrictedMassReal_eq_projectedActiveMultiplicity_toReal
      Y active f hf X]
    exact hmass
  · exact hKT

variable {depth : Nat} {nominalRadius : Nat → NNReal}
  {Index : Nat → Type*}
  [∀ l, Fintype (Index l)] [∀ l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  {spacing : Real} {siteCount gridConstant : Nat}

/-- Collision-cell specialization: the fixed-grid/100-neighbour producer
automatically discharges Katz--Tao and the hierarchy collision certificate
automatically supplies the shared source `100T` hull. -/
theorem selectedHierarchyCollisionCell_popularRestricted_halfMass_le_originalUnion
    (grid : FixedShearCopyGridCertificate siteCount gridConstant)
    (joint : HierarchyJointRandomMotionCertificate H G)
    (wz : HierarchyLevelWZSeparationData H)
    (k : Fin depth) (p : Index (k.1 + 1))
    (hp : p ∈ (G.toDependentSource.layer k).activeParents)
    (a : ModelCandidate (hierarchyCollisionGrid H G joint k p))
    (r : Fin (repetitions G.toDependentSource k))
    (baseD rho : Real) (hspacing : 0 < spacing) (hrho : 0 ≤ rho)
    (source : Finset
      (SelectedHierarchyCollisionCellIndex H G joint k p a r))
    (hselected :
      (Finset.univ : Finset
        (SelectedHierarchyCollisionCellIndex H G joint k p a r)) ⊆
      fixedVerticalChartIndices
        (selectedHierarchyCollisionCellFamily H G joint k p a r) source)
    (hcluster : ∀ l,
      |tubeGraphD
          ((selectedHierarchyCollisionCellFamily H G joint k p a r).tubes l) -
        baseD| ≤ rho)
    (hsiteCount : 0 < siteCount)
    (Y : Shading
      (tubeBodyFamily
        (selectedHierarchyCollisionCellFamily H G joint k p a r).tubes))
    (active : Finset
      (SelectedHierarchyCollisionCellIndex H G joint k p a r))
    (X : Set Space)
    (alpha cap : Real) (halphaPos : 0 < alpha) (hcapPos : 0 < cap)
    (hmass : alpha * active.card * cap ≤
      ∑ i ∈ active, restrictedMassReal Y X i) :
    ENNReal.ofReal (alpha / 2 * active.card * cap) ≤
      ((16 *
          ((gridConstant * commonHundredNeighbourPackingConstant : Nat) :
            ENNReal)) *
        (volume
            (translatedSharedHundredHullContainer
              (shearReducedShift spacing (siteCount := siteCount))
              (selectedHierarchyCollisionCellFamily H G joint k p a r)
              (selectedHierarchyCollisionCell_sharedHundredSourceContainer
                H G joint k p a r) : Set Space) /
          popularCarrierFloor alpha cap)) *
        (volume
            (indexedTranslatedActualShadingUnion
              (shearReducedShift spacing (siteCount := siteCount))
              (selectedHierarchyCollisionCellFamily H G joint k p a r) Y) /
          (siteCount : ENNReal)) := by
  have hKT :=
    selectedHierarchyCollisionCell_fullTranslatedFamily_isKatzTao
      grid joint wz k p hp a r baseD rho hspacing hrho source hselected
        hcluster
  simpa only [Fintype.card_fin] using
    (popularRestricted_halfMass_le_sharedHundredHull_originalUnion
      (htau := ⟨⟨0, hsiteCount⟩⟩)
      (shift := shearReducedShift spacing (siteCount := siteCount))
      (fine := selectedHierarchyCollisionCellFamily H G joint k p a r)
      (shared :=
        selectedHierarchyCollisionCell_sharedHundredSourceContainer
          H G joint k p a r)
      (Y := Y) (active := active) (X := X)
      (alpha := alpha) (cap := cap) halphaPos hcapPos hmass hKT)

#print axioms popularCarrierFloor_le_carrierMass_of_mem
#print axioms popularRestricted_exactBudget_le_retainCarrierFloor_shadingMass
#print axioms popularRestricted_halfMass_le_retainCarrierFloor_shadingMass
#print axioms projectedSlice_halfMass_le_retainCarrierFloor_shadingMass
#print axioms indexedTranslatedActualShadingUnion_retainCarrierFloor_subset
#print axioms popularRestricted_halfMass_le_sharedHundredHull_originalUnion
#print axioms projectedSlice_halfMass_le_sharedHundredHull_originalUnion
#print axioms selectedHierarchyCollisionCell_popularRestricted_halfMass_le_originalUnion

end
end FamilyStickyHierarchyWZ2TranslatedCollisionCellPopularFloorUnionV1
