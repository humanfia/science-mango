import FamilyStickyGrounding.FamilyStickyWZ2TranslatedActualShadingInstantiationV1
import FamilyStickyGrounding.FamilyStickyWZ2AmbientCinematicTranslationVolumeV1
import FamilyStickyGrounding.Family6AffineKatzTaoTransportV3
import FamilyStickyCinematicL32WZL3FixedVerticalChartAdapterV1

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1

open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2CinematicTranslationV1
open FamilyStickyWZ2TranslatedShadingUnionCovarianceV1
open FamilyStickyWZ2AmbientCinematicTranslationVolumeV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyWZ2TranslatedActualShadingInstantiationV1
open FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyCinematicL32WZL3FixedVerticalChartAdapterV1
open Family6AffineConvexVolumeCoreV1
open Family6AffineKatzTaoTransportV3
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-!
# Density and Katz--Tao provenance for translated WZ2 copies

The WZ2 ambient parameter translation is bundled below as an actual affine
equivalence.  This packages each transported tube body as a convex body and
each transported carrier as a genuine `Shading`.  A single copy preserves
shading density and the source Katz--Tao constant.  The full product-indexed
family has the same density, but the unconditional Katz--Tao estimate proved
here has the explicit loss `Fintype.card tau`; no uniform multi-copy constant
is accepted as a field or premise.
-/

/-- Linear part of the ambient WZ2 shear. -/
def ambientCinematicLinearShear (d0 : Real) : Space ≃ₗ[Real] Space where
  toFun p := point3 (p 0) (p 1 + d0 * p 2) (p 2)
  invFun p := point3 (p 0) (p 1 - d0 * p 2) (p 2)
  left_inv p := by
    ext i
    fin_cases i <;> simp [point3]
  right_inv p := by
    ext i
    fin_cases i <;> simp [point3]
  map_add' p q := by
    ext i
    fin_cases i <;> simp [point3]; ring
  map_smul' c p := by
    ext i
    fin_cases i <;> simp [point3]; ring

/-- The ambient parameter translation as an affine equivalence. -/
def ambientCinematicAffineEquiv
    (a0 b0 d0 : Real) : Space ≃ᵃ[Real] Space :=
  AffineEquiv.mk' (ambientCinematicTranslation a0 b0 d0)
    (ambientCinematicLinearShear d0) 0 (by
      intro p
      ext i
      fin_cases i <;>
        simp [ambientCinematicTranslation, ambientCinematicLinearShear,
          point3];
        ring)

@[simp]
theorem ambientCinematicAffineEquiv_apply
    (a0 b0 d0 : Real) (p : Space) :
    ambientCinematicAffineEquiv a0 b0 d0 p =
      ambientCinematicTranslation a0 b0 d0 p :=
  rfl

/-- Convex-body family of one translated copy. -/
def fixedTranslatedBodyFamily
    {kappa : Type*} (a0 b0 d0 : Real) (F : ConvexFamily kappa) :
    ConvexFamily kappa :=
  affineImageFamily (ambientCinematicAffineEquiv a0 b0 d0) F

/-- All translated copies, retaining the product index even if parameters
from different copies collide. -/
def indexedTranslatedBodyFamily
    {tau kappa : Type*}
    (shift : tau -> ReducedLineParameter) (F : ConvexFamily kappa) :
    ConvexFamily (tau × kappa) :=
  fun ji => fixedTranslatedBodyFamily
    (shift ji.1).1 (shift ji.1).2.1 (shift ji.1).2.2 F ji.2

@[simp]
theorem coe_fixedTranslatedBodyFamily
    {kappa : Type*} (a0 b0 d0 : Real) (F : ConvexFamily kappa)
    (i : kappa) :
    (fixedTranslatedBodyFamily a0 b0 d0 F i : Set Space) =
      ambientCinematicTranslation a0 b0 d0 '' (F i : Set Space) :=
  rfl

@[simp]
theorem coe_indexedTranslatedBodyFamily
    {tau kappa : Type*}
    (shift : tau -> ReducedLineParameter) (F : ConvexFamily kappa)
    (ji : tau × kappa) :
    (indexedTranslatedBodyFamily shift F ji : Set Space) =
      ambientCinematicTranslation
          (shift ji.1).1 (shift ji.1).2.1 (shift ji.1).2.2 ''
        (F ji.2 : Set Space) :=
  rfl

/-- The literal product-indexed translated carriers form a genuine shading
of the affine-image convex-body family. -/
def indexedTranslatedActualShading
    {tau kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (Y : Shading (tubeBodyFamily fine.tubes)) :
    Shading
      (indexedTranslatedBodyFamily shift (tubeBodyFamily fine.tubes)) where
  carrier ji := indexedTranslatedActualShadingCarrier shift fine Y ji
  measurable_carrier ji := by
    exact
      (ambientCinematicTranslationMeasurableEquiv
        (shift ji.1).1 (shift ji.1).2.1
        (shift ji.1).2.2).measurableSet_image.mpr
          (Y.measurable_carrier ji.2)
  carrier_subset ji := by
    exact indexedTranslatedActualShadingCarrier_subset_tubeImage
      shift fine Y ji.1 ji.2

@[simp]
theorem indexedTranslatedActualShading_carrier
    {tau kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (Y : Shading (tubeBodyFamily fine.tubes))
    (ji : tau × kappa) :
    (indexedTranslatedActualShading shift fine Y).carrier ji =
      indexedTranslatedActualShadingCarrier shift fine Y ji :=
  rfl

/-- Total shading mass over all copies is the copy count times the original
shading mass. -/
theorem indexedTranslatedActualShading_shadingMass
    {tau kappa : Type*} {delta : NNReal}
    [Fintype tau] [Fintype kappa] [DecidableEq kappa]
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (Y : Shading (tubeBodyFamily fine.tubes)) :
    (indexedTranslatedActualShading shift fine Y).shadingMass =
      (Fintype.card tau : ENNReal) * Y.shadingMass := by
  classical
  unfold Shading.shadingMass
  rw [Fintype.sum_prod_type]
  simp_rw [indexedTranslatedActualShading_carrier,
    indexedTranslatedActualShadingCarrier,
    volume_translatedShadingCarrier]
  simp [nsmul_eq_mul]

/-- Summed convex-family volume over all copies has the same copy factor. -/
theorem indexedTranslatedBodyFamily_familyVolume
    {tau kappa : Type*}
    [Fintype tau] [Fintype kappa]
    (shift : tau -> ReducedLineParameter) (F : ConvexFamily kappa) :
    familyVolume (indexedTranslatedBodyFamily shift F) =
      (Fintype.card tau : ENNReal) * familyVolume F := by
  classical
  unfold familyVolume
  rw [Fintype.sum_prod_type]
  simp_rw [coe_indexedTranslatedBodyFamily,
    volume_ambientCinematicTranslation_image]
  simp [nsmul_eq_mul]

/-- For any nonempty finite set of translation copies, translated-copy
shading density is exactly the source density. -/
theorem indexedTranslatedActualShading_shadingDensity
    {tau kappa : Type*} {delta : NNReal}
    [Fintype tau] [Nonempty tau]
    [Fintype kappa] [DecidableEq kappa]
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (Y : Shading (tubeBodyFamily fine.tubes)) :
    (indexedTranslatedActualShading shift fine Y).shadingDensity =
      Y.shadingDensity := by
  unfold Shading.shadingDensity
  rw [indexedTranslatedActualShading_shadingMass,
    indexedTranslatedBodyFamily_familyVolume]
  apply ENNReal.mul_div_mul_left
  · exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty tau)).ne'
  · exact ENNReal.coe_ne_top

/-- One affine shear copy preserves the source Katz--Tao constant exactly. -/
theorem fixedTranslatedBodyFamily_isKatzTao
    {kappa : Type*} [Fintype kappa]
    {C : ENNReal} (a0 b0 d0 : Real) (F : ConvexFamily kappa)
    (hKT : IsKatzTao C F) :
    IsKatzTao C (fixedTranslatedBodyFamily a0 b0 d0 F) := by
  exact isKatzTao_affineImageFamily
    (ambientCinematicAffineEquiv a0 b0 d0) F hKT

/-- Contained mass of the product-indexed family is the sum of the contained
masses of its individual copies. -/
theorem containedMass_indexedTranslatedBodyFamily
    {tau kappa : Type*} [Fintype tau] [Fintype kappa]
    (shift : tau -> ReducedLineParameter) (F : ConvexFamily kappa)
    (K : ConvexBody Space) :
    containedMass (indexedTranslatedBodyFamily shift F) K =
      ∑ j, containedMass
        (fixedTranslatedBodyFamily
          (shift j).1 (shift j).2.1 (shift j).2.2 F) K := by
  classical
  unfold containedMass containedIndices
  rw [← Finset.univ_product_univ, Finset.sum_filter, Finset.sum_product]
  simp only [Finset.sum_filter]
  rfl

/-- Without spacing information, the internally derived multi-copy
Katz--Tao constant has the explicit factor `card tau`. -/
theorem indexedTranslatedBodyFamily_isKatzTao_card_mul
    {tau kappa : Type*} [Fintype tau] [Fintype kappa]
    {C : ENNReal}
    (shift : tau -> ReducedLineParameter) (F : ConvexFamily kappa)
    (hKT : IsKatzTao C F) :
    IsKatzTao ((Fintype.card tau : ENNReal) * C)
      (indexedTranslatedBodyFamily shift F) := by
  intro K
  unfold IsKatzTaoAt
  rw [containedMass_indexedTranslatedBodyFamily]
  calc
    (∑ j, containedMass
        (fixedTranslatedBodyFamily
          (shift j).1 (shift j).2.1 (shift j).2.2 F) K) <=
        ∑ _j : tau, C * volume (K : Set Space) := by
      apply Finset.sum_le_sum
      intro j _hj
      exact fixedTranslatedBodyFamily_isKatzTao
        (shift j).1 (shift j).2.1 (shift j).2.2 F hKT K
    _ = ((Fintype.card tau : ENNReal) * C) *
        volume (K : Set Space) := by
      simp [nsmul_eq_mul]
      ac_rfl

/-- A certified WZ `L_3` source is already entirely in the literal fixed
vertical chart, so this stage has no hidden cardinality loss. -/
theorem fixedVerticalChartIndices_eq_source_of_wzL3
    {delta : NNReal} {kappa : Type*} [DecidableEq kappa]
    (S : WZL3UniformTubeSource delta kappa) :
    fixedVerticalChartIndices S.family S.source = S.source := by
  apply Finset.Subset.antisymm
  · exact fixedVerticalChartIndices_subset_source S.family S.source
  · exact source_subset_fixedVerticalChartIndices S

theorem card_fixedVerticalChartIndices_of_wzL3
    {delta : NNReal} {kappa : Type*} [DecidableEq kappa]
    (S : WZL3UniformTubeSource delta kappa) :
    (fixedVerticalChartIndices S.family S.source).card = S.source.card := by
  rw [fixedVerticalChartIndices_eq_source_of_wzL3]

theorem card_translatedFixedVerticalChartIndices_of_wzL3
    {tau kappa : Type*} [Fintype tau]
    {delta : NNReal} [DecidableEq kappa]
    (S : WZL3UniformTubeSource delta kappa) :
    Fintype.card
        (tau × ↥(fixedVerticalChartIndices S.family S.source)) =
      Fintype.card tau * S.source.card := by
  rw [Fintype.card_prod, Fintype.card_coe,
    card_fixedVerticalChartIndices_of_wzL3]

#print axioms ambientCinematicLinearShear
#print axioms ambientCinematicAffineEquiv_apply
#print axioms coe_fixedTranslatedBodyFamily
#print axioms indexedTranslatedActualShading_carrier
#print axioms indexedTranslatedActualShading_shadingMass
#print axioms indexedTranslatedBodyFamily_familyVolume
#print axioms indexedTranslatedActualShading_shadingDensity
#print axioms fixedTranslatedBodyFamily_isKatzTao
#print axioms containedMass_indexedTranslatedBodyFamily
#print axioms indexedTranslatedBodyFamily_isKatzTao_card_mul
#print axioms fixedVerticalChartIndices_eq_source_of_wzL3
#print axioms card_fixedVerticalChartIndices_of_wzL3
#print axioms card_translatedFixedVerticalChartIndices_of_wzL3

end
end FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1
