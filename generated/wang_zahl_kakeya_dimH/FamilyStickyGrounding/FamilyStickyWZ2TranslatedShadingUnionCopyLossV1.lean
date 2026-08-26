import FamilyStickyGrounding.FamilyStickyWZ2TranslatedActualShadingInstantiationV1
import FamilyStickyGrounding.FamilyStickyWZ2AmbientCinematicTranslationVolumeV1

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyWZ2TranslatedShadingUnionCopyLossV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2CinematicTranslationV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyWZ2TranslatedShadingUnionCovarianceV1
open FamilyStickyWZ2TranslatedActualShadingInstantiationV1
open FamilyStickyWZ2AmbientCinematicTranslationVolumeV1

noncomputable section

/-!
# Returning a translated-copy union bound to the original shading

The proof of the Katz--Tao-at-every-scale branch of the sticky theorem forms
finitely many volume-preserving translates of one shaded tube family.  Its
last deterministic step uses that the union of all translated copies has
volume at most the number of copies times the volume of the original shaded
union.

The WZ2 translation modules already prove the exact carrier covariance and
three-dimensional volume preservation.  This file performs the previously
missing finite-union step for the literal product-indexed translated shading.
It does not assume a union-volume comparison as a callback.
-/

universe u v

/-- The literal union of every carrier in every translated copy.  Product
indexing retains repeated copies and repeated source indices. -/
def indexedTranslatedActualShadingUnion
    {tau : Type u} {kappa : Type v} {delta : NNReal}
    [DecidableEq kappa]
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (Y : Shading (tubeBodyFamily fine.tubes)) : Set Space :=
  ⋃ ji : tau × kappa,
    indexedTranslatedActualShadingCarrier shift fine Y ji

/-- The product-indexed carrier union is exactly the union, over copy
indices, of the ambient cinematic image of the original shaded union. -/
theorem indexedTranslatedActualShadingUnion_eq_iUnion_copy
    {tau : Type u} {kappa : Type v} {delta : NNReal}
    [DecidableEq kappa]
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (Y : Shading (tubeBodyFamily fine.tubes)) :
    indexedTranslatedActualShadingUnion shift fine Y =
      ⋃ j : tau,
        ambientCinematicTranslation
            (shift j).1 (shift j).2.1 (shift j).2.2 ''
          Y.shadedUnion := by
  ext p
  constructor
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨⟨j, i⟩, hji⟩
    rcases hji with ⟨q, hq, rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨j, q, ?_, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, hq⟩
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨j, q, hq, rfl⟩
    rcases Set.mem_iUnion.mp hq with ⟨i, hi⟩
    apply Set.mem_iUnion.mpr
    exact ⟨(j, i), q, hi, rfl⟩

/-- A finite family of actual cinematic translates costs at most its literal
copy cardinality in ambient union volume. -/
theorem volume_indexedTranslatedActualShadingUnion_le_card_mul
    {tau : Type u} {kappa : Type v} {delta : NNReal}
    [Fintype tau] [DecidableEq kappa]
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (Y : Shading (tubeBodyFamily fine.tubes)) :
    volume (indexedTranslatedActualShadingUnion shift fine Y) <=
      (Fintype.card tau : ENNReal) * volume Y.shadedUnion := by
  rw [indexedTranslatedActualShadingUnion_eq_iUnion_copy]
  calc
    volume
        (⋃ j : tau,
          ambientCinematicTranslation
              (shift j).1 (shift j).2.1 (shift j).2.2 ''
            Y.shadedUnion) <=
      ∑ j : tau,
        volume
          (ambientCinematicTranslation
              (shift j).1 (shift j).2.1 (shift j).2.2 ''
            Y.shadedUnion) :=
      measure_iUnion_fintype_le volume _
    _ = ∑ _j : tau, volume Y.shadedUnion := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact volume_ambientCinematicTranslation_image
        (shift j).1 (shift j).2.1 (shift j).2.2 Y.shadedUnion
    _ = (Fintype.card tau : ENNReal) * volume Y.shadedUnion := by
      simp [nsmul_eq_mul]

/-- Any lower bound proved for the complete translated union returns to the
original shaded union after exactly the finite copy-cardinality loss.  The
division formulation is safe even for an empty copy type. -/
theorem lower_div_card_le_volume_originalShadedUnion
    {tau : Type u} {kappa : Type v} {delta : NNReal}
    [Fintype tau] [DecidableEq kappa]
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (Y : Shading (tubeBodyFamily fine.tubes))
    (lower : ENNReal)
    (hlower : lower <=
      volume (indexedTranslatedActualShadingUnion shift fine Y)) :
    lower / (Fintype.card tau : ENNReal) <= volume Y.shadedUnion := by
  apply ENNReal.div_le_of_le_mul'
  exact hlower.trans
    (volume_indexedTranslatedActualShadingUnion_le_card_mul shift fine Y)

/-- If an upstream union theorem controls the original shaded mass by a
factor times the *average translated-copy union volume*, then that factor is
an upper bound for the original average multiplicity.  This is the final
deterministic division in the Katz--Tao-at-every-scale argument. -/
theorem averageMultiplicity_le_of_shadingMass_le_factor_mul_copyAverage
    {tau : Type u} {kappa : Type v} {delta : NNReal}
    [Fintype tau] [Fintype kappa] [DecidableEq kappa]
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (Y : Shading (tubeBodyFamily fine.tubes))
    (factor : ENNReal)
    (hmass : Y.shadingMass <=
      factor *
        (volume (indexedTranslatedActualShadingUnion shift fine Y) /
          (Fintype.card tau : ENNReal))) :
    Y.averageMultiplicity <= factor := by
  have hcopyAverage :
      volume (indexedTranslatedActualShadingUnion shift fine Y) /
          (Fintype.card tau : ENNReal) <= volume Y.shadedUnion :=
    lower_div_card_le_volume_originalShadedUnion shift fine Y _ le_rfl
  unfold Shading.averageMultiplicity
  apply ENNReal.div_le_of_le_mul
  exact hmass.trans (mul_le_mul' le_rfl hcopyAverage)

#print axioms indexedTranslatedActualShadingUnion_eq_iUnion_copy
#print axioms volume_indexedTranslatedActualShadingUnion_le_card_mul
#print axioms lower_div_card_le_volume_originalShadedUnion
#print axioms averageMultiplicity_le_of_shadingMass_le_factor_mul_copyAverage

end

end FamilyStickyWZ2TranslatedShadingUnionCopyLossV1
