import Family8Grounding.Family8PositiveCarrierShadingRestrictionV4

/-!
# Local volume preservation under positive-carrier restriction

Removing the zero-volume carrier pieces preserves not only the volume of the
whole shaded union, but also its volume inside every measurable window.  The
raw shading and its positive-carrier restriction are kept fixed throughout.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8PositiveCarrierShadingRestrictionLocalVolumeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8PositiveCarrierShadingRestrictionV4

noncomputable section

set_option autoImplicit false
set_option warningAsError true

universe u

variable {iota : Type u} [Fintype iota] {F : ConvexFamily iota}

/-- Restricting a finite shading to its positive-volume carriers preserves
the volume of its shaded union inside the same measurable window. -/
theorem positiveCarrierShading_shadedUnion_inter_volume
    (Y : Shading F) (Omega : Set Space) (_hOmega : MeasurableSet Omega) :
    volume ((positiveCarrierShading Y).shadedUnion ∩ Omega) =
      volume (Y.shadedUnion ∩ Omega) := by
  have hzeroInter :
      volume (zeroCarrierUnion Y ∩ Omega) = 0 :=
    measure_mono_null Set.inter_subset_left (volume_zeroCarrierUnion Y)
  have hnull :
      (((positiveCarrierShading Y).shadedUnion ∩ Omega) ∪
          (zeroCarrierUnion Y ∩ Omega) : Set Space) =ᵐ[volume]
        ((positiveCarrierShading Y).shadedUnion ∩ Omega : Set Space) :=
    union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr hzeroInter)
  have hdecomp :
      (((positiveCarrierShading Y).shadedUnion ∪ zeroCarrierUnion Y) ∩
          Omega) =
        ((positiveCarrierShading Y).shadedUnion ∩ Omega) ∪
          (zeroCarrierUnion Y ∩ Omega) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_union]
    tauto
  rw [shadedUnion_eq_positiveCarrier_union_zeroCarrier Y, hdecomp]
  exact (measure_congr hnull).symm

#print axioms positiveCarrierShading_shadedUnion_inter_volume

end

end Family8PositiveCarrierShadingRestrictionLocalVolumeV1
