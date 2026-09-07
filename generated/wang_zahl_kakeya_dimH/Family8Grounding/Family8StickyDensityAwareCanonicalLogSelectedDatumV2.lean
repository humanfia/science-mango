import Family8Grounding.Family8StickyDensityAwareCanonicalLogPartitionV2
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1

/-!
# The canonical logarithmic refinement as an actual datum

ADD-only successor of V1, correcting its namespace and universe annotations.
The logarithmic selection changes only refinement metadata; the tube function
is literal.  Hence the source shading and all geometric datum quantities can
be used on the selected family without a cast or a comparison loss.
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal NNReal

namespace Family8StickyDensityAwareCanonicalLogSelectedDatumV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8StickyDensityAwareCanonicalLogBucketSelectedV1
open Family8StickyDensityAwareCanonicalLogRestrictedFamiliesV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The source actual datum retagged by the canonical logarithmic refinement.
The original shading has definitionally the required body-family type. -/
def densityAwareSelectedActualDatum
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    ActualTubeDatum delta index where
  family := densityAwareSelectedFineFamily
    S A hA hdelta hrho hactive
  shading := D.shading

@[simp] theorem densityAwareSelectedActualDatum_family
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    (densityAwareSelectedActualDatum
      D S A hA hdelta hrho hactive).family =
      densityAwareSelectedFineFamily S A hA hdelta hrho hactive :=
  rfl

@[simp] theorem densityAwareSelectedActualDatum_shading
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    (densityAwareSelectedActualDatum
      D S A hA hdelta hrho hactive).shading = D.shading :=
  rfl

@[simp] theorem densityAwareSelectedActualDatum_family_tubes
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) (i : index) :
    (densityAwareSelectedActualDatum
      D S A hA hdelta hrho hactive).family.tubes i =
      D.family.tubes i :=
  rfl

@[simp] theorem densityAwareSelectedActualDatum_actualFamilyVolume
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    (densityAwareSelectedActualDatum
      D S A hA hdelta hrho hactive).actualFamilyVolume =
      D.actualFamilyVolume :=
  rfl

@[simp] theorem densityAwareSelectedActualDatum_shadingMass
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    (densityAwareSelectedActualDatum
      D S A hA hdelta hrho hactive).shading.shadingMass =
      D.shading.shadingMass :=
  rfl

@[simp] theorem densityAwareSelectedActualDatum_shadedUnion
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    (densityAwareSelectedActualDatum
      D S A hA hdelta hrho hactive).shading.shadedUnion =
      D.shading.shadedUnion :=
  rfl

@[simp] theorem densityAwareSelectedActualDatum_averageMultiplicity
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    (densityAwareSelectedActualDatum
      D S A hA hdelta hrho hactive).shading.averageMultiplicity =
      D.shading.averageMultiplicity :=
  rfl

/-- Actual admissibility survives literally because every tube is unchanged. -/
theorem ActualTubeDatum.IsAdmissible.densityAwareSelected
    {D : ActualTubeDatum delta index} (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    (densityAwareSelectedActualDatum
      D S A hA hdelta hrho hactive).IsAdmissible :=
  { delta_pos := hD.delta_pos
    delta_le_half := hD.delta_le_half
    contained_in_unit_ball := hD.contained_in_unit_ball
    pairwise_essentiallyDistinct := hD.pairwise_essentiallyDistinct }

@[simp] theorem densityAwareSelectedActualDatum_katzTaoHypotheses_iff
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) (eta : Real) :
    KatzTaoHypotheses
        (densityAwareSelectedActualDatum
          D S A hA hdelta hrho hactive) eta ↔
      KatzTaoHypotheses D eta :=
  Iff.rfl

@[simp] theorem densityAwareSelectedActualDatum_frostmanHypotheses_iff
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) (eta : Real) :
    FrostmanHypotheses
        (densityAwareSelectedActualDatum
          D S A hA hdelta hrho hactive) eta ↔
      FrostmanHypotheses D eta :=
  Iff.rfl

theorem densityAwareSelectedActualDatum_isKatzTao_iff
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) (C : ENNReal) :
    IsKatzTao C
        (densityAwareSelectedActualDatum
          D S A hA hdelta hrho hactive).family.bodyFamily ↔
      IsKatzTao C D.family.bodyFamily :=
  Iff.rfl

#print axioms densityAwareSelectedActualDatum
#print axioms densityAwareSelectedActualDatum_actualFamilyVolume
#print axioms densityAwareSelectedActualDatum_averageMultiplicity
#print axioms ActualTubeDatum.IsAdmissible.densityAwareSelected
#print axioms densityAwareSelectedActualDatum_katzTaoHypotheses_iff
#print axioms densityAwareSelectedActualDatum_frostmanHypotheses_iff
#print axioms densityAwareSelectedActualDatum_isKatzTao_iff

end
end Family8StickyDensityAwareCanonicalLogSelectedDatumV2
