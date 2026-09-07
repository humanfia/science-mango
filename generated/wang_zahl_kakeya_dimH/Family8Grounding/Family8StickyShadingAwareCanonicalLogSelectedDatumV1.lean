import Family8Grounding.Family8StickyShadingAwareCanonicalLogPartitionV1
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1

/-!
# The shading-aware logarithmic refinement as an actual datum

Only uniform-refinement metadata changes.  The indexed tubes and the actual
source shading are definitionally unchanged, while the chosen refinement is
the one produced by the shading-mass weighted selector.
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal NNReal

namespace Family8StickyShadingAwareCanonicalLogSelectedDatumV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareCanonicalLogRestrictedFamiliesV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- Retag the source datum by the literal shading-aware selected fine family.
The selector itself is run on the source datum's actual shading. -/
def shadingAwareSelectedActualDatum
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (A : ENNReal)
    (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn D.shading S.activeFine ≠ 0) :
    ActualTubeDatum delta index where
  family := shadingAwareSelectedFineFamily
    S D.shading A hA0 hAtop hrho hactive hmass
  shading := D.shading

@[simp] theorem shadingAwareSelectedActualDatum_family
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (A : ENNReal)
    (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn D.shading S.activeFine ≠ 0) :
    (shadingAwareSelectedActualDatum
      D S A hA0 hAtop hrho hactive hmass).family =
      shadingAwareSelectedFineFamily
        S D.shading A hA0 hAtop hrho hactive hmass :=
  rfl

@[simp] theorem shadingAwareSelectedActualDatum_shading
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (A : ENNReal)
    (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn D.shading S.activeFine ≠ 0) :
    (shadingAwareSelectedActualDatum
      D S A hA0 hAtop hrho hactive hmass).shading = D.shading :=
  rfl

@[simp] theorem shadingAwareSelectedActualDatum_family_tubes
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (A : ENNReal)
    (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn D.shading S.activeFine ≠ 0) (i : index) :
    (shadingAwareSelectedActualDatum
      D S A hA0 hAtop hrho hactive hmass).family.tubes i =
      D.family.tubes i :=
  rfl

@[simp] theorem shadingAwareSelectedActualDatum_actualFamilyVolume
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (A : ENNReal)
    (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn D.shading S.activeFine ≠ 0) :
    (shadingAwareSelectedActualDatum
      D S A hA0 hAtop hrho hactive hmass).actualFamilyVolume =
      D.actualFamilyVolume :=
  rfl

@[simp] theorem shadingAwareSelectedActualDatum_shadingMass
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (A : ENNReal)
    (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn D.shading S.activeFine ≠ 0) :
    (shadingAwareSelectedActualDatum
      D S A hA0 hAtop hrho hactive hmass).shading.shadingMass =
      D.shading.shadingMass :=
  rfl

@[simp] theorem shadingAwareSelectedActualDatum_shadedUnion
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (A : ENNReal)
    (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn D.shading S.activeFine ≠ 0) :
    (shadingAwareSelectedActualDatum
      D S A hA0 hAtop hrho hactive hmass).shading.shadedUnion =
      D.shading.shadedUnion :=
  rfl

@[simp] theorem shadingAwareSelectedActualDatum_averageMultiplicity
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (A : ENNReal)
    (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn D.shading S.activeFine ≠ 0) :
    (shadingAwareSelectedActualDatum
      D S A hA0 hAtop hrho hactive hmass).shading.averageMultiplicity =
      D.shading.averageMultiplicity :=
  rfl

/-- Admissibility is unchanged because every actual tube is unchanged. -/
theorem ActualTubeDatum.IsAdmissible.shadingAwareSelected
    {D : ActualTubeDatum delta index} (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (A : ENNReal)
    (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn D.shading S.activeFine ≠ 0) :
    (shadingAwareSelectedActualDatum
      D S A hA0 hAtop hrho hactive hmass).IsAdmissible :=
  { delta_pos := hD.delta_pos
    delta_le_half := hD.delta_le_half
    contained_in_unit_ball := hD.contained_in_unit_ball
    pairwise_essentiallyDistinct := hD.pairwise_essentiallyDistinct }

@[simp] theorem shadingAwareSelectedActualDatum_katzTaoHypotheses_iff
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (A : ENNReal)
    (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn D.shading S.activeFine ≠ 0) (eta : Real) :
    KatzTaoHypotheses
        (shadingAwareSelectedActualDatum
          D S A hA0 hAtop hrho hactive hmass) eta ↔
      KatzTaoHypotheses D eta :=
  Iff.rfl

@[simp] theorem shadingAwareSelectedActualDatum_frostmanHypotheses_iff
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (A : ENNReal)
    (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn D.shading S.activeFine ≠ 0) (eta : Real) :
    FrostmanHypotheses
        (shadingAwareSelectedActualDatum
          D S A hA0 hAtop hrho hactive hmass) eta ↔
      FrostmanHypotheses D eta :=
  Iff.rfl

theorem shadingAwareSelectedActualDatum_isKatzTao_iff
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (A : ENNReal)
    (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn D.shading S.activeFine ≠ 0) (C : ENNReal) :
    IsKatzTao C
        (shadingAwareSelectedActualDatum
          D S A hA0 hAtop hrho hactive hmass).family.bodyFamily ↔
      IsKatzTao C D.family.bodyFamily :=
  Iff.rfl

#print axioms shadingAwareSelectedActualDatum
#print axioms shadingAwareSelectedActualDatum_actualFamilyVolume
#print axioms shadingAwareSelectedActualDatum_averageMultiplicity
#print axioms ActualTubeDatum.IsAdmissible.shadingAwareSelected
#print axioms shadingAwareSelectedActualDatum_katzTaoHypotheses_iff
#print axioms shadingAwareSelectedActualDatum_frostmanHypotheses_iff
#print axioms shadingAwareSelectedActualDatum_isKatzTao_iff

end
end Family8StickyShadingAwareCanonicalLogSelectedDatumV1
