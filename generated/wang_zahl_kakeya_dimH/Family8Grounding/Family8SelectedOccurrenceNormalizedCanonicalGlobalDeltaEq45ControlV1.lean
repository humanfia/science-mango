import Family8Grounding.Family8AmbientFamilyVolumeDensityV2
import Family8Grounding.Family8SelectedOccurrenceNormalizedGlobalOwnerEq45ControlV1
import Mathlib.Tactic

/-!
# Canonical global Delta for the normalized selected outer family

The global-owner Equation (45) wrapper only needs an ambient Frostman
constant and one ambient-mass coefficient.  For the exact selected outer
family, that coefficient has a canonical minimal choice: its actual indexed
family volume divided by the actual raw ambient volume.

The resulting `NNReal` `Delta` is the literal finite product of the Frostman
constant and this density.  No enlarged numerical envelope, raw plank datum,
inside-thickening callback, or nonconstant owner is introduced.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceNormalizedCanonicalGlobalDeltaEq45ControlV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8AmbientFamilyVolumeDensityV2
open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerHullCommonScaleDatumV1
open Family8SelectedOccurrenceNormalizedGlobalOwnerEq45ControlV1
open Family8SelectedOccurrenceNormalizedOuterDatumV1
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8UniqueOwnerLocalDeltaMaxThickControlV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

variable {delta : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {active : Finset iota}

variable
  (P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates active) (hullContainer fine.bodyFamily) active)

/-- The canonical minimal `NNReal` concentration coefficient for the exact
selected outer family.  The density is deliberately measured before the
common affine normalization, where the supplied Frostman certificate lives.
-/
def selectedOccurrenceNormalizedOuterCanonicalDelta
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (ambient : ConvexBody Space) (CF : ENNReal) : NNReal :=
  (CF * ambientFamilyVolumeDensity
    (selectedOccurrenceOuterFamily P Rside) ambient).toNNReal

/-- When the two defining factors are finite, coercing the canonical
coefficient back to `ENNReal` recovers their exact product. -/
theorem selectedOccurrenceNormalizedOuterCanonicalDelta_coe
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (ambient : ConvexBody Space) (CF : ENNReal)
    (hCF : CF ≠ ∞)
    (hambientVolume : volume (ambient : Set Space) ≠ 0) :
    (selectedOccurrenceNormalizedOuterCanonicalDelta
        P Rside ambient CF : ENNReal) =
      CF * ambientFamilyVolumeDensity
        (selectedOccurrenceOuterFamily P Rside) ambient := by
  unfold selectedOccurrenceNormalizedOuterCanonicalDelta
  rw [ENNReal.coe_toNNReal]
  exact ENNReal.mul_ne_top hCF
    (ambientFamilyVolumeDensity_ne_top
      (selectedOccurrenceOuterFamily P Rside) ambient hambientVolume)

/-- The exact selected-occurrence normalized datum has global-owner
Equation (45) control with the literal canonical `Delta`.  Positive volume
of the normalized unit-scale ambient body forces positive volume of its raw
preimage under the normalization equivalence, so no extra raw-volume premise
is exposed to callers. -/
theorem selectedOccurrenceNormalizedOuter_frostmanThickenedPlankControl_canonicalGlobalDelta
    (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta)
    (labelOuter : Fin 3 -> Int)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (hlabel : ∀ k, k ∈ Rside →
      sideShapeLabel (winnerLongSide P hdelta k) = labelOuter)
    (ambient : ConvexBody Space)
    (ambientComparisonConstant : NNReal)
    (ambient_is_unit_scale : IsPlank ambientComparisonConstant 1 1
      (affineImageConvexBody
        (selectedOccurrenceNormalizedOuterAffineEquiv labelOuter) ambient))
    {CF : ENNReal}
    (hF : IsFrostmanIn CF
      (selectedOccurrenceOuterFamily P Rside) ambient)
    (hCF : CF ≠ ∞) :
    FrostmanThickenedPlankControl
      (selectedOccurrenceNormalizedOuterDatum P Y hdelta labelOuter Rside
        hlabel ambient ambientComparisonConstant ambient_is_unit_scale
        hF.family_subset)
      (uniqueOwnerLocalDeltaThickM 576
        (selectedOccurrenceNormalizedOuterCanonicalDelta
          P Rside ambient CF)
        (bucketShortA labelOuter) (bucketShortB labelOuter)) := by
  let A := ambientFamilyVolumeDensity
    (selectedOccurrenceOuterFamily P Rside) ambient
  have hnormalizedVolume :
      volume (affineImageConvexBody
        (selectedOccurrenceNormalizedOuterAffineEquiv labelOuter) ambient :
          Set Space) ≠ 0 :=
    ne_of_gt ambient_is_unit_scale.volume_pos
  have hambientVolume : volume (ambient : Set Space) ≠ 0 := by
    intro hzero
    apply hnormalizedVolume
    rw [volume_affineImageConvexBody, hzero, mul_zero]
  have hambientTop : volume (ambient : Set Space) ≠ ∞ :=
    ambient.isCompact.measure_lt_top.ne
  have hbaseEq :
      containedMass (selectedOccurrenceOuterFamily P Rside) ambient =
        A * volume (ambient : Set Space) := by
    exact containedMass_eq_ambientFamilyVolumeDensity_mul
      (selectedOccurrenceOuterFamily P Rside) ambient hF.family_subset
      hambientVolume hambientTop
  have hDeltaEq :
      (selectedOccurrenceNormalizedOuterCanonicalDelta
          P Rside ambient CF : ENNReal) = CF * A := by
    dsimp only [A]
    exact selectedOccurrenceNormalizedOuterCanonicalDelta_coe
      P Rside ambient CF hCF hambientVolume
  exact
    selectedOccurrenceNormalizedOuter_frostmanThickenedPlankControl_of_globalAmbient
      P Y hdelta labelOuter Rside hlabel ambient ambientComparisonConstant
      ambient_is_unit_scale hF hbaseEq.le (le_of_eq hDeltaEq.symm)

#print axioms selectedOccurrenceNormalizedOuterCanonicalDelta
#print axioms selectedOccurrenceNormalizedOuterCanonicalDelta_coe
#print axioms
  selectedOccurrenceNormalizedOuter_frostmanThickenedPlankControl_canonicalGlobalDelta

end

end Family8SelectedOccurrenceNormalizedCanonicalGlobalDeltaEq45ControlV1
