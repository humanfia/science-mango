import Family8Grounding.Family8SelectedOccurrenceMaxOwnerHullFrostmanProducerV3
import Family8Grounding.Family8PaperEq45MaxOwnerRefinedBundleV2
import Family8Grounding.Family8AmbientFamilyVolumeDensityV2
import Mathlib.Tactic

/-!
# Constructing the max-owner Equation (45) input from source data

This adapter removes the two conclusion-valued analytic fields from the
paper-facing max-owner input.  Refined Frostman is produced by the actual
max-witness/body-cover construction, and ambient density is the literal
indexed family-volume quotient.  The only remaining geometric family field
is the genuine common `IsPlank` certificate.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxOwnerRefinedInputProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8AmbientFamilyVolumeDensityV2
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8PaperEq45MaxOwnerRefinedBundleV2
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerHullAggregateV2
open Family8SelectedOccurrenceMaxOwnerHullFrostmanProducerV3
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho a b : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (C : StickyScaleCover fine rho)
  {P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine}

/-- The exact Frostman constant produced from the selected source fine
certificate and the witness-to-hull cover. -/
def maxOwnerRefinedFrostmanConstant
    (CF : ENNReal) (M : Nat) (delta a b : NNReal) : ENNReal :=
  maxOwnerHullWitnessCoverLoss delta a b * (CF * (16 * (M : ENNReal)))

/-- Build the paper-facing max-owner input without accepting either a
refined-Frostman theorem or an ambient-mass upper bound. -/
noncomputable def paperEq45MaxOwnerRefinedInput_of_sourceFine
    (Y : Shading fine.bodyFamily)
    (R0 : Finset (Fin (blocks fine.bodyFamily P).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMaxOwnerMass C P Y R0) loss)
    (M : Nat)
    (hcard : ∀ k ∈ R0, (blockAt fine.bodyFamily P k).fiber.card ≤ M)
    (hrho : 0 < rho) (hb : b ≤ rho)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (comparisonConstant : NNReal)
    (all_isPlank : ∀ q, IsPlank comparisonConstant a b
      (selectedOccurrenceMaxOwnerHullFamily C P Y
        (occurrencesMaxOwnedBy C P Y R0 W.selected) q))
    (ambient : ConvexBody Space) (ambientComparisonConstant : NNReal)
    (ambient_is_unit_scale : IsPlank ambientComparisonConstant 1 1 ambient)
    (contained_in_ambient : ∀ q,
      (selectedOccurrenceMaxOwnerHullFamily C P Y
        (occurrencesMaxOwnedBy C P Y R0 W.selected) q : Set Space) ⊆
        (ambient : Set Space))
    (CF : ENNReal)
    (source_frostman : IsFrostmanOn CF fine.bodyFamily
      (selectedOccurrenceFineIndices P
        (occurrencesMaxOwnedBy C P Y R0 W.selected)) ambient)
    (Delta : NNReal)
    (hDelta : maxOwnerRefinedFrostmanConstant CF M delta a b *
      ambientFamilyVolumeDensity
        (selectedOccurrenceMaxOwnerHullFamily C P Y
          (occurrencesMaxOwnedBy C P Y R0 W.selected)) ambient ≤
        (Delta : ENNReal)) :
    PaperEq45MaxOwnerRefinedInput C Y R0 loss W a b := by
  let R := occurrencesMaxOwnedBy C P Y R0 W.selected
  let F := selectedOccurrenceMaxOwnerHullFamily C P Y R
  have hcardR : ∀ k ∈ R,
      (blockAt fine.bodyFamily P k).fiber.card ≤ M := by
    intro k hk
    exact hcard k ((mem_occurrencesMaxOwnedBy C P Y R0 W.selected k).mp hk).1
  have hFrostman : IsFrostmanIn
      (maxOwnerRefinedFrostmanConstant CF M delta a b) F ambient := by
    exact selectedOccurrenceMaxOwnerHull_isFrostmanIn C Y R M hcardR ambient
      source_frostman hdelta hdeltaHalf comparisonConstant all_isPlank
      contained_in_ambient
  have hvolume0 : volume (ambient : Set Space) ≠ 0 :=
    ne_of_gt ambient_is_unit_scale.volume_pos
  have hvolumeTop : volume (ambient : Set Space) ≠ ∞ :=
    ambient.isCompact.measure_lt_top.ne
  have hmass : containedMass F ambient =
      ambientFamilyVolumeDensity F ambient * volume (ambient : Set Space) :=
    containedMass_eq_ambientFamilyVolumeDensity_mul F ambient
      contained_in_ambient hvolume0 hvolumeTop
  exact
    { rho_pos := hrho
      b_le_rho := hb
      fibreCardCap := M
      fibreCard_le := hcard
      comparisonConstant := comparisonConstant
      all_isPlank := all_isPlank
      ambient := ambient
      ambientComparisonConstant := ambientComparisonConstant
      ambient_is_unit_scale := ambient_is_unit_scale
      contained_in_ambient := contained_in_ambient
      frostmanConstant := maxOwnerRefinedFrostmanConstant CF M delta a b
      refined_frostman := hFrostman
      ambientDensity := ambientFamilyVolumeDensity F ambient
      ambient_mass_upper := hmass.le
      Delta := Delta
      Delta_dominates := hDelta }

#print axioms maxOwnerRefinedFrostmanConstant
#print axioms paperEq45MaxOwnerRefinedInput_of_sourceFine

end
end Family8PaperEq45MaxOwnerRefinedInputProducerV1
