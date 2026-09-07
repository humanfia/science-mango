import Family8Grounding.Family8SelectedOccurrenceActiveParentOwnerV11
import Family8Grounding.Family8SelectedOccurrenceEq45CoreV2
import Mathlib.Tactic

/-!
# Actual-owner producer for the Equation (45) V3 bundle

The exact owner-selected occurrences are packaged into the paper-facing V3
input.  The core supplies only non-owner structure; unique ownership and the
literal owner-fibre `Delta_max` bound are derived from V9 and V11.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceActiveParentOwnerV15

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8PaperEq45SelectedOccurrenceBundleV3
open Family8SelectedOccurrenceActiveParentOwnerV5
open Family8SelectedOccurrenceActiveParentOwnerV7
open Family8SelectedOccurrenceActiveParentOwnerV9
open Family8SelectedOccurrenceActiveParentOwnerV11
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceEq45CoreV2
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

/-- Assemble the V3 paper input on the actual-parent weighted selection.
No thick-count or unique-owner conclusion occurs among the arguments. -/
def paperEq45InputV3_of_actualOwner
    (hpure : ParentPure C P)
    (Y : Shading fine.bodyFamily)
    (R0 : Finset (Fin (blocks fine.bodyFamily P).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMassByActiveParent C P Y R0) loss)
    (K : PaperEq45SelectedOccurrenceCore P Y
      (occurrencesOwnedBy C P R0 W.selected) a b)
    (Delta : NNReal)
    (hinside : AdmissibleThickeningInsideOwner C
      (occurrencesOwnedBy C P R0 W.selected) K.datum
      (selectedOccurrenceActiveParent C
        (occurrencesOwnedBy C P R0 W.selected)))
    (hlocal : OwnerFiberIsKatzTao (Delta := Delta) C K.datum
      (selectedOccurrenceActiveParent C
        (occurrencesOwnedBy C P R0 W.selected))) :
    PaperEq45SelectedOccurrenceInputV3 P Y
      (occurrencesOwnedBy C P R0 W.selected) a b (Fin C.coarseCard) where
  comparisonConstant := K.comparisonConstant
  all_isPlank := K.all_isPlank
  ambient := K.ambient
  ambientComparisonConstant := K.ambientComparisonConstant
  ambient_is_unit_scale := K.ambient_is_unit_scale
  contained_in_ambient := K.contained_in_ambient
  fiberCard_dyadicUniform := K.fiberCard_dyadicUniform
  sourceCF := K.sourceCF
  lowerDensity := K.lowerDensity
  upperDensity := K.upperDensity
  lowerDensity_ne_zero := K.lowerDensity_ne_zero
  lowerDensity_ne_top := K.lowerDensity_ne_top
  source_fine_frostman := K.source_fine_frostman
  blockMass_lower := K.blockMass_lower
  blockMass_upper := K.blockMass_upper
  owner := selectedOccurrenceActiveParent C
    (occurrencesOwnedBy C P R0 W.selected)
  uniqueOwner := by
    exact thickenedPlankUniqueOwner_ownedOccurrences C hpure Y R0 loss W
      K.datum rfl hinside
  Delta := Delta
  ownerFiberDeltaMax_le := by
    exact ownerFiberDeltaMax_le_of_ownerFiberIsKatzTao
      (Delta := Delta) C K.datum
      (selectedOccurrenceActiveParent C
        (occurrencesOwnedBy C P R0 W.selected)) hlocal

#print axioms paperEq45InputV3_of_actualOwner

end


end Family8SelectedOccurrenceActiveParentOwnerV15
