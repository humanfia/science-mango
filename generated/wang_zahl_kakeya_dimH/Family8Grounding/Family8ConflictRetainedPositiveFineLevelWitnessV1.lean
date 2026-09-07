import Family8Grounding.Family8ExactAssemblyActualAverageBridgeV1
import Family8Grounding.Family8SelectedOccurrenceMaxOwnerHullAggregateV2
import Family8Grounding.Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
import Mathlib.Tactic

/-!
# A positive exact conflict-retained occurrence gives a same-occurrence fine witness

The doubled-parent conflict selector retains a literal finite set of greedy
occurrences.  If its max-owner hull shading has positive mass, one occurrence
in that exact set has positive max-owner carrier.  That carrier is contained
first in the induced carrier of the same occurrence and then in the source
fine-level shading of an exact assembly over `some q`.

No canonical `R0 = univ` specialization and no reselection of the occurrence
is used.  The core theorem asks only for positivity on the already retained
set; the second theorem derives this premise from positivity before conflict
selection using the selector's actual weighted-mass inequality.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ConflictRetainedPositiveFineLevelWitnessV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8SelectedOccurrenceMaxOwnerHullAggregateV2
open Family8SelectedOccurrenceMaxOwnerHullQualityV3
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (C : StickyScaleCover fine rho)
  (P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine)
  (Y : Shading fine.bodyFamily)
  {assemblyLoss : Nat}
  (A : FactoringMultiplicityAssembly.ExactAssembly
    (convexFactorization fine.bodyFamily P) Y assemblyLoss)
  {R0 : Finset (Fin (blocks fine.bodyFamily P).length)}
  {conflictLoss : ENNReal}
  (W : DoubledParentConflictWeightedSelection C
    (occurrenceMaxOwnerMass C P A.refinement.shading R0) conflictLoss)

/-- Positivity on the exact conflict-retained occurrence set selects one
literal occurrence `q` in that set whose honest source fine-level shading at
`some q` has positive shaded-union volume. -/
theorem exists_conflictRetainedPositiveFineLevelWitness
    (hretained : 0 <
      (selectedOccurrenceMaxOwnerHullShading C P A.refinement.shading
        (occurrencesMaxOwnedBy C P A.refinement.shading R0 W.selected)).shadingMass) :
    ∃ q ∈ occurrencesMaxOwnedBy C P A.refinement.shading R0 W.selected,
      0 < volume (sourceFineLevelShading A (some q)).shadedUnion := by
  rw [selectedOccurrenceMaxOwnerHullShading_mass_eq_sum] at hretained
  rw [Finset.sum_pos_iff] at hretained
  obtain ⟨q, hq, hqPositive⟩ := hretained
  refine ⟨q, hq, ?_⟩
  have houter : occurrenceMaxOwnerCarrier C P A.refinement.shading q ⊆
      ((convexFactorization fine.bodyFamily P).inducedShading
        A.refinement.shading).carrier (some q) :=
    occurrenceMaxOwnerCarrier_subset_outerCarrier
      C P A.refinement.shading q
  have hsource :
      ((convexFactorization fine.bodyFamily P).inducedShading
        A.refinement.shading).carrier (some q) ⊆
        (sourceFineLevelShading A (some q)).shadedUnion := by
    intro x hx
    obtain ⟨_hqCoarse, i, hiFiber, hxi⟩ :=
      ((convexFactorization fine.bodyFamily P).mem_inducedShading_carrier_iff
        A.refinement.shading (some q) x).mp hx
    have hparent :
        (convexFactorization fine.bodyFamily P).index.parent i = some q :=
      ((convexFactorization fine.bodyFamily P).index.mem_fiber i (some q)).mp
        hiFiber |>.2
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    simpa only [hparent] using
      (refinement_carrier_subset_sourceFineLevelShading A i hxi)
  exact hqPositive.trans_le (measure_mono (houter.trans hsource))

/-- Positive max-owner mass before conflict extraction remains positive after
the actual weighted selector, so the same exact retained set supplies the
fine-level witness above. -/
theorem exists_conflictRetainedPositiveFineLevelWitness_of_fullMass
    (hfull : 0 <
      (selectedOccurrenceMaxOwnerHullShading
        C P A.refinement.shading R0).shadingMass) :
    ∃ q ∈ occurrencesMaxOwnedBy C P A.refinement.shading R0 W.selected,
      0 < volume (sourceFineLevelShading A (some q)).shadedUnion := by
  have hretention := selectedMaxOwner_refinedShadedMass_retention
    C P A.refinement.shading R0 conflictLoss W
  have hproduct : 0 < conflictLoss *
      (selectedOccurrenceMaxOwnerHullShading C P A.refinement.shading
        (occurrencesMaxOwnedBy C P A.refinement.shading R0 W.selected)).shadingMass :=
    hfull.trans_le hretention
  have hretained : 0 <
      (selectedOccurrenceMaxOwnerHullShading C P A.refinement.shading
        (occurrencesMaxOwnedBy C P A.refinement.shading R0 W.selected)).shadingMass :=
    (ENNReal.mul_pos_iff.mp hproduct).2
  exact exists_conflictRetainedPositiveFineLevelWitness
    C P Y A W hretained

#print axioms exists_conflictRetainedPositiveFineLevelWitness
#print axioms exists_conflictRetainedPositiveFineLevelWitness_of_fullMass

end

end Family8ConflictRetainedPositiveFineLevelWitnessV1
