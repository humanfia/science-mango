import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalSelectedNonemptyV3
import Family8Grounding.Family8SelectedOccurrenceOuterMassPositiveV2
import Mathlib.Tactic

/-!
# Source-mass production of canonical selected nonemptiness

The upper cover is active on every source index.  Thus nonzero source shaded
mass survives the full occurrence factorization and the exact-degree
max-owner conflict selection, yielding a nonempty literal selected fine set.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessCanonicalSelectedNonemptyV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8PaperEq45MaxWitnessCanonicalSelectedFieldsV1
open Family8PaperEq45MaxWitnessCanonicalSelectedFiniteV2
open Family8PaperEq45MaxWitnessCanonicalSelectedNonemptyV3
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8SelectedOccurrenceOuterMassPositiveV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho sigma : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (S : StickyScaleCover fine rho)
  (U : StickyScaleCover (S.coarse.restrictTo S.activeCoarse) sigma)
  (P : GreedyDensityPartition S.activeCoarseFamily
    (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
    (hullContainer S.activeCoarseFamily) Finset.univ)
  (Y : Shading S.activeCoarseFamily)

theorem canonicalSelectedFine_nonempty_of_sourceShadingMass_ne_zero
    (hsource : Y.shadingMass ≠ 0) :
    (selectedOccurrenceFineIndices (actualUpperPartition S U P)
      (canonicalSelectedOccurrences S U P Y)).Nonempty := by
  have houter : (selectedOccurrenceOuterShading
      (actualUpperPartition S U P) Y Finset.univ).shadingMass ≠ 0 :=
    selectedOccurrenceOuterShading_univ_mass_ne_zero_of_active_eq_univ
      (actualUpperPartition S U P) Y
      (actualUpperCover_activeFine_eq_univ S U) hsource
  exact canonicalSelectedFine_nonempty_of_outerShadingMass_ne_zero
    S U P Y houter

#print axioms canonicalSelectedFine_nonempty_of_sourceShadingMass_ne_zero

end
end Family8PaperEq45MaxWitnessCanonicalSelectedNonemptyV5
