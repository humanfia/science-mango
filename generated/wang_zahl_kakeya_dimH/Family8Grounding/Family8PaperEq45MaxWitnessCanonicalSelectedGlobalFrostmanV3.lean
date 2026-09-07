import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalSelectedFieldsV1
import Family8Grounding.Family8SelectedOccurrenceUniformTubeGlobalFrostmanV1
import Mathlib.Tactic

/-!
# Global Frostman control on the actual canonical selected occurrence source

The exact-degree canonical selection is a literal occurrence restriction of
the upper active-parent family.  Uniform tube volume bounds therefore turn
global normalized Frostman control into selected-source control as soon as
that literal selected fine set is nonempty, with loss `16 * N`.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessCanonicalSelectedGlobalFrostmanV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8PaperEq45MaxWitnessCanonicalSelectedFieldsV1
open Family8PaperEq45MaxWitnessCanonicalSelectedFiniteV2
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8SelectedOccurrenceUniformTubeGlobalFrostmanV1
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

theorem canonicalSelected_source_frostman_of_nonempty
    (sourceAmbient : ConvexBody Space) {C : ENNReal}
    (hglobal : IsFrostmanOn C S.activeCoarseFamily Finset.univ sourceAmbient)
    (hselected : (selectedOccurrenceFineIndices
      (actualUpperPartition S U P) (canonicalSelectedOccurrences S U P Y)).Nonempty)
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹) :
    IsFrostmanOn
      (C * (16 * (Fintype.card (ActiveParentIndex S) : ENNReal)))
      S.activeCoarseFamily
      (selectedOccurrenceFineIndices (actualUpperPartition S U P)
        (canonicalSelectedOccurrences S U P Y)) sourceAmbient := by
  have hglobal' : IsFrostmanOn C S.activeCoarseFamily U.activeFine
      sourceAmbient := by
    simpa only [actualUpperCover_activeFine_eq_univ S U] using hglobal
  have hsource := selectedOccurrence_source_frostman_of_selectedFine_nonempty
    (fine := S.coarse.restrictTo S.activeCoarse)
    (P := actualUpperPartition S U P)
    (R := canonicalSelectedOccurrences S U P Y)
    sourceAmbient hglobal' hselected hrhoHalf
  have hsource' : IsFrostmanOn
      (C * (16 * (U.activeFine.card : ENNReal)))
      S.activeCoarseFamily
      (selectedOccurrenceFineIndices (actualUpperPartition S U P)
        (canonicalSelectedOccurrences S U P Y)) sourceAmbient := by
    refine ⟨?_, ?_⟩
    · intro i hi
      exact hsource.1 i hi
    · intro K hK
      exact hsource.2 K hK
  simpa only [actualUpperCover_activeFine_eq_univ S U,
    Finset.card_univ, Fintype.card_coe] using hsource'

#print axioms canonicalSelected_source_frostman_of_nonempty

end
end Family8PaperEq45MaxWitnessCanonicalSelectedGlobalFrostmanV3
