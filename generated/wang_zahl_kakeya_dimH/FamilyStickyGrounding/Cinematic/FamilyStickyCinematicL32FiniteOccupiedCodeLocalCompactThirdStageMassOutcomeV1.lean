import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageMassTopV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageMassOutcomeV1

open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageAtScalesV1
open FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageMassTopV1
open FamilyStickyCinematicL32FiniteNestedValueFibresExternalPivotThirdStageV1
open FamilyStickyCinematicL32FiniteNestedValueFibresExternalPivotCurvatureThirdStageV1
open FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageV1
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerTwoCenterV1
open FamilyStickyCinematicL32Lemma315ExternalContainerCurvatureRatioNumericsV1
open FamilyStickyCinematicL32Lemma316AutomaticCompactC2GreedySelectionTwoCenterV1
open FamilyStickyCinematicL32Lemma316CompactC2GreedySelectionV1

noncomputable section

universe u v

/-!
# Callback-free occupied-code third-stage mass outcome

This is the last package-free seam before actual grid geometry.  It makes
both finite choices (one local two-stage outcome for every occupied code,
then one global third-stage outcome) and simultaneously transports an
arbitrary source mass through both packing losses.

The source mass is charged to the raw code fibres only once.  Code tags are
retained through the third stage, and no disjointness of transformed endpoint
tubes across codes is asserted.
-/

/-- The exact local packing factor used by every occupied-code outcome. -/
def finiteOccupiedCodeLocalPacking
    (comparisonLambda curvatureRatio : Real) : ENNReal :=
  pyzClosedNeighbourBound
    (pyzLemma312TwoScalePackingLambda comparisonLambda curvatureRatio)

/-- The exact cross-code packing factor used by the third-stage outcome. -/
def finiteOccupiedCodeThirdPacking
    (codeBound : ENNReal) (comparisonLambda curvatureRatio externalRatio : Real) :
    ENNReal :=
  codeBound *
    pyzExternalContainerCurvatureClosedNeighbourCap
      (pyzLemma312TwoScalePackingLambda comparisonLambda curvatureRatio)
      externalRatio

/-- Automatic local choices and the automatic cross-code weighted greedy
selection, together with their honest mass estimate.  The cap is required
for every local selected pivot, which is exactly the interface supplied by
an owner-container mass theorem and is independent of the later finite
choice of `Q`. -/
theorem exists_finiteOccupiedCodeLocalCompactThirdStageOutcome_and_mass_le
    {code : Type v} {item : Type u}
    [Fintype code] [DecidableEq code] [DecidableEq item]
    (rawAt : code -> Finset item)
    (rectangleAt : item -> C2GraphRectangle)
    (domain : Set Real)
    (localCenterAt : code -> C2GraphRectangle)
    (globalCenter : C2GraphRectangle)
    {delta localScale referenceScale comparisonLambda curvatureRatio
      centerGap externalRatio : Real}
    (codeBound : ENNReal) (weightAt : code -> item -> ENNReal)
    (G : FiniteOccupiedCodeLocalCompactCurvatureData rawAt rectangleAt
      domain localCenterAt globalCenter delta localScale referenceScale
        comparisonLambda curvatureRatio centerGap externalRatio codeBound)
    (sourceMass cap : ENNReal)
    (hpartition : sourceMass <=
      ∑ k ∈ (Finset.univ : Finset code), ∑ a ∈ rawAt k, weightAt k a)
    (hcap : forall k, forall a,
      a ∈ finiteOccupiedCodeLocalCompactSelectedAt rawAt rectangleAt domain
        localCenterAt globalCenter codeBound weightAt G k ->
      finiteOccupiedCodeLocalCompactClusterWeightAt rawAt rectangleAt domain
        localCenterAt globalCenter codeBound weightAt G k a <= cap) :
    Exists fun Q : CompactC2AtScalesThirdStageOutcome
      (codeSelectedCandidates (Finset.univ : Finset code)
        (finiteOccupiedCodeLocalCompactSelectedAt rawAt rectangleAt domain
          localCenterAt globalCenter codeBound weightAt G))
      (codeSelectedRectangleAt rectangleAt) domain globalCenter delta
        localScale referenceScale comparisonLambda
      (codeSelectedCandidateWeight
        (finiteOccupiedCodeLocalCompactClusterWeightAt rawAt rectangleAt
          domain localCenterAt globalCenter codeBound weightAt G))
      (finiteOccupiedCodeThirdPacking codeBound comparisonLambda
        curvatureRatio externalRatio) =>
      sourceMass <=
        finiteOccupiedCodeLocalPacking comparisonLambda curvatureRatio *
          finiteOccupiedCodeThirdPacking codeBound comparisonLambda
            curvatureRatio externalRatio *
          (Q.selected.card : ENNReal) * cap := by
  let selectedAt := finiteOccupiedCodeLocalCompactSelectedAt rawAt
    rectangleAt domain localCenterAt globalCenter codeBound weightAt G
  let clusterWeightAt := finiteOccupiedCodeLocalCompactClusterWeightAt rawAt
    rectangleAt domain localCenterAt globalCenter codeBound weightAt G
  let localPacking := finiteOccupiedCodeLocalPacking comparisonLambda
    curvatureRatio
  let thirdPacking := finiteOccupiedCodeThirdPacking codeBound
    comparisonLambda curvatureRatio externalRatio
  obtain ⟨Q⟩ := exists_finiteOccupiedCodeLocalCompactThirdStageOutcome
    rawAt rectangleAt domain localCenterAt globalCenter codeBound weightAt G
  have hlocalEach : forall k, k ∈ (Finset.univ : Finset code) ->
      (∑ a ∈ rawAt k, weightAt k a) <=
        localPacking * ∑ a ∈ selectedAt k, clusterWeightAt k a := by
    intro k _hk
    simpa only [localPacking, finiteOccupiedCodeLocalPacking, selectedAt,
      clusterWeightAt] using
      finiteOccupiedCodeLocalCompact_rawMass_le_selectedClusterMass rawAt
        rectangleAt domain localCenterAt globalCenter codeBound weightAt G k
  have hlocal : sourceMass <= localPacking *
      codeSelectedCandidateMass (Finset.univ : Finset code) selectedAt
        clusterWeightAt := by
    calc
      sourceMass <=
          ∑ k ∈ (Finset.univ : Finset code), ∑ a ∈ rawAt k, weightAt k a :=
        hpartition
      _ <= ∑ k ∈ (Finset.univ : Finset code),
          localPacking * ∑ a ∈ selectedAt k, clusterWeightAt k a := by
        exact Finset.sum_le_sum fun k hk => hlocalEach k hk
      _ = localPacking *
          ∑ k ∈ (Finset.univ : Finset code),
            ∑ a ∈ selectedAt k, clusterWeightAt k a := by
        rw [Finset.mul_sum]
      _ = localPacking *
          codeSelectedCandidateMass (Finset.univ : Finset code) selectedAt
            clusterWeightAt := by
        rw [codeSelectedCandidateMass_eq_sum]
  have hcapQ : forall q, q ∈ Q.selected ->
      codeSelectedCandidateWeight clusterWeightAt q <= cap := by
    intro q hq
    have hmem := mem_codeSelectedCandidates_iff
      (Finset.univ : Finset code) selectedAt q
    have hvertex : q ∈ codeSelectedCandidates
        (Finset.univ : Finset code) selectedAt := Q.selected_subset hq
    have hlocalSelected : q.2 ∈ selectedAt q.1 := (hmem.mp hvertex).2
    simpa only [clusterWeightAt, selectedAt,
      codeSelectedCandidateWeight] using hcap q.1 q.2 hlocalSelected
  refine ⟨Q, ?_⟩
  simpa only [localPacking, thirdPacking] using
    mass_le_local_mul_third_mul_selectedCard_mul_cap sourceMass
      (codeSelectedCandidates (Finset.univ : Finset code) selectedAt)
      (compactC2ComparableAtScales (codeSelectedRectangleAt rectangleAt)
        domain globalCenter delta localScale referenceScale comparisonLambda)
      (codeSelectedCandidateWeight clusterWeightAt)
      localPacking thirdPacking cap Q hlocal hcapQ

#print axioms finiteOccupiedCodeLocalPacking
#print axioms finiteOccupiedCodeThirdPacking
#print axioms exists_finiteOccupiedCodeLocalCompactThirdStageOutcome_and_mass_le

end

end FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageMassOutcomeV1
