import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeArbitrarySeparatedPairE2FirstHitOwnerCapProducerV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

open Set MeasureTheory
open scoped BigOperators ENNReal Interval

namespace FamilyStickyCinematicL32Prop41ActualGPrimeArbitraryPairE2FirstHitOwnerFubiniV3

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualGPrimeArbitrarySeparatedPairE2FirstHitOwnerCapProducerV2
open FamilyStickyCinematicL32Prop41ActualGPrimeArbitrarySeparatedPairWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedSelectedCountingNumericsV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CanonicalSeparatedBallPairV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairENNRealSelectionV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1

noncomputable section

universe u v

/-!
# Fubini aggregation of the actual per-pair owner envelopes

For every separated centre pair with a nonempty common-label fibre, the
arbitrary-pair producer supplies a real weighted C-grid package and its
fixed-C owner envelope.  Pairs with an empty common-label fibre contribute
exactly zero.  Finite choice therefore bounds the entire centre-first Fubini
mass by a sum of actual owner envelopes.

This deliberately stops before estimating that last sum.  A naive uniform
bound would multiply by the number of centre pairs; the missing paper input
is the sharper sharing/packing of owners across distinct pairs.
-/

/-- The entire actual centre-pair first-hit mass is bounded by a family of
realized package-local owner envelopes.  Empty common-label fibres are
assigned zero rather than an artificial package. -/
theorem exists_actualGPrimeCenterPairOwnerEnvelopeSum
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (E : Set (Real × Real))
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (centerTube : Tube radius) (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal globalDelta : Real)
    (facts : ActualCenteredHalfY1ActiveGeometryFacts fine physical E
      Y1.activeAtPoint tubeAt f f1 f2 outerA outerB hOuter hf hf1
      tGlobal globalDelta)
    (pointSource : ActualCenteredHalfPointRectangleSource E centerTube tubeAt
      f outerA outerB tGlobal)
    (hpointE : forall r, r ∈ fineLabels -> pointAt r ∈ E)
    (sharp : ActualY1SharpFineScaleNumerics
      (radius : Real) globalDelta tGlobal (outerB - outerA))
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hft : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc outerA outerB))
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (hD : D = y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hf hf1 (radius : Real)
      (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
      globalDelta tGlobal)
    (e2Label : Int) (keep : iota -> fineLabel -> Prop)
    (ballRadius : Real)
    (hsymm : forall x y, N.distance x y = N.distance y x)
    (htriangle : forall x center y,
      N.distance x y <= N.distance x center + N.distance center y)
    (hballRadiusLower : N.delta <= ballRadius)
    (hballRadiusUpper : ballRadius <= N.ceiling)
    (hdistance : forall i j, N.distance i j =
      projectedTubePairCoefficientDistance
        (D.fine.tubes i) (D.fine.tubes j))
    (hsmall : ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness
      (radius : Real) globalDelta tGlobal (4 * ballRadius))
    (hcount : ActualY1PaperFineCNormalizedSelectedCountingSmallness
      (radius : Real) globalDelta tGlobal (4 * ballRadius))
    (hDfine : D.fine = fine)
    (hfamily : N.family =
      actualGlobalNormIndexFamily fine physical tGlobal centerTube) :
    exists ownerEnvelopeAt : iota × iota -> ENNReal,
      (forall pair, pair ∈ richSeparatedCenterPairs N.family
          (canonicalTenRadiusSeparated N ballRadius) (fun _ _ => True) ->
        actualGPrimeWeightedCommonFineCenterMass N D keep
            (actualGPrimeE2FirstHitLabelWeight D e2Label)
            pair.1 pair.2 <= ownerEnvelopeAt pair) ∧
      (forall pair, pair ∈ richSeparatedCenterPairs N.family
          (canonicalTenRadiusSeparated N ballRadius) (fun _ _ => True) ->
        (actualGPrimeCommonFineCenterLabels
          N D keep pair.1 pair.2).Nonempty ->
        exists r, r ∈ actualGPrimeCommonFineCenterLabels
            N D keep pair.1 pair.2 ∧
          exists O : ActualGPrimeArbitrarySeparatedPairWeightedUniformOutcome
            fine N D keep pair ballRadius
              (actualGPrimeE2FirstHitLabelWeight D e2Label)
              f outerA outerB globalDelta tGlobal,
            ownerEnvelopeAt pair =
              actualGPrimeArbitraryPairOwnerEnvelope fine N D e2Label keep
                pair.1 pair.2 ballRadius O.omega f outerA outerB globalDelta
                  tGlobal O.package) ∧
      (forall pair, pair ∈ richSeparatedCenterPairs N.family
          (canonicalTenRadiusSeparated N ballRadius) (fun _ _ => True) ->
        ¬(actualGPrimeCommonFineCenterLabels
          N D keep pair.1 pair.2).Nonempty ->
        ownerEnvelopeAt pair = 0) ∧
      actualGPrimeWeightedFineSeparatedCenterPairMass N D keep ballRadius
          (actualGPrimeE2FirstHitLabelWeight D e2Label) <=
        ∑ pair ∈ richSeparatedCenterPairs N.family
          (canonicalTenRadiusSeparated N ballRadius) (fun _ _ => True),
            ownerEnvelopeAt pair := by
  classical
  let pairs := richSeparatedCenterPairs N.family
    (canonicalTenRadiusSeparated N ballRadius) (fun _ _ => True)
  have hex : forall pair : iota × iota, exists envelope : ENNReal,
      (pair ∈ pairs ->
        actualGPrimeWeightedCommonFineCenterMass N D keep
            (actualGPrimeE2FirstHitLabelWeight D e2Label)
            pair.1 pair.2 <= envelope) ∧
      (pair ∈ pairs ->
        (actualGPrimeCommonFineCenterLabels
          N D keep pair.1 pair.2).Nonempty ->
        exists r, r ∈ actualGPrimeCommonFineCenterLabels
            N D keep pair.1 pair.2 ∧
          exists O : ActualGPrimeArbitrarySeparatedPairWeightedUniformOutcome
            fine N D keep pair ballRadius
              (actualGPrimeE2FirstHitLabelWeight D e2Label)
              f outerA outerB globalDelta tGlobal,
            envelope =
              actualGPrimeArbitraryPairOwnerEnvelope fine N D e2Label keep
                pair.1 pair.2 ballRadius O.omega f outerA outerB globalDelta
                  tGlobal O.package) ∧
      (pair ∈ pairs ->
        ¬(actualGPrimeCommonFineCenterLabels
          N D keep pair.1 pair.2).Nonempty ->
        envelope = 0) := by
    intro pair
    by_cases hp : pair ∈ pairs
    · by_cases hcommon : (actualGPrimeCommonFineCenterLabels
          N D keep pair.1 pair.2).Nonempty
      · obtain ⟨r, hr⟩ := hcommon
        have hrich := (mem_richSeparatedCenterPairs_iff
          (left := pair.1) (right := pair.2)).mp hp
        have hrData := (mem_actualGPrimeCommonFineCenterLabels_iff
          N D keep pair.1 pair.2 r).mp hr
        have hpairAt : pair ∈
            actualGPrimeFineSeparatedPairsAt N D keep ballRadius r := by
          rw [actualGPrimeFineSeparatedPairsAt_eq_family_filter]
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_product.mpr ⟨hrich.1, hrich.2.1⟩,
            hrich.2.2.1, hrData.2.1, hrData.2.2⟩
        obtain ⟨O, hO⟩ :=
          exists_actualGPrimeArbitrarySeparatedPairWeightedOwnerCap
            fine physical E Y1 fineLabels pointAt centerTube tubeAt f f1 f2
              outerA outerB hOuter hf hf1 tGlobal globalDelta facts
                pointSource hpointE sharp hparameter hft hf1Lower hf1Upper
                  hf2 hf2Continuous N D hD e2Label keep ballRadius r pair
                    hpairAt hsymm htriangle hballRadiusLower hballRadiusUpper
                      hdistance hsmall hcount hDfine hfamily
        refine ⟨actualGPrimeArbitraryPairOwnerEnvelope fine N D e2Label keep
            pair.1 pair.2 ballRadius O.omega f outerA outerB globalDelta
              tGlobal O.package, ?_, ?_, ?_⟩
        · intro _
          exact hO
        · intro _ _
          exact ⟨r, hr, O, rfl⟩
        · intro _ hempty
          exact (hempty ⟨r, hr⟩).elim
      · have hlabels : actualGPrimeCommonFineCenterLabels
            N D keep pair.1 pair.2 = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hcommon
        refine ⟨0, ?_, ?_, ?_⟩
        · intro _
          unfold actualGPrimeWeightedCommonFineCenterMass
          rw [hlabels]
          simp
        · intro _ hnonempty
          exact (hcommon hnonempty).elim
        · intro _ _
          rfl
    · refine ⟨0, ?_, ?_, ?_⟩
      · intro hp'
        exact (hp hp').elim
      · intro hp'
        exact (hp hp').elim
      · intro hp'
        exact (hp hp').elim
  choose ownerEnvelopeAt howner using hex
  refine ⟨ownerEnvelopeAt, ?_, ?_, ?_, ?_⟩
  · intro pair hp
    exact (howner pair).1 hp
  · intro pair hp hcommon
    exact (howner pair).2.1 hp hcommon
  · intro pair hp hempty
    exact (howner pair).2.2 hp hempty
  · unfold actualGPrimeWeightedFineSeparatedCenterPairMass
    unfold richSeparatedPairENNRealWeightTotal
    apply Finset.sum_le_sum
    intro pair hp
    exact (howner pair).1 hp

#print axioms exists_actualGPrimeCenterPairOwnerEnvelopeSum

end

end FamilyStickyCinematicL32Prop41ActualGPrimeArbitraryPairE2FirstHitOwnerFubiniV3
