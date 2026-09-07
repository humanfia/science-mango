import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighHalfSampledLensV3
import FamilyStickyCinematicL32PyzActualCanonicalPayloadLocalEstimateV5
import FamilyStickyCinematicL32PyzActualWeightedPositiveCenterOverlapV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstAllCenterLowHalfMomentV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzActualCanonicalPayloadLocalEstimateV5
open FamilyStickyCinematicL32PyzActualCenteredHalfLocalizedSupportActualCleanV1
open FamilyStickyCinematicL32PyzActualProjectedNormThreeBallIndexedOverlapV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32PyzQuasiProductCarrierStripMeasureV1
open FamilyStickyCinematicL32PyzQuasiProductFrostmanBoundV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u v w

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-- A weighted estimate indexed by any injective subset of actual cover
centres.  Unlike the older all-positive-cell theorem, the source need only
charge the supplied subset from below.  Thus it is the exact finite summation
interface required by the mass-weighted low half. -/
theorem actual_weighted_indexedCenterSubset_overlap
    {X : Type w} [MeasurableSpace X]
    {alpha : Type v} [DecidableEq alpha]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (mu : Measure X)
    (fine : UniformTubeFamily radius iota) (ambient : Finset iota)
    (hradius : 0 < radius)
    (hpair : Set.Pairwise (ambient : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    {globalScale : Real} (hglobalScale : 0 < globalScale)
    (low : Finset alpha) (centerAt : alpha -> Tube radius)
    (hcenterAt_injective : Function.Injective centerAt)
    (hcenterAt : forall a, a ∈ low ->
      centerAt a ∈ finiteMetricCoverCenters
        (activeTubeImage fine ambient)
        projectedTubePairCoefficientDistance globalScale
        (fun U V => projectedTubePairCoefficientDistance_comm U V))
    (cell : alpha -> Set X) (weight commonCost sourceMass : ENNReal)
    (hhalf : sourceMass / 2 <= ∑ a ∈ low, mu (cell a))
    (hlocal : forall a, a ∈ low ->
      weight * mu (cell a) <=
        commonCost *
          ((actualProjectedNormThreeBallIndices fine ambient globalScale
            (centerAt a)).card : ENNReal)) :
    weight * (sourceMass / 2) <=
      commonCost * ((19 ^ 3 * ambient.card : Nat) : ENNReal) := by
  let centers := finiteMetricCoverCenters
    (activeTubeImage fine ambient)
    projectedTubePairCoefficientDistance globalScale
    (fun U V => projectedTubePairCoefficientDistance_comm U V)
  have himage : low.image centerAt ⊆ centers := by
    intro center hcenter
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hcenter
    exact hcenterAt a ha
  have hsumImage :
      ∑ center ∈ low.image centerAt,
          (actualProjectedNormThreeBallIndices fine ambient globalScale
            center).card <=
        ∑ center ∈ centers,
          (actualProjectedNormThreeBallIndices fine ambient globalScale
            center).card := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro center hcenter
      exact himage hcenter
    · intro center _hcenter _hnot
      omega
  have hsumLowEq :
      (∑ a ∈ low,
        (actualProjectedNormThreeBallIndices fine ambient globalScale
          (centerAt a)).card) =
        ∑ center ∈ low.image centerAt,
          (actualProjectedNormThreeBallIndices fine ambient globalScale
            center).card := by
    rw [Finset.sum_image]
    intro a _ha b _hb hab
    exact hcenterAt_injective hab
  have hsumAll :
      ∑ center ∈ centers,
          (actualProjectedNormThreeBallIndices fine ambient globalScale
            center).card <=
        19 ^ 3 * ambient.card := by
    simpa only [centers] using
      sum_actualProjectedNormThreeBallIndices_card_le fine ambient hradius
        hpair hglobalScale
  have hsumCard :
      ∑ a ∈ low,
          (actualProjectedNormThreeBallIndices fine ambient globalScale
            (centerAt a)).card <=
        19 ^ 3 * ambient.card :=
    hsumLowEq.trans_le (hsumImage.trans hsumAll)
  have hsumCardCast :
      ((∑ a ∈ low,
          (actualProjectedNormThreeBallIndices fine ambient globalScale
            (centerAt a)).card : Nat) : ENNReal) <=
        ((19 ^ 3 * ambient.card : Nat) : ENNReal) := by
    exact_mod_cast hsumCard
  calc
    weight * (sourceMass / 2) <=
        weight * (∑ a ∈ low, mu (cell a)) :=
      mul_le_mul_right hhalf weight
    _ = ∑ a ∈ low, weight * mu (cell a) := by
      rw [Finset.mul_sum]
    _ <= ∑ a ∈ low,
        commonCost *
          ((actualProjectedNormThreeBallIndices fine ambient globalScale
            (centerAt a)).card : ENNReal) :=
      Finset.sum_le_sum hlocal
    _ = commonCost *
        ((∑ a ∈ low,
          (actualProjectedNormThreeBallIndices fine ambient globalScale
            (centerAt a)).card : Nat) : ENNReal) := by
      simp only [Nat.cast_sum, Finset.mul_sum]
    _ <= commonCost * ((19 ^ 3 * ambient.card : Nat) : ENNReal) :=
      mul_le_mul_right hsumCardCast commonCost

/-- Fully actual low-half summation.  The local estimate is constructed from
each selected canonical payload and the stored norm-cell geometry; no local
moment conclusion is accepted as a callback.  The injective centre map lets
the three-ball overlap theorem remove the number of low cells. -/
theorem actualLowPayloadHalfMoment_sum
    {alphaIndex : Type v} [DecidableEq alphaIndex]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {E : Set (Real × Real)} {alpha : Real} {C : ENNReal}
    (Q : PyzCarrierQuasiProduct E
      (pyzFrostmanIntervalBound (radius : Real) alpha C))
    (S : WZL3UniformTubeSource radius iota)
    (ambient : Finset iota) (hambient : ambient ⊆ S.source)
    (hunit : forall i, i ∈ ambient ->
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (physicalBase : Set (Real × Real))
    (hphysicalBase : MeasurableSet physicalBase)
    (f : Real -> Real) (hfContinuous : Continuous f)
    (f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (halpha : 0 <= alpha) (halphaOne : alpha <= 1)
    (hfun : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hfun1 : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (globalScale : Real) (hglobalScale : 0 < globalScale)
    (low : Finset alphaIndex) (centerAt : alphaIndex -> Tube radius)
    (hcenterAt_injective : Function.Injective centerAt)
    (hcenterAt : forall a, a ∈ low ->
      centerAt a ∈ finiteMetricCoverCenters
        (activeTubeImage S.family ambient)
        projectedTubePairCoefficientDistance globalScale
        (fun U V => projectedTubePairCoefficientDistance_comm U V))
    (base : alphaIndex -> Set (Real × Real))
    (hbase : forall a, MeasurableSet (base a))
    (hbaseSubset : forall a, a ∈ low -> base a ⊆ E)
    (normExponent tangencyExponent : Real)
    (logCount lower upper multiplicity : Nat)
    (hradius : 0 < radius)
    (hradiusSixteen : (radius : Real) <= 16)
    (hradiusTangency : (radius : Real) <= 36 * globalScale)
    (hnormExponent : 0 <= normExponent)
    (htangencyExponent : 0 <= tangencyExponent)
    (hbaseBand : forall a, a ∈ low ->
      let physical :=
        actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB
      base a ⊆ physical.multiplicityBand lower upper)
    (payloadAt : forall a,
      ActualPositiveCenterCanonicalPayload volume (base a) (hbase a) S.family
        (actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
        f f1 f2 outerA outerB hOuter hf hf1 globalScale (centerAt a)
          tangencyExponent)
    (hpairAmbient : Set.Pairwise (ambient : Set iota) fun i j =>
      EssentiallyDistinct (S.family.tubes i) (S.family.tubes j))
    (hpairAt : forall a, a ∈ low ->
      let physical :=
        actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB
      Set.Pairwise (physical.activeAtPoint (payloadAt a).q : Set iota)
        (fun i j => EssentiallyDistinct (S.family.tubes i) (S.family.tubes j)))
    (hactiveCapAt : forall a, a ∈ low ->
      let physical :=
        actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB
      forall center, center ∈ actualProjectedCriticalFamily S.family
          (physical.activeAtPoint (payloadAt a).q) ->
        (activeNearCoefficientIndices S.family
          (physical.activeAtPoint (payloadAt a).q) center
          (radius : Real)).card <= multiplicity)
    (hfamilyAt : forall a, a ∈ low ->
      let physical :=
        actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB
      (actualProjectedAmbientCriticalFamily S.family physical.ambient
        (physical.activeAtPoint (payloadAt a).q)).Nonempty)
    (hnormBallSubsetAt : forall a (ha : a ∈ low),
      let physical :=
        actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB
      let family := actualProjectedAmbientCriticalFamily S.family
        physical.ambient (physical.activeAtPoint (payloadAt a).q)
      finiteNormCriticalBall family projectedTubePairCoefficientDistance
          (radius : Real) 16 normExponent (hfamilyAt a ha) ⊆
        finiteIncidenceNormLocalizedFamilyValue
          (actualProjectedAmbientCriticalFamily S.family physical.ambient)
          projectedTubePairCoefficientDistance globalScale (centerAt a)
          (physical.activeAtPoint (payloadAt a).q))
    (hnormScaleLowerAt : forall a, a ∈ low ->
      let physical :=
        actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB
      (radius : Real) / 2 <
        actualProjectedAmbientNormScale S.family physical 16 normExponent
          (payloadAt a).q)
    (hlow : forall a, a ∈ low ->
      pyzE2DegreeLower (payloadAt a).finalLabel < 24 * logCount)
    (sourceMass : ENNReal)
    (hhalf : sourceMass / 2 <= ∑ a ∈ low, volume (base a)) :
    actualCanonicalPayloadGlobalWeight lower globalScale normExponent
        tangencyExponent * (sourceMass / 2) <=
      actualCanonicalPayloadCommonCost radius globalScale ambient.card
          multiplicity logCount normExponent tangencyExponent alpha C *
        ((19 ^ 3 * ambient.card : Nat) : ENNReal) := by
  apply actual_weighted_indexedCenterSubset_overlap volume S.family ambient
    hradius hpairAmbient hglobalScale low centerAt hcenterAt_injective
      hcenterAt base
      (actualCanonicalPayloadGlobalWeight lower globalScale normExponent
        tangencyExponent)
      (actualCanonicalPayloadCommonCost radius globalScale ambient.card
        multiplicity logCount normExponent tangencyExponent alpha C)
      sourceMass hhalf
  intro a ha
  exact actualCanonicalPayload_localEstimate Q S ambient hambient hunit
    physicalBase hphysicalBase (base a) (hbase a) (hbaseSubset a ha)
      f hfContinuous f1 f2 outerA outerB hOuter hf hf1 hparameter halpha
        halphaOne hfun hfun1 globalScale (centerAt a) normExponent
          tangencyExponent logCount lower upper multiplicity hradius
            hradiusSixteen hradiusTangency hnormExponent htangencyExponent
              (hbaseBand a ha) (payloadAt a) (hpairAt a ha)
                (hactiveCapAt a ha) (hfamilyAt a ha)
                  (hnormBallSubsetAt a ha) (hnormScaleLowerAt a ha)
                    (hlow a ha)

#print axioms actual_weighted_indexedCenterSubset_overlap
#print axioms actualLowPayloadHalfMoment_sum

end
end FamilyStickyCinematicL32PyzActualNormFirstAllCenterLowHalfMomentV4
