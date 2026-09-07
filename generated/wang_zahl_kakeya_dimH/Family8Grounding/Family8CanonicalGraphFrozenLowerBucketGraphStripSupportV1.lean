import Family8Grounding.Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
import Family8Grounding.Family8ProjectedTubeImageGraphStripSupportV1
import Family8Grounding.Family8ShadingAwareProjectedPhysicalImageSupportV1
import Family8Grounding.Family8ShadingAwareProjectedPhysicalLowerBucketV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CenteredFractionIntervalsV1
import Mathlib.Tactic

/-!
# Same-graph lower-bucket support in the honest three-radius strip

For indices in the literal selected graph, the graph certificate already
stores radius-two spatial support, and the graph itself is a subset of the
fixed vertical chart.  A positive lower-fibre level therefore puts every
carrier of the same lower-bucket physical datum in the `[-2,2]` graph strip
of transverse width `3 * tau`.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CanonicalGraphFrozenLowerBucketGraphStripSupportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7FirstCrossingFullCoefficientGraphCertificateV4
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8ProjectedTubeImageGraphStripSupportV1
open Family8ShadingAwareProjectedPhysicalImageSupportV1
open Family8ShadingAwareProjectedPhysicalLowerBucketV1
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32ProjectedTubeCarrierMeasurabilityV1
open FamilyStickyCinematicL32PyzQuasiProductCarrierStripMeasureV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-- The literal same-R lower-bucket physical datum has ambient carrier
support in the honest `[-2,2]`, width-`3 tau` graph strip. -/
theorem sameGraph_lowerBucket_carrier_subset_pyzGraphStrip_three
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    {fibreFloor : ENNReal} (hfibreFloor : 0 < fibreFloor) :
    let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
    let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
      VS R.label
    let Z := firstCrossingFamilyGraphBucketShading
      R.axis R.label F P R.A R.k
    let f0 : Real → Real := fun _ => 0
    let physical := shadingAwareProjectedPhysicalLowerBucket Z graph f0
      (measurable_const : Measurable f0) Set.univ MeasurableSet.univ
      Set.univ MeasurableSet.univ fibreFloor
    ∀ i, i ∈ physical.ambient → physical.carrier i ⊆
      pyzCarrierGraphStrip (-2) 2
        (projectedTubeCinematicTrace f0 (VS.family.tubes i))
        (3 * (tau : Real)) := by
  dsimp only
  let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
  let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
    VS R.label
  let Z := firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k
  let f0 : Real → Real := fun _ => 0
  let Q := Classical.choice R.graphCertificate
  intro i hi q hq
  have hiGraph : i ∈ graph := by
    change i ∈ graph at hi
    exact hi
  have hiSource : i ∈ VS.source :=
    (mem_verticalSourceGraphCBucketFiber_iff
      ((tau : Real) / 2) VS R.label i).mp hiGraph |>.1
  have hvertical : (1 / 2 : Real) ≤
      |(VS.family.tubes i).axis.direction 2| :=
    VS.source_direction_final_half i hiSource
  have hB2 : (VS.family.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 2 := by
    simpa only [VS, graph] using Q.vertical_b2 i hiGraph
  have hpositive : q ∈
      (shadingAwareProjectedPhysical Z graph f0
        (measurable_const : Measurable f0) Set.univ MeasurableSet.univ
        Set.univ MeasurableSet.univ).carrier i := by
    change q ∈ Set.univ ∩
      {u | 0 < shadingFiberMass
        (shadingWindowRestriction Z f0
          (measurable_const : Measurable f0) Set.univ MeasurableSet.univ
          Set.univ MeasurableSet.univ) f0 i u}
    refine ⟨Set.mem_univ q, ?_⟩
    change q ∈ Set.univ ∩
      {u | fibreFloor ≤ shadingFiberMass
        (shadingWindowRestriction Z f0
          (measurable_const : Measurable f0) Set.univ MeasurableSet.univ
          Set.univ MeasurableSet.univ) f0 i u} at hq
    exact hfibreFloor.trans_le hq.2
  have himage : q ∈ projectedTubeImageCarrier f0
      (VS.family.tubes i) :=
    shadingAwareProjectedPhysical_carrier_subset_projectedTubeImageCarrier
      VS.family Z graph f0 (measurable_const : Measurable f0)
      Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ i hpositive
  exact projectedTubeImageCarrier_subset_pyzGraphStrip_negTwo_two_three
    (VS.family.tubes i) hvertical hB2 (by simpa only [f0] using himage)

/-- The same statement in the centered-sixteenth notation used by the
low-moment consumer.  The outer interval `[-32,32]` has centered sixteenth
exactly `[-2,2]`. -/
theorem sameGraph_lowerBucket_carrier_subset_centeredWideStrip_three
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    {fibreFloor : ENNReal} (hfibreFloor : 0 < fibreFloor) :
    let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
    let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
      VS R.label
    let Z := firstCrossingFamilyGraphBucketShading
      R.axis R.label F P R.A R.k
    let f0 : Real → Real := fun _ => 0
    let physical := shadingAwareProjectedPhysicalLowerBucket Z graph f0
      (measurable_const : Measurable f0) Set.univ MeasurableSet.univ
      Set.univ MeasurableSet.univ fibreFloor
    ∀ i, i ∈ physical.ambient → physical.carrier i ⊆
      pyzCarrierGraphStrip
        (centeredFractionLeft (-32) 32 (1 / 16 : Real))
        (centeredFractionRight (-32) 32 (1 / 16 : Real))
        (projectedTubeCinematicTrace f0 (VS.family.tubes i))
        (3 * (tau : Real)) := by
  have hleft : centeredFractionLeft (-32) 32 (1 / 16 : Real) = -2 := by
    norm_num [centeredFractionLeft]
  have hright :
      centeredFractionRight (-32) 32 (1 / 16 : Real) = 2 := by
    norm_num [centeredFractionRight]
  simpa only [hleft, hright] using
    sameGraph_lowerBucket_carrier_subset_pyzGraphStrip_three
      R hfibreFloor

#print axioms sameGraph_lowerBucket_carrier_subset_pyzGraphStrip_three
#print axioms
  sameGraph_lowerBucket_carrier_subset_centeredWideStrip_three

end
end Family8CanonicalGraphFrozenLowerBucketGraphStripSupportV1
