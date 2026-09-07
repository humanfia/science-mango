import Family8Grounding.Family8CanonicalGraphFrozenGraphActiveLowerBucketNativeCoreCapFreeV1
import Family8Grounding.Family8CanonicalGraphFrozenDisplayedGraphLowerProducerV1
import Family8Grounding.Family8Family7ShadingMassPositiveProjectedActiveRegionV1
import Mathlib.Tactic

/-!
# A retained lower-bucket payment inside the same frozen graph

The qualitative positive-band constructor used to discard the numerical
quantity selected before the native high/low split.  This file records the
literal payment which survives without any coefficient cap:

`fibreFloor * native source mass`.

It is bounded by the shading mass of the same graph and hence, after dividing
by the actual source-family volume and the two graph-selection losses, by the
source-density quotient stored in the graph certificate.  No displayed
coefficient comparison is assumed.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalGraphFrozenLowerBucketSourceDensityPaymentV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenGraphActiveLowerBucketNativeCoreCapFreeV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7LowerBucketGenericNativeBranchCoreV1
open Family8Family7ShadingMassPositiveProjectedActiveRegionV1
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8ShadingAwareProjectedPhysicalLowerBucketV1
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyAtEveryScaleCoreV1
open Family8StickyShadingAwareLogBucketSelectionV1
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2ShadingPopularityV2

noncomputable section

universe u

/-! ## Generic lower-bucket payment -/

/-- A measurable part of a positive-cardinality lower-fibre bucket pays its
literal fibre floor into the mass of the same window-restricted shading. -/
theorem fibreFloor_mul_volume_le_activeWindowShadingMass_of_band
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set (Real × Real)) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) (fibreFloor : ENNReal)
    (lower upper : Nat) (hlower : 1 <= lower)
    (E : Set (Real × Real)) (hEmeasurable : MeasurableSet E)
    (hE : E ⊆
      (shadingAwareProjectedPhysicalLowerBucket
        Y active f hf X hX I hI fibreFloor).multiplicityBand lower upper) :
    fibreFloor * volume E <=
      ∑ i ∈ active,
        volume ((shadingWindowRestriction Y f hf X hX I hI).carrier i) := by
  let physical := shadingAwareProjectedPhysicalLowerBucket
    Y active f hf X hX I hI fibreFloor
  let Ywindow := shadingWindowRestriction Y f hf X hX I hI
  have hpoint : forall x, x ∈ E ->
      fibreFloor <= projectedActiveMultiplicity Ywindow active f x := by
    intro x hx
    have hxBand := physical.mem_multiplicityBand.mp (hE hx)
    have hcardNat : 1 <= (physical.activeAtPoint x).card :=
      hlower.trans hxBand.2.1
    have hcardENN : (1 : ENNReal) <=
        ((physical.activeAtPoint x).card : ENNReal) := by
      exact_mod_cast hcardNat
    calc
      fibreFloor = fibreFloor * 1 := (mul_one fibreFloor).symm
      _ <= fibreFloor * ((physical.activeAtPoint x).card : ENNReal) := by
        exact mul_le_mul' le_rfl hcardENN
      _ <= projectedActiveMultiplicity Ywindow active f x := by
        simpa only [physical, Ywindow] using
          level_mul_activeAtPoint_card_le_projectedActiveMultiplicity
            Y active f hf X hX I hI fibreFloor x
  calc
    fibreFloor * volume E =
        ∫⁻ _x in E, fibreFloor
          ∂(volume : Measure (Real × Real)) := by
      rw [setLIntegral_const]
    _ <= ∫⁻ x in E, projectedActiveMultiplicity Ywindow active f x
        ∂(volume : Measure (Real × Real)) := by
      exact setLIntegral_mono' hEmeasurable hpoint
    _ = ∑ i ∈ active,
        restrictedMass Ywindow (twistedProjection f ⁻¹' E) i := by
      exact lintegral_projectedActiveMultiplicity_eq_sum_restrictedMass
        Ywindow active f hf E
    _ <= ∑ i ∈ active, volume (Ywindow.carrier i) := by
      exact Finset.sum_le_sum fun i _hi =>
        restrictedMass_le_carrierMass Ywindow
          (twistedProjection f ⁻¹' E) i

/-! ## Same frozen graph transport -/

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-- The literal graph shading is a submass of the source-active shading from
which the frozen assembly was selected. -/
theorem graphShadingMass_le_sourceActiveFineShadingMass
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF) :
    (firstCrossingFamilyGraphBucketShading
      R.axis R.label F P R.A R.k).shadingMass <=
      (sourceActiveFineShading P Y).shadingMass := by
  let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
    (firstCrossingFamilyVerticalSource R.axis F P R.k) R.label
  let coordinate := firstCrossingFamilyCoordinateShading R.axis F P R.A R.k
  have hgraphFinal :
      (firstCrossingFamilyGraphBucketShading
          R.axis R.label F P R.A R.k).shadingMass <=
        (finalFiberShading R.A R.k).shadingMass := by
    calc
      (firstCrossingFamilyGraphBucketShading
          R.axis R.label F P R.A R.k).shadingMass =
          shadingMassOn coordinate graph := by
        symm
        simpa only [coordinate, graph] using
          firstCrossingFamilyCoordinateShading_shadingMassOn_graph
            R.axis R.label F P R.A R.k
      _ <= shadingMassOn coordinate (P.index.fiber R.k) := by
        unfold shadingMassOn
        exact Finset.sum_le_sum_of_subset
          (by
            simpa only [graph] using
              firstCrossingFamilyGraphBucket_subset_fiber
                R.axis R.label F P R.k)
      _ = (finalFiberShading R.A R.k).shadingMass := by
        simpa only [coordinate] using
          firstCrossingFamilyCoordinateShading_shadingMassOn_fiber
            R.axis F P R.A R.k
  have hfinalRefinement :
      (finalFiberShading R.A R.k).shadingMass <=
        R.A.refinement.shading.shadingMass := by
    simpa only [finalFiberShading, fiberShading] using
      (IndexedShadingRefinement.shadingMass_le
        (IndexedShadingRefinement.restrictTo
          R.A.refinement.shading (P.index.fiber R.k)))
  let sourceRestriction := IndexedShadingRefinement.restrictTo Y P.index.fine
  let refinementInsideSource :
      IndexedShadingRefinement sourceRestriction.shading :=
    { indices := R.A.refinement.indices
      shading := R.A.refinement.shading
      carrier_subset := by
        intro i x hx
        have hi : i ∈ R.A.refinement.indices := by
          by_contra hni
          rw [R.A.refinement.carrier_eq_empty_of_not_mem i hni] at hx
          exact hx.elim
        change x ∈ (if i ∈ P.index.fine then Y.carrier i else ∅)
        rw [if_pos (R.A.indices_subset_fine hi)]
        exact R.A.refinement.carrier_subset i hx
      carrier_eq_empty_of_not_mem := R.A.refinement.carrier_eq_empty_of_not_mem }
  have hrefinementSource : R.A.refinement.shading.shadingMass <=
      (sourceActiveFineShading P Y).shadingMass := by
    rw [sourceActiveFineShading_shadingMass]
    simpa only [refinementInsideSource, sourceRestriction] using
      (IndexedShadingRefinement.shadingMass_le refinementInsideSource)
  exact hgraphFinal.trans (hfinalRefinement.trans hrefinementSource)

/-- The norm-cell mass retained by the cap-free same-graph constructor gives
a genuine lower bound for the source-density quotient.  This is the precise
positive payment available before any high/low or first-hit selection. -/
theorem lowerBucketNormCellPayment_le_sourceDensityQuotient
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (n : Nat) (hn : 1 <= n) (fibreFloor : ENNReal) (normLabel : Int)
    (D :
      let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
      let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
        VS R.label
      let Z := firstCrossingFamilyGraphBucketShading
        R.axis R.label F P R.A R.k
      let f0 : Real -> Real := fun _ => 0
      let hf0 : Continuous f0 := continuous_const
      LowerBucketNativeBranchCore VS Z graph f0 hf0
        Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ fibreFloor)
    (hsourceEq :
      let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
      let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
        VS R.label
      let Z := firstCrossingFamilyGraphBucketShading
        R.axis R.label F P R.A R.k
      let f0 : Real -> Real := fun _ => 0
      let physical := shadingAwareProjectedPhysicalLowerBucket Z graph f0
        measurable_const Set.univ MeasurableSet.univ Set.univ
          MeasurableSet.univ fibreFloor
      let normScale := actualProjectedAmbientNormScale VS.family physical 16 0
      let E_norm := continuumCriticalSingleDyadicCell
        (physical.multiplicityBand n n) normScale normLabel
      volume E_norm = D.sourceMass) :
    (((fibreFloor * D.sourceMass) /
          familyVolume (sourceActiveFineFamily P)) /
        ((R.A.loss : ENNReal) * (P.index.coarse.card : ENNReal))) /
        R.graphLoss <=
      ((sourceActiveFineShading P Y).shadingDensity /
          ((R.A.loss : ENNReal) * (P.index.coarse.card : ENNReal))) /
        R.graphLoss := by
  let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
  let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
    VS R.label
  let Z := firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k
  let f0 : Real -> Real := fun _ => 0
  let hf0 : Continuous f0 := continuous_const
  let physical := shadingAwareProjectedPhysicalLowerBucket Z graph f0
    measurable_const Set.univ MeasurableSet.univ Set.univ
      MeasurableSet.univ fibreFloor
  let normScale := actualProjectedAmbientNormScale VS.family physical 16 0
  let E_norm := continuumCriticalSingleDyadicCell
    (physical.multiplicityBand n n) normScale normLabel
  have hEmeasurable : MeasurableSet E_norm := by
    exact measurableSet_continuumCriticalSingleDyadicCell
      (physical.measurableSet_multiplicityBand n n)
      (measurable_actualProjectedAmbientNormScale
        VS.family physical 16 0) normLabel
  have hEsubset : E_norm ⊆ physical.multiplicityBand n n := by
    intro x hx
    exact hx.1
  have hpaySum :=
    fibreFloor_mul_volume_le_activeWindowShadingMass_of_band
      Z graph f0 measurable_const Set.univ MeasurableSet.univ
        Set.univ MeasurableSet.univ fibreFloor n n hn E_norm
          hEmeasurable hEsubset
  have hwindow : forall i,
      (shadingWindowRestriction Z f0 measurable_const
        Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ).carrier i =
          Z.carrier i := by
    intro i
    simp [shadingWindowRestriction, shadingProjectionWindow, f0]
  have hsumEq :
      (∑ i ∈ graph,
        volume ((shadingWindowRestriction Z f0 measurable_const
          Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ).carrier i)) =
        Z.shadingMass := by
    simp_rw [hwindow]
    change (∑ i ∈ graph,
      volume (((IndexedShadingRefinement.restrictTo
        (firstCrossingFamilyVerticalShading R.axis F P R.A R.k) graph).shading
          ).carrier i)) =
      (IndexedShadingRefinement.restrictTo
        (firstCrossingFamilyVerticalShading R.axis F P R.A R.k) graph).shading.shadingMass
    rw [shadingMass_restrictTo_eq_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [IndexedShadingRefinement.restrictTo_carrier, if_pos hi]
  have hpayGraph : fibreFloor * D.sourceMass <= Z.shadingMass := by
    rw [← hsourceEq]
    exact hpaySum.trans_eq hsumEq
  have hpaySource : fibreFloor * D.sourceMass <=
      (sourceActiveFineShading P Y).shadingMass :=
    hpayGraph.trans (by
      simpa only [Z] using graphShadingMass_le_sourceActiveFineShadingMass R)
  have hpayDensity :
      (fibreFloor * D.sourceMass) /
          familyVolume (sourceActiveFineFamily P) <=
        (sourceActiveFineShading P Y).shadingDensity := by
    unfold Shading.shadingDensity
    exact ENNReal.div_le_div_right hpaySource _
  exact ENNReal.div_le_div_right
    (ENNReal.div_le_div_right hpayDensity
      ((R.A.loss : ENNReal) * (P.index.coarse.card : ENNReal)))
    R.graphLoss

#print axioms fibreFloor_mul_volume_le_activeWindowShadingMass_of_band
#print axioms graphShadingMass_le_sourceActiveFineShadingMass
#print axioms lowerBucketNormCellPayment_le_sourceDensityQuotient

end
end Family8CanonicalGraphFrozenLowerBucketSourceDensityPaymentV1
