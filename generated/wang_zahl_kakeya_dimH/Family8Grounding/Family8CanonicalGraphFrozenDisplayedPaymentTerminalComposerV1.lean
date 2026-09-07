import Family8Grounding.Family8CanonicalGraphFrozenLowerBucketGraphVolumeCalibrationV1
import Family8Grounding.Family8CanonicalGraphFrozenDisplayedCoefficientHRowCorrelationV1
import Family8Grounding.Family8CanonicalGraphFrozenActualLedgerSelectionFirstDSOV1
import Family8Grounding.Family8CanonicalGraphFrozenDisplayedGraphLowerProducerV1
import Family8Grounding.Family8CanonicalGraphFrozenExplicitTruncationHighMassSourceDominationV1
import Mathlib.Tactic

/-!
# Terminal composer from a same-graph displayed payment

This file isolates the shortest scalar seam consumed by
`SameAssemblyGraphFrozenActualLedgerDSOClosure`.  For the literal graph
selected by `R`, it turns

`displayed * volume Z.shadedUnion <= Wp <= Z.shadingMass`

into `displayed <= R.graphAverage`.  The continuation-style endpoint can be
fed directly to the existing closure consumer, without restating its long
list of downstream arguments.

The lower-bucket specialization proves `Wp <= Z.shadingMass` internally, so
its sole analytic payment premise is the displayed-volume calibration.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8CanonicalGraphFrozenDisplayedPaymentTerminalComposerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenActualLedgerSelectionFirstDSOV1
open Family8CanonicalGraphFrozenDisplayedCoefficientHRowCorrelationV1
open Family8CanonicalGraphFrozenDisplayedGraphLowerProducerV1
open Family8CanonicalGraphFrozenExplicitTruncationHighMassSourceDominationV1
open Family8CanonicalGraphFrozenLowFibreWeightedTailV1
open Family8CanonicalGraphFrozenLowerBucketGraphVolumeCalibrationV1
open Family8CanonicalGraphFrozenLowerBucketSameGraphShadingMassPaymentV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7LowerBucketGenericNativeBranchCoreV1
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8ShadingAwareProjectedPhysicalLowerBucketV1
open Family8ShadingAwareProjectedPhysicalV3
open Family8SquarePlankHRowSelectionFirstSetupV1
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyWZ2ProjectionSliceRetentionV1

noncomputable section

variable {tau rho delta : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-! ## The weakest same-graph scalar bridge -/

/-- A payment into any intermediate `Wp`, followed by its domination by the
literal selected graph mass, bounds the displayed coefficient by the exact
selected graph average.  `S` and `hMassEq` make an upstream mass alias
explicit without requiring it to be definitionally equal to the graph mass.
-/
theorem displayed_le_graphAverage_of_sameGraph_payment
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (displayed Wp S : ENNReal)
    (hPayment :
      let Z := firstCrossingFamilyGraphBucketShading
        R.axis R.label F P R.A R.k
      displayed * volume Z.shadedUnion <= Wp)
    (hWp : Wp <= S)
    (hMassEq :
      let Z := firstCrossingFamilyGraphBucketShading
        R.axis R.label F P R.A R.k
      S = Z.shadingMass) :
    displayed <= R.graphAverage := by
  let Z := firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k
  let Q := Classical.choice R.graphCertificate
  have hgraphMass : Z.shadingMass ≠ 0 := by
    simpa only [Z] using Q.graph_mass_ne_zero
  have hvolume0 : volume Z.shadedUnion ≠ 0 :=
    volume_shadedUnion_ne_zero_of_shadingMass_ne_zero Z hgraphMass
  have hvolumeTop : volume Z.shadedUnion ≠ ∞ :=
    volume_shadedUnion_ne_top Z
  have hPayment' : displayed * volume Z.shadedUnion <= Wp := by
    simpa only [Z] using hPayment
  have hMassEq' : S = Z.shadingMass := by
    simpa only [Z] using hMassEq
  have hmul : displayed * volume Z.shadedUnion <= Z.shadingMass :=
    hPayment'.trans (hWp.trans_eq hMassEq')
  have hdiv : displayed <= Z.shadingMass / volume Z.shadedUnion :=
    (ENNReal.le_div_iff_mul_le
      (Or.inl hvolume0) (Or.inl hvolumeTop)).2 hmul
  simpa only [SameAssemblyFullCoefficientGraphIdentity.graphAverage,
    Shading.averageMultiplicity, Z] using hdiv

/-- Exact specialization matching the `hDisplayedToGraph` input of
`SameAssemblyGraphFrozenActualLedgerDSOClosure`. -/
theorem actualLedgerClosure_displayedInput_of_sameGraph_payment
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (X selectorLoss : ENNReal) (outputEta : Real) (Wp S : ENNReal)
    (hPayment :
      let Z := firstCrossingFamilyGraphBucketShading
        R.axis R.label F P R.A R.k
      (selectorLoss *
          (128 * (delta : ENNReal) ^ (-outputEta) * X)) *
        volume Z.shadedUnion <= Wp)
    (hWp : Wp <= S)
    (hMassEq :
      let Z := firstCrossingFamilyGraphBucketShading
        R.axis R.label F P R.A R.k
      S = Z.shadingMass) :
    selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X) <=
      R.graphAverage := by
  exact displayed_le_graphAverage_of_sameGraph_payment
    R (selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X))
      Wp S hPayment hWp hMassEq

/-! ## Continuation-style terminal consumption -/

/-- Feed the exact displayed-input proposition to any already partially
applied terminal consumer.  In particular, `consume` may be the existing
`SameAssemblyGraphFrozenActualLedgerDSOClosure` after all arguments before
and after `hDisplayedToGraph` have been abstracted by a local continuation.
-/
theorem consume_actualLedgerClosure_of_sameGraph_payment
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (X selectorLoss : ENNReal) (outputEta : Real) (Wp S : ENNReal)
    (Goal : Prop)
    (consume :
      (selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X) <=
        R.graphAverage) -> Goal)
    (hPayment :
      let Z := firstCrossingFamilyGraphBucketShading
        R.axis R.label F P R.A R.k
      (selectorLoss *
          (128 * (delta : ENNReal) ^ (-outputEta) * X)) *
        volume Z.shadedUnion <= Wp)
    (hWp : Wp <= S)
    (hMassEq :
      let Z := firstCrossingFamilyGraphBucketShading
        R.axis R.label F P R.A R.k
      S = Z.shadingMass) : Goal := by
  apply consume
  exact actualLedgerClosure_displayedInput_of_sameGraph_payment
    R X selectorLoss outputEta Wp S hPayment hWp hMassEq

/-! ## Even shorter density-floor route -/

/-- Any displayed coefficient already below the retained same-graph source
density quotient is automatically below the literal selected graph average.
Unlike the payment route, this is a direct transitivity argument and needs no
volume cancellation hypotheses. -/
theorem displayed_le_graphAverage_of_le_sourceDensityQuotient
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (displayed : ENNReal)
    (hDisplayed :
      displayed <=
        ((sourceActiveFineShading P Y).shadingDensity /
            ((R.A.loss : ENNReal) *
              (P.index.coarse.card : ENNReal))) /
          R.graphLoss) :
    displayed <= R.graphAverage := by
  exact hDisplayed.trans (sourceDensityQuotient_le_graphAverage R)

/-- Density-floor specialization in the exact scalar shape consumed by
`SameAssemblyGraphFrozenActualLedgerDSOClosure`. -/
theorem actualLedgerClosure_displayedInput_of_le_sourceDensityQuotient
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (X selectorLoss : ENNReal) (outputEta : Real)
    (hDisplayed :
      selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X) <=
        ((sourceActiveFineShading P Y).shadingDensity /
            ((R.A.loss : ENNReal) *
              (P.index.coarse.card : ENNReal))) /
          R.graphLoss) :
    selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X) <=
      R.graphAverage := by
  exact displayed_le_graphAverage_of_le_sourceDensityQuotient
    R (selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X))
      hDisplayed

/-- Continuation-style terminal consumption of the shortest density-floor
scalar premise. -/
theorem consume_actualLedgerClosure_of_le_sourceDensityQuotient
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (X selectorLoss : ENNReal) (outputEta : Real)
    (Goal : Prop)
    (consume :
      (selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X) <=
        R.graphAverage) -> Goal)
    (hDisplayed :
      selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X) <=
        ((sourceActiveFineShading P Y).shadingDensity /
            ((R.A.loss : ENNReal) *
              (P.index.coarse.card : ENNReal))) /
          R.graphLoss) : Goal := by
  apply consume
  exact actualLedgerClosure_displayedInput_of_le_sourceDensityQuotient
    R X selectorLoss outputEta hDisplayed

/-! ## Explicit-truncation high-mass specialization -/

/-- For any `p` supplied by the upstream explicit no-`ell` selector, its
exact-card high mass is already paid by the literal same-graph shading mass.
This theorem does not select `p`; consequently only the displayed-volume
payment into the caller's fixed high mass remains as a premise. -/
theorem displayed_le_graphAverage_of_explicitTruncationHighMass_payment
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (p : Nat) (displayed : ENNReal)
    (hPayment :
      let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
      let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
        VS R.label
      let Z := firstCrossingFamilyGraphBucketShading
        R.axis R.label F P R.A R.k
      let f0 : Real -> Real := fun _ => 0
      let Yw := shadingWindowRestriction Z f0 measurable_const
        Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
      let densityFloor :=
        ((sourceActiveFineShading P Y).shadingDensity /
          ((R.A.loss : ENNReal) * (P.index.coarse.card : ENNReal))) /
          R.graphLoss
      let level0 := densityFloor * (tau : ENNReal) / 96
      let highPhysical :=
        positiveLowerFibreProjectedPhysical Yw graph f0
          measurable_const level0
      let E := highPhysical.multiplicityBand
      displayed * volume Z.shadedUnion <=
        highFibreWeightedMass Yw graph f0 level0 (E p p)) :
    displayed <= R.graphAverage := by
  have hsource :=
    sameGraph_explicitLevel_exactCard_highMass_le_source_eq_graphShadingMass
      R p
  dsimp only at hPayment hsource
  exact displayed_le_graphAverage_of_sameGraph_payment
    R displayed _ _ hPayment hsource.1 hsource.2

/-- Exact closure-input shape from the explicit-truncation high-mass
payment; this theorem has no separate `Wp <= S` premise. -/
theorem actualLedgerClosure_displayedInput_of_explicitTruncationHighMass_payment
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (p : Nat) (X selectorLoss : ENNReal) (outputEta : Real)
    (hPayment :
      let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
      let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
        VS R.label
      let Z := firstCrossingFamilyGraphBucketShading
        R.axis R.label F P R.A R.k
      let f0 : Real -> Real := fun _ => 0
      let Yw := shadingWindowRestriction Z f0 measurable_const
        Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
      let densityFloor :=
        ((sourceActiveFineShading P Y).shadingDensity /
          ((R.A.loss : ENNReal) * (P.index.coarse.card : ENNReal))) /
          R.graphLoss
      let level0 := densityFloor * (tau : ENNReal) / 96
      let highPhysical :=
        positiveLowerFibreProjectedPhysical Yw graph f0
          measurable_const level0
      let E := highPhysical.multiplicityBand
      (selectorLoss *
          (128 * (delta : ENNReal) ^ (-outputEta) * X)) *
        volume Z.shadedUnion <=
          highFibreWeightedMass Yw graph f0 level0 (E p p)) :
    selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X) <=
      R.graphAverage := by
  exact displayed_le_graphAverage_of_explicitTruncationHighMass_payment
    R p (selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X))
      hPayment

/-- Terminal continuation from the sole explicit-truncation analytic
payment to an existing closure consumer. -/
theorem consume_actualLedgerClosure_of_explicitTruncationHighMass_payment
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (p : Nat) (X selectorLoss : ENNReal) (outputEta : Real)
    (Goal : Prop)
    (consume :
      (selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X) <=
        R.graphAverage) -> Goal)
    (hPayment :
      let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
      let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
        VS R.label
      let Z := firstCrossingFamilyGraphBucketShading
        R.axis R.label F P R.A R.k
      let f0 : Real -> Real := fun _ => 0
      let Yw := shadingWindowRestriction Z f0 measurable_const
        Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
      let densityFloor :=
        ((sourceActiveFineShading P Y).shadingDensity /
          ((R.A.loss : ENNReal) * (P.index.coarse.card : ENNReal))) /
          R.graphLoss
      let level0 := densityFloor * (tau : ENNReal) / 96
      let highPhysical :=
        positiveLowerFibreProjectedPhysical Yw graph f0
          measurable_const level0
      let E := highPhysical.multiplicityBand
      (selectorLoss *
          (128 * (delta : ENNReal) ^ (-outputEta) * X)) *
        volume Z.shadedUnion <=
          highFibreWeightedMass Yw graph f0 level0 (E p p)) : Goal := by
  apply consume
  exact
    actualLedgerClosure_displayedInput_of_explicitTruncationHighMass_payment
      R p X selectorLoss outputEta hPayment

/-! ## Lower-bucket specialization: only the analytic calibration remains -/

/-- For the canonical lower-bucket norm cell, domination of `Wp` by the same
graph shading mass is automatic.  Thus this continuation exposes only the
displayed-volume payment as the analytic seam before the terminal consumer.
-/
theorem consume_actualLedgerClosure_of_lowerBucket_volumeCalibration
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
      volume E_norm = D.sourceMass)
    (X selectorLoss : ENNReal) (outputEta : Real)
    (Goal : Prop)
    (consume :
      (selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X) <=
        R.graphAverage) -> Goal)
    (hCalibration :
      let Z := firstCrossingFamilyGraphBucketShading
        R.axis R.label F P R.A R.k
      (selectorLoss *
          (128 * (delta : ENNReal) ^ (-outputEta) * X)) *
        volume Z.shadedUnion <= fibreFloor * D.sourceMass) : Goal := by
  apply consume
  exact displayed_le_graphAverage_of_sameGraph_volumeCalibration
    R n hn fibreFloor normLabel D hsourceEq
      (selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X))
        hCalibration

#print axioms displayed_le_graphAverage_of_sameGraph_payment
#print axioms actualLedgerClosure_displayedInput_of_sameGraph_payment
#print axioms consume_actualLedgerClosure_of_sameGraph_payment
#print axioms displayed_le_graphAverage_of_le_sourceDensityQuotient
#print axioms
  actualLedgerClosure_displayedInput_of_le_sourceDensityQuotient
#print axioms consume_actualLedgerClosure_of_le_sourceDensityQuotient
#print axioms
  displayed_le_graphAverage_of_explicitTruncationHighMass_payment
#print axioms
  actualLedgerClosure_displayedInput_of_explicitTruncationHighMass_payment
#print axioms
  consume_actualLedgerClosure_of_explicitTruncationHighMass_payment
#print axioms
  consume_actualLedgerClosure_of_lowerBucket_volumeCalibration

end
end Family8CanonicalGraphFrozenDisplayedPaymentTerminalComposerV1
