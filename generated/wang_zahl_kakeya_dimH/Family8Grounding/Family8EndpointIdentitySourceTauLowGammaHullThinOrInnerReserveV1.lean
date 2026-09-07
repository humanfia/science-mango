import Family8Grounding.Family8EndpointIdentitySourceTauHighGammaInnerReserveV1
import Family8Grounding.Family8SelectedParentAdaptiveScaleReservePowerLowerV1
import Mathlib.Tactic

/-!
# Endpoint identity low-gamma hull-thin or exact local inner reserve

At the endpoint scale `rho = delta`, apply the selected-parent paper hull
dichotomy with `tau = 1`.  The thin branch is literally
`hullShortestSide J <= 1`.  In the flat branch, one finite-constant
absorption and the stated numerical margin supply the scale reserve consumed
by the existing same-bucket Proposition 6.6(A) lemma.

The payment bucket is fixed throughout: the label, occurrence witness, and
V3 actual full-fibre cap are not reselected, and no all-label premise is
introduced.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8EndpointIdentitySourceTauLowGammaHullThinOrInnerReserveV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8EndpointIdentitySourceTauHighGammaInnerReserveV1
open Family8EndpointIdentitySourceTauSameOccurrenceProp66APowerBudgetV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentAdaptiveInnerSourceReserveV1
open Family8SelectedParentAdaptiveScaleReservePowerLowerV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessGeometryV1
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessProducerV1
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalMassPopularEndpointV3
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- For one fixed occupied payment bucket at the endpoint scale, low gamma
and the single displayed exponent margin close the exact V3 local inner
residual unless the selected parent hull is already paper-thin. -/
theorem selectedParent_endpointIdentity_lowGamma_paperHullThin_or_prop66AInner_fixedResidual
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (S : StickyScaleCover fine delta)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hdelta P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hdelta label})
    (hsmallPacking : selectedParentCenteredHalfPostAdaptiveProxyScale
      delta delta r label / 8 <= (1 / 100 : NNReal))
    {outputEta absorbEta reserveEta innerEpsilon gamma : Real}
    (hgammaTwoThirds : gamma <= 2 / 3)
    (hinnerEpsilon : 0 <= innerEpsilon)
    (hreserveEta : 0 < reserveEta)
    (hnumericalMargin :
      gamma + absorbEta + 2 * outputEta + reserveEta <=
        innerEpsilon / 2)
    (hsmall : delta <=
      adaptiveScaleReserveFlatConstantThreshold gamma reserveEta) :
    let J := selectedParentGreedyBlockJohnFrame S hdelta P k
    hullShortestSide J <= 1 ∨
      (delta : ENNReal) ^ (-(2 + absorbEta)) <=
        (delta : ENNReal) ^ (2 * outputEta) *
          proposition66AInnerFactor delta
            (bucketShortA label) (bucketShortB label)
            (centeredAdaptiveActualBucketFullFiberNatCap
              S hdelta P k r hr label
                (endpointIdentitySourceTauPackingKatzTaoConstant
                  delta delta))
            innerEpsilon gamma := by
  dsimp only
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hdelta P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  have hWmem : (W.1 : {p // p ∈ B}) ∈
      selectedParentPlankBucketIndices e S B hdelta label := by
    simpa only [e, B] using W.2
  have hWshape : sideShapeLabel
      (selectedParentLongRelabeledSide e S B hdelta W.1) = label := by
    change (W.1 : {p // p ∈ B}) ∈ sideShapeBucket Finset.univ
      (fun p => selectedParentLongRelabeledSide e S B hdelta p) label at hWmem
    exact (mem_sideShapeBucket_iff _ _ _ _).mp hWmem |>.2
  have hoccupied : SelectedBucketOccupied S hdelta P k r hr label := by
    rw [SelectedBucketOccupied]
    exact mem_occupiedWeightBuckets_iff.mpr
      <| ⟨W.1, Finset.mem_univ _, hWshape⟩
  have hdeltaOne : delta <= 1 := hdeltaHalf.trans (by norm_num)
  have hdeltaOneENN : (delta : ENNReal) <= 1 := by
    exact_mod_cast hdeltaOne
  have hbranch := selectedParent_paperHullThin_or_bucketFlat
    hfineContained S hdelta hdeltaOne P k r hr label W 1
  rcases hbranch with hthin | hflat
  · left
    simpa only [sub_self, NNReal.rpow_zero] using hthin
  · right
    have hflatOne : bucketShortA label <= 286654464 * delta := by
      simpa only [NNReal.rpow_one] using hflat
    have hscaleRaw :
        (delta : ENNReal) ^
            (reserveEta - (1 : Real) * (innerEpsilon / 2)) <=
          (delta : ENNReal) ^ (-innerEpsilon / 2) *
            ((bucketShortB label : ENNReal) /
              (bucketShortA label : ENNReal)) *
            (((delta : ENNReal) / (bucketShortA label : ENNReal)) ^
              (2 - 3 * gamma)) := by
      apply delta_rpow_absorb_sub_radiusGain_le_scaleReserve
        (delta := delta) (rho := delta)
        (a := bucketShortA label) (b := bucketShortB label)
        (alpha := (1 : Real)) (innerEpsilon := innerEpsilon)
        (beta := gamma) (absorbExponent := reserveEta)
        hdelta hdelta hinnerEpsilon hgammaTwoThirds
        (bucketShortA_pos label) (bucketShortA_le_bucketShortB label)
      · simpa only [NNReal.rpow_one] using (le_rfl : delta <= delta)
      · exact hflatOne
      · exact hreserveEta
      · exact hsmall
    have hpowerMonotone :
        (delta : ENNReal) ^
            (-(gamma + absorbEta + 2 * outputEta)) <=
          (delta : ENNReal) ^
            (reserveEta - (1 : Real) * (innerEpsilon / 2)) := by
      exact ENNReal.rpow_le_rpow_of_exponent_ge hdeltaOneENN (by
        linarith)
    have hscaleReserve :
        (delta : ENNReal) ^
            (-(gamma + absorbEta + 2 * outputEta)) <=
          (delta : ENNReal) ^ (-innerEpsilon / 2) *
            ((bucketShortB label : ENNReal) /
              (bucketShortA label : ENNReal)) *
            (((delta : ENNReal) / (bucketShortA label : ENNReal)) ^
              (2 - 3 * gamma)) :=
      hpowerMonotone.trans hscaleRaw
    exact sameBucket_localScaleReserve_implies_prop66AInner_fixedResidual
      S P k r hr label hdelta hoccupied hdeltaHalf hsmallPacking
        (hgammaTwoThirds.trans (by norm_num)) hscaleReserve

#print axioms
  selectedParent_endpointIdentity_lowGamma_paperHullThin_or_prop66AInner_fixedResidual

end
end Family8EndpointIdentitySourceTauLowGammaHullThinOrInnerReserveV1
