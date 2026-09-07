import Family8Grounding.Family8SelectedParentSideHullDyadicActualCountScalarV1
import Family8Grounding.Family8CoreHighFiberDensitySameQExactJointOuterHullTwoScaleV1
import Family8Grounding.Family8OuterInnerMismatchHighGammaPackingBridgeV1
import Mathlib.Tactic

/-!
# Selected-side dyadic hull payment in the two-scale actual-count endpoint

This is the direct object bridge from the literal winning parent block to the
two-scale whole Proposition 6.6(A) consumer.  The exact inverse density from
the outer coefficient, the selected-side hull, and the actual block count are
kept in one scalar.  The outer and inner John labels remain independent; the
endpoint packing coefficient absorbs their genuine mismatch only after the
outer-times-inner product has been assembled.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentSideHullDyadicTwoScaleJointV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family8CoreHighFiberDensitySameQExactJointOuterHullTwoScaleV1
open Family8EndpointIdentitySourceTauSameOccurrenceProp66APowerBudgetV1
open Family8OuterInnerMismatchHighGammaPackingBridgeV1
open Family8Prop51JointOccurrenceWeightedSelectionV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8Prop66InnerScaleMismatchAbsorptionV1
open Family8SelectedOccurrenceOuterInnerScaleMismatchPowerV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentSideHullDyadicActualCountScalarV1
open Family8SelectedParentSideHullReserveProducerV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Direct hJoint producer at the actual selected-block count.  Its sole
scale input is the combined side-envelope/dyadic/count inequality; there is
no independent hull reserve and no replacement of the count by one. -/
theorem selectedParent_jointOuterHullReserve_twoScale_actualCount_of_sideEnvelope
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine delta) (hdelta : 0 < delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (labelInner : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hdelta P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hdelta labelInner})
    (base : ENNReal) (bucketKey : Nat)
    (hband : InENNRealDyadicBand base bucketKey
      (blockDensity S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P k)))
    (hbaseOne : 1 ≤ base) (hbaseTop : base ≠ ∞)
    (outerA outerB : NNReal) (plankCount : Nat)
    (coefficientLoss outerCF sourceCF refinementLoss johnLoss
      sourceDensity geometryLoss : ENNReal)
    {epsilon beta : Real} (hbeta0 : 0 ≤ beta) (hbetaOne : beta ≤ 1)
    (houterCF : outerCF ≤ coefficientLoss * sourceCF *
      ((2 : ENNReal) ^ bucketKey * base)⁻¹)
    (hjointScale :
      johnLoss *
          ((((2 : ENNReal) ^ (beta / 2) *
                (selectedParentSideHullEnvelope delta
                  (bucketShortA labelInner)) ^ (beta / 2)) *
              ((2 : ENNReal) ^ bucketKey * base) ^ (beta - 1)) *
            ((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal) ^
              (1 - beta / 2)) ≤
        (sourceDensity * geometryLoss) *
          proposition66AInnerFactor delta
            (bucketShortA labelInner) (bucketShortB labelInner)
            (blockAt S.activeCoarseFamily P k).fiber.card epsilon beta) :
    johnLoss *
          ((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal) *
        proposition66AOuterFactor delta outerA outerB plankCount
          (outerCF * refinementLoss) epsilon beta ≤
      (sourceDensity * geometryLoss *
          coefficientLoss ^ (1 - beta / 2)) *
        (proposition66AOuterFactor delta outerA outerB plankCount
            (sourceCF * refinementLoss) epsilon beta *
          proposition66AInnerFactor delta
            (bucketShortA labelInner) (bucketShortB labelInner)
            (blockAt S.activeCoarseFamily P k).fiber.card epsilon beta) := by
  have hdeltaOne : delta ≤ 1 := hdeltaHalf.trans (by norm_num)
  have hscalar :=
    selectedParent_twoScale_actualCount_hscalar_of_sideEnvelope
      hfineContained S hdelta hdeltaOne hdeltaHalf P k
      sourceDensity geometryLoss johnLoss r hr labelInner W base bucketKey
      hband hbaseOne hbaseTop hbeta0 hbetaOne hjointScale
  exact jointOuterHullReserve_twoScale_actualCount_of_inverseDensityOuterCF
    (delta := delta) (outerA := outerA) (outerB := outerB)
    (innerA := bucketShortA labelInner)
    (innerB := bucketShortB labelInner)
    (plankCount := plankCount)
    (tubesPerPlank := (blockAt S.activeCoarseFamily P k).fiber.card)
    (d0 := (2 : ENNReal) ^ bucketKey * base)
    (coefficientLoss := coefficientLoss) (outerCF := outerCF)
    (sourceCF := sourceCF) (refinementLoss := refinementLoss)
    (johnLoss := johnLoss) (sourceDensity := sourceDensity)
    (geometryLoss := geometryLoss) (epsilon := epsilon) (beta := beta)
    hbetaOne houterCF hscalar

/-- Endpoint terminal form with the actual block count and two genuinely
different labels.  The exact mismatch is absorbed into the endpoint packing
coefficient after the two-scale product is formed. -/
theorem selectedParent_average_le_endpointPackedFrostmanFactor_twoLabels_actualCount
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine delta) (hdelta : 0 < delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (labelOuter labelInner : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hdelta P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hdelta labelInner})
    (hrel : Prop66OuterInnerLabelScaleRelation
      (delta / 576) (delta / 11943936) labelOuter labelInner)
    (base : ENNReal) (bucketKey : Nat)
    (hband : InENNRealDyadicBand base bucketKey
      (blockDensity S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P k)))
    (hbaseOne : 1 ≤ base) (hbaseTop : base ≠ ∞)
    {plankCount totalCount : Nat}
    {average geometricScale jacobian sourceDensity area johnLoss rawLoss
      geometryLoss coefficientLoss outerCF sourceCF refinementLoss
      countLoss : ENNReal}
    {epsilon beta : Real} (hbeta0 : 0 ≤ beta) (hbetaOne : beta ≤ 1)
    (hsource0 : jacobian * (sourceDensity * area) ≠ 0)
    (hsourceTop : jacobian * (sourceDensity * area) ≠ ∞)
    (hcount :
      ((plankCount * (blockAt S.activeCoarseFamily P k).fiber.card : Nat) :
          ENNReal) ≤ countLoss * (totalCount : ENNReal))
    (houterCF : outerCF ≤ coefficientLoss * sourceCF *
      ((2 : ENNReal) ^ bucketKey * base)⁻¹)
    (hjointScale :
      johnLoss *
          ((((2 : ENNReal) ^ (beta / 2) *
                (selectedParentSideHullEnvelope delta
                  (bucketShortA labelInner)) ^ (beta / 2)) *
              ((2 : ENNReal) ^ bucketKey * base) ^ (beta - 1)) *
            ((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal) ^
              (1 - beta / 2)) ≤
        (sourceDensity * geometryLoss) *
          proposition66AInnerFactor delta
            (bucketShortA labelInner) (bucketShortB labelInner)
            (blockAt S.activeCoarseFamily P k).fiber.card epsilon beta)
    (hscaled :
      (jacobian * (sourceDensity * area)) * average ≤
        rawLoss *
          (proposition66AOuterFactor delta
              (bucketShortA labelOuter) (bucketShortB labelOuter)
              plankCount (outerCF * refinementLoss) epsilon beta *
            (blockDensity S.activeCoarseFamily
                (blockAt S.activeCoarseFamily P k) * geometricScale)))
    (hJohn :
      blockDensity S.activeCoarseFamily
            (blockAt S.activeCoarseFamily P k) * geometricScale ≤
        jacobian *
          (johnLoss *
            (((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal) *
              area))) :
    average ≤
      (rawLoss * geometryLoss *
          coefficientLoss ^ (1 - beta / 2) *
          (outerInnerMismatchEndpointConstant beta *
            countLoss ^ (1 - beta / 2))) *
        proposition66AFrostmanFactor delta
          (bucketShortA labelOuter) (bucketShortB labelOuter) totalCount
          (endpointIdentitySourceTauPackingKatzTaoConstant delta delta *
            (sourceCF * refinementLoss)) epsilon beta := by
  let m : Nat := (blockAt S.activeCoarseFamily P k).fiber.card
  let outerBound : ENNReal := proposition66AOuterFactor delta
    (bucketShortA labelOuter) (bucketShortB labelOuter) plankCount
    (outerCF * refinementLoss) epsilon beta
  let targetCF : ENNReal := sourceCF * refinementLoss
  let densityLoss : ENNReal := coefficientLoss ^ (1 - beta / 2)
  let mismatch : ENNReal := prop66InnerScaleMismatchLoss
    (bucketShortA labelOuter) (bucketShortB labelOuter)
    (bucketShortA labelInner) (bucketShortB labelInner) beta
  let packing : ENNReal :=
    endpointIdentitySourceTauPackingKatzTaoConstant delta delta
  have hJoint :=
    selectedParent_jointOuterHullReserve_twoScale_actualCount_of_sideEnvelope
      hfineContained S hdelta hdeltaHalf P k r hr labelInner W base bucketKey
      hband hbaseOne hbaseTop
      (bucketShortA labelOuter) (bucketShortB labelOuter) plankCount
      coefficientLoss outerCF sourceCF refinementLoss johnLoss
      sourceDensity geometryLoss hbeta0 hbetaOne houterCF hjointScale
  have hbase :=
    average_le_wholeProp66AFrostmanFactor_of_jointOuterHullReserve_twoScale_actualCount
      (delta := delta)
      (outerA := bucketShortA labelOuter)
      (outerB := bucketShortB labelOuter)
      (innerA := bucketShortA labelInner)
      (innerB := bucketShortB labelInner)
      (plankCount := plankCount) (tubesPerPlank := m)
      (totalCount := totalCount) (average := average)
      (d := blockDensity S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P k))
      (outerBound := outerBound) (geometricScale := geometricScale)
      (jacobian := jacobian) (sourceDensity := sourceDensity) (area := area)
      (johnLoss := johnLoss) (rawLoss := rawLoss)
      (geometryLoss := geometryLoss) (targetCF := targetCF)
      (densityLoss := densityLoss) (countLoss := countLoss)
      (epsilon := epsilon) (beta := beta)
      hdelta
      (hrel.outerFloor_pos.trans_le hrel.outerFloor_le_shortA)
      ((hrel.outerFloor_pos.trans_le hrel.outerFloor_le_shortA).trans_le
        (bucketShortA_le_bucketShortB labelOuter))
      (hrel.innerFloor_pos.trans_le hrel.innerFloor_le_shortA)
      ((hrel.innerFloor_pos.trans_le hrel.innerFloor_le_shortA).trans_le
        (bucketShortA_le_bucketShortB labelInner))
      hbeta0 hbetaOne hsource0 hsourceTop
      (by simpa only [m] using hcount)
      (by simpa only [outerBound] using hscaled)
      (by simpa only [m] using hJohn)
      (by simpa only [m, outerBound, targetCF, densityLoss] using hJoint)
  have hmismatchFloor : mismatch ≤
      (((delta / 576 : NNReal) : ENNReal) ^ (-beta)) *
        (((delta / 11943936 : NNReal) : ENNReal) ^
          (2 * beta - 2)) := by
    simpa only [mismatch] using hrel.innerMismatchLoss_le hbeta0 hbetaOne
  have hmismatch : mismatch ≤
      outerInnerMismatchEndpointConstant beta *
        packing ^ (1 - beta / 2) := by
    exact mismatch_le_constant_mul_endpointPacking_of_endpointFloorBound
      hdelta (hbetaOne.trans (by norm_num)) hmismatchFloor
  have habsorb :
      mismatch *
          proposition66AFrostmanFactor delta
            (bucketShortA labelOuter) (bucketShortB labelOuter) totalCount
            targetCF epsilon beta ≤
        outerInnerMismatchEndpointConstant beta *
          proposition66AFrostmanFactor delta
            (bucketShortA labelOuter) (bucketShortB labelOuter) totalCount
            (packing * targetCF) epsilon beta := by
    exact mismatch_mul_frostmanFactor_le_loss_mul_packedFrostmanFactor
      (delta := delta) (a := bucketShortA labelOuter)
      (b := bucketShortB labelOuter) (tubeCount := totalCount)
      (CF := targetCF) (packing := packing) (mismatch := mismatch)
      (loss := outerInnerMismatchEndpointConstant beta)
      (epsilon := epsilon) (beta := beta)
      (hbetaOne.trans (by norm_num)) hmismatch
  calc
    average ≤
        (rawLoss * geometryLoss * densityLoss *
            (mismatch * countLoss ^ (1 - beta / 2))) *
          proposition66AFrostmanFactor delta
            (bucketShortA labelOuter) (bucketShortB labelOuter) totalCount
            targetCF epsilon beta := by
      simpa only [m, outerBound, targetCF, densityLoss, mismatch] using hbase
    _ = (rawLoss * geometryLoss * densityLoss *
          countLoss ^ (1 - beta / 2)) *
        (mismatch *
          proposition66AFrostmanFactor delta
            (bucketShortA labelOuter) (bucketShortB labelOuter) totalCount
            targetCF epsilon beta) := by ac_rfl
    _ ≤ (rawLoss * geometryLoss * densityLoss *
          countLoss ^ (1 - beta / 2)) *
        (outerInnerMismatchEndpointConstant beta *
          proposition66AFrostmanFactor delta
            (bucketShortA labelOuter) (bucketShortB labelOuter) totalCount
            (packing * targetCF) epsilon beta) :=
      mul_le_mul' le_rfl habsorb
    _ = (rawLoss * geometryLoss *
          coefficientLoss ^ (1 - beta / 2) *
          (outerInnerMismatchEndpointConstant beta *
            countLoss ^ (1 - beta / 2))) *
        proposition66AFrostmanFactor delta
          (bucketShortA labelOuter) (bucketShortB labelOuter) totalCount
          (endpointIdentitySourceTauPackingKatzTaoConstant delta delta *
            (sourceCF * refinementLoss)) epsilon beta := by
      dsimp only [densityLoss, packing, targetCF]
      ac_rfl

#print axioms
  selectedParent_jointOuterHullReserve_twoScale_actualCount_of_sideEnvelope
#print axioms
  selectedParent_average_le_endpointPackedFrostmanFactor_twoLabels_actualCount

end
end Family8SelectedParentSideHullDyadicTwoScaleJointV1
