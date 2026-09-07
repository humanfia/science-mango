import Family8Grounding.Family8ComparableRLocalKTWholeEq32ScalarV1
import Family8Grounding.Family8SelectedParentBlockDensityJohnHullCancellationV1
import Mathlib.Tactic

/-!
# Literal block-density / John-hull payment for the inner joint gate

The local Cordoba coefficient should not be bounded by a global Katz--Tao
constant.  On the selected block, its literal density cancels against the
literal winning hull.  After the tube-volume bounds are used, the only
geometric quantity left is

`(blockCard * blockDensity⁻¹)^(beta/2)`.

This is the normalized winning-hull volume which the endpoint hull/scale
reserve is supposed to pay.  The final theorem turns precisely that reserve
into the weak inner joint gate used by
`Family8ComparableRLocalKTWholeEq32ScalarV1`; no standalone Equation (46)
claim is introduced.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentBlockDensityHullReserveInnerJointV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8ComparableRLocalKTWholeEq32ScalarV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentBlockDensityJohnHullCancellationV1
open Family8SelectedParentCertifiedPlankCordobaActualJohnContainerV7
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The indexed volume of one literal selected greedy block is at most its
literal card times the standard radius-`rho` tube upper area. -/
theorem selectedParentBlock_familyVolume_le_card_mul_eight_sq
    (S : StickyScaleCover fine rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length) :
    familyVolume
        (selectedCoarseFamily S.activeCoarseFamily
          (blockAt S.activeCoarseFamily P k).fiber) <=
      ((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal) *
        (8 * (rho : ENNReal) ^ 2) := by
  rw [selectedCoarseFamily_volume]
  calc
    (∑ p ∈ (blockAt S.activeCoarseFamily P k).fiber,
        volume (S.activeCoarseFamily p : Set Space)) <=
      ∑ _p ∈ (blockAt S.activeCoarseFamily P k).fiber,
        8 * (rho : ENNReal) ^ 2 := by
      exact Finset.sum_le_sum fun p _hp => by
        change volume (S.coarse.tubes p.1).carrier <=
          8 * (rho : ENNReal) ^ 2
        exact (S.coarse.tubes p.1).volume_le_eight_mul_sq_of_le_half
          hrhoHalf
    _ = ((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal) *
        (8 * (rho : ENNReal) ^ 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul]


/-- The matching lower tube-area estimate on the same selected block. -/
theorem selectedParentBlock_card_mul_half_sq_le_familyVolume
    (S : StickyScaleCover fine rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length) :
    ((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal) *
        ((rho : ENNReal) ^ 2 / 2) <=
      familyVolume
        (selectedCoarseFamily S.activeCoarseFamily
          (blockAt S.activeCoarseFamily P k).fiber) := by
  rw [selectedCoarseFamily_volume]
  calc
    ((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal) *
        ((rho : ENNReal) ^ 2 / 2) =
      ∑ _p ∈ (blockAt S.activeCoarseFamily P k).fiber,
        (rho : ENNReal) ^ 2 / 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ <= ∑ p ∈ (blockAt S.activeCoarseFamily P k).fiber,
        volume (S.activeCoarseFamily p : Set Space) := by
      exact Finset.sum_le_sum fun p _hp => by
        change (rho : ENNReal) ^ 2 / 2 <=
          volume (S.coarse.tubes p.1).carrier
        exact (S.coarse.tubes p.1).half_sq_le_volume_of_le_half hrhoHalf

/-- The residual card divided by block density is no larger than the literal
winning hull volume measured in tube-area units. -/
theorem selectedParentBlock_card_mul_blockDensity_inv_le_hullVolume_div_area
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (hd0 : blockDensity S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k) ≠ 0)
    (hdTop : blockDensity S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k) ≠ ∞) :
    ((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal) *
        (blockDensity S.activeCoarseFamily
          (blockAt S.activeCoarseFamily P k))⁻¹ <=
      volume ((blockAt S.activeCoarseFamily P k).body : Set Space) /
        ((rho : ENNReal) ^ 2 / 2) := by
  let d := blockDensity S.activeCoarseFamily
    (blockAt S.activeCoarseFamily P k)
  let card := ((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal)
  let area := (rho : ENNReal) ^ 2 / 2
  let V := volume ((blockAt S.activeCoarseFamily P k).body : Set Space)
  have harea0 : area ≠ 0 := by
    dsimp only [area]
    exact ENNReal.div_ne_zero.mpr
      ⟨ENNReal.pow_ne_zero (ENNReal.coe_ne_zero.mpr hrho.ne') 2,
        by norm_num⟩
  have hareaTop : area ≠ ∞ := by
    dsimp only [area]
    exact ENNReal.div_ne_top
      (ENNReal.pow_ne_top ENNReal.coe_ne_top) (by norm_num)
  have hlower := selectedParentBlock_card_mul_half_sq_le_familyVolume
    S hrhoHalf P k
  have hdensity :=
    blockDensity_mul_hullVolume_eq_selectedParentBlock_familyVolume
      S hrho P k
  have hcancel : d * d⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by simpa only [d] using hd0)
      (by simpa only [d] using hdTop)
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl harea0) (Or.inl hareaTop)).2
  calc
    (card * d⁻¹) * area = (card * area) * d⁻¹ := by ac_rfl
    _ <= familyVolume
        (selectedCoarseFamily S.activeCoarseFamily
          (blockAt S.activeCoarseFamily P k).fiber) * d⁻¹ :=
      mul_le_mul' (by simpa only [card, area] using hlower) le_rfl
    _ = (d * V) * d⁻¹ := by
      rw [hdensity]
    _ = (d * d⁻¹) * V := by ac_rfl
    _ = V := by rw [hcancel, one_mul]
/-- The local density times the literal thresholded Cordoba numerator is
bounded by the same bucket Jacobian times the literal block card and tube
area.  The constant `16` is exactly the conversion
`8*rho^2 = 16*(rho^2/2)`. -/
theorem blockDensity_mul_thresholdedCordobaNumerator_le_jacobian_card_area
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int) :
    let d := blockDensity S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k)
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let J := affineJacobian (bucketNormalizedAffineEquiv e label)
    let card := ((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal)
    let area := (rho : ENNReal) ^ 2 / 2
    let G := certifiedPlankThresholdedAngleScaleCap 576 *
      (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3))
    d * G <= J *
      ((16 * certifiedPlankThresholdedAngleScaleCap 576 *
          (288 : ENNReal) ^ 3) * (card * area)) := by
  dsimp only
  let d := blockDensity S.activeCoarseFamily
    (blockAt S.activeCoarseFamily P k)
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let J := affineJacobian (bucketNormalizedAffineEquiv e label)
  let card := ((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal)
  let area := (rho : ENNReal) ^ 2 / 2
  let G := certifiedPlankThresholdedAngleScaleCap 576 *
    (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3))
  have hJohn :=
    blockDensity_mul_selectedParentBucketNormalizedJohnContainer_volume_le
      S hrho P k r hr label
  have hvolume := selectedParentBlock_familyVolume_le_card_mul_eight_sq
    S hrhoHalf P k
  have hcontainer :
      volume (selectedParentBucketNormalizedJohnContainer
        S hrho P k r label : Set Space) =
        (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3)) :=
    volume_selectedParentBucketNormalizedJohnContainer
      S hrho P k r label
  have harea :
      8 * (rho : ENNReal) ^ 2 =
        16 * ((rho : ENNReal) ^ 2 / 2) := by
    rw [div_eq_mul_inv]
    have hcancel : (2 : ENNReal)⁻¹ * 2 = 1 :=
      ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
    have hc : (2 : ENNReal)⁻¹ * 16 = 8 := by
      calc
        (2 : ENNReal)⁻¹ * 16 = ((2 : ENNReal)⁻¹ * 2) * 8 := by ring
        _ = 8 := by rw [hcancel, one_mul]
    calc
      8 * (rho : ENNReal) ^ 2 = (rho : ENNReal) ^ 2 * 8 := by ac_rfl
      _ = (rho : ENNReal) ^ 2 * ((2 : ENNReal)⁻¹ * 16) := by rw [hc]
      _ = 16 * ((rho : ENNReal) ^ 2 * (2 : ENNReal)⁻¹) := by ac_rfl
  calc
    d * G = certifiedPlankThresholdedAngleScaleCap 576 *
        (d * volume (selectedParentBucketNormalizedJohnContainer
          S hrho P k r label : Set Space)) := by
      rw [hcontainer]
      dsimp only [G]
      ac_rfl
    _ <= certifiedPlankThresholdedAngleScaleCap 576 *
        (J * ((288 : ENNReal) ^ 3 *
          familyVolume (selectedCoarseFamily S.activeCoarseFamily
            (blockAt S.activeCoarseFamily P k).fiber))) :=
      mul_le_mul' le_rfl (by simpa only [d, e, J] using hJohn)
    _ <= certifiedPlankThresholdedAngleScaleCap 576 *
        (J * ((288 : ENNReal) ^ 3 *
          (card * (8 * (rho : ENNReal) ^ 2)))) :=
      mul_le_mul' le_rfl
        (mul_le_mul' le_rfl (mul_le_mul' le_rfl (by
          simpa only [card] using hvolume)))
    _ = J * ((16 * certifiedPlankThresholdedAngleScaleCap 576 *
          (288 : ENNReal) ^ 3) * (card * area)) := by
      dsimp only [area]
      rw [harea]
      ac_rfl

/-- Pure scalar John/card conversion.  If the endpoint pays the normalized
hull ratio `(card/d)^(beta/2)` against the count-one inner factor, the exact
density split produces the weak inner joint gate at the literal block card.
-/
theorem localDensityInnerJoint_of_cardDensityHullReserve
    {delta a b : NNReal} {tubesPerPlank : Nat}
    {d geometricScale jacobian sourceDensity area johnLoss geometryLoss :
      ENNReal}
    {epsilon beta : Real}
    (hbeta0 : 0 <= beta) (hbetaOne : beta <= 1)
    (hd0 : d ≠ 0) (hdTop : d ≠ ∞)
    (hcard0 : (tubesPerPlank : ENNReal) ≠ 0)
    (hJohn : d * geometricScale <=
      jacobian * (johnLoss * ((tubesPerPlank : ENNReal) * area)))
    (hreserve :
      johnLoss *
          (((tubesPerPlank : ENNReal) * d⁻¹) ^ (beta / 2)) <=
        (sourceDensity * geometryLoss) *
          proposition66AInnerFactor delta a b 1 epsilon beta) :
    d ^ (1 - beta / 2) * geometricScale <=
      (jacobian * (sourceDensity * area) * geometryLoss) *
        proposition66AInnerFactor
          delta a b tubesPerPlank epsilon beta := by
  let m : ENNReal := (tubesPerPlank : ENNReal)
  let h : Real := beta / 2
  let p : Real := 1 - beta / 2
  have hh0 : 0 <= h := by dsimp only [h]; linarith
  have hp0 : 0 <= p := by dsimp only [p]; linarith
  have hm0 : m ≠ 0 := by simpa only [m] using hcard0
  have hmTop : m ≠ ∞ := by simp [m]
  have hdPower : d ^ p = d * d ^ (-h) := by
    have hpEq : p = 1 + (-h) := by
      dsimp only [p, h]
      ring
    calc
      d ^ p = d ^ (1 + (-h)) := by rw [hpEq]
      _ = d ^ (1 : Real) * d ^ (-h) := by
        rw [ENNReal.rpow_add _ _ hd0 hdTop]
      _ = d * d ^ (-h) := by rw [ENNReal.rpow_one]
  have hmSplit : m = m ^ p * m ^ h := by
    have hph : p + h = 1 := by
      dsimp only [p, h]
      ring
    calc
      m = m ^ (1 : Real) := (ENNReal.rpow_one m).symm
      _ = m ^ (p + h) := by rw [hph]
      _ = m ^ p * m ^ h := by
        rw [ENNReal.rpow_add _ _ hm0 hmTop]
  have hratioPower : (m * d⁻¹) ^ h = m ^ h * d ^ (-h) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hh0, ENNReal.inv_rpow,
      <- ENNReal.rpow_neg]
  have hmInvPower : m * d ^ (-h) = (m * d⁻¹) ^ h * m ^ p := by
    have hmSplitMul := congrArg (fun x : ENNReal => x * d ^ (-h)) hmSplit
    calc
      m * d ^ (-h) = (m ^ p * m ^ h) * d ^ (-h) := hmSplitMul
      _ = (m ^ h * d ^ (-h)) * m ^ p := by ac_rfl
      _ = (m * d⁻¹) ^ h * m ^ p := by rw [hratioPower]
  have hinnerCount :=
    proposition66AInnerFactor_eq_countOne_mul_card_rpow
      delta a b tubesPerPlank epsilon beta hbetaOne
  calc
    d ^ (1 - beta / 2) * geometricScale =
        (d * geometricScale) * d ^ (-h) := by
      rw [show 1 - beta / 2 = p by rfl, hdPower]
      ac_rfl
    _ <= (jacobian * (johnLoss * (m * area))) * d ^ (-h) :=
      mul_le_mul' (by simpa only [m] using hJohn) le_rfl
    _ = (jacobian * johnLoss * area) * (m * d ^ (-h)) := by
      ac_rfl
    _ = (jacobian * area) *
        ((johnLoss * (m * d⁻¹) ^ h) * m ^ p) := by
      rw [hmInvPower]
      ac_rfl
    _ <= (jacobian * area) *
        (((sourceDensity * geometryLoss) *
          proposition66AInnerFactor delta a b 1 epsilon beta) * m ^ p) :=
      mul_le_mul' le_rfl (mul_le_mul' (by
        simpa only [m, h] using hreserve) le_rfl)
    _ = (jacobian * (sourceDensity * area) * geometryLoss) *
        (proposition66AInnerFactor delta a b 1 epsilon beta *
          (tubesPerPlank : ENNReal) ^ (1 - beta / 2)) := by
      dsimp only [m, p]
      ac_rfl
    _ = (jacobian * (sourceDensity * area) * geometryLoss) *
        proposition66AInnerFactor
          delta a b tubesPerPlank epsilon beta := by
      rw [<- hinnerCount]

/-- Object-level specialization of the preceding scalar bridge.  Its sole
new input is the honest normalized-hull reserve on the already selected
`k` and `label`. -/
theorem selectedParent_blockDensity_innerJoint_of_hullReserve
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (sourceDensity geometryLoss : ENNReal)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    {epsilon beta : Real}
    (hbeta0 : 0 <= beta) (hbetaOne : beta <= 1)
    (hd0 : blockDensity S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k) ≠ 0)
    (hdTop : blockDensity S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k) ≠ ∞)
    (hreserve :
      let d := blockDensity S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P k)
      let card := ((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal)
      (16 * certifiedPlankThresholdedAngleScaleCap 576 *
          (288 : ENNReal) ^ 3) * (card * d⁻¹) ^ (beta / 2) <=
        (sourceDensity * geometryLoss) *
          proposition66AInnerFactor rho
            (bucketShortA label) (bucketShortB label) 1 epsilon beta) :
    let d := blockDensity S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k)
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let sourceFactor := affineJacobian (bucketNormalizedAffineEquiv e label) *
      (sourceDensity * ((rho : ENNReal) ^ 2 / 2))
    let G := certifiedPlankThresholdedAngleScaleCap 576 *
      (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3))
    d ^ (1 - beta / 2) * G <=
      (sourceFactor * geometryLoss) *
        proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label)
          (blockAt S.activeCoarseFamily P k).fiber.card epsilon beta := by
  dsimp only at hreserve ⊢
  apply localDensityInnerJoint_of_cardDensityHullReserve
    hbeta0 hbetaOne hd0 hdTop
  · exact_mod_cast Finset.card_ne_zero.mpr
      (blockAt S.activeCoarseFamily P k).fiber_nonempty
  · simpa only using
      blockDensity_mul_thresholdedCordobaNumerator_le_jacobian_card_area
        S hrho hrhoHalf P k r hr label
  · simpa only using hreserve

#print axioms selectedParentBlock_familyVolume_le_card_mul_eight_sq
#print axioms
  blockDensity_mul_thresholdedCordobaNumerator_le_jacobian_card_area
#print axioms localDensityInnerJoint_of_cardDensityHullReserve
#print axioms selectedParent_blockDensity_innerJoint_of_hullReserve

end
end Family8SelectedParentBlockDensityHullReserveInnerJointV1
