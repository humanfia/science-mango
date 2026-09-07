import Family8Grounding.Family8SelectedOccurrenceNormalizedOuterScaleBridgeV1
import Family8Grounding.Family8SelectedParentAngleBucketLogarithmicLossV2
import Family8Grounding.Family8SelectedParentJohnPlankSideWidthBridgeV5
import Family8Grounding.Family8Prop66InnerScaleMismatchAbsorptionV1
import Mathlib.Tactic

/-!
# Selected-occurrence outer/inner label mismatch as an explicit power loss

The normalized outer greedy winner and the selected parent inside the
winning occurrence are produced by different John constructions.  Their
dyadic side labels therefore must not be identified.  This file records the
honest relation that is available: both normalized side pairs lie between a
positive geometric floor and one.

For the endpoint-facing mismatch

`prop66InnerScaleMismatchLoss outerA outerB innerA innerB beta`,

the two independent floors give the branch-free bound

`outerFloor^(-beta) * innerFloor^(2 * beta - 2)`.

For the actual labels, the outer floor is `deltaOuter / 576`.  The inner
selected-parent floor proved below is `rho / 11943936 = rho / 3456^2`.
There is no assertion that the two labels agree, and no fixed or merely
polylogarithmic mismatch bound is claimed: without an additional
cross-scale comparability theorem the power dependence on the geometric
floors is genuine.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8SelectedOccurrenceOuterInnerScaleMismatchPowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8Prop66InnerScaleMismatchAbsorptionV1
open Family8SelectedOccurrenceNormalizedOuterScaleBridgeV1
open Family8SelectedParentAngleBucketLogarithmicLossV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

/-! ## Pure scalar mismatch bound -/

/-- A branch-free bound for the scale mismatch used by the actual
selected-occurrence Equation (46) seam.

The hypotheses only place the outer and inner side pairs in two possibly
different intervals `[outerFloor, 1]` and `[innerFloor, 1]`.  In particular,
no ordering between an outer side and an inner side is assumed. -/
theorem prop66InnerScaleMismatchLoss_le_separate_floor_rpow
    {outerFloor innerFloor outerA outerB innerA innerB : NNReal}
    {beta : Real}
    (_houterFloor : 0 < outerFloor)
    (hinnerFloor : 0 < innerFloor)
    (houterFloorA : outerFloor <= outerA)
    (houterAB : outerA <= outerB)
    (houterBOne : outerB <= 1)
    (hinnerFloorA : innerFloor <= innerA)
    (hinnerAB : innerA <= innerB)
    (hinnerBOne : innerB <= 1)
    (hbeta : 0 <= beta)
    (hbetaOne : beta <= 1) :
    prop66InnerScaleMismatchLoss outerA outerB innerA innerB beta <=
      (outerFloor : ENNReal) ^ (-beta) *
        (innerFloor : ENNReal) ^ (2 * beta - 2) := by
  let FO : ENNReal := outerFloor
  let FI : ENNReal := innerFloor
  let AO : ENNReal := outerA
  let BO : ENNReal := outerB
  let AI : ENNReal := innerA
  let BI : ENNReal := innerB
  let r : Real := 1 - 2 * beta
  let s : Real := 1 - beta
  have hs : 0 <= s := by
    dsimp only [s]
    linarith
  have hFI0 : FI ≠ 0 := ENNReal.coe_ne_zero.mpr hinnerFloor.ne'
  have hAI0 : AI ≠ 0 := ENNReal.coe_ne_zero.mpr
    (hinnerFloor.trans_le hinnerFloorA).ne'
  have hBI0 : BI ≠ 0 := ENNReal.coe_ne_zero.mpr
    (hinnerFloor.trans_le (hinnerFloorA.trans hinnerAB)).ne'
  have hFITop : FI ≠ ∞ := ENNReal.coe_ne_top
  have hAOTop : AO ≠ ∞ := ENNReal.coe_ne_top
  have hBOTop : BO ≠ ∞ := ENNReal.coe_ne_top
  have hFOAO : FO <= AO := ENNReal.coe_le_coe.mpr houterFloorA
  have hFIAI : FI <= AI := ENNReal.coe_le_coe.mpr hinnerFloorA
  have hFIBI : FI <= BI := ENNReal.coe_le_coe.mpr
    (hinnerFloorA.trans hinnerAB)
  have hAOOne : AO <= 1 := ENNReal.coe_le_coe.mpr
    (houterAB.trans houterBOne)
  have hBOOne : BO <= 1 := ENNReal.coe_le_coe.mpr houterBOne
  have hAIOne : AI <= 1 := ENNReal.coe_le_coe.mpr
    (hinnerAB.trans hinnerBOne)
  have hdiv (X Y : ENNReal) (hXTop : X ≠ ∞)
      (hY0 : Y ≠ 0) (t : Real) :
      (X / Y) ^ t = X ^ t * Y ^ (-t) := by
    rw [div_eq_mul_inv,
      ENNReal.mul_rpow_of_ne_top hXTop (ENNReal.inv_ne_top.mpr hY0) t,
      ENNReal.inv_rpow, <- ENNReal.rpow_neg]
  have houterAExp : AO ^ r <= FO ^ (-beta) := by
    have hfirst : AO ^ r <= AO ^ (-beta) := by
      apply ENNReal.rpow_le_rpow_of_exponent_ge hAOOne
      dsimp only [r]
      linarith
    refine hfirst.trans ?_
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv'
      (ENNReal.rpow_le_rpow hFOAO hbeta)
  have houterBExp : BO ^ s <= 1 :=
    ENNReal.rpow_le_one hBOOne hs
  have hinnerAExp : AI ^ (-r) <= FI ^ (beta - 1) := by
    have hfirst : AI ^ (-r) <= AI ^ (beta - 1) := by
      apply ENNReal.rpow_le_rpow_of_exponent_ge hAIOne
      dsimp only [r]
      linarith
    refine hfirst.trans ?_
    rw [show beta - 1 = -s by dsimp only [s]; ring,
      ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv'
      (ENNReal.rpow_le_rpow hFIAI hs)
  have hinnerBExp : BI ^ (-s) <= FI ^ (beta - 1) := by
    rw [ENNReal.rpow_neg,
      show beta - 1 = -s by dsimp only [s]; ring,
      ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv'
      (ENNReal.rpow_le_rpow hFIBI hs)
  have hinnerCombine :
      FI ^ (beta - 1) * FI ^ (beta - 1) =
        FI ^ (2 * beta - 2) := by
    rw [<- ENNReal.rpow_add (beta - 1) (beta - 1) hFI0 hFITop]
    congr 1
    ring
  unfold prop66InnerScaleMismatchLoss
  change
    (AO / AI) ^ r * (BO / BI) ^ s <=
      FO ^ (-beta) * FI ^ (2 * beta - 2)
  rw [hdiv AO AI hAOTop hAI0 r, hdiv BO BI hBOTop hBI0 s]
  calc
    (AO ^ r * AI ^ (-r)) * (BO ^ s * BI ^ (-s)) =
        (AO ^ r * BO ^ s) * (AI ^ (-r) * BI ^ (-s)) := by
          ac_rfl
    _ <= (FO ^ (-beta) * 1) *
        (FI ^ (beta - 1) * FI ^ (beta - 1)) :=
      mul_le_mul'
        (mul_le_mul' houterAExp houterBExp)
        (mul_le_mul' hinnerAExp hinnerBExp)
    _ = FO ^ (-beta) * FI ^ (2 * beta - 2) := by
      rw [mul_one, hinnerCombine]

/-- A deliberately coarser integer-power corollary.  This is useful for
ledgers which do not retain `beta`, but the preceding beta-dependent bound
is substantially cheaper and should be preferred at the endpoint. -/
theorem prop66InnerScaleMismatchLoss_le_separate_floor_integer_power
    {outerFloor innerFloor outerA outerB innerA innerB : NNReal}
    {beta : Real}
    (houterFloor : 0 < outerFloor)
    (hinnerFloor : 0 < innerFloor)
    (houterFloorA : outerFloor <= outerA)
    (houterAB : outerA <= outerB)
    (houterBOne : outerB <= 1)
    (hinnerFloorA : innerFloor <= innerA)
    (hinnerAB : innerA <= innerB)
    (hinnerBOne : innerB <= 1)
    (hbeta : 0 <= beta)
    (hbetaOne : beta <= 1) :
    prop66InnerScaleMismatchLoss outerA outerB innerA innerB beta <=
      (outerFloor : ENNReal) ^ (-1 : Real) *
        (innerFloor : ENNReal) ^ (-2 : Real) := by
  have hmain := prop66InnerScaleMismatchLoss_le_separate_floor_rpow
    houterFloor hinnerFloor houterFloorA houterAB houterBOne
    hinnerFloorA hinnerAB hinnerBOne hbeta hbetaOne
  have houterFloorOne : (outerFloor : ENNReal) <= 1 :=
    ENNReal.coe_le_coe.mpr (houterFloorA.trans (houterAB.trans houterBOne))
  have hinnerFloorOne : (innerFloor : ENNReal) <= 1 :=
    ENNReal.coe_le_coe.mpr (hinnerFloorA.trans (hinnerAB.trans hinnerBOne))
  calc
    prop66InnerScaleMismatchLoss outerA outerB innerA innerB beta <=
        (outerFloor : ENNReal) ^ (-beta) *
          (innerFloor : ENNReal) ^ (2 * beta - 2) := hmain
    _ <= (outerFloor : ENNReal) ^ (-1 : Real) *
        (innerFloor : ENNReal) ^ (-2 : Real) := by
      apply mul_le_mul'
      · apply ENNReal.rpow_le_rpow_of_exponent_ge houterFloorOne
        linarith
      · apply ENNReal.rpow_le_rpow_of_exponent_ge hinnerFloorOne
        linarith

/-! ## The actual selected-parent normalized width floor -/

/-- An occupied selected-parent label has normalized short width at least
`rho / 11943936`.  The auxiliary contraction `r` cancels exactly.

This is the width-floor counterpart of
`bucketShortB_div_bucketShortA_le_selectedParentRatio`; it uses the same
raw side floor `r*rho/3456` and raw side ceiling `1728*r`, together with the
factor-two dyadic band. -/
theorem selectedParent_rho_div_11943936_le_bucketShortA
    {delta rho : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {fine : UniformTubeFamily delta index}
    (hfineContained : forall i, (fine.tubes i).carrier <=
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (hoccupied : label ∈ occupiedWeightBuckets
      (Finset.univ : Finset
        {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
      (fun p => sideShapeLabel
        (selectedParentLongRelabeledSide
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho p))) :
    rho / 11943936 <= bucketShortA label := by
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let side : {p // p ∈ B} -> Fin 3 -> NNReal := fun p =>
    selectedParentLongRelabeledSide e S B hrho p
  rcases mem_occupiedWeightBuckets_iff.mp hoccupied with
    ⟨p, _hp, hpLabel⟩
  have hpos : forall i, 0 < side p i := by
    intro i
    exact selectedParentLongRelabeledSide_pos e S B hrho p i
  have hband0 := sideShapeUpper_half_lt_and_le hpos (0 : Fin 3)
  have hband1 := sideShapeUpper_half_lt_and_le hpos (1 : Fin 3)
  have hband2 := sideShapeUpper_half_lt_and_le hpos (2 : Fin 3)
  change sideShapeLabel (side p) = label at hpLabel
  rw [hpLabel] at hband0 hband1 hband2
  have hfloor0 : selectedParentSideFloor rho r <= side p 0 :=
    selectedParentContractedLongRelabeledSide_floor
      hfineContained S hrho hrhoOne P k r hr p 0
  have hfloor1 : selectedParentSideFloor rho r <= side p 1 :=
    selectedParentContractedLongRelabeledSide_floor
      hfineContained S hrho hrhoOne P k r hr p 1
  have hside2Upper : side p 2 <= 1728 * r :=
    selectedParentContractedLongRelabeledSide_le
      S hrho P k r hr p 2
  have hU0Lower : selectedParentSideFloor rho r <=
      sideShapeUpper label 0 := hfloor0.trans hband0.2
  have hU1Lower : selectedParentSideFloor rho r <=
      sideShapeUpper label 1 := hfloor1.trans hband1.2
  have hU2Upper : sideShapeUpper label 2 <= 3456 * r := by
    apply le_of_lt
    nlinarith [hband2.1, hside2Upper]
  have hU2Pos : 0 < sideShapeUpper label 2 :=
    sideShapeUpper_pos label 2
  have hscale :
      rho * (3456 * r) =
        selectedParentSideFloor rho r * 11943936 := by
    apply NNReal.eq
    norm_num [selectedParentSideFloor, NNReal.coe_div, NNReal.coe_mul]
    ring
  by_cases h01 : sideShapeUpper label 0 <= sideShapeUpper label 1
  · simp only [bucketShortA, if_pos h01]
    apply (div_le_div_iff₀ (by norm_num : (0 : NNReal) < 11943936)
      hU2Pos).2
    calc
      rho * sideShapeUpper label 2 <= rho * (3456 * r) :=
        mul_le_mul' le_rfl hU2Upper
      _ = selectedParentSideFloor rho r * 11943936 := hscale
      _ <= sideShapeUpper label 0 * 11943936 :=
        mul_le_mul' hU0Lower le_rfl
  · simp only [bucketShortA, if_neg h01]
    apply (div_le_div_iff₀ (by norm_num : (0 : NNReal) < 11943936)
      hU2Pos).2
    calc
      rho * sideShapeUpper label 2 <= rho * (3456 * r) :=
        mul_le_mul' le_rfl hU2Upper
      _ = selectedParentSideFloor rho r * 11943936 := hscale
      _ <= sideShapeUpper label 1 * 11943936 :=
        mul_le_mul' hU1Lower le_rfl

/-- Occupancy also certifies that the inner normalized long coordinate is
the denominator, hence the larger short endpoint is at most one. -/
theorem selectedParent_occupied_bucketShortB_le_one
    {delta rho : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {fine : UniformTubeFamily delta index}
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (hoccupied : label ∈ occupiedWeightBuckets
      (Finset.univ : Finset
        {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
      (fun p => sideShapeLabel
        (selectedParentLongRelabeledSide
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho p))) :
    bucketShortB label <= 1 := by
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let side : {p // p ∈ B} -> Fin 3 -> NNReal := fun p =>
    selectedParentLongRelabeledSide e S B hrho p
  rcases mem_occupiedWeightBuckets_iff.mp hoccupied with
    ⟨p, _hp, hpLabel⟩
  have hpos : forall i, 0 < side p i := by
    intro i
    exact selectedParentLongRelabeledSide_pos e S B hrho p i
  have h02 := sideShapeUpper_le_of_side_le hpos
    (selectedParentLongRelabeledSide_le_two e S B hrho p 0)
  have h12 := sideShapeUpper_le_of_side_le hpos
    (selectedParentLongRelabeledSide_le_two e S B hrho p 1)
  change sideShapeLabel (side p) = label at hpLabel
  rw [hpLabel] at h02 h12
  exact bucketShortB_le_one label h02 h12

/-! ## A relation between the two genuinely distinct labels -/

/-- The relation needed by Proposition 6.6 is two independent normalized
scale envelopes, not equality of labels. -/
structure Prop66OuterInnerLabelScaleRelation
    (outerFloor innerFloor : NNReal)
    (labelOuter labelInner : Fin 3 -> Int) : Prop where
  outerFloor_pos : 0 < outerFloor
  innerFloor_pos : 0 < innerFloor
  outerFloor_le_shortA : outerFloor <= bucketShortA labelOuter
  innerFloor_le_shortA : innerFloor <= bucketShortA labelInner
  outerShortB_le_one : bucketShortB labelOuter <= 1
  innerShortB_le_one : bucketShortB labelInner <= 1

/-- The label relation immediately supplies the endpoint-facing mismatch
bound, with the actual outer and inner floors retained separately. -/
theorem Prop66OuterInnerLabelScaleRelation.innerMismatchLoss_le
    {outerFloor innerFloor : NNReal}
    {labelOuter labelInner : Fin 3 -> Int}
    (hrel : Prop66OuterInnerLabelScaleRelation
      outerFloor innerFloor labelOuter labelInner)
    {beta : Real} (hbeta : 0 <= beta) (hbetaOne : beta <= 1) :
    prop66InnerScaleMismatchLoss
        (bucketShortA labelOuter) (bucketShortB labelOuter)
        (bucketShortA labelInner) (bucketShortB labelInner) beta <=
      (outerFloor : ENNReal) ^ (-beta) *
        (innerFloor : ENNReal) ^ (2 * beta - 2) := by
  exact prop66InnerScaleMismatchLoss_le_separate_floor_rpow
    hrel.outerFloor_pos hrel.innerFloor_pos
    hrel.outerFloor_le_shortA (bucketShortA_le_bucketShortB labelOuter)
    hrel.outerShortB_le_one
    hrel.innerFloor_le_shortA (bucketShortA_le_bucketShortB labelInner)
    hrel.innerShortB_le_one hbeta hbetaOne

/-- A common outer winner label has normalized `bucketShortB <= 1`.
This is independent of the unit-ball support needed for its positive floor. -/
theorem selectedOccurrenceNormalizedOuter_bucketShortB_le_one
    {deltaOuter : NNReal} {outerIndex : Type}
    [Fintype outerIndex] [DecidableEq outerIndex]
    {fineOuter : UniformTubeFamily deltaOuter outerIndex}
    {activeOuter : Finset outerIndex}
    (Pouter : GreedyDensityPartition fineOuter.bodyFamily
      (hullCandidates activeOuter)
      (hullContainer fineOuter.bodyFamily) activeOuter)
    (hdeltaOuter : 0 < deltaOuter)
    (labelOuter : Fin 3 -> Int)
    (Rside : Finset (Fin (blocks fineOuter.bodyFamily Pouter).length))
    (hRside : Rside.Nonempty)
    (hlabelOuter : forall k, k ∈ Rside ->
      sideShapeLabel (winnerLongSide Pouter hdeltaOuter k) = labelOuter) :
    bucketShortB labelOuter <= 1 := by
  obtain ⟨k, hk⟩ := hRside
  have hpos : forall j, 0 < winnerLongSide Pouter hdeltaOuter k j :=
    fun j => winnerLongSide_pos Pouter hdeltaOuter k j
  have h02 := sideShapeUpper_le_of_side_le hpos
    (winnerLongSide_le_two Pouter hdeltaOuter k 0)
  have h12 := sideShapeUpper_le_of_side_le hpos
    (winnerLongSide_le_two Pouter hdeltaOuter k 1)
  rw [hlabelOuter k hk] at h02 h12
  exact bucketShortB_le_one labelOuter h02 h12

/-- The actual outer winner label and actual occupied selected-parent label
satisfy the two-floor relation.  The theorem intentionally has independent
outer and inner ambient families: no definitional identification of their
John choices or labels is required. -/
theorem selectedOuterWinner_innerSelectedParent_labelScaleRelation
    {deltaOuter : NNReal} {outerIndex : Type}
    [Fintype outerIndex] [DecidableEq outerIndex]
    {fineOuter : UniformTubeFamily deltaOuter outerIndex}
    {activeOuter : Finset outerIndex}
    (Pouter : GreedyDensityPartition fineOuter.bodyFamily
      (hullCandidates activeOuter)
      (hullContainer fineOuter.bodyFamily) activeOuter)
    (hdeltaOuter : 0 < deltaOuter)
    (labelOuter : Fin 3 -> Int)
    (Rside : Finset (Fin (blocks fineOuter.bodyFamily Pouter).length))
    (hRside : Rside.Nonempty)
    (hlabelOuter : forall k, k ∈ Rside ->
      sideShapeLabel (winnerLongSide Pouter hdeltaOuter k) = labelOuter)
    (hfineOuterContained : forall i, i ∈ activeOuter ->
      (fineOuter.tubes i).carrier <= Metric.closedBall (0 : Space) 1)
    {delta rho : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {fine : UniformTubeFamily delta index}
    (hfineContained : forall i, (fine.tubes i).carrier <=
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (labelInner : Fin 3 -> Int)
    (hoccupied : labelInner ∈ occupiedWeightBuckets
      (Finset.univ : Finset
        {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
      (fun p => sideShapeLabel
        (selectedParentLongRelabeledSide
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho p))) :
    Prop66OuterInnerLabelScaleRelation
      (deltaOuter / 576) (rho / 11943936) labelOuter labelInner := by
  refine
    { outerFloor_pos := div_pos hdeltaOuter (by norm_num)
      innerFloor_pos := div_pos hrho (by norm_num)
      outerFloor_le_shortA := ?_
      innerFloor_le_shortA := ?_
      outerShortB_le_one := ?_
      innerShortB_le_one := ?_ }
  · exact selectedOccurrenceNormalizedOuter_delta_div_576_le_bucketShortA
      Pouter hdeltaOuter labelOuter Rside hRside hlabelOuter
      hfineOuterContained
  · exact selectedParent_rho_div_11943936_le_bucketShortA
      hfineContained S hrho hrhoOne P k r hr labelInner hoccupied
  · exact selectedOccurrenceNormalizedOuter_bucketShortB_le_one
      Pouter hdeltaOuter labelOuter Rside hRside hlabelOuter
  · exact selectedParent_occupied_bucketShortB_le_one
      S hrho P k r hr labelInner hoccupied

/-- Direct endpoint form: the actual label mismatch is an explicit power
of the two geometric floors, with no side-label equality hypothesis. -/
theorem selectedOuterWinner_innerSelectedParent_innerMismatchLoss_le
    {deltaOuter : NNReal} {outerIndex : Type}
    [Fintype outerIndex] [DecidableEq outerIndex]
    {fineOuter : UniformTubeFamily deltaOuter outerIndex}
    {activeOuter : Finset outerIndex}
    (Pouter : GreedyDensityPartition fineOuter.bodyFamily
      (hullCandidates activeOuter)
      (hullContainer fineOuter.bodyFamily) activeOuter)
    (hdeltaOuter : 0 < deltaOuter)
    (labelOuter : Fin 3 -> Int)
    (Rside : Finset (Fin (blocks fineOuter.bodyFamily Pouter).length))
    (hRside : Rside.Nonempty)
    (hlabelOuter : forall k, k ∈ Rside ->
      sideShapeLabel (winnerLongSide Pouter hdeltaOuter k) = labelOuter)
    (hfineOuterContained : forall i, i ∈ activeOuter ->
      (fineOuter.tubes i).carrier <= Metric.closedBall (0 : Space) 1)
    {delta rho : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {fine : UniformTubeFamily delta index}
    (hfineContained : forall i, (fine.tubes i).carrier <=
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (labelInner : Fin 3 -> Int)
    (hoccupied : labelInner ∈ occupiedWeightBuckets
      (Finset.univ : Finset
        {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
      (fun p => sideShapeLabel
        (selectedParentLongRelabeledSide
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho p)))
    {beta : Real} (hbeta : 0 <= beta) (hbetaOne : beta <= 1) :
    prop66InnerScaleMismatchLoss
        (bucketShortA labelOuter) (bucketShortB labelOuter)
        (bucketShortA labelInner) (bucketShortB labelInner) beta <=
      (((deltaOuter / 576 : NNReal) : ENNReal) ^ (-beta)) *
        (((rho / 11943936 : NNReal) : ENNReal) ^ (2 * beta - 2)) := by
  have hrel := selectedOuterWinner_innerSelectedParent_labelScaleRelation
    Pouter hdeltaOuter labelOuter Rside hRside hlabelOuter
    hfineOuterContained hfineContained S hrho hrhoOne P k r hr
    labelInner hoccupied
  exact hrel.innerMismatchLoss_le hbeta hbetaOne

#print axioms prop66InnerScaleMismatchLoss_le_separate_floor_rpow
#print axioms prop66InnerScaleMismatchLoss_le_separate_floor_integer_power
#print axioms selectedParent_rho_div_11943936_le_bucketShortA
#print axioms selectedParent_occupied_bucketShortB_le_one
#print axioms Prop66OuterInnerLabelScaleRelation.innerMismatchLoss_le
#print axioms selectedOccurrenceNormalizedOuter_bucketShortB_le_one
#print axioms selectedOuterWinner_innerSelectedParent_labelScaleRelation
#print axioms selectedOuterWinner_innerSelectedParent_innerMismatchLoss_le

end

end Family8SelectedOccurrenceOuterInnerScaleMismatchPowerV1
