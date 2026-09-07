import Family8Grounding.Family8LongSeparatedBufferedCompatiblePairV1
import Family8Grounding.Family8FrostmanAmbientEnlargementV1

/-!
# Frostman transfer through the genuine long-separated buffered pair

The upper-parent buffer has an explicit finite-family ambient-volume loss.
This file transports upper Frostman control through that enlargement and then
feeds the resulting cover to the compatible-pair C-uniform theorem.  The loss
is geometric and scale-local; no `delta^-2` captured-tube-box bound is used.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8LongSeparatedBufferedAdjacentFrostmanV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CompatibleStickyScalePairCUniformFrostmanV1
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8FrostmanAmbientEnlargementV1
open Family8LongSeparatedBufferedCompatiblePairV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta r R : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {lower : StickyScaleCover fine r}
  {upper : StickyScaleCover fine R}

/-- Exact uniform ambient-volume loss for buffering the finite upper family. -/
def bufferedUpperAmbientLoss
    (upper : StickyScaleCover fine R) (q : NNReal) : ENNReal :=
  ⨆ k : Fin upper.coarseCard,
    volume (((upper.coarse.tubes k).buffer q).carrier) /
      volume ((upper.coarse.tubes k).carrier)

/-- Every buffered upper tube pays at most the displayed finite-family loss. -/
theorem bufferedUpper_volume_le_ambientLoss_mul
    (upper : StickyScaleCover fine R) (q : NNReal)
    (hR : 0 < R) (k : Fin upper.coarseCard) :
    volume (((upper.coarse.tubes k).buffer q).carrier) <=
      bufferedUpperAmbientLoss upper q *
        volume ((upper.coarse.tubes k).carrier) := by
  have hvolume0 : volume ((upper.coarse.tubes k).carrier) ≠ 0 :=
    ne_of_gt ((upper.coarse.tubes k).volume_pos hR)
  have hvolumeTop : volume ((upper.coarse.tubes k).carrier) ≠ ∞ :=
    (upper.coarse.tubes k).volume_lt_top.ne
  calc
    volume (((upper.coarse.tubes k).buffer q).carrier) =
        (volume (((upper.coarse.tubes k).buffer q).carrier) /
          volume ((upper.coarse.tubes k).carrier)) *
            volume ((upper.coarse.tubes k).carrier) :=
      (ENNReal.div_mul_cancel hvolume0 hvolumeTop).symm
    _ <= bufferedUpperAmbientLoss upper q *
        volume ((upper.coarse.tubes k).carrier) := by
      exact mul_le_mul' (le_iSup (fun l : Fin upper.coarseCard =>
        volume (((upper.coarse.tubes l).buffer q).carrier) /
          volume ((upper.coarse.tubes l).carrier)) k) le_rfl

/-- Frostman control survives buffering the upper coarse tubes with precisely
the finite-family ambient-volume loss. -/
theorem bufferedUpperScaleCover_isFrostmanAtScale
    (upper : StickyScaleCover fine R) (q : NNReal)
    (hR : 0 < R) {baseError : ENNReal}
    (hupper : StickyScaleCover.IsFrostmanAtScale upper baseError) :
    StickyScaleCover.IsFrostmanAtScale (bufferedUpperScaleCover upper q)
      (bufferedUpperAmbientLoss upper q * baseError) := by
  intro k hk K hK
  have hraw : IsFrostmanIn baseError (upper.fiberFamily k)
      (upper.coarse.tubes k).body := by
    apply (isFrostmanIn_iff_concentration_le).2
    exact ⟨upper.fiber_carrier_subset_parent k, hupper k hk⟩
  have hbuffered :
      IsFrostmanIn (bufferedUpperAmbientLoss upper q * baseError)
        (upper.fiberFamily k) ((upper.coarse.tubes k).buffer q).body := by
    exact isFrostmanIn_enlarge_ambient hraw
      (by
        simpa only [Tube.coe_body] using
          Tube.carrier_subset_buffer (upper.coarse.tubes k) q)
      (by
        simpa only [Tube.coe_body] using
          bufferedUpper_volume_le_ambientLoss_mul upper q hR k)
  change concentration (upper.fiberFamily k) K <=
    (bufferedUpperAmbientLoss upper q * baseError) *
      concentration (upper.fiberFamily k)
        ((upper.coarse.tubes k).buffer q).body
  have hK' : (K : Set Space) ⊆
      ((upper.coarse.tubes k).buffer q).carrier := by
    change (K : Set Space) ⊆ ((upper.coarse.tubes k).buffer q).carrier at hK
    exact hK
  exact (isFrostmanIn_iff_concentration_le).1 hbuffered |>.2 K
    (by simpa only [Tube.coe_body] using hK')

/-- The resulting literal interval cover has the desired adjacent normalized
Frostman bound. -/
theorem longSeparated_intervalCover_isFrostmanAtScale
    (hFine : fine.refinement.refined.Nonempty)
    (hr : 0 < r) (hsep : 4 * r <= R)
    (hpartition : IsDoubledParentPartitioning upper)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrHalf : r <= (2 : NNReal)⁻¹)
    {baseError uniformity : ENNReal}
    (huniform : IsCUniform lower uniformity)
    (hupper : StickyScaleCover.IsFrostmanAtScale upper baseError) :
    StickyScaleCover.IsFrostmanAtScale
      (longSeparatedBufferedPair (lower := lower) (upper := upper)
        hFine hr hsep hpartition).intervalCover
      ((bufferedUpperAmbientLoss upper (4 * r) * baseError) *
        ((16 * uniformity) * 16)) := by
  have hfourPos : 0 < 4 * r := by positivity
  have hR : 0 < R := hfourPos.trans_le hsep
  exact
    CompatibleStickyScalePair.intervalCover_isFrostmanAtScale_of_upperFrostman_cUniform
      (longSeparatedBufferedPair (lower := lower) (upper := upper)
        hFine hr hsep hpartition)
      hdeltaPos hdeltaHalf hrHalf huniform
      (bufferedUpperScaleCover_isFrostmanAtScale upper (4 * r) hR hupper)

#print axioms bufferedUpper_volume_le_ambientLoss_mul
#print axioms bufferedUpperScaleCover_isFrostmanAtScale
#print axioms longSeparated_intervalCover_isFrostmanAtScale

end
end Family8LongSeparatedBufferedAdjacentFrostmanV1
