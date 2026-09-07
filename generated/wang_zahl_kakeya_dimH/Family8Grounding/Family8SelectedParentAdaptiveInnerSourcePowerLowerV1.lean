import Family8Grounding.Family8SelectedParentAdaptiveInnerSourcePowerReserveV1
import Mathlib.Tactic

/-!
# A genuine delta-power lower bound for the actual adaptive inner factor

The prior source-power reserve was stated in the loss direction
`C * R <= delta^(-p) * inner`.  On an occupied selected-parent bucket, the
same active coarse family contains an actual positive-volume tube.  Hence an
`IsKatzTao C` certificate forces `1 <= C`.  Cancelling the explicit delta
power therefore gives the directly consumable lower bound
`delta^p * R <= inner`, with no lower-bound premise on `C`.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentAdaptiveInnerSourcePowerLowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8SelectedParentAdaptiveInnerSourcePowerReserveV1
open Family8SelectedParentAdaptiveInnerSourceReserveV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
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

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- An occupied bucket supplies a positive-volume active coarse member, so
any Katz--Tao constant for the actual active coarse family is at least one. -/
theorem one_le_sourceKatzTaoConstant_of_selectedBucketOccupied
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (hoccupied : SelectedBucketOccupied S hrho P k r hr label)
    (C : ENNReal) (hKT : IsKatzTao C S.activeCoarseFamily) :
    (1 : ENNReal) ≤ C := by
  classical
  obtain ⟨p, _hp, _hlabel⟩ := mem_occupiedWeightBuckets_iff.mp
    (by simpa only [SelectedBucketOccupied] using hoccupied)
  let i : ActiveParentIndex S := p.1
  have hvolPos : 0 < volume (S.activeCoarseFamily i : Set Space) := by
    change 0 < volume (S.coarse.tubes i.1).carrier
    exact (S.coarse.tubes i.1).volume_pos hrho
  have hi : i ∈ containedIndices S.activeCoarseFamily
      (S.activeCoarseFamily i) :=
    (mem_containedIndices S.activeCoarseFamily
      (S.activeCoarseFamily i) i).2 Set.Subset.rfl
  have hvolTop : volume (S.activeCoarseFamily i : Set Space) < ∞ :=
    (S.activeCoarseFamily i).isCompact.measure_lt_top
  have hmass : volume (S.activeCoarseFamily i : Set Space) ≤
      ∑ j ∈ containedIndices S.activeCoarseFamily
        (S.activeCoarseFamily i),
          volume (S.activeCoarseFamily j : Set Space) :=
    Finset.single_le_sum
      (fun j _hj => (show (0 : ENNReal) ≤
        volume (S.activeCoarseFamily j : Set Space) from bot_le)) hi
  have hconc : (1 : ENNReal) ≤
      concentration S.activeCoarseFamily (S.activeCoarseFamily i) := by
    unfold concentration
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hvolPos.ne') (Or.inl hvolTop.ne)).2
    simpa using hmass
  exact hconc.trans
    ((isKatzTao_iff_concentration_le.mp hKT) (S.activeCoarseFamily i))

/-- The exact delta-power gain obtained from the actual source KT constant
and the selected bucket's scale/aspect reserve. -/
theorem selectedParent_deltaBetaHalf_mul_scaleReserve_le_adaptiveActualInnerFactor
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (hoccupied : SelectedBucketOccupied S hrho P k r hr label)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hsmallPacking : selectedParentCenteredHalfPostAdaptiveProxyScale
      delta rho r label / 8 ≤ (1 / 100 : NNReal))
    (C : ENNReal) (coarseExponent epsilon beta : Real)
    (hKT : IsKatzTao C S.activeCoarseFamily)
    (hCpower : C ≤ (delta : ENNReal) ^ (-coarseExponent))
    (hbeta : 0 ≤ beta) (hbetaTwo : beta ≤ 2) :
    (delta : ENNReal) ^ (coarseExponent * (beta / 2)) *
      ((rho : ENNReal) ^ (-epsilon / 2) *
        ((bucketShortB label : ENNReal) /
          (bucketShortA label : ENNReal)) *
        (((rho : ENNReal) / (bucketShortA label : ENNReal)) ^
          (2 - 3 * beta))) ≤
      proposition66AInnerFactor rho
        (bucketShortA label) (bucketShortB label)
        (centeredAdaptiveActualBucketFullFiberNatCap
          S hrho P k r hr label C) epsilon beta := by
  let R : ENNReal :=
    (rho : ENNReal) ^ (-epsilon / 2) *
      ((bucketShortB label : ENNReal) /
        (bucketShortA label : ENNReal)) *
      (((rho : ENNReal) / (bucketShortA label : ENNReal)) ^
        (2 - 3 * beta))
  let p : Real := coarseExponent * (beta / 2)
  let inner : ENNReal := proposition66AInnerFactor rho
    (bucketShortA label) (bucketShortB label)
    (centeredAdaptiveActualBucketFullFiberNatCap
      S hrho P k r hr label C) epsilon beta
  have hCOne : (1 : ENNReal) ≤ C :=
    one_le_sourceKatzTaoConstant_of_selectedBucketOccupied
      S hrho P k r hr label hoccupied C hKT
  have hRle : R ≤ C * R := by
    calc
      R = 1 * R := by simp
      _ ≤ C * R := mul_le_mul' hCOne le_rfl
  have hsource :=
    selectedParent_sourceConstant_mul_scaleReserve_le_deltaBetaHalfLoss_mul_adaptiveActualInnerFactor
      S hrho P k r hr label hoccupied hdelta hdeltaHalf hsmallPacking
        C coarseExponent epsilon beta hCpower hbeta hbetaTwo
  have hCR : C * R ≤ (delta : ENNReal) ^ (-p) * inner := by
    simpa only [R, p, inner, show
      (-coarseExponent) * (beta / 2) =
        -(coarseExponent * (beta / 2)) by ring] using hsource
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  calc
    (delta : ENNReal) ^ p * R ≤
        (delta : ENNReal) ^ p * (C * R) :=
      mul_le_mul' le_rfl hRle
    _ ≤ (delta : ENNReal) ^ p *
        ((delta : ENNReal) ^ (-p) * inner) :=
      mul_le_mul' le_rfl hCR
    _ = inner := by
      rw [← mul_assoc, ← ENNReal.rpow_add p (-p) hd0 hdTop]
      simp
    _ = proposition66AInnerFactor rho
        (bucketShortA label) (bucketShortB label)
        (centeredAdaptiveActualBucketFullFiberNatCap
          S hrho P k r hr label C) epsilon beta := rfl

#print axioms one_le_sourceKatzTaoConstant_of_selectedBucketOccupied
#print axioms
  selectedParent_deltaBetaHalf_mul_scaleReserve_le_adaptiveActualInnerFactor

end
end Family8SelectedParentAdaptiveInnerSourcePowerLowerV1
