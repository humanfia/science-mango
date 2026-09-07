import Family8Grounding.Family8SelectedParentAdaptiveScaleReservePowerLowerV2
import Family8Grounding.Family8SelectedParentAdaptiveInnerScaleReserveV1
import Family8Grounding.Family8SelectedParentCanonicalBufferedAdaptivePowerResidualV1
import Mathlib.Tactic

/-!
# Actual-scale hull-thin or adaptive global power residual

This is the scale-generic form of the source-tau residual.  Its only scale
input is the genuine upper envelope `rho <= delta ^ alpha`; consequently it
can be instantiated on the density-aware selected sticky cover at its actual
buffered radius.  No Equation (46) conclusion is accepted as a premise.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentActualScaleAdaptiveGlobalPowerResidualV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentAdaptiveInnerSourceReserveV1
open Family8SelectedParentAdaptiveScaleReservePowerLowerV1
open Family8SelectedParentAdaptiveInnerScaleReserveV1
open Family8SelectedParentAdaptiveScaleReservePowerLowerV2
open Family8SelectedParentCanonicalBufferedAdaptivePowerResidualV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessGeometryV1
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessProducerV1
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

def selectedParentActualScaleEq46PaperTau
    (alpha innerEpsilon beta absorbExponent coefficientExponent etaF : Real) :
    Real :=
  canonicalEq46PaperFlatnessTau alpha (2 - 3 * beta)
    (innerEpsilon / 2)
    (absorbExponent + coefficientExponent + 2 + 2 * etaF)

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- At any actual sticky scale with a proved delta-power upper envelope, an
occupied bucket is paper hull-thin or satisfies the exact global-cap power
residual used by the card-weighted Equation (46) chain. -/
theorem selectedParent_actualScale_paperHullThin_or_globalPowerResidual
    (hfineContained : forall i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (alpha : Real) (halpha : 0 < alpha)
    (hrhoUpper : rho <= delta ^ alpha)
    (G : StickyScaleCover fine rho)
    (P : GreedyDensityPartition G.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex G)))
      (hullContainer G.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks G.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (hoccupied : SelectedBucketOccupied G hrho P k r hr label)
    (adaptiveC : ENNReal)
    (innerEpsilon beta absorbExponent coefficientExponent etaF : Real)
    (hinnerEpsilon : 0 <= innerEpsilon)
    (hbetaStrict : beta < 2 / 3)
    (habsorbExponent : 0 < absorbExponent)
    (hreserve : 0 <=
      absorbExponent + coefficientExponent + 2 + 2 * etaF)
    (hsmall : delta <=
      adaptiveScaleReserveFlatConstantThreshold beta absorbExponent) :
    let paperTau := selectedParentActualScaleEq46PaperTau alpha
      innerEpsilon beta absorbExponent coefficientExponent etaF
    let J := selectedParentGreedyBlockJohnFrame G hrho P k
    hullShortestSide J <= rho ^ (1 - paperTau) ∨
      (delta : ENNReal) ^ (-coefficientExponent) <=
        (delta : ENNReal) ^ 2 *
          ((delta : ENNReal) ^ (2 * etaF) *
            proposition66AInnerFactor rho
              (bucketShortA label) (bucketShortB label)
              (centeredAdaptiveGlobalFullFiberNatCap G hrho P r hr adaptiveC)
              innerEpsilon beta) := by
  dsimp only
  let q : Real := 2 - 3 * beta
  let u : Real := innerEpsilon / 2
  let reserveBudget : Real :=
    absorbExponent + coefficientExponent + 2 + 2 * etaF
  let paperTau : Real :=
    canonicalEq46PaperFlatnessTau alpha q u reserveBudget
  let g : Real := absorbExponent + alpha *
    (-u + (1 - paperTau) * q)
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame G hrho P k) r hr
  let B := (blockAt G.activeCoarseFamily P k).fiber
  have hoccupiedRaw : label ∈ occupiedWeightBuckets
      (Finset.univ : Finset {p // p ∈ B})
      (fun p => sideShapeLabel
        (selectedParentLongRelabeledSide e G B hrho p)) := by
    simpa only [SelectedBucketOccupied, e, B] using hoccupied
  obtain ⟨p, _hp, hpLabel⟩ :=
    mem_occupiedWeightBuckets_iff.mp hoccupiedRaw
  let W : {p // p ∈ selectedParentPlankBucketIndices
      e G B hrho label} := ⟨p, by
    rw [selectedParentPlankBucketIndices, mem_sideShapeBucket_iff]
    exact ⟨Finset.mem_univ _, hpLabel⟩⟩
  let J := selectedParentGreedyBlockJohnFrame G hrho P k
  by_cases hthin : hullShortestSide J <= rho ^ (1 - paperTau)
  · exact Or.inl hthin
  · right
    have hq : 0 < q := by dsimp only [q]; linarith
    have hu : 0 <= u := by dsimp only [u]; linarith
    have hbudget := canonicalEq46PaperFlatnessTau_exponent_budget
      (alpha := alpha) (q := q) (u := u) (p := 0)
      (absorbExponent := absorbExponent)
      (coefficientExponent := coefficientExponent) (etaF := etaF)
      halpha hq hu (by simpa only [reserveBudget, zero_add] using hreserve)
    have hflatExponent : -innerEpsilon / 2 +
        (1 - paperTau) * (2 - 3 * beta) <= 0 := by
      simpa only [paperTau, reserveBudget, q, u, neg_div,
        selectedParentActualScaleEq46PaperTau, zero_add] using hbudget.1
    have hexponent : 2 + 2 * etaF + g <= -coefficientExponent := by
      simpa only [g, paperTau, reserveBudget, q, u,
        selectedParentActualScaleEq46PaperTau, zero_add] using hbudget.2
    have hflatBranch := selectedParent_paperHullThin_or_bucketFlat
      hfineContained G hrho hrhoOne P k r hr label W paperTau
    have hflat : bucketShortA label <= 286654464 * rho ^ paperTau := by
      rcases hflatBranch with hlocalThin | hflat
      · exact False.elim (hthin (by simpa only [J] using hlocalThin))
      · exact hflat
    have hscale : (delta : ENNReal) ^ g <=
        (rho : ENNReal) ^ (-innerEpsilon / 2) *
          ((bucketShortB label : ENNReal) /
            (bucketShortA label : ENNReal)) *
          (((rho : ENNReal) / (bucketShortA label : ENNReal)) ^
            (2 - 3 * beta)) := by
      simpa only [g, paperTau, reserveBudget, q, u, neg_div,
        selectedParentActualScaleEq46PaperTau] using
        delta_rpow_absorb_add_flatRadiusExponent_le_scaleReserve
          hdelta hrho hbetaStrict.le (bucketShortA_pos label)
          (bucketShortA_le_bucketShortB label) hrhoUpper hflat
          hflatExponent habsorbExponent hsmall
    have hoccupiedLabels : label ∈
        selectedParentOccupiedShapeLabels G hrho P k r hr := by
      simpa only [selectedParentOccupiedShapeLabels, e, B] using hoccupiedRaw
    have hreserveInner :=
      selectedParent_scaleReserve_le_adaptiveGlobalInnerFactor
        G hrho P k r hr label hoccupiedLabels adaptiveC innerEpsilon beta
          (hbetaStrict.le.trans (by norm_num))
    have hinner : (delta : ENNReal) ^ g <=
        proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label)
          (centeredAdaptiveGlobalFullFiberNatCap G hrho P r hr adaptiveC)
          innerEpsilon beta := hscale.trans hreserveInner
    exact delta_negativePower_le_quadratic_mul_inner_of_powerLower
      hdelta (hdeltaHalf.trans (by norm_num)) hexponent hinner

#print axioms
  selectedParent_actualScale_paperHullThin_or_globalPowerResidual

end
end Family8SelectedParentActualScaleAdaptiveGlobalPowerResidualV1
