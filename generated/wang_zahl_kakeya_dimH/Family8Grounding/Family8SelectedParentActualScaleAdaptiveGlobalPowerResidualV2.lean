import Family8Grounding.Family8SelectedParentActualScaleAdaptiveGlobalPowerResidualV1

/-!
# Uniform actual-scale adaptive residual dichotomy

Finite logic lifts the callback-free one-bucket theorem to all occupied
buckets of the same actual sticky cover.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentActualScaleAdaptiveGlobalPowerResidualV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentAdaptiveInnerSourceReserveV1
open Family8SelectedParentAdaptiveScaleReservePowerLowerV1
open Family8SelectedParentActualScaleAdaptiveGlobalPowerResidualV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessGeometryV1
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem selectedParent_actualScale_exists_occupied_paperHullThin_or_forall_globalPowerResidual
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (alpha : Real) (halpha : 0 < alpha)
    (hrhoUpper : rho ≤ delta ^ alpha)
    (G : StickyScaleCover fine rho)
    (P : GreedyDensityPartition G.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex G)))
      (hullContainer G.activeCoarseFamily) Finset.univ)
    (r : NNReal) (hr : 0 < r)
    (adaptiveC : ENNReal)
    (innerEpsilon beta absorbExponent coefficientExponent etaF : Real)
    (hinnerEpsilon : 0 ≤ innerEpsilon)
    (hbetaStrict : beta < 2 / 3)
    (habsorbExponent : 0 < absorbExponent)
    (hreserve : 0 ≤
      absorbExponent + coefficientExponent + 2 + 2 * etaF)
    (hsmall : delta ≤
      adaptiveScaleReserveFlatConstantThreshold beta absorbExponent) :
    let paperTau := selectedParentActualScaleEq46PaperTau alpha
      innerEpsilon beta absorbExponent coefficientExponent etaF
    (∃ k : Fin (blocks G.activeCoarseFamily P).length,
      ∃ label : Fin 3 → Int,
        SelectedBucketOccupied G hrho P k r hr label ∧
        hullShortestSide
          (selectedParentGreedyBlockJohnFrame G hrho P k) ≤
          rho ^ (1 - paperTau)) ∨
      (∀ k : Fin (blocks G.activeCoarseFamily P).length,
        ∀ label : Fin 3 → Int,
          SelectedBucketOccupied G hrho P k r hr label →
          (delta : ENNReal) ^ (-coefficientExponent) ≤
            (delta : ENNReal) ^ 2 *
              ((delta : ENNReal) ^ (2 * etaF) *
                proposition66AInnerFactor rho
                  (bucketShortA label) (bucketShortB label)
                  (centeredAdaptiveGlobalFullFiberNatCap G hrho P r hr adaptiveC)
                  innerEpsilon beta)) := by
  dsimp only
  let paperTau := selectedParentActualScaleEq46PaperTau alpha
    innerEpsilon beta absorbExponent coefficientExponent etaF
  by_cases hthin : ∃ k : Fin (blocks G.activeCoarseFamily P).length,
      ∃ label : Fin 3 → Int,
        SelectedBucketOccupied G hrho P k r hr label ∧
        hullShortestSide
          (selectedParentGreedyBlockJohnFrame G hrho P k) ≤
          rho ^ (1 - paperTau)
  · exact Or.inl hthin
  · right
    intro k label hoccupied
    rcases selectedParent_actualScale_paperHullThin_or_globalPowerResidual
        hfineContained hdelta hdeltaHalf hrho hrhoOne alpha halpha hrhoUpper
        G P k r hr label hoccupied adaptiveC innerEpsilon beta
        absorbExponent coefficientExponent etaF hinnerEpsilon hbetaStrict
        habsorbExponent hreserve hsmall with hlocalThin | hresidual
    · exfalso
      apply hthin
      exact ⟨k, label, hoccupied, by
        simpa only [paperTau] using hlocalThin⟩
    · exact hresidual

#print axioms
  selectedParent_actualScale_exists_occupied_paperHullThin_or_forall_globalPowerResidual

end
end Family8SelectedParentActualScaleAdaptiveGlobalPowerResidualV2
