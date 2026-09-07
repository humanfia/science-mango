import Family8Grounding.Family8SelectedParentAdaptiveScaleReservePowerLowerV2
import Mathlib.Tactic

/-!
# Source-tau actual scale-reserve power

The identified long witness gives the literal source-tau radius bound
`tau_m <= delta^stoppingEpsilon`.  Applying the arbitrary-paper-parameter
hull-flatness scalar core at that radius produces the scale reserve used by
the full source-tau Equation (46) consumer.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentSourceTauAdaptiveScaleReservePowerLowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8SelectedParentAdaptiveScaleReservePowerLowerV1
open Family8SelectedParentAdaptiveScaleReservePowerLowerV2
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessGeometryV1
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessProducerV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  {Cmulti : CoherentStickyMultiscaleCover fine}
  {depth N : Nat} {stoppingEpsilon : Real} {eta : Nat → Real}
  {scaleSequence : FiniteScaleSequence delta depth}

theorem selectedParent_sourceTau_nonHullThin_scaleReservePowerLower
    (D : IdentifiedFrostmanDividingWitness
      fine Cmulti N stoppingEpsilon eta scaleSequence)
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (hdelta : 0 < delta)
    (G : StickyScaleCover fine (scaleSequence.tau D.m))
    (P : GreedyDensityPartition G.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex G)))
      (hullContainer G.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks G.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame G
          (hdelta.trans_le (scaleSequence.delta_le_tau D.m)) P k) r hr)
      G (blockAt G.activeCoarseFamily P k).fiber
        (hdelta.trans_le (scaleSequence.delta_le_tau D.m)) label})
    (paperTau innerEpsilon beta absorbExponent : Real)
    (hnotHullThin : ¬ hullShortestSide
      (selectedParentGreedyBlockJohnFrame G
        (hdelta.trans_le (scaleSequence.delta_le_tau D.m)) P k) ≤
          scaleSequence.tau D.m ^ (1 - paperTau))
    (hbetaTwoThirds : beta ≤ 2 / 3)
    (hflatRadiusExponent :
      -innerEpsilon / 2 + (1 - paperTau) * (2 - 3 * beta) ≤ 0)
    (habsorbExponent : 0 < absorbExponent)
    (hsmall : delta ≤
      adaptiveScaleReserveFlatConstantThreshold beta absorbExponent) :
    (delta : ENNReal) ^
        (absorbExponent + stoppingEpsilon *
          (-innerEpsilon / 2 +
            (1 - paperTau) * (2 - 3 * beta))) ≤
      (scaleSequence.tau D.m : ENNReal) ^ (-innerEpsilon / 2) *
        ((bucketShortB label : ENNReal) /
          (bucketShortA label : ENNReal)) *
        (((scaleSequence.tau D.m : ENNReal) /
          (bucketShortA label : ENNReal)) ^ (2 - 3 * beta)) := by
  let rho := scaleSequence.tau D.m
  let hrho : 0 < rho := hdelta.trans_le (scaleSequence.delta_le_tau D.m)
  have hrhoOne : rho ≤ 1 :=
    CoherentStickyMultiscaleCover.tau_le_one scaleSequence D.m
  have hlong := D.long
  change (scaleSequence.tau D.m : ENNReal) ≤
      (delta : ENNReal) ^ stoppingEpsilon *
        (scaleSequence.theta D.m : ENNReal) at hlong
  have hlongNN : scaleSequence.tau D.m ≤
      delta ^ stoppingEpsilon * scaleSequence.theta D.m := by
    rw [← ENNReal.coe_rpow_of_ne_zero hdelta.ne' stoppingEpsilon,
      ← ENNReal.coe_mul] at hlong
    exact ENNReal.coe_le_coe.mp hlong
  have hrhoUpper : rho ≤ delta ^ stoppingEpsilon := by
    calc
      rho ≤ delta ^ stoppingEpsilon * scaleSequence.theta D.m := hlongNN
      _ ≤ delta ^ stoppingEpsilon * 1 :=
        mul_le_mul_of_nonneg_left (scaleSequence.theta_le_one D.m)
          (by positivity)
      _ = delta ^ stoppingEpsilon := mul_one _
  have hflatBranch := selectedParent_paperHullThin_or_bucketFlat
    hfineContained G hrho hrhoOne P k r hr label W paperTau
  have hflat : bucketShortA label ≤
      286654464 * rho ^ paperTau := by
    rcases hflatBranch with hthin | hflat
    · exact False.elim (hnotHullThin hthin)
    · exact hflat
  apply delta_rpow_absorb_add_flatRadiusExponent_le_scaleReserve
    hdelta hrho hbetaTwoThirds (bucketShortA_pos label)
      (bucketShortA_le_bucketShortB label)
  · exact hrhoUpper
  · exact hflat
  · exact hflatRadiusExponent
  · exact habsorbExponent
  · exact hsmall

#print axioms selectedParent_sourceTau_nonHullThin_scaleReservePowerLower

end
end Family8SelectedParentSourceTauAdaptiveScaleReservePowerLowerV1
