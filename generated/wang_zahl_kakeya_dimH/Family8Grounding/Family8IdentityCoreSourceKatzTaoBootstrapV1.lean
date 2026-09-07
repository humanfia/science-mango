import Family8Grounding.Family8IdentityRadiusSourceKatzTaoTransportV1
import Family8Grounding.Family8NormalizedLongIntervalCoreBootstrapV1

/-!
# Source Katz--Tao adapter for the identity-coherent long core

This file specializes the common-core bootstrap to the concrete identity
coherent cover.  Its coarse Katz--Tao premise is discharged from a source
Katz--Tao hypothesis using the exact radius-enlargement loss.  The remaining
displayed scalar premise deliberately retains that loss: removing it would
require genuine aggregation at the canonical radius, which the identity
cover does not perform.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8IdentityCoreSourceKatzTaoBootstrapV1

open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8CanonicalLowerBufferedScaleV4
open Family8IdentityRadiusSourceKatzTaoTransportV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8StickyParentHullVolumeBoundV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The finite `NNReal` form of the explicit radius-enlargement ratio. -/
def identityRadiusKatzTaoVolumeRatioNNReal
    (delta rho : NNReal) : NNReal :=
  (8 * rho ^ 2) / (delta ^ 2 / 2)

@[simp] theorem coe_identityRadiusKatzTaoVolumeRatioNNReal
    (delta rho : NNReal) (hdeltaPos : 0 < delta) :
    (identityRadiusKatzTaoVolumeRatioNNReal delta rho : ENNReal) =
      identityRadiusKatzTaoVolumeRatio delta rho := by
  have hden : delta ^ 2 / 2 ≠ 0 :=
    div_ne_zero (pow_ne_zero 2 hdeltaPos.ne') (by norm_num)
  simp only [identityRadiusKatzTaoVolumeRatioNNReal,
    identityRadiusKatzTaoVolumeRatio, ENNReal.coe_div hden,
    ENNReal.coe_div (by norm_num : (2 : NNReal) ≠ 0),
    ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat]

/-- At the canonical radius of an identity-coherent core, source Katz--Tao
produces the exact coarse Katz--Tao input used by the long bootstrap. -/
theorem identityCore_canonicalBufferedGlobalCover_isKatzTaoAtScale_of_source
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family (identityRadiusCoherentCover D.family)
        P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hrhoHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹)
    {A : ENNReal} (hKTsource : IsKatzTao A D.family.bodyFamily) :
    (canonicalBufferedGlobalCover
      W hD.delta_pos P.epsilon_pos.le hepsilonHalf).IsKatzTaoAtScale
        (identityRadiusKatzTaoVolumeRatio delta
          (canonicalBufferedRadius W) * A) := by
  have hdeltaB : delta <= canonicalBufferedRadius W :=
    (S.delta_le_tau W.m).trans
      (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
  change
    (identityRadiusScaleCover D.family (canonicalBufferedRadius W)
      hdeltaB).IsKatzTaoAtScale
        (identityRadiusKatzTaoVolumeRatio delta
          (canonicalBufferedRadius W) * A)
  exact identityRadiusScaleCover_isKatzTaoAtScale_of_sourceKatzTao
      D.family (canonicalBufferedRadius W)
        ((S.delta_le_tau W.m).trans
          (tau_le_canonicalBufferedRadius W
            hD.delta_pos P.epsilon_pos.le))
        hD.delta_pos hD.delta_le_half hrhoHalf hKTsource

/-- The common-core long bootstrap with its coarse Katz--Tao theorem produced
from source Katz--Tao.  The last scalar budget exposes the unavoidable
identity-radius enlargement ratio rather than hiding it in a callback. -/
theorem longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_identityCore_source
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family (identityRadiusCoherentCover D.family)
        P.N P.epsilon P.eta S)
    (A : NNReal)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hrhoHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹)
    (hfine : D.family.refinement.refined.Nonempty)
    (hC : canonicalFrostmanConstant
        (canonicalBufferedGlobalCover
          W hD.delta_pos P.epsilon_pos.le hepsilonHalf).activeCoarseFamily
        closedBallFourBody <=
      (S.tau W.m : ENNReal) ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P W.stage))
    (htauSmall : S.tau W.m <=
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P W.stage)
    (hKTsource : IsKatzTao (A : ENNReal) D.family.bodyFamily)
    (hAKT : 1024 *
        (identityRadiusKatzTaoVolumeRatioNNReal delta
          (canonicalBufferedRadius W) * A) <=
      S.tau W.m ^
        (-longIntervalDeltaLoss P.epsilon
          (10 * P.eta W.stage / (P.epsilon * beta)))) :
    longIntervalKatzTaoRHSENNReal
        (S.tau W.m) (canonicalBufferedRadius W)
        (activeCoarseCardScaleMass
          (canonicalBufferedGlobalCover
            W hD.delta_pos P.epsilon_pos.le hepsilonHalf))
        P.epsilon (10 * P.eta W.stage / (P.epsilon * beta)) beta <=
      longIntervalFrostmanTargetENNReal
        (S.tau W.m) (canonicalBufferedRadius W)
        (activeCoarseCardScaleMass
          (canonicalBufferedGlobalCover
            W hD.delta_pos P.epsilon_pos.le hepsilonHalf))
        (10 * P.eta W.stage / (P.epsilon * beta)) gamma := by
  apply
    Family8NormalizedLongIntervalCoreBootstrapV1.longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_coreActual
      D hD (identityRadiusCoherentCover D.family) S P W
        (identityRadiusKatzTaoVolumeRatioNNReal delta
          (canonicalBufferedRadius W) * A)
        hbeta hgamma hepsilonHalf hrhoHalf hfine hC htauSmall
  · simpa only [ENNReal.coe_mul,
      coe_identityRadiusKatzTaoVolumeRatioNNReal delta
        (canonicalBufferedRadius W) hD.delta_pos] using
      identityCore_canonicalBufferedGlobalCover_isKatzTaoAtScale_of_source
        D hD S P W hepsilonHalf hrhoHalf hKTsource
  · exact hAKT

#print axioms
  identityCore_canonicalBufferedGlobalCover_isKatzTaoAtScale_of_source
#print axioms
  longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_identityCore_source

end

end Family8IdentityCoreSourceKatzTaoBootstrapV1
