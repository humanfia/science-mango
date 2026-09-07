import Family8Grounding.Family8ActiveCoarseCanonicalFrostmanXLowerParameterLadderV8
import Family8Grounding.Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4
import Family8Grounding.Family8LongIntervalBootstrapNumericsV1

/-!
# Long-interval bootstrap on one literal endpoint cover

The scalar long-interval argument does not intrinsically need an all-real
coherent cover.  It needs one actual radius-`b` sticky cover, its coarse
Frostman constant, and its coarse Katz--Tao certificate.  This file exposes
that discrete endpoint interface directly.

Consequently an exact-uniform selected partition can be used here without
first manufacturing a coherent interpolation at every real radius.  Any
remaining obligation is visibly on this same literal endpoint cover.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8DiscreteLongIntervalEndpointBootstrapV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8ParameterLadderV1
open Family8StickyParentHullVolumeBoundV1
open FamilyStickyAtEveryScaleCoreV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover

noncomputable section

/-- A single literal endpoint cover supplies the complete two-sided `X`
bootstrap.  There is no coherent-cover or interval-parent argument in the
statement. -/
theorem longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_discreteEndpoint
    {delta b globalDelta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {epsilon0 beta gamma : Real}
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (U : StickyScaleCover D.family b)
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    (A : NNReal)
    (hglobal : 0 < globalDelta) (hglobalOne : globalDelta <= 1)
    (hglobalB : globalDelta <= b)
    (hbUpper : b <= globalDelta ^ (1 - P.epsilon))
    (hbHalf : b <= (2 : NNReal)⁻¹)
    (hcoarse : U.activeCoarse.Nonempty)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hC : canonicalFrostmanConstant U.activeCoarseFamily
        closedBallFourBody <=
      (globalDelta : ENNReal) ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P j))
    (hglobalSmall : globalDelta <=
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P j)
    (hKT : U.IsKatzTaoAtScale (A : ENNReal))
    (hAKT : 1024 * A <= globalDelta ^
      (-longIntervalDeltaLoss P.epsilon
        (10 * P.eta j / (P.epsilon * beta)))) :
    longIntervalKatzTaoRHSENNReal
        globalDelta b (activeCoarseCardScaleMass U)
        P.epsilon (10 * P.eta j / (P.epsilon * beta)) beta <=
      longIntervalFrostmanTargetENNReal
        globalDelta b (activeCoarseCardScaleMass U)
        (10 * P.eta j / (P.epsilon * beta)) gamma := by
  let X := activeCoarseCardScaleMass U
  have hb : 0 < b := hglobal.trans_le hglobalB
  have hXLower :
      globalDelta ^ (10 * P.eta j / (P.epsilon * beta)) <= X := by
    dsimp only [X]
    exact
      Family8ActiveCoarseCanonicalFrostmanXLowerParameterLadderV8.StickyScaleCover.parameterLadder_global_rpow_le_activeCoarseCardScaleMass_of_canonical
        (delta := delta) (rho := b) (iota := iota)
        (globalDelta := globalDelta)
        (epsilon0 := epsilon0) (beta := beta) (gamma := gamma)
        D hD U P j hbeta hglobal hb hbHalf hcoarse hC hglobalSmall
  have hXUpperCore : X <= 1024 * A := by
    dsimp only [X]
    exact
      Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4.StickyScaleCover.activeCoarseCardScaleMass_le_1024_mul_nnreal_of_isKatzTaoAtScale
        D hD U hbHalf A hKT
  have hXUpper : X <= globalDelta ^
      (-longIntervalDeltaLoss P.epsilon
        (10 * P.eta j / (P.epsilon * beta))) :=
    hXUpperCore.trans hAKT
  exact longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal
    P j hglobal hglobalOne hglobalB hbUpper hXLower hXUpper hbeta hgamma

#print axioms
  longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_discreteEndpoint

end
end Family8DiscreteLongIntervalEndpointBootstrapV1
