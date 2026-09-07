import Family8Grounding.Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5
import Family8Grounding.Family8ActiveCoarseCanonicalFrostmanXLowerParameterLadderV8

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8IdentifiedDividingWitnessCanonicalXLowerV2

open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open Family8StickyParentHullVolumeBoundV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover

noncomputable section

/-!
# The identified first-long witness supplies the canonical `X` lower bound

This module specializes the canonical Frostman-to-card-scale-mass estimate to
the actual node selected by an `IdentifiedFrostmanDividingWitness`.  The
global scale is exactly `tau_m`, the buffered scale is the canonical radius
`b`, and the family counted by `X = b^2 |T_b|` is the actual active coarse
family of the coherent `delta -> b` cover.

The only substantive upstream input retained here is the paper's
maximal-density Frostman-constant estimate for that active coarse family.
The remaining hypotheses are explicit nondegeneracy and scale-range facts;
no final bootstrap inequality is accepted as an input.
-/

namespace Witness

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The identified dividing witness, at its canonical buffered scale, has
the exact parameter-ladder lower bound for `X = b^2 |T_b|`. -/
theorem parameterLadder_global_rpow_le_canonicalBufferedCardScaleMass
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family C P.N P.epsilon P.eta S)
    (hbeta : 0 < beta)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hrhoHalf :
      Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedRadius W <=
        (2 : NNReal)⁻¹)
    (hfine : D.family.refinement.refined.Nonempty)
    (hC : canonicalFrostmanConstant
        (Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedGlobalCover
          W hD.delta_pos P.epsilon_pos.le hepsilonHalf).activeCoarseFamily
        closedBallFourBody <=
      (S.tau W.m : ENNReal) ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P W.stage))
    (htauSmall : S.tau W.m <=
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P W.stage) :
    S.tau W.m ^ (10 * P.eta W.stage / (P.epsilon * beta)) <=
      activeCoarseCardScaleMass
        (Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedGlobalCover
          W hD.delta_pos P.epsilon_pos.le hepsilonHalf) := by
  let U :=
    Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedGlobalCover
      W hD.delta_pos P.epsilon_pos.le hepsilonHalf
  have htau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hrho : 0 <
      Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedRadius W :=
    Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedRadius_pos
      W hD.delta_pos P.epsilon_pos.le
  have hcoarse : U.activeCoarse.Nonempty :=
    Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedGlobalCover_activeCoarse_nonempty
      W hD.delta_pos P.epsilon_pos.le hepsilonHalf hfine
  exact
    Family8ActiveCoarseCanonicalFrostmanXLowerParameterLadderV8.StickyScaleCover.parameterLadder_global_rpow_le_activeCoarseCardScaleMass_of_canonical
      (delta := delta)
      (rho :=
        Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedRadius W)
      (iota := iota) (globalDelta := S.tau W.m)
      (epsilon0 := epsilon0) (beta := beta) (gamma := gamma)
      D hD U P W.stage hbeta htau hrho hrhoHalf hcoarse hC htauSmall

#print axioms parameterLadder_global_rpow_le_canonicalBufferedCardScaleMass

end Witness

end
end Family8IdentifiedDividingWitnessCanonicalXLowerV2
