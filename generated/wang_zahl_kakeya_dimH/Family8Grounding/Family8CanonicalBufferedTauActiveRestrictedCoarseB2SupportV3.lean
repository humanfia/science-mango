import Family8Grounding.Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3
import Family8Grounding.Family8StickyActiveCoarseB2SupportV5
import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictionV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set
open scoped NNReal

namespace Family8CanonicalBufferedTauActiveRestrictedCoarseB2SupportV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyActiveCoarseB2SupportV5

noncomputable section

namespace Witness

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}

theorem canonicalBufferedTauActiveRestrictedCoarse_carrier_subset_closedBall_two
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness D.family C N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    (hbufferedSixteenth : canonicalBufferedRadius W <= (1 / 16 : NNReal)) :
    let U := canonicalBufferedTauActiveCover
      D hD C S W hepsilon hepsilonHalf
    forall q,
      ((activeFineRestrictedScaleCover U).coarse.tubes q).carrier ⊆
        Metric.closedBall (0 : Space) 2 := by
  dsimp only
  let U := canonicalBufferedTauActiveCover
    D hD C S W hepsilon hepsilonHalf
  let G := canonicalBufferedGlobalCover W hD.delta_pos hepsilon hepsilonHalf
  intro q
  let e : {k // k ∈ U.activeCoarse} ≃ Fin U.activeCoarse.card :=
    U.activeCoarse.equivFin
  let k : {k // k ∈ U.activeCoarse} := e.symm q
  have hfamily : U.activeCoarseFamily = G.activeCoarseFamily :=
    canonicalBufferedTauActiveCover_activeCoarseFamily_eq_global
      D hD C S W hepsilon hepsilonHalf
  have hsupport := activeCoarseFamily_body_subset_closedBall_two
    D hD G hbufferedSixteenth k
  have hbody : U.activeCoarseFamily k = G.activeCoarseFamily k :=
    congrFun hfamily k
  change (U.activeCoarseFamily k : Set Space) ⊆
    Metric.closedBall (0 : Space) 2
  rw [hbody]
  exact hsupport

#print axioms
  canonicalBufferedTauActiveRestrictedCoarse_carrier_subset_closedBall_two

end Witness
end
end Family8CanonicalBufferedTauActiveRestrictedCoarseB2SupportV3
