import Family8Grounding.Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Family8Grounding.Family8StickySelectedParentGreedyBlockFrostmanV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CanonicalBufferedTauActiveKatzTaoEveryScaleV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8StickySelectedParentGreedyBlockFrostmanV3

noncomputable section

/-!
# Every-scale Katz--Tao control on the canonical tau-active cover

The tau-active interval cover and the original global buffered cover have
the same active coarse bodies.  We use the existing body-preserving finite
reindexing theorem, rather than relying on generated `Fintype` instances, to
transport the all-scale certificate.  No intermediate admissibility premise
or new quantitative hypothesis is introduced.
-/

namespace Witness

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}

theorem canonicalBufferedTauActiveCover_isKatzTaoAtScale_of_everyScale
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness D.family C N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    {KT : ENNReal} (hKT : C.base.IsKatzTaoAtEveryScale KT) :
    (canonicalBufferedTauActiveCover D hD C S W
      hepsilon hepsilonHalf).IsKatzTaoAtScale KT := by
  let U := canonicalBufferedTauActiveCover
    D hD C S W hepsilon hepsilonHalf
  let G := canonicalBufferedGlobalCover
    W hD.delta_pos hepsilon hepsilonHalf
  have hG : G.IsKatzTaoAtScale KT := by
    exact hKT (canonicalBufferedRadius W)
      ((S.delta_le_tau W.m).trans
        (tau_le_canonicalBufferedRadius W hD.delta_pos hepsilon))
      (canonicalBufferedRadius_le_one W hD.delta_pos hepsilon hepsilonHalf)
  have hfamily : U.activeCoarseFamily = G.activeCoarseFamily :=
    canonicalBufferedTauActiveCover_activeCoarseFamily_eq_global
      D hD C S W hepsilon hepsilonHalf
  intro K
  rw [concentration_eq_of_bodyPreservingEquiv
    (Equiv.refl {k // k ∈ U.activeCoarse})
    U.activeCoarseFamily G.activeCoarseFamily
    (fun k => congrFun hfamily k) K]
  exact hG K

#print axioms
  canonicalBufferedTauActiveCover_isKatzTaoAtScale_of_everyScale

end Witness
end
end Family8CanonicalBufferedTauActiveKatzTaoEveryScaleV3
