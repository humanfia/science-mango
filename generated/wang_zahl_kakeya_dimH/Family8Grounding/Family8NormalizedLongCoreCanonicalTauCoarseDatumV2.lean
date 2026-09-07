import Family8Grounding.Family8NormalizedLongIntervalCoreConsumerV1
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import FamilyStickyGrounding.FamilyStickyHierarchyEndpointPrefixShadingTransportV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8NormalizedLongCoreCanonicalTauCoarseDatumV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

/-!
# Canonical tau-active datum from the normalized long core, V2

The old tau-active construction was parameterized by an identified witness,
although its definitions used only the selected node and the scale ordering.
This successor freezes the identical literal covers directly on
`NormalizedLongIntervalCoreWitness`.  In particular, neither discarded
outside upper estimate is reconstructed or assumed.  V1 omitted the
namespace exporting `EssentiallyDistinct` and is not imported.
-/

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}

/-- The literal global `delta -> tau_m` cover selected by the core. -/
def tauScaleCover
    (D : ActualTubeDatum delta iota)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family C N epsilon eta S) :
    StickyScaleCover D.family (S.tau W.m) :=
  C.base.cover (S.tau W.m) (S.delta_le_tau W.m)
    ((S.tau_le_theta W.m).trans (S.theta_le_one W.m))

/-- The honest active tau-parent family with its parent-aggregated shading. -/
def tauActiveCoarseDatum
    (D : ActualTubeDatum delta iota)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family C N epsilon eta S) :
    ActualTubeDatum (S.tau W.m)
      {k // k ∈ (tauScaleCover D C S W).activeCoarse} where
  family := (tauScaleCover D C S W).coarse.restrictTo
    (tauScaleCover D C S W).activeCoarse
  shading := parentAggregatedShading (tauScaleCover D C S W) D.shading

@[simp]
theorem tauActiveCoarseDatum_family_tubes
    (D : ActualTubeDatum delta iota)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family C N epsilon eta S)
    (k : {k // k ∈ (tauScaleCover D C S W).activeCoarse}) :
    (tauActiveCoarseDatum D C S W).family.tubes k =
      (tauScaleCover D C S W).coarse.tubes k.1 :=
  rfl

@[simp]
theorem tauActiveCoarseDatum_refined
    (D : ActualTubeDatum delta iota)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family C N epsilon eta S) :
    (tauActiveCoarseDatum D C S W).family.refinement.refined = Finset.univ :=
  rfl

/-- The two geometric obligations needed only when the tau-parent datum is
used as an admissible actual datum. -/
structure TauActiveCoarseAdmissibility
    (D : ActualTubeDatum delta iota)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family C N epsilon eta S) : Prop where
  contained_in_unit_ball : forall
    k : {k // k ∈ (tauScaleCover D C S W).activeCoarse},
    ((tauScaleCover D C S W).coarse.tubes k.1).carrier ⊆
      Metric.closedBall (0 : Space) 1
  pairwise_essentiallyDistinct :
    Set.Pairwise
      (Set.univ : Set {k // k ∈ (tauScaleCover D C S W).activeCoarse})
      (fun k l => EssentiallyDistinct
        ((tauScaleCover D C S W).coarse.tubes k.1)
        ((tauScaleCover D C S W).coarse.tubes l.1))

theorem tauActiveCoarseDatum_isAdmissible
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family C N epsilon eta S)
    (hepsilon : 0 <= epsilon)
    (hrhoHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹)
    (hgeometry : TauActiveCoarseAdmissibility D C S W) :
    (tauActiveCoarseDatum D C S W).IsAdmissible where
  delta_pos := hD.delta_pos.trans_le (S.delta_le_tau W.m)
  delta_le_half :=
    (tau_le_canonicalBufferedRadius W hD.delta_pos hepsilon).trans hrhoHalf
  contained_in_unit_ball := hgeometry.contained_in_unit_ball
  pairwise_essentiallyDistinct := hgeometry.pairwise_essentiallyDistinct

/-- The literal `tau_m -> b` cover, reindexed by its active tau parents. -/
def canonicalBufferedTauActiveCover
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family C N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2) :
    StickyScaleCover (tauActiveCoarseDatum D C S W).family
      (canonicalBufferedRadius W) := by
  classical
  let I := canonicalBufferedIntervalCover W hD.delta_pos
    hepsilon hepsilonHalf
  exact
    { coarseCard := I.coarseCard
      coarse := I.coarse
      activeFine := Finset.univ
      activeCoarse := I.activeCoarse
      parent := fun k => I.parent k.1
      activeFine_eq_refined := rfl
      activeCoarse_eq_refined := I.activeCoarse_eq_refined
      parent_mem := by
        intro k _hk
        exact I.parent_mem k.1 k.2
      parent_surjective := by
        intro l hl
        obtain ⟨k, hk, hparent⟩ := I.parent_surjective l hl
        exact ⟨⟨k, hk⟩, Finset.mem_univ _, hparent⟩
      carrier_subset := by
        intro k _hk
        exact I.carrier_subset k.1 k.2 }

@[simp]
theorem canonicalBufferedTauActiveCover_activeFine
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family C N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2) :
    (canonicalBufferedTauActiveCover
      D hD C S W hepsilon hepsilonHalf).activeFine = Finset.univ :=
  rfl

/-- Coherence identifies the active `b` parents in the interval and global
views definitionally. -/
theorem canonicalBufferedTauActiveCover_activeCoarseFamily_eq_global
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family C N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2) :
    (canonicalBufferedTauActiveCover
      D hD C S W hepsilon hepsilonHalf).activeCoarseFamily =
      (canonicalBufferedGlobalCover
        W hD.delta_pos hepsilon hepsilonHalf).activeCoarseFamily := by
  rfl

#print axioms tauScaleCover
#print axioms tauActiveCoarseDatum
#print axioms tauActiveCoarseDatum_family_tubes
#print axioms tauActiveCoarseDatum_refined
#print axioms tauActiveCoarseDatum_isAdmissible
#print axioms canonicalBufferedTauActiveCover
#print axioms canonicalBufferedTauActiveCover_activeCoarseFamily_eq_global

end
end Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
