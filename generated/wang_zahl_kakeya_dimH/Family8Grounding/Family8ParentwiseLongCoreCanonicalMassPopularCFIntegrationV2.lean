import Family8Grounding.Family8ParentwiseLongCoreCanonicalMassPopularCFIntegrationV1
import Mathlib.Tactic

/-!
# Restricted canonical parentwise LongCore to mass-popular CF integration

The endpoint DSO forms its frozen assembly on the active-fine restriction of
the canonical tau-active cover.  This successor transports the literal
all-parent barrier across exactly that reindexing before running the
mass-popular selector.  The selected parent therefore carries all four
record conclusions on the same restricted cover and the same assembly.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8ParentwiseLongCoreCanonicalMassPopularCFIntegrationV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8AllParentCFBarrierSelectedTransportV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParentwiseLongCoreCanonicalMassPopularCFV1
open Family8ParentwiseLongCoreCanonicalMassPopularCFV1.ParentwiseNormalizedLongIntervalCoreWitness
open Family8ParentwiseNormalizedLongIntervalCoreSelectorV1
open Family8ParentwiseNormalizedLongIntervalCoreSelectorV1.ParentwiseNormalizedLongIntervalCoreWitness
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8StickySelectedFineAssemblyMassPopularV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}

/-- The parentwise barrier and mass-popular selector composed on the exact
active-fine-restricted cover used by the endpoint DSO. -/
theorem exists_canonicalTauActiveRestricted_massPopularSelectedParentWithCF
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (hepsilon : 0 <= epsilon)
    (Wparent : ParentwiseNormalizedLongIntervalCoreWitness
      D hD C N epsilon hepsilon eta S)
    (hFine : D.family.refinement.refined.Nonempty)
    (hepsilonHalf : epsilon <= 1 / 2) :
    let W := Wparent.toNormalizedLongIntervalCoreWitness
      D hD C S hepsilon hFine
    let U0 := canonicalBufferedTauActiveCover
      D hD C S W hepsilon hepsilonHalf
    let U := activeFineRestrictedScaleCover U0
    let lower : ENNReal :=
      (((canonicalBufferedRadius W / S.tau W.m : NNReal) : ENNReal) ^
        eta W.stage)
    forall (Y : Shading (activeFineRestrictedFamily U0).bodyFamily)
      (r : Real)
      (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        (toConvexFactorization U) Y r),
      (IndexedShadingRefinement.restrictTo Y U.activeFine).shading.shadingMass
          ≠ 0 ->
        Nonempty (MassPopularSelectedParentWithCF U Y r A lower) := by
  dsimp only
  intro Y r A hsource
  let W := Wparent.toNormalizedLongIntervalCoreWitness
    D hD C S hepsilon hFine
  let U0 := canonicalBufferedTauActiveCover
    D hD C S W hepsilon hepsilonHalf
  let U := activeFineRestrictedScaleCover U0
  let lower : ENNReal :=
    (((canonicalBufferedRadius W / S.tau W.m : NNReal) : ENNReal) ^
      eta W.stage)
  have H0 : AllActiveParentCFBarrier U0 lower := by
    simpa only [W, U0, lower] using
      ParentwiseNormalizedLongIntervalCoreWitness.canonicalBufferedTauActive_allParentCFBarrier
        D hD C S hepsilon hepsilonHalf Wparent hFine
  have H : AllActiveParentCFBarrier U lower := by
    simpa only [U] using
      Family8ParentwiseLongCoreCanonicalMassPopularCFV1.AllActiveParentCFBarrier.activeFineRestricted
        H0
  change Nonempty (MassPopularSelectedParentWithCF U Y r A lower)
  exact exists_massPopularSelectedParentWithCF U Y r A hsource H

#print axioms
  exists_canonicalTauActiveRestricted_massPopularSelectedParentWithCF

end
end Family8ParentwiseLongCoreCanonicalMassPopularCFIntegrationV2
