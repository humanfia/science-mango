import Family8Grounding.Family8ParentwiseLongCoreCanonicalMassPopularCFV1
import Mathlib.Tactic

/-!
# Canonical parentwise LongCore to mass-popular CF integration

This thin module applies the literal all-parent LongCore barrier to the same
canonical tau-active cover on which the frozen mass-popular assembly is
formed.  The selected parent therefore carries its mass, average-product,
and normalized-CF conclusions on one object; no maximum-to-selected-parent
inference or callback is introduced.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8ParentwiseLongCoreCanonicalMassPopularCFIntegrationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8AllParentCFBarrierSelectedTransportV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParentwiseLongCoreCanonicalMassPopularCFV1
open Family8ParentwiseLongCoreCanonicalMassPopularCFV1.ParentwiseNormalizedLongIntervalCoreWitness
open Family8ParentwiseNormalizedLongIntervalCoreSelectorV1
open Family8ParentwiseNormalizedLongIntervalCoreSelectorV1.ParentwiseNormalizedLongIntervalCoreWitness
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8StickySelectedFineAssemblyMassPopularV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}

/-- The canonical parentwise LongCore barrier and the mass-popular selector
compose on the literal same tau-active cover and frozen assembly. -/
theorem exists_canonicalTauActive_massPopularSelectedParentWithCF
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
    let U := canonicalBufferedTauActiveCover
      D hD C S W hepsilon hepsilonHalf
    let lower : ENNReal :=
      (((canonicalBufferedRadius W / S.tau W.m : NNReal) : ENNReal) ^
        eta W.stage)
    forall (Y : Shading (tauActiveCoarseDatum D C S W).family.bodyFamily)
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
  let U := canonicalBufferedTauActiveCover
    D hD C S W hepsilon hepsilonHalf
  let lower : ENNReal :=
    (((canonicalBufferedRadius W / S.tau W.m : NNReal) : ENNReal) ^
      eta W.stage)
  have H : AllActiveParentCFBarrier U lower := by
    simpa only [W, U, lower] using
      ParentwiseNormalizedLongIntervalCoreWitness.canonicalBufferedTauActive_allParentCFBarrier
        D hD C S hepsilon hepsilonHalf Wparent hFine
  change Nonempty (MassPopularSelectedParentWithCF U Y r A lower)
  exact exists_massPopularSelectedParentWithCF U Y r A
    (by simpa only [U] using hsource) H

#print axioms exists_canonicalTauActive_massPopularSelectedParentWithCF

end
end Family8ParentwiseLongCoreCanonicalMassPopularCFIntegrationV1
