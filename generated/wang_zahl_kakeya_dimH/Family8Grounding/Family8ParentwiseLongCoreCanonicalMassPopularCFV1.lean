import Family8Grounding.Family8ParentwiseNormalizedLongIntervalCoreSelectorV1
import Family8Grounding.Family8AllParentCFBarrierSelectedTransportV1
import Family8Grounding.Family8NormalizedLongCoreTauActiveCFAtTransportV2
import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictedCFAtV1
import Family8Grounding.Family8StickySelectedFineAssemblyMassPopularV1
import Family8Grounding.Family8SelectedFineFiberCardCapTransportV2
import Mathlib.Tactic

/-!
# Parentwise LongCore barrier on the canonical mass-popular assembly parent

The paper's LongCore lower barrier is universal over the active parents of
the literal buffered interval cover.  This file transports that memberwise
statement through the two honest reindexings used by the frozen assembly:
first to the canonical tau-active cover, then to its active-fine restriction.
The final record stores the normalized-CF lower bound on the very same old
parent represented by the mass-popular selected-fine assembly fibre.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3600000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8ParentwiseLongCoreCanonicalMassPopularCFV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8AllParentCFBarrierSelectedTransportV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveCFAtTransportV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParentwiseNormalizedLongIntervalCoreSelectorV1
open Family8ParentwiseNormalizedLongIntervalCoreSelectorV1.ParentwiseNormalizedLongIntervalCoreWitness
open Family8SelectedFineFiberCardCapTransportV2
open Family8StickyActiveRestrictedCoarseKatzTaoV1
open Family8StickyScaleCoverActiveFineRestrictedCFAtV1.StickyScaleCover
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8StickySelectedFineAssemblyFiberBridgeV1
open Family8StickySelectedFineAssemblyMassPopularV1
open Family8StickySelectedFineSubtypeScaleCoverV1
open Family8StickyFiberContractedJohnProxyDatumV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

namespace AllActiveParentCFBarrier

/-- The all-parent barrier survives the full active-fine reindexing used as
the source cover of the frozen assembly. -/
theorem activeFineRestricted
    {S : StickyScaleCover fine rho} {lower : ENNReal}
    (H : AllActiveParentCFBarrier S lower) :
    AllActiveParentCFBarrier (activeFineRestrictedScaleCover S) lower := by
  constructor
  intro q
  rw [activeFineRestricted_parentNormalizedFiberCFAt_eq S q]
  exact H.lower_at (restrictedCoarseEquivActive S q.1)

end AllActiveParentCFBarrier

variable {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}

namespace ParentwiseNormalizedLongIntervalCoreWitness

/-- A faithful parentwise LongCore gives the same all-parent barrier on the
canonical tau-active cover.  The equality of normalized constants across the
tau-active reindexing is literal and body-preserving. -/
theorem canonicalBufferedTauActive_allParentCFBarrier
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    (Wparent : ParentwiseNormalizedLongIntervalCoreWitness
      D hD C N epsilon hepsilon eta S)
    (hFine : D.family.refinement.refined.Nonempty) :
    let W := Wparent.toNormalizedLongIntervalCoreWitness
      D hD C S hepsilon hFine
    AllActiveParentCFBarrier
      (canonicalBufferedTauActiveCover
        D hD C S W hepsilon hepsilonHalf)
      ((((canonicalBufferedRadius W / S.tau W.m : NNReal) : ENNReal) ^
        eta W.stage)) := by
  dsimp only
  let W := Wparent.toNormalizedLongIntervalCoreWitness
    D hD C S hepsilon hFine
  have hbufferedW :
      S.IsBuffered epsilon W.m (canonicalBufferedRadius W) :=
    canonicalBufferedRadius_isBuffered W hD.delta_pos hepsilon hepsilonHalf
  have hbufferedParent :
      S.IsBuffered epsilon Wparent.m (canonicalBufferedRadius W) := by
    simpa only [W,
      ParentwiseNormalizedLongIntervalCoreWitness.toNormalizedLongIntervalCoreWitness]
      using hbufferedW
  constructor
  intro q
  rw [canonicalBufferedTauActive_parentNormalizedFiberCFAt_eq_interval
    D hD C S W hepsilon hepsilonHalf q]
  have hparent := Wparent.middle_parentwise_lower
    (canonicalBufferedRadius W) hbufferedParent q
  convert hparent using 1 <;> rfl

end ParentwiseNormalizedLongIntervalCoreWitness

variable {r : Real}

/-- The old assembly-cover parent represented by a selected-fine coarse
index. -/
def selectedFineOldParent
    (S : StickyScaleCover fine rho) (selected : Finset index)
    (q : Fin (selectedFineParentValues S selected).card) :
    Fin S.coarseCard :=
  ((selectedFineParentValues S selected).equivFin.symm q).1

/-- One record tying all downstream properties to one literal selected
parent: it is mass-popular, survives geometrically, is the second factor in
the actual-average product, and its old assembly-cover parent obeys the
LongCore normalized-CF lower barrier. -/
structure MassPopularSelectedParentWithCF
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) (r : Real)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (toConvexFactorization S) Y r)
    (lower : ENNReal) where
  q : {q // q ∈
    (selectedFineScaleCover S A.refinement.indices
      (assembly_indices_subset_activeFine S Y r A)).activeCoarse}
  oldParent_active :
    selectedFineOldParent S A.refinement.indices q.1 ∈ S.activeCoarse
  cf_lower : lower <= parentNormalizedFiberCFAt S
    ⟨selectedFineOldParent S A.refinement.indices q.1, oldParent_active⟩
  source_mass :
    (sourceActiveFineShading (toConvexFactorization S) Y).shadingMass <=
      (A.loss : ENNReal) * (S.activeCoarse.card : ENNReal) *
        (stickyFiberSourceShading
          (selectedFineScaleCover S A.refinement.indices
            (assembly_indices_subset_activeFine S Y r A))
          (selectedFineShading S A.refinement.indices A.refinement.shading)
          q.1).shadingMass
  positive_union : 0 < volume
    (stickyFiberSourceShading
      (selectedFineScaleCover S A.refinement.indices
        (assembly_indices_subset_activeFine S Y r A))
      (selectedFineShading S A.refinement.indices A.refinement.shading)
      q.1).shadedUnion
  average_product :
    (actualRefinementShading A).averageMultiplicity <=
      4 * (A.frozenCoarse.averageMultiplicity *
        (stickyFiberSourceShading
          (selectedFineScaleCover S A.refinement.indices
            (assembly_indices_subset_activeFine S Y r A))
          (selectedFineShading S A.refinement.indices A.refinement.shading)
          q.1).averageMultiplicity)

/-- The mass-popular producer, strengthened by an all-parent normalized-CF
barrier without changing its selected parent. -/
theorem exists_massPopularSelectedParentWithCF
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) (r : Real)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (toConvexFactorization S) Y r)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y S.activeFine).shading.shadingMass
        ≠ 0)
    {lower : ENNReal} (H : AllActiveParentCFBarrier S lower) :
    Nonempty (MassPopularSelectedParentWithCF S Y r A lower) := by
  obtain ⟨q, hmass, hpositive, hproduct⟩ :=
    exists_selectedFine_massPopular_sameAssemblyFiber_product
      S Y r A hsource
  let oldParent := selectedFineOldParent S A.refinement.indices q.1
  have hactive : oldParent ∈ S.activeCoarse := by
    exact selectedFineScaleCover_parent_mem_activeCoarse
      S A.refinement.indices
        (assembly_indices_subset_activeFine S Y r A) q.1
  exact ⟨{
    q := q
    oldParent_active := hactive
    cf_lower := H.lower_at ⟨oldParent, hactive⟩
    source_mass := hmass
    positive_union := hpositive
    average_product := hproduct }⟩

#print axioms AllActiveParentCFBarrier.activeFineRestricted
#print axioms
  ParentwiseNormalizedLongIntervalCoreWitness.canonicalBufferedTauActive_allParentCFBarrier
#print axioms MassPopularSelectedParentWithCF
#print axioms exists_massPopularSelectedParentWithCF

end
end Family8ParentwiseLongCoreCanonicalMassPopularCFV1
