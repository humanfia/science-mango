import Family8Grounding.Family8CoreHighBlockDensityCardUpperV1
import Family8Grounding.Family8CoreHighPrefixFiberDensityBucketFineShadingV1

/-!
# Automatic occupied density-band coverage for the core-high prefix

For the active-parent actual datum, every occupied core-high occurrence has
density strictly above the high threshold.  Its density is also at most its
literal fibre cardinality, hence at most the total number of active parents.
When the threshold is at least one, the elementary base-two logarithmic bound
therefore places each occupied occurrence in one of the finitely many bands
based at that same threshold and consumed by the joint fibre-density bucket.

No density claim is made for an unoccupied greedy block.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CoreHighOccupiedDensityBandCoverageV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8CoreHighBlockDensityCardUpperV1
open Family8CoreHighPrefixFiberDensityBucketFineShadingV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8Prop51JointOccurrenceWeightedSelectionV1
open Family8TauActiveParentGreedyLowCallbackOrSameOccurrenceWeightedCordobaCoreV1
open Family8TauActiveParentGreedyRetainedHighPrefixSplitV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The literal active-parent high prefix automatically has occupied-only
density coverage based at its high threshold, with exponent range given by
the logarithm of the active-parent count. -/
theorem activeParent_coreHighPrefixWithFirstHitMass_to_densityCovered
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (A : ENNReal) (hA : 1 ≤ A)
    (hhigh : CoreHighPrefixWithFirstHitMass
      (activeParentActualTubeDatum S Y) A) :
    CoreHighPrefixWithFirstHitMassDensityCovered
      (activeParentActualTubeDatum S Y) A A
      (Nat.log 2 (Fintype.card (ActiveParentIndex S))) := by
  obtain ⟨P, selected, hfirst, hcover⟩ := hhigh
  refine ⟨P, selected, hcover, hfirst, ?_⟩
  intro q hq
  have hcore := coreHighOccurrence_of_mem_occupied
    (activeParentActualTubeDatum S Y) P A selected hcover hq
  unfold CoreHighConcentrationOccurrence at hcore
  simp only [activeParentActualTubeDatum_family_bodyFamily] at hcore
  have hlower : A ≤
      blockDensity S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P q) :=
    hcore.1.le
  have hdensityCard :=
    selectedParent_blockDensity_le_fiberCard S hrho P q
  have hfiberCard :
      ((blockAt S.activeCoarseFamily P q).fiber.card : ENNReal) ≤
        (Fintype.card (ActiveParentIndex S) : ENNReal) := by
    exact_mod_cast Finset.card_le_univ
      (blockAt S.activeCoarseFamily P q).fiber
  have hcardLogNat :
      Fintype.card (ActiveParentIndex S) <
        2 ^ (Nat.log 2 (Fintype.card (ActiveParentIndex S)) + 1) :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two _
  have hcardLog :
      (Fintype.card (ActiveParentIndex S) : ENNReal) <
        (2 : ENNReal) ^
          (Nat.log 2 (Fintype.card (ActiveParentIndex S)) + 1) := by
    exact_mod_cast hcardLogNat
  apply exists_ennrealDyadicBand_of_bounds hlower
  calc
    blockDensity S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P q) ≤
        ((blockAt S.activeCoarseFamily P q).fiber.card : ENNReal) :=
      hdensityCard
    _ ≤ (Fintype.card (ActiveParentIndex S) : ENNReal) := hfiberCard
    _ < (2 : ENNReal) ^
        (Nat.log 2 (Fintype.card (ActiveParentIndex S)) + 1) := hcardLog
    _ ≤ (2 : ENNReal) ^
          (Nat.log 2 (Fintype.card (ActiveParentIndex S)) + 1) * A := by
      simpa only [mul_one] using (mul_le_mul' le_rfl hA)

#print axioms activeParent_coreHighPrefixWithFirstHitMass_to_densityCovered

end

end Family8CoreHighOccupiedDensityBandCoverageV1
