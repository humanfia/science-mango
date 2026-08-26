import FamilyStickyGrounding.FamilyStickyScaleChainFullyAutomaticWZPackedParentCodeEndpointV2
import FamilyStickyGrounding.FamilyStickyWZ2SharedHundredSourceConstantEndpointV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainSharedParentContainerEndpointV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainTwoExponentStoppingCoreV2
open FamilyStickyScaleChainTwoParameterRecoveredEndpointV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyScaleChainFullyAutomaticFixedLocalCardEndpointV2
open FamilyStickyScaleChainWZPackedSeedLocalCardBudgetV2
open FamilyStickyScaleChainFullyAutomaticWZPackedParentCodeEndpointV2
open FamilyStickyScaleChainCollisionCellSiblingRigidityProducerV1
open FamilyStickyScaleChainParentPartitionCollisionCellSiblingRigidityProducerV1
open FamilyStickyScaleChainCanonicalParentCellCoverageProducerV1
open FamilyStickyRandomWZLineParameterGeometryV1
open FamilyStickyWZ2SharedHundredSourceConstantEndpointV1
open FamilyStickyRandomWZCommonNeighbourPackingV1
open FamilyStickyCapturedTubeBoxWidthV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1

noncomputable section

/-!
# A dimension-only parent bound from one real shared parent container

The existing hierarchy hypotheses do not put all active level-zero parents
in a bounded region: tube base points live in an unbounded Euclidean space,
while branching and collision-cell packing are local to one parent.  Thus
levelwise WZ separation alone cannot bound the number of spatially separated
parents.

This module isolates one concrete geometric datum that closes exactly that
gap.  The genuinely active parent subtype in `Index 1`, equipped with the
actual `effectiveFamily 1` tubes, is required to lie in one literal common
`100`-tube container.  Level-one WZ separation then bounds the parent count
by `commonHundredNeighbourPackingConstant`.  The resulting real parent code
feeds the existing parent-code endpoint, so the initial refined family has
the dimension-only local-card parameter

`commonHundredNeighbourPackingConstant ^ 2`.

The shared-container datum is an additional global confinement hypothesis;
it is not claimed to follow from the current hierarchy, random-motion,
branching, or parent-cell-capture interfaces.  As in the underlying endpoint,
the Sticky branch retains its ambient-index-cardinality loss.
-/

universe u

variable {depth N : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type u}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {gapEpsilon targetExponent : Real} {eta : Nat -> Real}

/-! ## The actual active-parent family -/

/-- The honest level-zero active parents, carrying their actual level-one
effective hierarchy tubes. -/
def levelZeroActiveParentFamily
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth) :
    UniformTubeFamily (H.effectiveRadius 1)
      (LevelZeroActiveParent H hdepth) :=
  (H.effectiveFamily 1).restrictTo
    ((H.step 0 hdepth).combinatorics.index.coarse)

@[simp]
theorem levelZeroActiveParentFamily_tubes
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth) (p : LevelZeroActiveParent H hdepth) :
    (levelZeroActiveParentFamily H hdepth).tubes p =
      (H.effectiveFamily 1).tubes p.1 :=
  rfl

/-- The missing global geometric confinement, stated on the real active
parent subtype rather than on an unrelated auxiliary family. -/
abbrev LevelZeroActiveParentsSharedHundredContainer
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth) :=
  SharedHundredSourceContainer (levelZeroActiveParentFamily H hdepth)

/-- Hierarchy-level WZ separation at level one restricts to the honest active
parent subtype. -/
theorem levelZeroActiveParentFamily_pairwise_WZEndpointParameterSeparated
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth) (W : HierarchyLevelWZSeparationData H) :
    Set.Pairwise
      (Set.univ : Set (LevelZeroActiveParent H hdepth))
      fun p q => WZEndpointParameterSeparated
        ((levelZeroActiveParentFamily H hdepth).tubes p)
        ((levelZeroActiveParentFamily H hdepth).tubes q) := by
  intro p _hp q _hq hpq
  change WZEndpointParameterSeparated
    ((H.effectiveFamily 1).tubes p.1)
    ((H.effectiveFamily 1).tubes q.1)
  apply W.separated 1 (by omega)
  · rw [← (H.step 0 hdepth).combinatorics.coarse_eq_refined]
    exact p.2
  · rw [← (H.step 0 hdepth).combinatorics.coarse_eq_refined]
    exact q.2
  · intro hpqValue
    apply hpq
    exact Subtype.ext hpqValue

/-- Positivity of the child radius at the first step propagates to its
level-one parent radius along the hierarchy's certified scale inequality. -/
theorem levelZeroActiveParentFamily_radius_pos
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H) (hdepth : 0 < depth) :
    0 < H.effectiveRadius 1 := by
  exact (G.childRadius_pos (zeroLayer hdepth)).trans_le
    (H.effectiveRadius_step_le 0 hdepth)

/-! ## Dimension-only parent and refined-card bounds -/

/-- A single literal shared parent container and actual level-one WZ
separation force the true active-parent count to have the WZ constant bound. -/
theorem levelZeroParentCount_le_commonHundredNeighbourPackingConstant
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H) (hdepth : 0 < depth)
    (W : HierarchyLevelWZSeparationData H)
    (shared : LevelZeroActiveParentsSharedHundredContainer H hdepth) :
    levelZeroParentCount H hdepth <=
      commonHundredNeighbourPackingConstant := by
  have hcard :=
    fintype_card_le_commonHundredNeighbourPackingConstant
      (levelZeroActiveParentFamily H hdepth)
      (levelZeroActiveParentFamily_radius_pos H G hdepth)
      (levelZeroActiveParentFamily_pairwise_WZEndpointParameterSeparated
        H hdepth W)
      shared
  simpa only [card_levelZeroActiveParent] using hcard

/-- The geometric shared-container bound is packaged as the exact real
parent code expected by the compressed WZ endpoint. -/
def levelZeroActiveParentCode_of_sharedHundredContainer
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H) (hdepth : 0 < depth)
    (W : HierarchyLevelWZSeparationData H)
    (shared : LevelZeroActiveParentsSharedHundredContainer H hdepth) :
    LevelZeroParentCode (H := H) hdepth
      commonHundredNeighbourPackingConstant where
  parentEmbedding := by
    apply (Function.Embedding.nonempty_of_card_le ?_).some
    simpa only [card_levelZeroActiveParent, Fintype.card_fin] using
      (levelZeroParentCount_le_commonHundredNeighbourPackingConstant
        H G hdepth W shared)

/-- The dimension-only local-card parameter obtained by applying WZ packing
once to the parent set and once inside each parent cell. -/
def sharedParentWZPackedSeedCardBound : Nat :=
  commonHundredNeighbourPackingConstant *
    commonHundredNeighbourPackingConstant

/-- Real parent-cell capture plus the shared-parent WZ bound gives a fully
dimension-only bound for the effective level-zero refined source. -/
theorem hierarchySharedParentWZPacked_refined_card_le
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (J : HierarchyJointRandomMotionCertificate H G)
    (hdepth : 0 < depth)
    (shared : LevelZeroActiveParentsSharedHundredContainer H hdepth)
    (Z : LevelZeroParentPartitionCollisionCellCapture H G J hdepth)
    (W : HierarchyLevelWZSeparationData H) :
    (H.effectiveFamily 0).refinement.refined.card <=
      sharedParentWZPackedSeedCardBound := by
  simpa only [sharedParentWZPackedSeedCardBound] using
    (hierarchyWZPacked_refined_card_le_parentLoss H
      (levelZeroActiveParentCode_of_sharedHundredContainer
        H G hdepth W shared)
      Z W)

/-! ## Dimension-only threshold and preferred hierarchy endpoint -/

/-- The automatic threshold at the fixed WZ-square local-card parameter. -/
def fullyAutomaticSharedParentWZPackedDeltaThreshold
    (eta : Nat -> Real) (N : Nat) (gapEpsilon : Real) : NNReal :=
  fullyAutomaticWZPackedParentCodeDeltaThreshold
    commonHundredNeighbourPackingConstant eta N gapEpsilon

theorem fullyAutomaticSharedParentWZPackedDeltaThreshold_pos
    (eta : Nat -> Real) (N : Nat) (gapEpsilon : Real) :
    0 < fullyAutomaticSharedParentWZPackedDeltaThreshold
      eta N gapEpsilon := by
  exact fullyAutomaticWZPackedParentCodeDeltaThreshold_pos
    commonHundredNeighbourPackingConstant eta N gapEpsilon

theorem fullyAutomaticSharedParentWZPackedDeltaThreshold_le_one
    (eta : Nat -> Real) (N : Nat) (gapEpsilon : Real) :
    fullyAutomaticSharedParentWZPackedDeltaThreshold
      eta N gapEpsilon <= 1 := by
  exact fullyAutomaticWZPackedParentCodeDeltaThreshold_le_one
    commonHundredNeighbourPackingConstant eta N gapEpsilon

theorem fullyAutomaticSharedParentWZPackedDeltaThreshold_lt_one
    (eta : Nat -> Real) {N : Nat} (N_pos : 1 <= N)
    (gapEpsilon : Real) :
    fullyAutomaticSharedParentWZPackedDeltaThreshold
      eta N gapEpsilon < 1 := by
  exact fullyAutomaticWZPackedParentCodeDeltaThreshold_lt_one
    commonHundredNeighbourPackingConstant eta N_pos gapEpsilon

/-- Readable terminal stage in which the shared parent container constructs
the fixed-size parent code internally. -/
def fullyAutomaticSharedParentWZPackedTerminalStage_of_levelZeroRadiusCompatible
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (J : HierarchyJointRandomMotionCertificate H G)
    (hdepth : 0 < depth)
    (shared : LevelZeroActiveParentsSharedHundredContainer H hdepth)
    (R : LevelZeroCanonicalHundredRadiusCompatible H)
    (W : HierarchyLevelWZSeparationData H)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticSharedParentWZPackedDeltaThreshold
        eta N gapEpsilon) : Nat :=
  fullyAutomaticWZPackedParentCodeTerminalStage_of_levelZeroRadiusCompatible
    H G J hdepth
    (levelZeroActiveParentCode_of_sharedHundredContainer
      H G hdepth W shared)
    R W gap_pos eta_monotone two_lt_eta_zero exponent_budget delta_le

/-- Preferred endpoint with dimension-only two-exponent local-card input.
The extra `shared` argument is precisely the global confinement absent from
the current hierarchy interfaces; no parent code or seed budget is public. -/
theorem identityFullyAutomaticSharedParentWZPacked_sticky_or_recoveredWitness_of_levelZeroRadiusCompatible
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (J : HierarchyJointRandomMotionCertificate H G)
    (hdepth : 0 < depth)
    (shared : LevelZeroActiveParentsSharedHundredContainer H hdepth)
    (R : LevelZeroCanonicalHundredRadiusCompatible H)
    (W : HierarchyLevelWZSeparationData H)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticSharedParentWZPackedDeltaThreshold
        eta N gapEpsilon) :
    (identityRadiusCoherentCover
        (H.effectiveFamily 0)).base.IsStickyAtEveryScale
      ((Fintype.card (Index 0) : ENNReal) *
        capturedTubeBoxLoss (H.effectiveRadius 0) 1)
      (((Fintype.card (Index 0) : ENNReal) *
          capturedTubeBoxLoss (H.effectiveRadius 0) 1) *
        (Fintype.card (Index 0) : ENNReal)) \/
      Nonempty (TwoExponentKatzTaoDividingWitness
        (H.effectiveRadius 0) N gapEpsilon targetExponent
        (recoveredProfileV2 eta
          (fullyAutomaticSharedParentWZPackedTerminalStage_of_levelZeroRadiusCompatible
            H G J hdepth shared R W gap_pos eta_monotone two_lt_eta_zero
            exponent_budget delta_le)
          targetExponent)) := by
  simpa
      [fullyAutomaticSharedParentWZPackedTerminalStage_of_levelZeroRadiusCompatible]
    using
      (identityFullyAutomaticWZPackedParentCode_sticky_or_recoveredWitness_of_levelZeroRadiusCompatible
        H G J hdepth
        (levelZeroActiveParentCode_of_sharedHundredContainer
          H G hdepth W shared)
        R W gap_pos eta_monotone two_lt_eta_zero exponent_budget
        room_at_bound delta_le)

/-- V1 literal-witness projection of the dimension-only preferred endpoint. -/
theorem identityFullyAutomaticSharedParentWZPacked_sticky_or_recoveredLiteralWitness_of_levelZeroRadiusCompatible
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (J : HierarchyJointRandomMotionCertificate H G)
    (hdepth : 0 < depth)
    (shared : LevelZeroActiveParentsSharedHundredContainer H hdepth)
    (R : LevelZeroCanonicalHundredRadiusCompatible H)
    (W : HierarchyLevelWZSeparationData H)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticSharedParentWZPackedDeltaThreshold
        eta N gapEpsilon) :
    (identityRadiusCoherentCover
        (H.effectiveFamily 0)).base.IsStickyAtEveryScale
      ((Fintype.card (Index 0) : ENNReal) *
        capturedTubeBoxLoss (H.effectiveRadius 0) 1)
      (((Fintype.card (Index 0) : ENNReal) *
          capturedTubeBoxLoss (H.effectiveRadius 0) 1) *
        (Fintype.card (Index 0) : ENNReal)) \/
      Nonempty (KatzTaoDividingWitness
        (H.effectiveRadius 0) N gapEpsilon
        (recoveredProfileV2 eta
          (fullyAutomaticSharedParentWZPackedTerminalStage_of_levelZeroRadiusCompatible
            H G J hdepth shared R W gap_pos eta_monotone two_lt_eta_zero
            exponent_budget delta_le)
          targetExponent)) := by
  rcases
      identityFullyAutomaticSharedParentWZPacked_sticky_or_recoveredWitness_of_levelZeroRadiusCompatible
        H G J hdepth shared R W gap_pos eta_monotone two_lt_eta_zero
        exponent_budget room_at_bound delta_le with sticky | witness
  · exact Or.inl sticky
  · rcases witness with ⟨witness⟩
    exact Or.inr ⟨witness.toV1⟩

#print axioms levelZeroActiveParentFamily_pairwise_WZEndpointParameterSeparated
#print axioms levelZeroParentCount_le_commonHundredNeighbourPackingConstant
#print axioms levelZeroActiveParentCode_of_sharedHundredContainer
#print axioms hierarchySharedParentWZPacked_refined_card_le
#print axioms fullyAutomaticSharedParentWZPackedDeltaThreshold_pos
#print axioms fullyAutomaticSharedParentWZPackedDeltaThreshold_le_one
#print axioms fullyAutomaticSharedParentWZPackedDeltaThreshold_lt_one
#print axioms fullyAutomaticSharedParentWZPackedTerminalStage_of_levelZeroRadiusCompatible
#print axioms identityFullyAutomaticSharedParentWZPacked_sticky_or_recoveredWitness_of_levelZeroRadiusCompatible
#print axioms identityFullyAutomaticSharedParentWZPacked_sticky_or_recoveredLiteralWitness_of_levelZeroRadiusCompatible

end
end FamilyStickyScaleChainSharedParentContainerEndpointV2
