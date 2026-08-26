import FamilyStickyGrounding.FamilyStickyHierarchyEndpointPrefixShadingTransportV1
import FamilyStickyGrounding.FamilyStickyHierarchyWZ2CollisionCellShadingRestrictionV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyHierarchyWZ2CollisionCellRetainedMassProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainArbitraryRadiusInterpolationV1
open FamilyStickyHierarchyEndpointPrefixBridgeV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.BodyPreservingEmbedding
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyCollisionTestGeometryProducerV1
open FamilyStickyHierarchyPreMotionHullTestSupportV1
open FamilyStickyHierarchySuppliedPackingJointRandomMotionV1
open FamilyStickyHierarchySuppliedPackingJointRandomMotionV1.SuppliedHierarchy
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyHierarchyWZ2CollisionCellSourceAdapterV1
open FamilyStickyHierarchyWZ2CollisionCellShadingRestrictionV1

noncomputable section

/-!
# Actual hierarchy shading and collision-cell mass retention

The endpoint/effective identification already records an injective,
body-preserving map from every active endpoint occurrence into one literal
effective hierarchy layer.  Empty extension along the composite map to the
whole level index therefore produces an actual shading of that effective
family.  In particular, its carrier is empty away from the hierarchy step's
active fine set.

For one fixed random-motion repetition, every active child belongs to the
collision cell centered at its own translated tube.  Summing those literal
self-cells and choosing a largest term gives one actual parent and one actual
model candidate which retain the whole produced level shading up to exactly
the number of active children.  No retained-mass or density conclusion is an
input to that selection.
-/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  {G : HierarchyRandomMotionGeometry H}
  {P : HierarchyPackingPlan.Plan H}
  (Q : SuppliedHierarchy.Certificate H G P)
  (C : CoherentStickyMultiscaleCover (H.effectiveFamily 0))
  (S : FiniteScaleSequence (H.effectiveRadius 0) depth)

namespace Identification

variable {H Q C S}
  (I : FamilyStickyHierarchyEndpointPrefixBridgeV1.Identification H Q C S)

/-- The endpoint-to-effective embedding, followed by the canonical subtype
map into the whole literal index type of the selected hierarchy level. -/
def endpointEffectiveLevelIndexEmbedding (m : Fin depth) :
    EndpointIndex H C S m ↪ Index (I.endpointEffective.layer m).1 where
  toFun := fun i => (I.endpointEffective.indexEmbedding m i).1
  inj' := by
    intro i j hij
    apply (I.endpointEffective.indexEmbedding m).injective
    exact Subtype.ext hij

@[simp]
theorem endpointEffectiveLevelIndexEmbedding_apply
    (m : Fin depth) (i : EndpointIndex H C S m) :
    endpointEffectiveLevelIndexEmbedding I m i =
      (I.endpointEffective.indexEmbedding m i).1 := rfl

/-- Body preservation remains literal after forgetting the active-index
subtype proof. -/
def endpointEffectiveLevelBodyEmbedding (m : Fin depth) :
    BodyPreservingEmbedding
      (endpointFamily H C S m)
      (H.effectiveFamily (I.endpointEffective.layer m).1).bodyFamily where
  index := endpointEffectiveLevelIndexEmbedding I m
  body_eq := by
    intro i
    simpa [FamilyStickyHierarchyEndpointPrefixBridgeV1.effectiveFamily]
      using I.endpointEffective.body_eq m i

/-- Actual level-`k` shading produced from the original level-zero shading:
first aggregate the endpoint's active fine pieces in their literal endpoint
parents, then extend those pieces by the empty set along the identified
effective-level occurrence embedding. -/
def effectiveLevelShading (m : Fin depth)
    (Y : Shading (H.effectiveFamily 0).bodyFamily) :
    Shading
      (H.effectiveFamily (I.endpointEffective.layer m).1).bodyFamily :=
  (endpointEffectiveLevelBodyEmbedding I m).pushforwardShading
    (FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover.parentAggregatedShading
      (upperEndpointCover C S m) Y)

@[simp]
theorem effectiveLevelShading_carrier_embedded
    (m : Fin depth) (Y : Shading (H.effectiveFamily 0).bodyFamily)
    (i : EndpointIndex H C S m) :
    (Identification.effectiveLevelShading I m Y).carrier
        (endpointEffectiveLevelIndexEmbedding I m i) =
      (FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover.parentAggregatedShading
        (upperEndpointCover C S m) Y).carrier i := by
  exact (endpointEffectiveLevelBodyEmbedding I m).pushforwardShading_carrier_index _ _

/-- The produced level shading has exactly the endpoint-parent aggregated
mass; empty extension introduces no hidden mass. -/
theorem effectiveLevelShading_shadingMass
    (m : Fin depth) (Y : Shading (H.effectiveFamily 0).bodyFamily) :
    (Identification.effectiveLevelShading I m Y).shadingMass =
      (FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover.parentAggregatedShading
        (upperEndpointCover C S m) Y).shadingMass := by
  exact (endpointEffectiveLevelBodyEmbedding I m).pushforwardShading_shadingMass _

/-- Every carrier outside the actual active fine set is definitionally the
empty extension.  This is the support fact needed for parent-fibre
decomposition. -/
theorem effectiveLevelShading_carrier_eq_empty_of_not_fine
    (m : Fin depth) (Y : Shading (H.effectiveFamily 0).bodyFamily)
    (i : Index (I.endpointEffective.layer m).1)
    (hi : i ∉
      ((H.step (I.endpointEffective.layer m).1
        (I.endpointEffective.layer m).2).combinatorics.index.fine)) :
    (Identification.effectiveLevelShading I m Y).carrier i = ∅ := by
  exact
    (endpointEffectiveLevelBodyEmbedding I m).pushforwardCarrier_of_not_range
      (FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover.parentAggregatedShading
        (upperEndpointCover C S m) Y) i (by
        intro hirange
        obtain ⟨j, hj⟩ := hirange
        apply hi
        rw [← hj]
        have hjFine := (I.endpointEffective.indexEmbedding m j).2
        rw [(H.step (I.endpointEffective.layer m).1
          (I.endpointEffective.layer m).2).combinatorics.fine_eq_refined]
        simpa [endpointEffectiveLevelBodyEmbedding,
          endpointEffectiveLevelIndexEmbedding_apply,
          MultiscaleTubeHierarchy.effectiveFamily,
          UniformTubeFamily.buffer] using hjFine)

end Identification

/-! ## Literal self-collision cells at one hierarchy layer -/


/-- Active children at one hierarchy step. -/
abbrev ActiveHierarchyChildIndex (k : Fin depth) :=
  {i : Index k.1 //
    i ∈ (H.step k.1 k.2).combinatorics.index.fine}

/-- The actual parent of an active hierarchy child. -/
def activeHierarchyChildParent (k : Fin depth)
    (i : ActiveHierarchyChildIndex (H := H) k) : Index (k.1 + 1) :=
  (H.step k.1 k.2).combinatorics.index.parent i.1

/-- The parent of an active child is an actual active parent of the random
motion layer. -/
theorem activeHierarchyChildParent_mem_activeParents
    (k : Fin depth) (i : ActiveHierarchyChildIndex (H := H) k) :
    activeHierarchyChildParent (H := H) k i ∈
      (G.toDependentSource.layer k).activeParents := by
  simpa [activeHierarchyChildParent,
    HierarchyRandomMotionGeometry.toDependentSource,
    hierarchyLayer] using
      (H.step k.1 k.2).combinatorics.index.parent_mem i.1 i.2

/-- At a fixed repetition, center the model collision test at the active
child's own translated tube. -/
def activeHierarchyChildModelCandidate
    (joint : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (r : Fin (repetitions G.toDependentSource k))
    (i : ActiveHierarchyChildIndex (H := H) k) :
    ModelCandidate
      (hierarchyCollisionGrid H G joint k
        (activeHierarchyChildParent (H := H) k i)) :=
  (⟨i.1, by
      change i.1 ∈
        (H.step k.1 k.2).combinatorics.index.fiber
          (activeHierarchyChildParent (H := H) k i)
      exact (H.step k.1 k.2).combinatorics.index.mem_fiber _ _ |>.2
        ⟨i.2, rfl⟩⟩,
    (joint.output.layerOutput k).omega r)

/-- The source child is literally a member of its own collision cell. -/
theorem activeHierarchyChild_mem_own_candidateCollisionFinset
    (joint : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (r : Fin (repetitions G.toDependentSource k))
    (i : ActiveHierarchyChildIndex (H := H) k) :
    i.1 ∈ candidateCollisionFinset
      (hierarchyCollisionGrid H G joint k
        (activeHierarchyChildParent (H := H) k i))
      (activeHierarchyChildModelCandidate (H := H) (G := G) joint k r i)
      ((joint.output.layerOutput k).omega r) := by
  apply (mem_candidateCollisionFinset _ _ _ _).2
  constructor
  · change i.1 ∈
      (H.step k.1 k.2).combinatorics.index.fiber
        (activeHierarchyChildParent (H := H) k i)
    exact (H.step k.1 k.2).combinatorics.index.mem_fiber _ _ |>.2
      ⟨i.2, rfl⟩
  · change
      (modelCandidateTube
        (hierarchyCollisionGrid H G joint k
          (activeHierarchyChildParent (H := H) k i))
        (activeHierarchyChildModelCandidate (H := H) (G := G) joint k r i)).carrier ⊆
      (hundredTube
        (modelCandidateTube
          (hierarchyCollisionGrid H G joint k
            (activeHierarchyChildParent (H := H) k i))
          (activeHierarchyChildModelCandidate (H := H) (G := G) joint k r i))).carrier
    exact carrier_subset_hundredTube _

/-- The actual collision-cell shading obtained by restricting a level
shading to the self-centered cell of one active child. -/
abbrev activeHierarchyChildCollisionCellShading
    (joint : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (r : Fin (repetitions G.toDependentSource k))
    (Y : Shading (H.effectiveFamily k.1).bodyFamily)
    (i : ActiveHierarchyChildIndex (H := H) k) :=
  selectedHierarchyCollisionCellShading joint k
    (activeHierarchyChildParent (H := H) k i)
    (activeHierarchyChildModelCandidate (H := H) (G := G) joint k r i) r Y

/-- One active shading piece is a term of its literal self-centered
collision-cell mass. -/
theorem activeHierarchyChild_piece_le_ownCollisionCell_shadingMass
    (joint : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (r : Fin (repetitions G.toDependentSource k))
    (Y : Shading (H.effectiveFamily k.1).bodyFamily)
    (i : ActiveHierarchyChildIndex (H := H) k) :
    volume (Y.carrier i.1) ≤
      (activeHierarchyChildCollisionCellShading (H := H) (G := G) joint k r Y i).shadingMass := by
  rw [selectedHierarchyCollisionCellShading_shadingMass]
  let cellIndex : SelectedHierarchyCollisionCellIndex H G joint k
      (activeHierarchyChildParent (H := H) k i)
      (activeHierarchyChildModelCandidate (H := H) (G := G) joint k r i) r :=
    ⟨i.1, activeHierarchyChild_mem_own_candidateCollisionFinset (H := H) (G := G) joint k r i⟩
  exact Finset.single_le_sum
    (f := fun j : SelectedHierarchyCollisionCellIndex H G joint k
      (activeHierarchyChildParent (H := H) k i)
      (activeHierarchyChildModelCandidate (H := H) (G := G) joint k r i) r =>
        volume (Y.carrier j.1))
    (fun _ _ => bot_le) (Finset.mem_univ cellIndex)

/-- The active child type is nonempty at every genuine hierarchy step. -/
theorem activeHierarchyChildIndex_nonempty (k : Fin depth) :
    Nonempty (ActiveHierarchyChildIndex (H := H) k) := by
  obtain ⟨p, hp⟩ :=
    (H.step k.1 k.2).combinatorics.coarse_nonempty
  obtain ⟨i, hi, _hip⟩ :=
    (H.step k.1 k.2).combinatorics.parent_surjective p hp
  exact ⟨⟨i, hi⟩⟩

/-- Finite self-cell selection.  If a level shading is supported on the
hierarchy step's active fine set, one actual self-centered collision cell
retains its entire mass up to exactly the number of active children. -/
theorem exists_activeHierarchyChild_shadingMass_le_card_mul_ownCollisionCell
    (joint : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (r : Fin (repetitions G.toDependentSource k))
    (Y : Shading (H.effectiveFamily k.1).bodyFamily)
    (hsupport : ∀ i : Index k.1,
      i ∉ (H.step k.1 k.2).combinatorics.index.fine →
        Y.carrier i = ∅) :
    ∃ i : ActiveHierarchyChildIndex (H := H) k,
      Y.shadingMass ≤
        (Fintype.card (ActiveHierarchyChildIndex (H := H) k) : ENNReal) *
          (activeHierarchyChildCollisionCellShading (H := H) (G := G) joint k r Y i).shadingMass := by
  classical
  let _ : Nonempty (ActiveHierarchyChildIndex (H := H) k) :=
    activeHierarchyChildIndex_nonempty (H := H) k
  let cellMass : ActiveHierarchyChildIndex (H := H) k → ENNReal :=
    fun i =>
      (activeHierarchyChildCollisionCellShading (H := H) (G := G) joint k r Y i).shadingMass
  obtain ⟨i, _hi, hmax⟩ :=
    Finset.exists_max_image
      (Finset.univ : Finset (ActiveHierarchyChildIndex (H := H) k))
      cellMass Finset.univ_nonempty
  refine ⟨i, ?_⟩
  have hsupportSum :
      Y.shadingMass =
        ∑ j ∈ (H.step k.1 k.2).combinatorics.index.fine,
          volume (Y.carrier j) := by
    unfold Shading.shadingMass
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _hj hjFine
    rw [hsupport j hjFine]
    simp
  calc
    Y.shadingMass =
        ∑ j ∈ (H.step k.1 k.2).combinatorics.index.fine,
          volume (Y.carrier j) := hsupportSum
    _ = ∑ j : ActiveHierarchyChildIndex (H := H) k,
          volume (Y.carrier j.1) := by
      rw [← Finset.attach_eq_univ]
      exact (Finset.sum_attach _ _).symm
    _ ≤ ∑ j : ActiveHierarchyChildIndex (H := H) k, cellMass j := by
      apply Finset.sum_le_sum
      intro j _hj
      exact activeHierarchyChild_piece_le_ownCollisionCell_shadingMass
        (H := H) (G := G) joint k r Y j
    _ ≤ (Finset.univ : Finset
          (ActiveHierarchyChildIndex (H := H) k)).card • cellMass i :=
      Finset.sum_le_card_nsmul _ cellMass (cellMass i)
        (fun j hj => hmax j hj)
    _ = (Fintype.card (ActiveHierarchyChildIndex (H := H) k) : ENNReal) *
          (activeHierarchyChildCollisionCellShading (H := H) (G := G) joint k r Y i).shadingMass := by
      simp [cellMass, nsmul_eq_mul]

/-! ## The actual endpoint-produced level shading enters the selection -/

variable {Q C S}

/-- The endpoint/effective producer automatically discharges the support
hypothesis of the self-cell selection theorem. -/
theorem exists_endpointEffectiveLevelShading_shadingMass_le_card_mul_cell
    (I : FamilyStickyHierarchyEndpointPrefixBridgeV1.Identification H Q C S)
    (m : Fin depth)
    (Y : Shading (H.effectiveFamily 0).bodyFamily)
    (r : Fin (repetitions G.toDependentSource
      (I.endpointEffective.layer m))) :
    ∃ i : ActiveHierarchyChildIndex
        (H := H) (I.endpointEffective.layer m),
      (Identification.effectiveLevelShading I m Y).shadingMass ≤
        (Fintype.card (ActiveHierarchyChildIndex
          (H := H) (I.endpointEffective.layer m)) : ENNReal) *
          (activeHierarchyChildCollisionCellShading (H := H) (G := G) Q.joint
            (I.endpointEffective.layer m) r
            (Identification.effectiveLevelShading I m Y) i).shadingMass := by
  apply exists_activeHierarchyChild_shadingMass_le_card_mul_ownCollisionCell
    (H := H) (G := G) Q.joint (I.endpointEffective.layer m) r (Identification.effectiveLevelShading I m Y)
  intro i hi
  exact Identification.effectiveLevelShading_carrier_eq_empty_of_not_fine I m Y i hi

/-- Density transport for the selected actual cell.  The only remaining
analytic input is a lower bound on the density of the explicitly produced
level shading, multiplied by the exact finite selection loss. -/
theorem exists_endpointEffectiveLevelShading_cell_densityLower
    (I : FamilyStickyHierarchyEndpointPrefixBridgeV1.Identification H Q C S)
    (m : Fin depth)
    (Y : Shading (H.effectiveFamily 0).bodyFamily)
    (r : Fin (repetitions G.toDependentSource
      (I.endpointEffective.layer m)))
    (alpha : Real)
    (hsourceDensity :
      ENNReal.ofReal alpha *
          (Fintype.card (ActiveHierarchyChildIndex
            (H := H) (I.endpointEffective.layer m)) : ENNReal) ≤
        (Identification.effectiveLevelShading I m Y).shadingDensity) :
    ∃ i : ActiveHierarchyChildIndex
        (H := H) (I.endpointEffective.layer m),
      ENNReal.ofReal alpha ≤
        (activeHierarchyChildCollisionCellShading (H := H) (G := G) Q.joint
          (I.endpointEffective.layer m) r
          (Identification.effectiveLevelShading I m Y) i).shadingDensity := by
  obtain ⟨i, hretained⟩ :=
    exists_endpointEffectiveLevelShading_shadingMass_le_card_mul_cell
      (H := H) (G := G) I m Y r
  refine ⟨i, ?_⟩
  let _ : Nonempty (ActiveHierarchyChildIndex
      (H := H) (I.endpointEffective.layer m)) := ⟨i⟩
  apply ofReal_le_selectedHierarchyCollisionCellShading_density_of_retainedMass
    Q.joint (I.endpointEffective.layer m)
      (activeHierarchyChildParent (H := H)
        (I.endpointEffective.layer m) i)
      (activeHierarchyChildModelCandidate (H := H) (G := G) Q.joint
        (I.endpointEffective.layer m) r i)
      r (Identification.effectiveLevelShading I m Y) alpha
      (Fintype.card (ActiveHierarchyChildIndex
        (H := H) (I.endpointEffective.layer m)) : ENNReal)
  · exact_mod_cast Fintype.card_ne_zero
  · exact ENNReal.coe_ne_top
  · exact hretained
  · exact hsourceDensity

#print axioms Identification.effectiveLevelShading
#print axioms Identification.effectiveLevelShading_shadingMass
#print axioms Identification.effectiveLevelShading_carrier_eq_empty_of_not_fine
#print axioms activeHierarchyChild_mem_own_candidateCollisionFinset
#print axioms activeHierarchyChild_piece_le_ownCollisionCell_shadingMass
#print axioms exists_activeHierarchyChild_shadingMass_le_card_mul_ownCollisionCell
#print axioms exists_endpointEffectiveLevelShading_shadingMass_le_card_mul_cell
#print axioms exists_endpointEffectiveLevelShading_cell_densityLower

end
end FamilyStickyHierarchyWZ2CollisionCellRetainedMassProducerV1
