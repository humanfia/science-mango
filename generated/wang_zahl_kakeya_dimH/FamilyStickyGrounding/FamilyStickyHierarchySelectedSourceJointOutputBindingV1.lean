import FamilyStickyGrounding.FamilyStickyHierarchySelectedSourceJointOutputSemanticTransportV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open Set
open scoped BigOperators NNReal

namespace FamilyStickyHierarchySelectedSourceJointOutputBindingV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyActualTubeTranslationV1
open FamilyStickyAllParentLayerDataV1
open FamilyStickyAllParentLayerDataV1.AllParentLayerData
open FamilyStickyAllParentLayerJointRepetitionsV1
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.Output
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1.HierarchyJointRandomMotionCertificate
open FamilyStickyHierarchyTerminalCarrierDedupV1
open FamilyStickyHierarchyTerminalSamePathWZEliminationV1
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyTerminalSourceChartBucketProducerV1
open FamilyStickyHierarchySelectedSourceNestedRestrictionV1
open FamilyStickyHierarchySelectedSourceJointOutputSemanticTransportV1
open FamilyStickyHierarchySelectedSourceJointOutputSemanticTransportV1.RestrictedJointOutputSemanticTransport

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Binding the genuine selected hierarchy to an old joint output

The recursively selected hierarchy has genuine subtype fibres. Its test
families are inherited from the corresponding old parents, while its radii
and certified branching factors agree with the old hierarchy. This module
constructs that geometry first, then isolates the two exact joint-output
selection fields which hierarchy restriction alone cannot determine.
-/

universe u

variable {depth : Nat} {nominalRadius : Nat → NNReal}
  {Index : Nat → Type u}
  [∀ l, Fintype (Index l)] [∀ l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}

/-- Forgetting a recursively selected parent proof lands in the old active
coarse set. -/
theorem selectedParent_val_mem_originalCoarse
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (k : Fin depth) (p : SelectedHierarchyIndex S (k.1 + 1)) :
    p.1 ∈ (H.step k.1 k.2).combinatorics.index.coarse := by
  rw [(H.step k.1 k.2).combinatorics.coarse_eq_refined]
  exact selectedLevelIndices_subset_refined S.selected_subset_source
    (k.1 + 1) (Nat.succ_le_iff.mpr k.2) p.2

/-- The old parent test suite, restricted only in its hierarchy indices,
provides genuine random-motion geometry for the rebuilt selected hierarchy. -/
def selectedHierarchyRandomMotionGeometry
    (G : HierarchyRandomMotionGeometry H)
    (S : SelectedTerminalSourceChartBucketGeometry (H := H)) :
    HierarchyRandomMotionGeometry (selectedHierarchy S) where
  tests := fun k p => G.tests k p.1
  childRadius_pos := by
    intro k
    simpa only [selectedHierarchy_effectiveRadius_eq] using
      G.childRadius_pos k
  childRadius_le_half := by
    intro k
    simpa only [selectedHierarchy_effectiveRadius_eq] using
      G.childRadius_le_half k
  parentRadius_le_one := by
    intro k
    simpa only [selectedHierarchy_effectiveRadius_eq] using
      G.parentRadius_le_one k
  childRadius_le_side_zero := by
    intro k p _hp K hK
    simpa only [selectedHierarchy_effectiveRadius_eq] using
      G.childRadius_le_side_zero k p.1
        (selectedParent_val_mem_originalCoarse S k p) K hK
  childRadius_le_side_one := by
    intro k p _hp K hK
    simpa only [selectedHierarchy_effectiveRadius_eq] using
      G.childRadius_le_side_one k p.1
        (selectedParent_val_mem_originalCoarse S k p) K hK
  branchingMeanScale := by
    intro k p _hp K hK
    simpa only [selectedHierarchy_effectiveRadius_eq,
      selectedHierarchy_step_branchingFactor] using
      G.branchingMeanScale k p.1
        (selectedParent_val_mem_originalCoarse S k p) K hK

/-- Short name for the actual selected hierarchy geometry. -/
abbrev SelectedGeometry
    (G : HierarchyRandomMotionGeometry H)
    (S : SelectedTerminalSourceChartBucketGeometry (H := H)) :=
  selectedHierarchyRandomMotionGeometry G S

/-- Selected parents inject into the old parent index type by forgetting only
the recursively generated membership proof. -/
def selectedParentEmbedding
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (k : Fin depth) :
    SelectedHierarchyIndex S (k.1 + 1) ↪ Index (k.1 + 1) :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- The selected layer test is the same test number over an honestly embedded
old parent. -/
def selectedLayerTestEmbedding
    (G : HierarchyRandomMotionGeometry H)
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (k : Fin depth) :
    ((SelectedGeometry G S).toDependentSource.layer k).Test ↪
      (G.toDependentSource.layer k).Test :=
  ⟨fun q => ⟨q.1.1, q.2⟩, by
    intro q r hqr
    rcases q with ⟨p, K⟩
    rcases r with ⟨q, L⟩
    have hpq : p = q := Subtype.ext (congrArg Sigma.fst hqr)
    subst q
    cases hqr
    rfl⟩

/-- Every actual selected active test maps to an actual old active test. -/
theorem selectedLayerTestEmbedding_mem_activeTests
    (G : HierarchyRandomMotionGeometry H)
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (k : Fin depth)
    (q : ((SelectedGeometry G S).toDependentSource.layer k).Test)
    (hq : q ∈ ((SelectedGeometry G S).toDependentSource.layer k).activeTests) :
    selectedLayerTestEmbedding G S k q ∈
      (G.toDependentSource.layer k).activeTests := by
  rw [AllParentLayerData.mem_activeTests_iff] at hq ⊢
  exact ⟨selectedParent_val_mem_originalCoarse S k q.1, hq.2⟩

/-! ## Images of the genuine selected active data -/

/-- The old-test image of the actual selected active test finset. -/
def selectedActiveTestsInOld
    (G : HierarchyRandomMotionGeometry H)
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (k : Fin depth) : Finset (G.toDependentSource.layer k).Test :=
  ((SelectedGeometry G S).toDependentSource.layer k).activeTests.image
    (selectedLayerTestEmbedding G S k)

/-- The selected active-test image is automatically contained in the old
active-test family. -/
theorem selectedActiveTestsInOld_subset
    (G : HierarchyRandomMotionGeometry H)
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (k : Fin depth) :
    selectedActiveTestsInOld G S k ⊆
      (G.toDependentSource.layer k).activeTests := by
  intro q hq
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
  exact selectedLayerTestEmbedding_mem_activeTests G S k r hr

/-- The old-parent image of the genuine selected active parent finset. -/
def selectedActiveParentsInOld
    (G : HierarchyRandomMotionGeometry H)
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (k : Fin depth) : Finset (Index (k.1 + 1)) :=
  ((SelectedGeometry G S).toDependentSource.layer k).activeParents.image
    Subtype.val

/-- Every selected active parent remains an old active parent. -/
theorem selectedActiveParentsInOld_subset
    (G : HierarchyRandomMotionGeometry H)
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (k : Fin depth) :
    selectedActiveParentsInOld G S k ⊆
      (G.toDependentSource.layer k).activeParents := by
  intro p hp
  obtain ⟨q, _hq, rfl⟩ := Finset.mem_image.mp hp
  exact selectedParent_val_mem_originalCoarse S k q

/-! ## The exact deterministic and random selection coherence seam -/

/-- Canonical injection between finite repetition coordinates from a cardinal
inequality. -/
def finEmbeddingOfLE {m n : Nat} (h : m ≤ n) : Fin m ↪ Fin n :=
  ⟨Fin.castLE h, by
    intro a b hab
    apply Fin.ext
    exact congrArg (fun z : Fin n => z.1) hab⟩

/-- A finite-coordinate embedding exists exactly when the corresponding
cardinality inequality holds. -/
theorem nonempty_finEmbedding_iff_le {m n : Nat} :
    Nonempty (Fin m ↪ Fin n) ↔ m ≤ n := by
  constructor
  · rintro ⟨e⟩
    simpa using Fintype.card_le_of_embedding e
  · intro h
    exact ⟨finEmbeddingOfLE h⟩

variable {G : HierarchyRandomMotionGeometry H}
  {S : SelectedTerminalSourceChartBucketGeometry (H := H)}

/-- Minimal coherence between an independently selected new joint output and
the old output. The first field is deterministic repetition-budget
monotonicity; the second says that the independently chosen packing centres
are literally compatible in ambient space. -/
structure SelectedHierarchyJointSelectionCoherence
    (C : HierarchyJointRandomMotionCertificate H G)
    (Cs : HierarchyJointRandomMotionCertificate
      (selectedHierarchy S) (SelectedGeometry G S)) : Prop where
  repetitions_le : ∀ k : Fin depth,
    repetitions (SelectedGeometry G S).toDependentSource k ≤
      repetitions G.toDependentSource k
  omega_compatible : ∀ (k : Fin depth)
      (j : Fin (repetitions (SelectedGeometry G S).toDependentSource k)),
    Cs.output.omega k j =
      C.output.omega k (Fin.castLE (repetitions_le k) j)

namespace SelectedHierarchyJointSelectionCoherence

variable {C : HierarchyJointRandomMotionCertificate H G}
  {Cs : HierarchyJointRandomMotionCertificate
    (selectedHierarchy S) (SelectedGeometry G S)}
  (Q : SelectedHierarchyJointSelectionCoherence C Cs)

/-- The canonical per-layer restricted-to-old repetition embedding. -/
def repetitionEmbedding (k : Fin depth) :
    Fin (repetitions (SelectedGeometry G S).toDependentSource k) ↪
      Fin (repetitions G.toDependentSource k) :=
  finEmbeddingOfLE (Q.repetitions_le k)

/-- A strict reverse repetition inequality is a sharp obstruction to the
requested restricted-to-old embedding. The counts here are the literal
`jointRepetitions` of the two actual hierarchy layers. -/
theorem no_repetitionEmbedding_of_old_lt
    (k : Fin depth)
    (h : repetitions G.toDependentSource k <
      repetitions (SelectedGeometry G S).toDependentSource k) :
    ¬ Nonempty
      (Fin (repetitions (SelectedGeometry G S).toDependentSource k) ↪
        Fin (repetitions G.toDependentSource k)) := by
  intro he
  have hle := nonempty_finEmbedding_iff_le.mp he
  omega

/-- The genuine selected hierarchy and selected output now automatically
produce the semantic transport certificate from the preceding module. -/
def toSemanticTransport : RestrictedJointOutputSemanticTransport C where
  newRepetitions := fun k =>
    repetitions (SelectedGeometry G S).toDependentSource k
  pathRestriction := {
    coordinateEmbedding := Q.repetitionEmbedding }
  layerChoice := fun k j =>
    (C.output.layerOutput k).omega (Q.repetitionEmbedding k j)
  layerChoice_eq_old := by intros; rfl
  newActiveTests := selectedActiveTestsInOld G S
  activeTests_subset := selectedActiveTestsInOld_subset G S
  newActiveParents := selectedActiveParentsInOld G S
  activeParents_subset := selectedActiveParentsInOld_subset G S

/-- The semantic restricted omega is the actual independently supplied
selected-output omega precisely because of the coherence field. -/
theorem semanticOmega_eq_selected
    (k : Fin depth)
    (j : Fin (Q.toSemanticTransport.newRepetitions k)) :
    Q.toSemanticTransport.omega k j = Cs.output.omega k j := by
  exact (Q.omega_compatible k j).symm

/-- A concrete mismatch at even one repetition coordinate rules out the
minimal selection coherence. -/
theorem omega_mismatch_obstruction
    (k : Fin depth)
    (j : Fin (repetitions (SelectedGeometry G S).toDependentSource k))
    (hneq : Cs.output.omega k j ≠
      C.output.omega k (Q.repetitionEmbedding k j)) : False := by
  exact hneq (Q.omega_compatible k j)

/-! ## Actual selected path and terminal occurrence transport -/

/-- The actual path type of the independently supplied selected hierarchy
embeds coordinatewise into the old path. -/
def selectedPathEmbedding : Cs.Path ↪ C.Path :=
  Q.toSemanticTransport.pathEmbedding

@[simp]
theorem selectedPathEmbedding_apply
    (path : Cs.Path) (k : Fin depth) :
    Q.selectedPathEmbedding path k = Q.repetitionEmbedding k (path k) :=
  rfl

/-- The actual selected prefix vector agrees with the old prefix vector along
the honest path embedding. -/
theorem selectedPrefixVector_compatible
    (path : Cs.Path) (k : Fin depth) :
    Cs.output.prefixVector path k =
      C.output.prefixVector (Q.selectedPathEmbedding path) k := by
  unfold FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.Output.prefixVector
  apply Finset.sum_congr rfl
  intro i _hi
  let j : Fin (repetitions (SelectedGeometry G S).toDependentSource i) := path i
  change Cs.output.omega i j =
    C.output.omega i (Fin.castLE (Q.repetitions_le i) j)
  exact Q.omega_compatible i j

/-- The actual selected total translation agrees with the old total
translation along the same path embedding. -/
theorem selectedComposedVector_compatible (path : Cs.Path) :
    Cs.output.toComposition.composedVector path =
      C.output.toComposition.composedVector (Q.selectedPathEmbedding path) := by
  change (∑ k, Cs.output.omega k (path k)) =
    ∑ k, C.output.omega k (Q.selectedPathEmbedding path k)
  apply Finset.sum_congr rfl
  intro k _hk
  let j : Fin (repetitions (SelectedGeometry G S).toDependentSource k) := path k
  change Cs.output.omega k j =
    C.output.omega k (Fin.castLE (Q.repetitions_le k) j)
  exact Q.omega_compatible k j

/-- Restricted hierarchy buffering changes only subtype proofs: the actual
selected effective tube and its old tube have the same carrier. -/
theorem selectedHierarchy_effectiveFamily_carrier_eq
    (l : Nat) (i : SelectedHierarchyIndex S l) :
    (((selectedHierarchy S).effectiveFamily l).tubes i).carrier =
      ((H.effectiveFamily l).tubes i.1).carrier := by
  unfold MultiscaleTubeHierarchy.effectiveFamily selectedHierarchy
    selectedHierarchyFamily
  change (((H.family l).tubes i.1).buffer
      ((selectedHierarchy S).accumulatedBuffer l)).carrier =
    (((H.family l).tubes i.1).buffer (H.accumulatedBuffer l)).carrier
  rw [selectedHierarchy_accumulatedBuffer_eq]

/-- The actual selected terminal occurrence embeds into the old terminal
occurrence. Both path and source maps are injective and neither is a cast. -/
def selectedFinalIndexEmbeddingToOld (a : Cs.FinalIndex) : C.FinalIndex :=
  (Q.selectedPathEmbedding a.1,
    ⟨a.2.1.1, S.selected_subset_source (by
      simpa only [selectedLevelIndices_zero] using a.2.1.2)⟩)

/-- The actual selected terminal embedding is injective. -/
theorem selectedFinalIndexEmbeddingToOld_injective :
    Function.Injective (Q.selectedFinalIndexEmbeddingToOld) := by
  intro a b hab
  apply Prod.ext
  · exact Q.selectedPathEmbedding.injective
      (congrArg (fun z : C.FinalIndex => z.1) hab)
  · apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : C.FinalIndex => z.2.1) hab

/-- Bundled actual selected terminal embedding. -/
def selectedFinalIndexEmbeddingToOldFn : Cs.FinalIndex ↪ C.FinalIndex :=
  ⟨Q.selectedFinalIndexEmbeddingToOld,
    Q.selectedFinalIndexEmbeddingToOld_injective⟩

/-- The actual selected terminal carrier is exactly the old terminal carrier
at the embedded occurrence. This uses carrier equality and vector
compatibility, not equality of differently indexed `Tube` or `Path` types. -/
theorem selectedTerminalCarrier_compatible (a : Cs.FinalIndex) :
    terminalCarrier Cs a =
      terminalCarrier C (Q.selectedFinalIndexEmbeddingToOld a) := by
  unfold terminalCarrier HierarchyJointRandomMotionCertificate.finalTube
  rw [translateTube_carrier, translateTube_carrier]
  rw [Q.selectedComposedVector_compatible]
  rw [selectedHierarchy_effectiveFamily_carrier_eq]
  rfl
include Q
/-- Any carrier-dependent load over the actual selected hierarchy output is
bounded by the corresponding old-output load. -/
theorem selectedTerminal_weighted_load_le_old
    (w : Set Space → Nat) :
    (∑ a : Cs.FinalIndex, w (terminalCarrier Cs a)) ≤
      ∑ a : C.FinalIndex, w (terminalCarrier C a) := by
  calc
    (∑ a : Cs.FinalIndex, w (terminalCarrier Cs a)) =
        ∑ a : Cs.FinalIndex,
          w (terminalCarrier C (selectedFinalIndexEmbeddingToOld Q a)) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [selectedTerminalCarrier_compatible Q]
    _ ≤ ∑ a : C.FinalIndex, w (terminalCarrier C a) :=
      sum_comp_embedding_le_sum_nat
        (selectedFinalIndexEmbeddingToOldFn Q)
        (fun a : C.FinalIndex => w (terminalCarrier C a))

/-- Direct actual-selected-output endpoint for the existing terminal WZ
multiplicity consumer. Restriction and transport add no further loss. -/
theorem selectedTerminal_weighted_load_le_WZMultiplicity
    (hdelta : 0 < H.effectiveRadius 0)
    (W : HierarchyLevelWZSeparationData H)
    (w : Set Space → Nat) :
    (∑ a : Cs.FinalIndex, w (terminalCarrier Cs a)) ≤
      terminalExactCarrierWZMultiplicityBound C *
        ∑ a ∈ terminalRepresentatives C, w (terminalCarrier C a) := by
  exact (selectedTerminal_weighted_load_le_old Q w).trans
    (terminal_weighted_load_le_WZMultiplicity_mul_representative_load
      C hdelta W w)

end SelectedHierarchyJointSelectionCoherence

end

#print axioms selectedParent_val_mem_originalCoarse
#print axioms selectedHierarchyRandomMotionGeometry
#print axioms selectedLayerTestEmbedding_mem_activeTests
#print axioms selectedActiveTestsInOld_subset
#print axioms selectedActiveParentsInOld_subset
#print axioms nonempty_finEmbedding_iff_le
#print axioms SelectedHierarchyJointSelectionCoherence.no_repetitionEmbedding_of_old_lt
#print axioms SelectedHierarchyJointSelectionCoherence.toSemanticTransport
#print axioms SelectedHierarchyJointSelectionCoherence.semanticOmega_eq_selected
#print axioms SelectedHierarchyJointSelectionCoherence.omega_mismatch_obstruction
#print axioms SelectedHierarchyJointSelectionCoherence.selectedPrefixVector_compatible
#print axioms SelectedHierarchyJointSelectionCoherence.selectedComposedVector_compatible
#print axioms SelectedHierarchyJointSelectionCoherence.selectedHierarchy_effectiveFamily_carrier_eq
#print axioms SelectedHierarchyJointSelectionCoherence.selectedFinalIndexEmbeddingToOld_injective
#print axioms SelectedHierarchyJointSelectionCoherence.selectedTerminalCarrier_compatible
#print axioms SelectedHierarchyJointSelectionCoherence.selectedTerminal_weighted_load_le_old
#print axioms SelectedHierarchyJointSelectionCoherence.selectedTerminal_weighted_load_le_WZMultiplicity

end FamilyStickyHierarchySelectedSourceJointOutputBindingV1
