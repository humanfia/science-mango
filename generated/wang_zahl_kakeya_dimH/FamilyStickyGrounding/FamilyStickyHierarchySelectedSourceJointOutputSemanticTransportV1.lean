import FamilyStickyGrounding.FamilyStickyHierarchySelectedSourceNestedRestrictionV1
import FamilyStickyGrounding.FamilyStickyHierarchyTerminalSamePathWZEliminationV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open Set
open scoped BigOperators NNReal

namespace FamilyStickyHierarchySelectedSourceJointOutputSemanticTransportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open FamilyStickyAllParentLayerDataV1
open FamilyStickyAllParentLayerDataV1.AllParentLayerData
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyAllParentLayerJointCollisionRandomMotionV1
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.Output
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1.HierarchyJointRandomMotionCertificate
open FamilyStickyHierarchyTerminalCarrierDedupV1
open FamilyStickyHierarchyTerminalSamePathWZEliminationV1
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyTerminalSourceChartBucketProducerV1
open FamilyStickyHierarchySelectedSourceNestedRestrictionV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Semantic restriction of a selected-source joint output

This module does not cast an old joint output to the recursively rebuilt
hierarchy.  Instead it records an honest coordinate embedding into the old
joint repetitions, transports the actual selected packing-centre choices,
and derives all path, motion, analytic-load, collision-load, and terminal
load statements along that embedding.
-/

universe u


/-! ## Finite sums along an honest embedding -/

/-- A nonnegative real-valued sum over an embedded finite subtype is bounded
by the full old sum. -/
theorem sum_comp_embedding_le_sum_of_nonneg
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (e : alpha ↪ beta) (f : beta → Real)
    (hf : ∀ b, 0 ≤ f b) :
    (∑ a, f (e a)) ≤ ∑ b, f b := by
  classical
  calc
    (∑ a, f (e a)) =
        ∑ b ∈ (Finset.univ : Finset alpha).image e, f b := by
      rw [Finset.sum_image]
      intro x _hx y _hy hxy
      exact e.injective hxy
    _ ≤ ∑ b ∈ (Finset.univ : Finset beta), f b := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro b hb
        exact Finset.mem_univ b
      · intro b _hb _hnot
        exact hf b
    _ = ∑ b, f b := by simp

/-- Natural-valued loads need no separate nonnegativity premise. -/
theorem sum_comp_embedding_le_sum_nat
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (e : alpha ↪ beta) (f : beta → Nat) :
    (∑ a, f (e a)) ≤ ∑ b, f b := by
  classical
  calc
    (∑ a, f (e a)) =
        ∑ b ∈ (Finset.univ : Finset alpha).image e, f b := by
      rw [Finset.sum_image]
      intro x _hx y _hy hxy
      exact e.injective hxy
    _ ≤ ∑ b ∈ (Finset.univ : Finset beta), f b :=
      Finset.sum_le_sum_of_subset (by
        intro b _hb
        exact Finset.mem_univ b)
    _ = ∑ b, f b := by simp

/-! ## Concrete semantic transport data for one old joint output -/

variable {depth : Nat} {nominalRadius : Nat → NNReal}
  {Index : Nat → Type u}
  [∀ l, Fintype (Index l)] [∀ l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}

/-- Minimal honest data for a restricted joint output.  New repetition
coordinates embed into the old joint repetitions.  Each new coordinate also
carries an actual old packing-centre choice; equality with the old choice is
strong enough to transport both ambient-vector and collision-grid semantics.
Active tests and active parents may only be deleted. -/
structure RestrictedJointOutputSemanticTransport
    (C : HierarchyJointRandomMotionCertificate H G) where
  newRepetitions : Fin depth → Nat
  pathRestriction : JointPathRestrictionCertificate
    (fun k => repetitions G.toDependentSource k) newRepetitions
  layerChoice : ∀ k, Fin (newRepetitions k) →
    ↥(C.output.layerOutput k).certificate.centers
  layerChoice_eq_old : ∀ k j,
    layerChoice k j =
      (C.output.layerOutput k).omega
        (pathRestriction.coordinateEmbedding k j)
  newActiveTests : ∀ k,
    Finset (G.toDependentSource.layer k).Test
  activeTests_subset : ∀ k,
    newActiveTests k ⊆ (G.toDependentSource.layer k).activeTests
  newActiveParents : ∀ k : Fin depth, Finset (Index (k.1 + 1))
  activeParents_subset : ∀ k,
    newActiveParents k ⊆ (G.toDependentSource.layer k).activeParents

namespace RestrictedJointOutputSemanticTransport

variable {C : HierarchyJointRandomMotionCertificate H G}
  (T : RestrictedJointOutputSemanticTransport C)

/-- The genuinely restricted dependent product path. -/
abbrev RestrictedPath := RepetitionPath T.newRepetitions

/-- Coordinatewise injection of restricted paths into the old joint path. -/
def pathEmbedding : T.RestrictedPath ↪ C.Path :=
  T.pathRestriction.pathEmbedding

/-- Actual ambient vector selected by a restricted layer coordinate. -/
def omega (k : Fin depth) (j : Fin (T.newRepetitions k)) : Space :=
  ((T.layerChoice k j).1 : Space)

/-- The restricted ambient vector is literally the old vector at the
embedded repetition coordinate. -/
theorem omega_compatible (k : Fin depth)
    (j : Fin (T.newRepetitions k)) :
    T.omega k j =
      C.output.omega k (T.pathRestriction.coordinateEmbedding k j) := by
  rw [omega, T.layerChoice_eq_old]
  rfl

/-- Prefix vector made from only the restricted coordinates. -/
def prefixVector (path : T.RestrictedPath) (k : Fin depth) : Space :=
  ∑ i ∈ Finset.univ.filter (fun i => i < k), T.omega i (path i)

/-- Restricted prefix motion is exactly the old prefix motion along the
embedded path. -/
theorem prefixVector_compatible (path : T.RestrictedPath) (k : Fin depth) :
    T.prefixVector path k =
      C.output.prefixVector (T.pathEmbedding path) k := by
  unfold prefixVector
    FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.Output.prefixVector
  apply Finset.sum_congr rfl
  intro i _hi
  rw [T.omega_compatible]
  rfl

/-- Total restricted multiscale translation vector. -/
def composedVector (path : T.RestrictedPath) : Space :=
  ∑ k, T.omega k (path k)

/-- Composed motion is also definitionally inherited along the path
embedding. -/
theorem composedVector_compatible (path : T.RestrictedPath) :
    T.composedVector path =
      C.output.toComposition.composedVector (T.pathEmbedding path) := by
  unfold composedVector
    FamilyStickyMultiscaleSharedMotionCompositionV1.MultiscaleSharedMotionComposition.composedVector
  apply Finset.sum_congr rfl
  intro k _hk
  rw [T.omega_compatible]
  rfl

/-- Restricting repetition coordinates can only decrease an analytic load. -/
theorem analyticLoad_le_old (k : Fin depth)
    (q : (G.toDependentSource.layer k).Test) :
    (∑ j, ((G.toDependentSource.layer k).singleLoadAt q
      (T.omega k j): Real)) ≤
    ∑ j, ((G.toDependentSource.layer k).singleLoadAt q
      (C.output.omega k j): Real) := by
  calc
    (∑ j, ((G.toDependentSource.layer k).singleLoadAt q
        (T.omega k j): Real)) =
        ∑ j, ((G.toDependentSource.layer k).singleLoadAt q
          (C.output.omega k
            (T.pathRestriction.coordinateEmbedding k j)): Real) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [T.omega_compatible]
    _ ≤ ∑ j, ((G.toDependentSource.layer k).singleLoadAt q
        (C.output.omega k j): Real) := by
      exact sum_comp_embedding_le_sum_of_nonneg
        (T.pathRestriction.coordinateEmbedding k)
        (fun j => ((G.toDependentSource.layer k).singleLoadAt q
          (C.output.omega k j) : Real)) (fun _ => Nat.cast_nonneg _)

/-- Every retained analytic test inherits the old all-parent load cap. -/
theorem allParentLoad
    (k : Fin depth) (q : (G.toDependentSource.layer k).Test)
    (hq : q ∈ T.newActiveTests k) :
    (∑ j, ((G.toDependentSource.layer k).singleLoadAt q
      (T.omega k j): Real)) ≤
      FamilyStickyAllParentLayerNumericsV1.AllParentLayerData.sourceTailParameter
          (G.toDependentSource.layer k) *
        (G.toDependentSource.layer k).paperCap q := by
  calc
    _ ≤ ∑ j, ((G.toDependentSource.layer k).singleLoadAt q
        (C.output.omega k j) : Real) := T.analyticLoad_le_old k q
    _ ≤ _ := by
      unfold FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.Output.omega
      exact (C.output.layerOutput k).allParentLoad q
        (T.activeTests_subset k hq)

/-- Prefix-load version consumed by the hierarchy certificate. -/
theorem allParentCommonPrefixLoad
    (path : T.RestrictedPath) (k : Fin depth)
    (q : (G.toDependentSource.layer k).Test)
    (hq : q ∈ T.newActiveTests k) :
    (∑ j,
      (FamilyStickyCommonPrefixLoadInvarianceV1.AllParentLayerData.commonPrefixSingleLoadAt
        (G.toDependentSource.layer k) q (T.prefixVector path k)
          (T.omega k j) : Real)) ≤
      FamilyStickyAllParentLayerNumericsV1.AllParentLayerData.sourceTailParameter
          (G.toDependentSource.layer k) *
        (G.toDependentSource.layer k).paperCap q := by
  simp_rw [
    FamilyStickyCommonPrefixLoadInvarianceV1.AllParentLayerData.commonPrefixSingleLoadAt_eq_singleLoadAt]
  exact T.allParentLoad k q hq

/-- Restricting repetition coordinates can only decrease each literal
candidate collision load. -/
theorem collisionLoad_le_old
    (k : Fin depth) (p : Index (k.1 + 1))
    (a : FamilyStickyRandomModelTubeCollisionGridV1.ModelCandidate
      (parentPackingGrid (G.toDependentSource.layer k)
        (C.output.layerOutput k).certificate p)) :
    (∑ j,
      FamilyStickyRandomModelTubeCollisionGridV1.candidateCollisionLoad
        (parentPackingGrid (G.toDependentSource.layer k)
          (C.output.layerOutput k).certificate p)
        a (T.layerChoice k j)) ≤
    ∑ j,
      FamilyStickyRandomModelTubeCollisionGridV1.candidateCollisionLoad
        (parentPackingGrid (G.toDependentSource.layer k)
          (C.output.layerOutput k).certificate p)
        a ((C.output.layerOutput k).omega j) := by
  calc
    (∑ j,
      FamilyStickyRandomModelTubeCollisionGridV1.candidateCollisionLoad
        (parentPackingGrid (G.toDependentSource.layer k)
          (C.output.layerOutput k).certificate p)
        a (T.layerChoice k j)) =
      ∑ j,
        FamilyStickyRandomModelTubeCollisionGridV1.candidateCollisionLoad
          (parentPackingGrid (G.toDependentSource.layer k)
            (C.output.layerOutput k).certificate p)
          a ((C.output.layerOutput k).omega
            (T.pathRestriction.coordinateEmbedding k j)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [T.layerChoice_eq_old]
    _ ≤ ∑ j,
      FamilyStickyRandomModelTubeCollisionGridV1.candidateCollisionLoad
        (parentPackingGrid (G.toDependentSource.layer k)
          (C.output.layerOutput k).certificate p)
        a ((C.output.layerOutput k).omega j) :=
      sum_comp_embedding_le_sum_nat
        (T.pathRestriction.coordinateEmbedding k)
        (fun j =>
          FamilyStickyRandomModelTubeCollisionGridV1.candidateCollisionLoad
            (parentPackingGrid (G.toDependentSource.layer k)
              (C.output.layerOutput k).certificate p)
            a ((C.output.layerOutput k).omega j))

/-- Every retained active parent inherits the old collision-load cap. -/
theorem allParentCollisionLoad
    (k : Fin depth) (p : Index (k.1 + 1))
    (hp : p ∈ T.newActiveParents k)
    (a : FamilyStickyRandomModelTubeCollisionGridV1.ModelCandidate
      (parentPackingGrid (G.toDependentSource.layer k)
        (C.output.layerOutput k).certificate p)) :
    (∑ j,
      FamilyStickyRandomModelTubeCollisionGridV1.candidateCollisionLoad
        (parentPackingGrid (G.toDependentSource.layer k)
          (C.output.layerOutput k).certificate p)
        a (T.layerChoice k j)) ≤
      Nat.ceil
        (FamilyStickyRandomTwoFamilyTailV1.completionTail
            (activeCollisionTests (G.toDependentSource.layer k)
              (C.output.layerOutput k).certificate).card
            (FamilyStickyAllParentLayerNumericsV1.AllParentLayerData.sourceTailParameter
              (G.toDependentSource.layer k)) *
          FamilyStickyRandomWZCommonNeighbourPackingV1.commonHundredNeighbourPackingConstant) := by
  exact (T.collisionLoad_le_old k p a).trans
    (C.output.allParentCollisionLoad k p
      (T.activeParents_subset k hp) a)

/-! ## Fully automatic source-only producer -/

/-- Restricting only the level-zero source does not alter any path coordinate
or layer test.  Hence all semantic transport data is generated identically
from the old output. -/
def identityPathTransport : RestrictedJointOutputSemanticTransport C where
  newRepetitions := fun k => repetitions G.toDependentSource k
  pathRestriction := {
    coordinateEmbedding := fun _ =>
      ⟨id, fun _ _ h => h⟩ }
  layerChoice := fun k j => (C.output.layerOutput k).omega j
  layerChoice_eq_old := by intros; rfl
  newActiveTests := fun k => (G.toDependentSource.layer k).activeTests
  activeTests_subset := fun _ => Finset.Subset.rfl
  newActiveParents := fun k => (G.toDependentSource.layer k).activeParents
  activeParents_subset := fun _ => Finset.Subset.rfl

/-- Selected-source wrapper: `S` changes only the terminal source subtype;
the honest path/output transport is the preceding identity producer. -/
def ofSelectedSource
    (C : HierarchyJointRandomMotionCertificate H G)
    (_S : SelectedTerminalSourceChartBucketGeometry (H := H)) :
    RestrictedJointOutputSemanticTransport C :=
  identityPathTransport (C := C)

@[simp]
theorem ofSelectedSource_newRepetitions
    (C : HierarchyJointRandomMotionCertificate H G)
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (k : Fin depth) :
    (ofSelectedSource C S).newRepetitions k =
      repetitions G.toDependentSource k :=
  rfl

@[simp]
theorem ofSelectedSource_omega
    (C : HierarchyJointRandomMotionCertificate H G)
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (k : Fin depth)
    (j : Fin ((ofSelectedSource C S).newRepetitions k)) :
    (ofSelectedSource C S).omega k j = C.output.omega k j :=
  rfl

/-! ## Direct terminal consumer -/

/-- Restrict both honest joint paths and the level-zero source.  This is the
terminal occurrence type produced by the semantic transport certificate. -/
abbrev RestrictedSelectedFinalIndex
    (S : SelectedTerminalSourceChartBucketGeometry (H := H)) :=
  T.RestrictedPath × {i // i ∈ S.selected}

/-- A restricted selected terminal occurrence embeds into the actual old
terminal occurrence type.  The two coordinates are transported separately;
no equality or cast between distinct path types is used. -/
def restrictedSelectedFinalIndexEmbedding
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (a : RestrictedSelectedFinalIndex T S) : C.FinalIndex :=
  (T.pathEmbedding a.1, ⟨a.2.1, by
    simpa only [levelZeroSource] using
      S.selected_subset_source a.2.2⟩)

theorem restrictedSelectedFinalIndexEmbedding_injective
    (S : SelectedTerminalSourceChartBucketGeometry (H := H)) :
    Function.Injective (restrictedSelectedFinalIndexEmbedding T S) := by
  intro a b hab
  apply Prod.ext
  · exact T.pathEmbedding.injective
      (congrArg (fun z : C.FinalIndex => z.1) hab)
  · apply Subtype.ext
    exact congrArg (fun z : C.FinalIndex => z.2.1) hab

/-- Bundled terminal embedding, suitable for finite-sum restriction. -/
def restrictedSelectedFinalIndexEmbeddingFn
    (S : SelectedTerminalSourceChartBucketGeometry (H := H)) :
    RestrictedSelectedFinalIndex T S ↪ C.FinalIndex :=
  ⟨restrictedSelectedFinalIndexEmbedding T S,
    restrictedSelectedFinalIndexEmbedding_injective T S⟩

/-- Actual old terminal tube attached to a restricted selected occurrence. -/
def restrictedSelectedFinalTube
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (a : RestrictedSelectedFinalIndex T S) :
    Tube (H.effectiveRadius 0) :=
  C.finalTube (restrictedSelectedFinalIndexEmbedding T S a)

/-- Its collision code is the literal old terminal carrier. -/
def restrictedSelectedTerminalCarrier
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (a : RestrictedSelectedFinalIndex T S) : Set Space :=
  (restrictedSelectedFinalTube T S a).carrier

@[simp]
theorem restrictedSelectedTerminalCarrier_eq
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (a : RestrictedSelectedFinalIndex T S) :
    restrictedSelectedTerminalCarrier T S a =
      terminalCarrier C (restrictedSelectedFinalIndexEmbedding T S a) :=
  rfl

/-- Any terminal load over the genuinely restricted occurrence type is no
larger than its old-output load. -/
theorem restrictedSelectedTerminal_weighted_load_le_old
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (w : Set Space → Nat) :
    (∑ a : RestrictedSelectedFinalIndex T S,
      w (restrictedSelectedTerminalCarrier T S a)) ≤
      ∑ a : C.FinalIndex, w (terminalCarrier C a) := by
  change (∑ a, w (terminalCarrier C
      (restrictedSelectedFinalIndexEmbeddingFn T S a))) ≤
    ∑ a : C.FinalIndex, w (terminalCarrier C a)
  exact sum_comp_embedding_le_sum_nat
    (restrictedSelectedFinalIndexEmbeddingFn T S)
    (fun a : C.FinalIndex => w (terminalCarrier C a))

/-- Direct terminal producer for the existing same-path/first-divergence WZ
consumer.  The selected source and restricted path introduce no new
multiplicity loss. -/
theorem restrictedSelectedTerminal_weighted_load_le_WZMultiplicity
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (hdelta : 0 < H.effectiveRadius 0)
    (W : HierarchyLevelWZSeparationData H)
    (w : Set Space → Nat) :
    (∑ a : RestrictedSelectedFinalIndex T S,
      w (restrictedSelectedTerminalCarrier T S a)) ≤
      terminalExactCarrierWZMultiplicityBound C *
        ∑ a ∈ terminalRepresentatives C, w (terminalCarrier C a) := by
  exact (restrictedSelectedTerminal_weighted_load_le_old T S w).trans
    (terminal_weighted_load_le_WZMultiplicity_mul_representative_load
      C hdelta W w)

/-- In the source-only specialization, the new terminal embedding is
definitionally the previously audited selected-source embedding. -/
@[simp]
theorem ofSelectedSource_restrictedSelectedFinalIndexEmbedding
    (C : HierarchyJointRandomMotionCertificate H G)
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (a : SelectedFinalIndex C S) :
    restrictedSelectedFinalIndexEmbedding (ofSelectedSource C S) S a =
      selectedFinalIndexEmbedding C S a :=
  rfl

/-! ## Sharp finite obstruction to automatic rebuilt-output transport -/

/-- Two new repetition choices cannot inject into one old repetition choice.
This is the minimal finite obstruction to manufacturing a path restriction
from hierarchy data that records only the two repetition counts. -/
theorem no_twoIntoOnePathRestriction :
    ¬ Nonempty
      (JointPathRestrictionCertificate oneRepetition twoRepetitions) := by
  rintro ⟨R⟩
  let e := R.coordinateEmbedding (0 : Fin 1)
  have heq : e (0 : Fin 2) = e (1 : Fin 2) := by
    apply Fin.ext
    simp [e, oneRepetition]
  have hfalse := e.injective heq
  have hval : (0 : Nat) = 1 := congrArg Fin.val hfalse
  norm_num at hval
/-- Thus no full semantic transport certificate can be automatic in this
finite repetition-increase example: its mandatory path field would already
contradict cardinality, before omega or load compatibility are considered. -/
theorem no_twoIntoOneSemanticTransportPath
    (P : JointPathRestrictionCertificate oneRepetition twoRepetitions) :
    False := by
  exact no_twoIntoOnePathRestriction ⟨P⟩

end RestrictedJointOutputSemanticTransport
end

end FamilyStickyHierarchySelectedSourceJointOutputSemanticTransportV1
