import FamilyStickyGrounding.FamilyStickyHierarchySelectedSourceJointOutputBindingV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open Set
open scoped BigOperators NNReal

namespace FamilyStickyHierarchySelectedSourceCoupledJointOutputProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth
open FamilyStickyAllParentLayerDataV1
open FamilyStickyAllParentLayerDataV1.AllParentLayerData
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyAllParentLayerJointCollisionRandomMotionV1
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
open FamilyStickyAllParentLayerNumericsV1.AllParentLayerData
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomTwoFamilyTailV1
open FamilyStickyRandomWZCommonNeighbourPackingV1
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
open FamilyStickyHierarchySelectedSourceJointOutputBindingV1
open FamilyStickyHierarchySelectedSourceJointOutputBindingV1.SelectedHierarchyJointSelectionCoherence

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Coupling a selected hierarchy output to an old joint output

The existing probabilistic constructor returns one existential output at a
time, so two invocations do not share their packing certificate or random
choice.  Here the selected output instead reuses the old packing certificate
and the prefix selected by the canonical repetition embedding.  Omega
compatibility is therefore produced, rather than assumed.
-/

universe u

variable {depth : Nat} {nominalRadius : Nat → NNReal}
  {Index : Nat → Type u}
  [∀ l, Fintype (Index l)] [∀ l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  {S : SelectedTerminalSourceChartBucketGeometry (H := H)}
  (C : HierarchyJointRandomMotionCertificate H G)
include C


/-- The selected hierarchy has exactly the same packing ball and mesh at one
layer, so the old packing certificate can be reused. -/
  def reusedPackingCertificate (k : Fin depth) :
      PackingCertificate
        (Metric.closedBall (0 : Space)
          (((SelectedGeometry G S).toDependentSource.motionRadius k : NNReal) : Real))
        ((SelectedGeometry G S).toDependentSource.delta k) where
    centers := (C.output.layerOutput k).certificate.centers
    centers_subset := by
      simpa only [selectedHierarchy_effectiveRadius_eq,
        HierarchyRandomMotionGeometry.toDependentSource] using
        (C.output.layerOutput k).certificate.centers_subset
    separated := by
      simpa only [selectedHierarchy_effectiveRadius_eq,
        HierarchyRandomMotionGeometry.toDependentSource] using
        (C.output.layerOutput k).certificate.separated
    cover := by
      simpa only [selectedHierarchy_effectiveRadius_eq,
        HierarchyRandomMotionGeometry.toDependentSource] using
        (C.output.layerOutput k).certificate.cover

/-- Reuse the old selected packing centre at the canonically embedded
repetition coordinate. -/
def reusedPackingCenter
    (k : Fin depth)
    (hle : repetitions (SelectedGeometry G S).toDependentSource k ≤
      repetitions G.toDependentSource k)
    (j : Fin (repetitions (SelectedGeometry G S).toDependentSource k)) :
    ↥(reusedPackingCertificate (S := S) C k).centers := by
  let oldCenter :=
    (C.output.layerOutput k).omega (Fin.castLE hle j)
  refine ⟨oldCenter.1, ?_⟩
  exact oldCenter.2

@[simp]
theorem reusedPackingCenter_val
    (k : Fin depth)
    (hle : repetitions (SelectedGeometry G S).toDependentSource k ≤
      repetitions G.toDependentSource k)
    (j : Fin (repetitions (SelectedGeometry G S).toDependentSource k)) :
    ((reusedPackingCenter C k hle j).1 : Space) =
      C.output.omega k (Fin.castLE hle j) :=
  rfl


/-- Exactly the facts that do not follow from independently selected
existential outputs.  The packing certificate and omega are deliberately not
fields: the coupled producer reuses the old certificate and its canonical
prefix. -/
structure ReusedOmegaSelectedOutputValidity : Prop where
  repetitions_le : ∀ k,
    repetitions (SelectedGeometry G S).toDependentSource k ≤
      repetitions G.toDependentSource k
  repetitions_one_le : ∀ k,
    1 ≤ repetitions (SelectedGeometry G S).toDependentSource k
  allParentLoad : ∀ (k : Fin depth)
      (q : ((SelectedGeometry G S).toDependentSource.layer k).Test),
    q ∈ ((SelectedGeometry G S).toDependentSource.layer k).activeTests →
      (∑ j, (((SelectedGeometry G S).toDependentSource.layer k).singleLoadAt q
        (((reusedPackingCenter C k (repetitions_le k) j).1 : Space)) : Real)) ≤
        sourceTailParameter ((SelectedGeometry G S).toDependentSource.layer k) *
          ((SelectedGeometry G S).toDependentSource.layer k).paperCap q
  allParentCollisionLoad : ∀ (k : Fin depth)
      (p : SelectedHierarchyIndex S (k.1 + 1)),
    p ∈ ((SelectedGeometry G S).toDependentSource.layer k).activeParents →
      ∀ a : ModelCandidate
        (parentPackingGrid
          ((SelectedGeometry G S).toDependentSource.layer k)
          (reusedPackingCertificate C k) p),
        (∑ j, candidateCollisionLoad
          (parentPackingGrid
            ((SelectedGeometry G S).toDependentSource.layer k)
            (reusedPackingCertificate C k) p)
          a (reusedPackingCenter C k (repetitions_le k) j)) ≤
          Nat.ceil
            (completionTail
                (activeCollisionTests
                  ((SelectedGeometry G S).toDependentSource.layer k)
                  (reusedPackingCertificate C k)).card
                (sourceTailParameter
                  ((SelectedGeometry G S).toDependentSource.layer k)) *
              commonHundredNeighbourPackingConstant)


namespace ReusedOmegaSelectedOutputValidity

variable (V : ReusedOmegaSelectedOutputValidity (S := S) C)
include V

/-- The selected one-layer output uses the old packing certificate and the
canonically embedded prefix of the old omega. -/
def toLayerOutput (k : Fin depth) :
    AllParentLayerJointCollisionOutput
      ((SelectedGeometry G S).toDependentSource.layer k)
      ((SelectedGeometry G S).toDependentSource.motionRadius k) where
  certificate := reusedPackingCertificate C k
  omega := reusedPackingCenter C k (V.repetitions_le k)
  repetitions_one_le := V.repetitions_one_le k
  allParentLoad := V.allParentLoad k
  allParentCollisionLoad := V.allParentCollisionLoad k
  vector_norm_le := by
    intro j
    change Fin (repetitions (SelectedGeometry G S).toDependentSource k) at j
    have h := (C.output.layerOutput k).vector_norm_le
      (Fin.castLE (V.repetitions_le k) j)
    unfold reusedPackingCenter
    dsimp only
    simpa only [selectedHierarchy_effectiveRadius_eq,
      HierarchyRandomMotionGeometry.toDependentSource] using h

/-- A literal selected multiscale output, not merely a semantic surrogate. -/
def toOutput :
    FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.Output
      (SelectedGeometry G S).toDependentSource where
  layerOutput := V.toLayerOutput

/-- The selected hierarchy certificate produced with shared randomness. -/
def toCertificate : HierarchyJointRandomMotionCertificate
    (selectedHierarchy S) (SelectedGeometry G S) where
  output := V.toOutput

/-- Both formerly missing coherence fields are now generated: repetition
monotonicity comes from the deterministic coupling input, while omega
compatibility is definitional from prefix reuse. -/
theorem toSelectionCoherence :
    SelectedHierarchyJointSelectionCoherence C V.toCertificate where
  repetitions_le := V.repetitions_le
  omega_compatible := by
    intro k j
    rfl

/-- Direct producer for the semantic transport certificate consumed by the
binding layer. -/
def toSemanticTransport : RestrictedJointOutputSemanticTransport C :=
  V.toSelectionCoherence.toSemanticTransport

@[simp]
theorem toCertificate_omega
    (k : Fin depth)
    (j : Fin (repetitions (SelectedGeometry G S).toDependentSource k)) :
    V.toCertificate.output.omega k j =
      C.output.omega k (Fin.castLE (V.repetitions_le k) j) :=
  rfl

/-- The coupled actual selected output reaches the terminal weighted-load
consumer with no extra restriction loss. -/
theorem terminal_weighted_load_le_WZMultiplicity
    (hdelta : 0 < H.effectiveRadius 0)
    (W : HierarchyLevelWZSeparationData H)
    (w : Set Space → Nat) :
    (∑ a : V.toCertificate.FinalIndex,
        w (terminalCarrier V.toCertificate a)) ≤
      terminalExactCarrierWZMultiplicityBound C *
        ∑ a ∈ terminalRepresentatives C, w (terminalCarrier C a) :=
  V.toSelectionCoherence.selectedTerminal_weighted_load_le_WZMultiplicity
    hdelta W w

end ReusedOmegaSelectedOutputValidity

/-- If the selected literal joint repetition count is larger at one layer,
no reused-prefix coupled output of this form exists. -/
theorem no_reusedOmegaSelectedOutputValidity_of_old_lt
    (k : Fin depth)
    (h : repetitions G.toDependentSource k <
      repetitions (SelectedGeometry G S).toDependentSource k) :
    ¬ Nonempty (ReusedOmegaSelectedOutputValidity (S := S) C) := by
  rintro ⟨V⟩
  exact (Nat.not_le_of_gt h) (V.repetitions_le k)

/-- Restricting a load and shrinking its permitted bound are independently
monotone facts and do not imply the new load inequality.  The four finite
numbers below are the sharp one-unit obstruction; it applies equally to the
analytic and collision right-hand sides. -/
theorem load_restriction_and_bound_shrink_obstruction :
    ∃ oldLoad selectedLoad oldBound selectedBound : Nat,
      selectedLoad ≤ oldLoad ∧ oldLoad ≤ oldBound ∧
        selectedBound ≤ oldBound ∧ ¬ selectedLoad ≤ selectedBound := by
  refine ⟨1, 1, 1, 0, ?_⟩
  omega

end

#print axioms reusedPackingCertificate
#print axioms reusedPackingCenter
#print axioms reusedPackingCenter_val
#print axioms ReusedOmegaSelectedOutputValidity.toLayerOutput
#print axioms ReusedOmegaSelectedOutputValidity.toOutput
#print axioms ReusedOmegaSelectedOutputValidity.toCertificate
#print axioms ReusedOmegaSelectedOutputValidity.toSelectionCoherence
#print axioms ReusedOmegaSelectedOutputValidity.toSemanticTransport
#print axioms ReusedOmegaSelectedOutputValidity.toCertificate_omega
#print axioms ReusedOmegaSelectedOutputValidity.terminal_weighted_load_le_WZMultiplicity
#print axioms no_reusedOmegaSelectedOutputValidity_of_old_lt
#print axioms load_restriction_and_bound_shrink_obstruction

end FamilyStickyHierarchySelectedSourceCoupledJointOutputProducerV1
