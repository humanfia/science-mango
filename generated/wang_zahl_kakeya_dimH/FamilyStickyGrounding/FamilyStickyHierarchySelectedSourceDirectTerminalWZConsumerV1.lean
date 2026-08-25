import FamilyStickyGrounding.FamilyStickyHierarchySelectedSourceJointOutputBindingV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open Set
open scoped BigOperators NNReal

namespace FamilyStickyHierarchySelectedSourceDirectTerminalWZConsumerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open FamilyStickyRandomWZLineParameterGeometryV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1.HierarchyJointRandomMotionCertificate
open FamilyStickyHierarchyTerminalCarrierDedupV1
open FamilyStickyHierarchyTerminalSamePathWZEliminationV1
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyTerminalSourceChartBucketProducerV1
open FamilyStickyHierarchySelectedSourceNestedRestrictionV1
open FamilyStickyHierarchySelectedSourceJointOutputBindingV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Direct terminal WZ consumer for an actual selected output

No old output occurs in the endpoint below.  Hierarchy-level WZ separation is
hereditary under the honest selected hierarchy restriction, so every actual
selected joint certificate can invoke the existing terminal WZ theorem on its
own path and representative types.  Old/selected output coherence is needed
only for a later comparison with an old carrier sum.
-/

universe u

variable {depth : Nat} {nominalRadius : Nat → NNReal}
  {Index : Nat → Type u}
  [∀ l, Fintype (Index l)] [∀ l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  {S : SelectedTerminalSourceChartBucketGeometry (H := H)}

/-- WZ endpoint separation restricts to the actual selected index subtypes at
every level.  This construction is independent of every random output. -/
theorem selectedHierarchyLevelWZSeparationData
    (W : HierarchyLevelWZSeparationData H) :
    HierarchyLevelWZSeparationData (selectedHierarchy S) where
  separated := by
    intro l hl i _hi j _hj hij
    have hiOld : i.1 ∈ (H.family l).refinement.refined :=
      selectedLevelIndices_subset_refined S.selected_subset_source l hl i.2
    have hjOld : j.1 ∈ (H.family l).refinement.refined :=
      selectedLevelIndices_subset_refined S.selected_subset_source l hl j.2
    have hijOld : i.1 ≠ j.1 := by
      intro hval
      apply hij
      exact Subtype.ext hval
    have hsep := W.separated l hl hiOld hjOld hijOld
    unfold WZEndpointParameterSeparated at hsep ⊢
    intro e f
    simpa only [orientedLineParameter,
      selectedHierarchy_effectiveFamily_axis,
      selectedHierarchy_effectiveRadius_eq] using hsep e f

/-- Positivity of the terminal scale is also inherited without loss. -/
theorem selectedHierarchy_effectiveRadius_zero_pos
    (hdelta : 0 < H.effectiveRadius 0) :
    0 < (selectedHierarchy S).effectiveRadius 0 := by
  simpa only [selectedHierarchy_effectiveRadius_eq] using hdelta


variable (Cs : HierarchyJointRandomMotionCertificate
  (selectedHierarchy S) (SelectedGeometry G S))
include Cs

/-- Direct selected-output multiplicity endpoint.  Its bound and occurrence
family are both those of `Cs`. -/
theorem selectedTerminalExactCarrierMultiplicityBound_le_own_WZMultiplicity
    (hdelta : 0 < H.effectiveRadius 0)
    (W : HierarchyLevelWZSeparationData H) :
    terminalExactCarrierMultiplicityBound Cs ≤
      terminalExactCarrierWZMultiplicityBound Cs := by
  exact terminalExactCarrierMultiplicityBound_le_WZMultiplicityBound Cs
    (selectedHierarchy_effectiveRadius_zero_pos (S := S) hdelta)
    (selectedHierarchyLevelWZSeparationData (S := S) W)

/-- Every exact carrier fibre of an arbitrary actual selected output has its
own terminal WZ multiplicity bound. -/
theorem selectedTerminalExactCarrierFiber_card_le_own_WZMultiplicity
    (hdelta : 0 < H.effectiveRadius 0)
    (W : HierarchyLevelWZSeparationData H)
    (a : Cs.FinalIndex) :
    Fintype.card (TerminalExactCarrierFiber Cs a) ≤
      terminalExactCarrierWZMultiplicityBound Cs := by
  exact terminalExactCarrierFiber_card_le_WZMultiplicityBound Cs
    (selectedHierarchy_effectiveRadius_zero_pos (S := S) hdelta)
    (selectedHierarchyLevelWZSeparationData (S := S) W) a

/-- Direct selected occurrence-cardinality endpoint, with no old path or old
carrier comparison. -/
theorem selectedFinalIndex_card_le_own_WZMultiplicity_mul_representatives
    (hdelta : 0 < H.effectiveRadius 0)
    (W : HierarchyLevelWZSeparationData H) :
    Fintype.card Cs.FinalIndex ≤
      terminalExactCarrierWZMultiplicityBound Cs *
        (terminalRepresentatives Cs).card := by
  exact finalIndex_card_le_WZMultiplicity_mul_representatives Cs
    (selectedHierarchy_effectiveRadius_zero_pos (S := S) hdelta)
    (selectedHierarchyLevelWZSeparationData (S := S) W)

/-- Any carrier-dependent load on `Cs` is bounded directly by the selected
representative load.  Coupling validity is absent from both assumptions and
conclusion. -/
theorem selectedTerminal_weighted_load_le_own_WZMultiplicity
    (hdelta : 0 < H.effectiveRadius 0)
    (W : HierarchyLevelWZSeparationData H)
    (w : Set Space → Nat) :
    (∑ a : Cs.FinalIndex, w (terminalCarrier Cs a)) ≤
      terminalExactCarrierWZMultiplicityBound Cs *
        ∑ a ∈ terminalRepresentatives Cs, w (terminalCarrier Cs a) := by
  exact terminal_weighted_load_le_WZMultiplicity_mul_representative_load Cs
    (selectedHierarchy_effectiveRadius_zero_pos (S := S) hdelta)
    (selectedHierarchyLevelWZSeparationData (S := S) W) w

/-- The strong-representative endpoint is equally intrinsic to the selected
output. -/
theorem selectedFinalIndex_card_le_own_WZMultiplicity_mul_strongRepresentatives
    (hdelta : 0 < H.effectiveRadius 0)
    (W : HierarchyLevelWZSeparationData H) :
    Fintype.card Cs.FinalIndex ≤
      terminalExactCarrierWZMultiplicityBound Cs *
        (terminalStrongMultiplicity Cs *
          (terminalStrongRepresentatives Cs).card) := by
  exact finalIndex_card_le_WZMultiplicity_mul_terminalStrongRepresentatives Cs
    (selectedHierarchy_effectiveRadius_zero_pos (S := S) hdelta)
    (selectedHierarchyLevelWZSeparationData (S := S) W)


omit Cs

/-- Existing joint-output existence applies directly to the selected hierarchy.
The only remaining probabilistic/numerical input is the selected hierarchy's
own collision-unit scale; no old output or cross-output coherence is used. -/
theorem exists_selectedCertificate_without_hundred_small
    (W : HierarchyLevelWZSeparationData H)
    (hcollisionUnit : HierarchyParentCollisionUnitScale
      (selectedHierarchy S) (SelectedGeometry G S)) :
    Nonempty (HierarchyJointRandomMotionCertificate
      (selectedHierarchy S) (SelectedGeometry G S)) := by
  exact exists_certificate_without_hundred_small
    (selectedHierarchy S) (SelectedGeometry G S)
    (selectedHierarchyLevelWZSeparationData (S := S) W) hcollisionUnit

/-- A concrete selected-output selector supplied by the existing existential
constructor.  Its randomness is entirely intrinsic to the selected hierarchy. -/
def selectSelectedCertificate_without_hundred_small
    (W : HierarchyLevelWZSeparationData H)
    (hcollisionUnit : HierarchyParentCollisionUnitScale
      (selectedHierarchy S) (SelectedGeometry G S)) :
    HierarchyJointRandomMotionCertificate
      (selectedHierarchy S) (SelectedGeometry G S) :=
  Classical.choice
    (exists_selectedCertificate_without_hundred_small
      (S := S) W hcollisionUnit)

/-- The selected certificate chosen by the existing constructor immediately
satisfies the direct terminal weighted-load endpoint. -/
theorem selectedCertificate_weighted_load_le_own_WZMultiplicity
    (hdelta : 0 < H.effectiveRadius 0)
    (W : HierarchyLevelWZSeparationData H)
    (hcollisionUnit : HierarchyParentCollisionUnitScale
      (selectedHierarchy S) (SelectedGeometry G S))
    (w : Set Space → Nat) :
    let Cs := selectSelectedCertificate_without_hundred_small
      (S := S) W hcollisionUnit
    (∑ a : Cs.FinalIndex, w (terminalCarrier Cs a)) ≤
      terminalExactCarrierWZMultiplicityBound Cs *
        ∑ a ∈ terminalRepresentatives Cs, w (terminalCarrier Cs a) := by
  dsimp only
  exact selectedTerminal_weighted_load_le_own_WZMultiplicity
    (selectSelectedCertificate_without_hundred_small
      (S := S) W hcollisionUnit) hdelta W w

/-- An intrinsic selected WZ bound contains no comparison with an old load.
The sharp one-unit finite example shows why an old-carrier-sum conclusion
still requires an embedding/coherence argument such as the binding module. -/
theorem own_selected_WZ_bound_does_not_imply_old_load_comparison :
    ∃ selectedLoad selectedWZBound oldLoad : Nat,
      selectedLoad ≤ selectedWZBound ∧ ¬ selectedLoad ≤ oldLoad := by
  exact ⟨1, 1, 0, by omega, by omega⟩

end

#print axioms selectedHierarchyLevelWZSeparationData
#print axioms selectedHierarchy_effectiveRadius_zero_pos
#print axioms selectedTerminalExactCarrierMultiplicityBound_le_own_WZMultiplicity
#print axioms selectedTerminalExactCarrierFiber_card_le_own_WZMultiplicity
#print axioms selectedFinalIndex_card_le_own_WZMultiplicity_mul_representatives
#print axioms selectedTerminal_weighted_load_le_own_WZMultiplicity
#print axioms selectedFinalIndex_card_le_own_WZMultiplicity_mul_strongRepresentatives
#print axioms exists_selectedCertificate_without_hundred_small
#print axioms selectSelectedCertificate_without_hundred_small
#print axioms selectedCertificate_weighted_load_le_own_WZMultiplicity
#print axioms own_selected_WZ_bound_does_not_imply_old_load_comparison

end FamilyStickyHierarchySelectedSourceDirectTerminalWZConsumerV1
