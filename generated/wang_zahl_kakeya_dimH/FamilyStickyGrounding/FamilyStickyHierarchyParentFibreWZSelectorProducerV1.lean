import FamilyStickyGrounding.FamilyStickyHierarchySelectedParentCollisionUnitScaleProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

open Set
open scoped NNReal

namespace FamilyStickyHierarchyParentFibreWZSelectorProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyRandomWZLineParameterGeometryV1
open FamilyStickyHierarchyTerminalSourceChartBucketProducerV1
open FamilyStickyHierarchySelectedSourceNestedRestrictionV1
open FamilyStickyHierarchySelectedSourceJointOutputBindingV1
open FamilyStickyHierarchyRadiusBranchingScalarClosureV1
open FamilyStickyHierarchyRadiusBranchingScalarClosureV1.ScalarCertificate
open FamilyStickyHierarchySelectedParentCollisionUnitScaleProducerV1

noncomputable section

/-!
# Parent-fibre WZ data and the intrinsic hierarchy selector

The joint collision selector never compares children belonging to different
parents.  Its exact geometric input is therefore pairwise WZ endpoint
separation inside every active hierarchy parent fibre, rather than full
pairwise separation on every refined level.

This module exposes that hierarchy-native datum, restricts it without loss to
the recursively selected hierarchy, and invokes the existing joint selector
directly.  Combining it with the scalar-certificate collision-scale producer
removes the formerly over-strong full-level WZ input from intrinsic selected
certificate existence.
-/

universe u v

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type u}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]

/-! ## The exact hierarchy-native geometric input -/

/-- Pairwise projective endpoint-parameter separation only among children of
one active parent, at every actual hierarchy step. -/
def HierarchyParentFibreWZData
    (H : MultiscaleTubeHierarchy depth nominalRadius Index) : Prop :=
  forall (k : Fin depth) (p : Index (k.1 + 1)),
    p ∈ (H.step k.1 k.2).combinatorics.index.coarse ->
      Set.Pairwise
        ((H.step k.1 k.2).combinatorics.index.fiber p : Set (Index k.1))
        fun i j => WZEndpointParameterSeparated
          ((H.effectiveFamily k.1).tubes i)
          ((H.effectiveFamily k.1).tubes j)

/-- Full refined-level WZ separation contains the parent-fibre datum as a
literal restriction. -/
theorem hierarchyParentFibreWZData_of_levelWZ
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (W : HierarchyLevelWZSeparationData H) :
    HierarchyParentFibreWZData H := by
  intro k p _hp i hi j hj hij
  apply W.separated k.1 (Nat.le_of_lt k.2)
  · have hiFine :=
      (((H.step k.1 k.2).combinatorics.index.mem_fiber i p).1 hi).1
    rw [(H.step k.1 k.2).combinatorics.fine_eq_refined] at hiFine
    exact hiFine
  · have hjFine :=
      (((H.step k.1 k.2).combinatorics.index.mem_fiber j p).1 hj).1
    rw [(H.step k.1 k.2).combinatorics.fine_eq_refined] at hjFine
    exact hjFine
  · exact hij

/-! ## Lossless transport through recursive hierarchy selection -/

/-- The parent map of a propositionally restricted adjacent step is the old
parent map after forgetting subtype membership proofs. -/
theorem restrictedParentIndex_val
    {r R : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    {child : UniformTubeFamily r iota}
    {parent : UniformTubeFamily R kappa}
    (A : AdjacentTubeStep child parent)
    (selected : Finset iota) (parents : Finset kappa)
    (hparents : forall p, p ∈ parents <->
      ∃ i ∈ selected, A.parentIndex i = p)
    (hselected_nonempty : selected.Nonempty)
    (hselected : selected ⊆ A.combinatorics.index.fine)
    (i : {i // i ∈ selected}) :
    ((RestrictedStep.ToParentSet.restrict A selected parents hparents
      hselected_nonempty hselected).parentIndex i).1 =
        A.parentIndex i.1 := by
  cases A <;> rfl

/-- Specialization of parent-map preservation to the recursively selected
hierarchy. -/
theorem selectedHierarchy_parentIndex_val
    {H : MultiscaleTubeHierarchy depth nominalRadius Index}
    (R : SelectedTerminalSourceChartBucketGeometry (H := H))
    (k : Fin depth) (i : SelectedHierarchyIndex R k.1) :
    (((selectedHierarchy R).step k.1 k.2).parentIndex i).1 =
      (H.step k.1 k.2).parentIndex i.1 := by
  unfold selectedHierarchy selectedHierarchyStep
  dsimp only
  apply restrictedParentIndex_val

/-- Every selected child-fibre membership forgets to membership in the
corresponding original parent fibre. -/
theorem selectedHierarchy_fibre_val_mem_original
    {H : MultiscaleTubeHierarchy depth nominalRadius Index}
    (R : SelectedTerminalSourceChartBucketGeometry (H := H))
    (k : Fin depth) (p : SelectedHierarchyIndex R (k.1 + 1))
    (i : SelectedHierarchyIndex R k.1)
    (hi : i ∈ ((selectedHierarchy R).step k.1 k.2).combinatorics.index.fiber p) :
    i.1 ∈ (H.step k.1 k.2).combinatorics.index.fiber p.1 := by
  have hiParts :=
    (((selectedHierarchy R).step k.1 k.2).combinatorics.index.mem_fiber i p).1 hi
  apply ((H.step k.1 k.2).combinatorics.index.mem_fiber i.1 p.1).2
  constructor
  · rw [(H.step k.1 k.2).combinatorics.fine_eq_refined]
    exact selectedLevelIndices_subset_refined R.selected_subset_source
      k.1 (Nat.le_of_lt k.2) i.2
  · have hiParent :
        ((selectedHierarchy R).step k.1 k.2).parentIndex i = p := by
      simpa [AdjacentTubeStep.parentIndex] using hiParts.2
    have hparent := congrArg Subtype.val hiParent
    rw [selectedHierarchy_parentIndex_val R k i] at hparent
    exact hparent

/-- Parent-fibre WZ separation restricts without changing its radius or tube
axes to the genuine recursively selected hierarchy. -/
theorem selectedHierarchy_parentFibreWZData
    {H : MultiscaleTubeHierarchy depth nominalRadius Index}
    (R : SelectedTerminalSourceChartBucketGeometry (H := H))
    (P : HierarchyParentFibreWZData H) :
    HierarchyParentFibreWZData (selectedHierarchy R) := by
  intro k p _hp i hi j hj hij
  have hpOld : p.1 ∈
      (H.step k.1 k.2).combinatorics.index.coarse :=
    selectedParent_val_mem_originalCoarse R k p
  have hiOld := selectedHierarchy_fibre_val_mem_original R k p i hi
  have hjOld := selectedHierarchy_fibre_val_mem_original R k p j hj
  have hijOld : i.1 ≠ j.1 := by
    intro h
    exact hij (Subtype.ext h)
  have hsep := P k p.1 hpOld hiOld hjOld hijOld
  unfold WZEndpointParameterSeparated at hsep ⊢
  intro e f
  simpa only [orientedLineParameter,
    selectedHierarchy_effectiveFamily_axis,
    selectedHierarchy_effectiveRadius_eq] using hsep e f

/-! ## The selector with the minimal fibre input -/

variable {H : MultiscaleTubeHierarchy depth nominalRadius Index}

/-- Hierarchy-native fibre separation is definitionally the one-layer input
for every geometry over `H`; analytic test catalogues do not occur. -/
theorem HierarchyParentFibreWZData.toLayerData
    (P : HierarchyParentFibreWZData H)
    (G : HierarchyRandomMotionGeometry H)
    (k : Fin depth) :
    ParentFibreWZSeparated (G.toDependentSource.layer k) := by
  intro p hp
  change p ∈ (H.step k.1 k.2).combinatorics.index.coarse at hp
  change Set.Pairwise
    ((H.step k.1 k.2).combinatorics.index.fiber p : Set (Index k.1))
    fun i j => WZEndpointParameterSeparated
      ((H.effectiveFamily k.1).tubes i)
      ((H.effectiveFamily k.1).tubes j)
  exact P k p hp

/-- Joint hierarchy selection with precisely the parent-fibre WZ geometry
that its collision estimates consume. -/
theorem exists_certificate_without_hundred_small_of_parentFibreWZ
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (P : HierarchyParentFibreWZData H)
    (hcollisionUnit : HierarchyParentCollisionUnitScale H G) :
    Nonempty (HierarchyJointRandomMotionCertificate H G) := by
  obtain ⟨O⟩ :=
    FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.exists_output_without_hundred_small
      G.toDependentSource
      (P.toLayerData G)
      (fun k p hp => by
        have hp' : p ∈ (H.step k.1 k.2).combinatorics.index.coarse := by
          simpa [HierarchyRandomMotionGeometry.toDependentSource,
            hierarchyLayer] using hp
        exact hcollisionUnit k p hp')
  exact ⟨⟨O⟩⟩

/-! ## Scalar-certificate selected intrinsic endpoint -/

/-- Scalar radius/branching data supplies the selected collision unit scale;
the original parent-fibre geometry supplies exactly the selected WZ input.
No full-level or cross-parent separation is required. -/
theorem exists_intrinsicSelectedCertificate_of_scalarCertificate_and_parentFibreWZ
    (C : ScalarCertificate H)
    (R : SelectedTerminalSourceChartBucketGeometry (H := H))
    (P : HierarchyParentFibreWZData H) :
    Nonempty (HierarchyJointRandomMotionCertificate
      (selectedHierarchy R)
      (SelectedGeometry ((toSourceGeometry H C).toHierarchyRandomMotionGeometry H) R)) := by
  exact exists_certificate_without_hundred_small_of_parentFibreWZ
    (selectedHierarchy R)
    (SelectedGeometry ((toSourceGeometry H C).toHierarchyRandomMotionGeometry H) R)
    (selectedHierarchy_parentFibreWZData R P)
    (selectedGeometry_parentCollisionUnitScale_of_scalarCertificate C R)

/-- Concrete intrinsic selected selector with only scalar and parent-fibre
geometric inputs. -/
noncomputable def selectIntrinsicSelectedCertificate_of_scalarCertificate_and_parentFibreWZ
    (C : ScalarCertificate H)
    (R : SelectedTerminalSourceChartBucketGeometry (H := H))
    (P : HierarchyParentFibreWZData H) :
    HierarchyJointRandomMotionCertificate
      (selectedHierarchy R)
      (SelectedGeometry ((toSourceGeometry H C).toHierarchyRandomMotionGeometry H) R) :=
  Classical.choice
    (exists_intrinsicSelectedCertificate_of_scalarCertificate_and_parentFibreWZ C R P)

/-! ## Sharp local obstruction -/

/-- At positive scale, two distinct children represented by the same tube in
one active parent fibre rule out the exact selector geometry. -/
theorem not_parentFibreWZData_of_duplicate_in_fibre
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (k : Fin depth) (p : Index (k.1 + 1))
    (hp : p ∈ (H.step k.1 k.2).combinatorics.index.coarse)
    (i j : Index k.1)
    (hi : i ∈ (H.step k.1 k.2).combinatorics.index.fiber p)
    (hj : j ∈ (H.step k.1 k.2).combinatorics.index.fiber p)
    (hij : i ≠ j)
    (hradius : 0 < H.effectiveRadius k.1)
    (heq : (H.effectiveFamily k.1).tubes i =
      (H.effectiveFamily k.1).tubes j) :
    Not (HierarchyParentFibreWZData H) := by
  intro P
  have hzero := P k p hp hi hj hij false false
  have hnonpos : (H.effectiveRadius k.1 : Real) <= 0 := by
    rw [heq] at hzero
    simpa using hzero
  have hpositive : 0 < (H.effectiveRadius k.1 : Real) := by
    exact_mod_cast hradius
  linarith

#print axioms hierarchyParentFibreWZData_of_levelWZ
#print axioms restrictedParentIndex_val
#print axioms selectedHierarchy_parentIndex_val
#print axioms selectedHierarchy_fibre_val_mem_original
#print axioms selectedHierarchy_parentFibreWZData
#print axioms HierarchyParentFibreWZData.toLayerData
#print axioms exists_certificate_without_hundred_small_of_parentFibreWZ
#print axioms exists_intrinsicSelectedCertificate_of_scalarCertificate_and_parentFibreWZ
#print axioms selectIntrinsicSelectedCertificate_of_scalarCertificate_and_parentFibreWZ
#print axioms not_parentFibreWZData_of_duplicate_in_fibre

end
end FamilyStickyHierarchyParentFibreWZSelectorProducerV1
