import FamilyStickyGrounding.FamilyStickyScaleChainCanonicalParentCellCoverageProducerV1
import FamilyStickyGrounding.FamilyStickyScaleChainBufferedHierarchyNormalizedV1
import FamilyStickyGrounding.FamilyStickyHierarchySelectedSourceJointOutputBindingV1
import FamilyStickyGrounding.FamilyStickyHierarchySelectedSourceDirectTerminalWZConsumerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainArbitraryRadiusInterpolationV1
open FamilyStickyScaleChainArbitraryRadiusBoundsV1
open FamilyStickyScaleChainParentNormalizerReverseProducerV1
open FamilyStickyScaleChainHierarchySiblingRigidityV1
open FamilyStickyScaleChainParentPartitionCollisionCellSiblingRigidityProducerV1
open FamilyStickyScaleChainHierarchySiblingRigidityProducerV1
open FamilyStickyScaleChainSelectedNestedSiblingRigidityProducerV1
open FamilyStickyScaleChainSelectedRestrictionParentPartitionCollisionBindingV1
open FamilyStickyScaleChainCanonicalParentCellCoverageProducerV1
open FamilyStickyScaleChainBufferedHierarchyNormalizedV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyTerminalSourceChartBucketProducerV1
open FamilyStickyHierarchySelectedSourceNestedRestrictionV1
open FamilyStickyHierarchySelectedSourceJointOutputBindingV1
open FamilyStickyHierarchySelectedSourceDirectTerminalWZConsumerV1
open FamilyStickyRandomWZCommonNeighbourPackingV1

noncomputable section

/-!
# Canonical selected covers and their honest coordinate seam

There are two constructions with sharply different scope.

* Every finite family has a canonical coherent cover at every real radius:
  keep one reindexed parent per fine index and only change its radius.  All
  cross-scale parent maps are identities.
* Every selected hierarchy step has a canonical adjacent endpoint cover:
  reindex its genuine effective coarse partition by `Fintype.equivFin`.
  Its lower and upper coordinates, and their parent square, are automatic.

The two constructions cannot in general be identified.  The real-radius
identity cover retains all level-zero occurrences, whereas an honest
hierarchy parent map may merge siblings.  Thus coordinates from the first
cover to level `l` exist by the natural ancestor map only when that actual
ancestor map is injective.  This module isolates precisely that finite seam;
it does not add an arbitrary cover-to-hierarchy callback.
-/

universe u v

/-! ## A canonical coherent identity cover at every real radius -/

/-- Reindex the radius-changed copy of a family by its canonical finite
enumeration.  Every active fine occurrence keeps its own parent. -/
def identityRadiusScaleCover
    {delta : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (rho : NNReal) (hdelta : delta <= rho) :
    StickyScaleCover fine rho where
  coarseCard := Fintype.card iota
  coarse := (fine.changeRadius rho).reindex (Fintype.equivFin iota)
  activeFine := fine.refinement.refined
  activeCoarse := fine.refinement.refined.map
    (Fintype.equivFin iota).toEmbedding
  parent := Fintype.equivFin iota
  activeFine_eq_refined := rfl
  activeCoarse_eq_refined := rfl
  parent_mem := by
    intro i hi
    exact Finset.mem_map.mpr ⟨i, hi, rfl⟩
  parent_surjective := by
    intro k hk
    refine ⟨(Fintype.equivFin iota).symm k, ?_, ?_⟩
    · simpa using hk
    · exact (Fintype.equivFin iota).apply_symm_apply k
  carrier_subset := by
    intro i _hi
    simpa using fine.tube_carrier_subset_changeRadius hdelta i

@[simp]
theorem identityRadiusScaleCover_parent
    {delta : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (rho : NNReal) (hdelta : delta <= rho) (i : iota) :
    (identityRadiusScaleCover fine rho hdelta).parent i =
      Fintype.equivFin iota i :=
  rfl

/-- The identity-radius covers are coherent for all real radii.  Between two
chosen radii the coarse indices do not change, and carrier containment is
the monotonicity of closed thickening in the radius. -/
def identityRadiusCoherentCover
    {delta : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) :
    CoherentStickyMultiscaleCover fine where
  base :=
    { cover := fun rho hdelta _hrho =>
        identityRadiusScaleCover fine rho hdelta }
  parent := fun _tau _rho _hdeltaTau _hTauRho _hRhoOne k => k
  parent_mem := by
    intro tau rho hdeltaTau hTauRho hRhoOne k hk
    change k ∈ fine.refinement.refined.map
      (Fintype.equivFin iota).toEmbedding at hk ⊢
    exact hk
  parent_surjective := by
    intro tau rho hdeltaTau hTauRho hRhoOne k hk
    refine ⟨k, ?_, rfl⟩
    change k ∈ fine.refinement.refined.map
      (Fintype.equivFin iota).toEmbedding at hk ⊢
    exact hk
  carrier_subset := by
    intro tau rho hdeltaTau hTauRho hRhoOne i _hi
    change
      Metric.cthickening (tau : Real)
          ((fine.tubes ((Fintype.equivFin iota).symm i)).axis.carrier) ⊆
        Metric.cthickening (rho : Real)
          ((fine.tubes ((Fintype.equivFin iota).symm i)).axis.carrier)
    exact Metric.cthickening_mono (by exact_mod_cast hTauRho) _

@[simp]
theorem identityRadiusCoherentCover_interval_parent
    {delta : NNReal} {depth : Nat} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (T : FiniteScaleSequence delta depth)
    (m : Fin depth) (rho : NNReal)
    (hTauRho : T.tau m <= rho) (hRhoTheta : rho <= T.theta m)
    (k : Fin (Fintype.card iota)) :
    (rhoToUpperCover (identityRadiusCoherentCover fine) T m rho
      hTauRho hRhoTheta).parent k = k :=
  rfl

/-! ## The genuine selected adjacent endpoint cover -/

/-- Reindex the coarse side of an honest partition by `Fin`, retaining the
literal parent assignment, surjectivity, and carrier containment. -/
def StickyScaleCover.ofCoarseTubePartitionReindex
    {delta rho : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [Fintype kappa]
    [DecidableEq iota] [DecidableEq kappa]
    {fine : UniformTubeFamily delta iota}
    {coarse : UniformTubeFamily rho kappa}
    (P : CoarseTubePartition fine coarse) :
    StickyScaleCover fine rho where
  coarseCard := Fintype.card kappa
  coarse := coarse.reindex (Fintype.equivFin kappa)
  activeFine := P.index.fine
  activeCoarse := P.index.coarse.map
    (Fintype.equivFin kappa).toEmbedding
  parent := fun i => Fintype.equivFin kappa (P.index.parent i)
  activeFine_eq_refined := P.fine_eq_refined
  activeCoarse_eq_refined := by
    change P.index.coarse.map (Fintype.equivFin kappa).toEmbedding =
      coarse.refinement.refined.map
        (Fintype.equivFin kappa).toEmbedding
    rw [P.coarse_eq_refined]
  parent_mem := by
    intro i hi
    exact Finset.mem_map.mpr
      ⟨P.index.parent i, P.index.parent_mem i hi, rfl⟩
  parent_surjective := by
    intro k hk
    obtain ⟨p, hp, hpk⟩ := Finset.mem_map.mp hk
    obtain ⟨i, hi, hip⟩ := P.parent_surjective p hp
    refine ⟨i, hi, ?_⟩
    rw [hip]
    change Fintype.equivFin kappa p = k at hpk
    exact hpk
  carrier_subset := by
    intro i hi
    simpa using P.carrier_subset i hi

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type u}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  (R : SelectedTerminalSourceChartBucketGeometry (H := H))

/-- The literal selected hierarchy partition at one adjacent effective step,
with only its coarse subtype canonically enumerated by `Fin`. -/
abbrev selectedAdjacentEndpointCover (l : Nat) (hl : l < depth) :
    StickyScaleCover ((selectedHierarchy R).effectiveFamily l)
      ((selectedHierarchy R).effectiveRadius (l + 1)) :=
  StickyScaleCover.ofCoarseTubePartitionReindex
    ((selectedHierarchy R).effectivePartition l hl)

abbrev SelectedAdjacentLowerParent (l : Nat) (hl : l < depth) :=
  {i // i ∈ (selectedAdjacentEndpointCover R l hl).activeFine}

abbrev SelectedAdjacentUpperParent (l : Nat) (hl : l < depth) :=
  {p // p ∈ (selectedAdjacentEndpointCover R l hl).activeCoarse}

/-- Lower endpoint coordinates forget only the active-membership proof. -/
def selectedAdjacentLowerCoordinate (l : Nat) (hl : l < depth) :
    SelectedAdjacentLowerParent R l hl ↪ SelectedHierarchyIndex R l where
  toFun := fun i => i.1
  inj' := by
    intro i j hij
    exact Subtype.ext hij

/-- Upper endpoint coordinates undo only the canonical finite enumeration. -/
def selectedAdjacentUpperCoordinate (l : Nat) (hl : l < depth) :
    SelectedAdjacentUpperParent R l hl ↪
      SelectedHierarchyIndex R (l + 1) where
  toFun := fun p => (Fintype.equivFin
    (SelectedHierarchyIndex R (l + 1))).symm p.1
  inj' := by
    intro p q hpq
    apply Subtype.ext
    exact (Fintype.equivFin
      (SelectedHierarchyIndex R (l + 1))).symm.injective hpq

/-- For the actual adjacent endpoint cover, the coordinate square commutes
by construction with the selected hierarchy parent map. -/
theorem selectedAdjacent_parent_commutes
    (l : Nat) (hl : l < depth)
    (i : SelectedAdjacentLowerParent R l hl) :
    ((selectedHierarchy R).step l hl).parentIndex
        (selectedAdjacentLowerCoordinate R l hl i) =
      selectedAdjacentUpperCoordinate R l hl
        ⟨(selectedAdjacentEndpointCover R l hl).parent i.1,
          (selectedAdjacentEndpointCover R l hl).parent_mem i.1 i.2⟩ := by
  change
    ((selectedHierarchy R).step l hl).parentIndex i.1 =
      (Fintype.equivFin (SelectedHierarchyIndex R (l + 1))).symm
        (Fintype.equivFin (SelectedHierarchyIndex R (l + 1))
          (((selectedHierarchy R).step l hl).parentIndex i.1))
  exact (Fintype.equivFin
    (SelectedHierarchyIndex R (l + 1))).symm_apply_apply _ |>.symm

/-! ## The selected hierarchy canonical all-radius cover -/

/-- Restricting either concrete adjacent-step constructor changes only parent
membership proofs; forgetting the new proof recovers the literal old parent. -/
theorem restrictedParentIndex_val_of_restrict
    {r s : NNReal} {iota kappa : Type u}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    {child : UniformTubeFamily r iota}
    {parent : UniformTubeFamily s kappa}
    (A : AdjacentTubeStep child parent)
    (selected : Finset iota) (parents : Finset kappa)
    (hparents : forall p, p ∈ parents ↔
      Exists fun i => i ∈ selected ∧ A.parentIndex i = p)
    (hselected_nonempty : selected.Nonempty)
    (hselected : selected ⊆ A.combinatorics.index.fine)
    (i : RestrictedStep.ToParentSet.ChildIndex A selected) :
    ((RestrictedStep.ToParentSet.restrict A selected parents hparents
      hselected_nonempty hselected).parentIndex i).1 =
        A.parentIndex i.1 := by
  cases A <;> rfl

/-- Iterate the literal parent maps of a hierarchy from level zero. This is
the only canonical map from level-zero occurrences to a later level. -/
def hierarchyAncestor
    {d : Nat} {radius : Nat -> NNReal} {I : Nat -> Type u}
    [forall l, Fintype (I l)] [forall l, DecidableEq (I l)]
    (K : MultiscaleTubeHierarchy d radius I) :
    (l : Nat) -> l <= d -> I 0 -> I l
  | 0, _hl, i => i
  | l + 1, hl, i =>
      (K.step l (by omega)).parentIndex
        (hierarchyAncestor K l (by omega) i)

@[simp]
theorem hierarchyAncestor_zero
    {d : Nat} {radius : Nat -> NNReal} {I : Nat -> Type u}
    [forall l, Fintype (I l)] [forall l, DecidableEq (I l)]
    (K : MultiscaleTubeHierarchy d radius I) (hd : 0 <= d)
    (i : I 0) :
    hierarchyAncestor K 0 hd i = i :=
  rfl

@[simp]
theorem hierarchyAncestor_succ
    {d : Nat} {radius : Nat -> NNReal} {I : Nat -> Type u}
    [forall l, Fintype (I l)] [forall l, DecidableEq (I l)]
    (K : MultiscaleTubeHierarchy d radius I)
    (l : Nat) (hl : l + 1 <= d) (i : I 0) :
    hierarchyAncestor K (l + 1) hl i =
      (K.step l (by omega)).parentIndex
        (hierarchyAncestor K l (by omega) i) :=
  rfl

/-- At level zero the rebuilt selected hierarchy has exactly all of its
subtype indices. The old selected chart-bucket estimates therefore furnish
an honest terminal-source geometry certificate for this whole new source. -/
def selectedHierarchyAllGeometry :
    SelectedTerminalSourceChartBucketGeometry
      (H := selectedHierarchy R) where
  selected := Finset.univ
  selected_nonempty := by
    obtain ⟨i, hi⟩ := R.selected_nonempty
    exact ⟨⟨i, hi⟩, Finset.mem_univ _⟩
  selected_subset_source := by
    intro i _hi
    change i ∈ R.selected.attach
    exact Finset.mem_attach R.selected i
  direction_two_ne_zero := by
    intro i _hi
    simpa only [selectedHierarchy_effectiveFamily_axis] using
      R.direction_two_ne_zero i.1 i.2
  graphC_halfBucket := by
    intro i _hi j _hj
    simpa only [projectedTubeGraphC, selectedHierarchy_effectiveFamily_axis,
      selectedHierarchy_effectiveRadius_eq] using
      R.graphC_halfBucket i.1 i.2 j.1 j.2

/-- The all-radius identity cover specialized to the genuine selected
level-zero hierarchy family. -/
abbrev selectedIdentityCoherentCover :=
  identityRadiusCoherentCover ((selectedHierarchy R).effectiveFamily 0)

/-- Canonical selected ancestor coordinates lift a level-zero selected index
into the all-source restriction and then iterate its literal parent maps. -/
def allSelectedAncestor (l : Nat) (hl : l <= depth) :
    SelectedHierarchyIndex R 0 ->
      SelectedHierarchyIndex (selectedHierarchyAllGeometry R) l :=
  fun i => hierarchyAncestor
    (selectedHierarchy (selectedHierarchyAllGeometry R)) l hl
      ⟨i, Finset.mem_univ _⟩

@[simp]
theorem selectedHierarchyAll_parent_val
    (l : Nat) (hl : l < depth)
    (i : SelectedHierarchyIndex (selectedHierarchyAllGeometry R) l) :
    (((selectedHierarchy (selectedHierarchyAllGeometry R)).step l hl).parentIndex i).1 =
      ((selectedHierarchy R).step l hl).parentIndex i.1 := by
  change
    ((selectedHierarchyStep (selectedHierarchyAllGeometry R) l hl).parentIndex i).1 =
      ((selectedHierarchy R).step l hl).parentIndex i.1
  unfold selectedHierarchyStep
  dsimp only
  apply restrictedParentIndex_val_of_restrict

/-- Exact finite seam for using the all-radius identity cover: every literal
level-zero occurrence must remain distinguishable after taking ancestors. -/
def SelectedAncestorInjective : Prop :=
  forall (l : Nat) (hl : l <= depth),
    Function.Injective (allSelectedAncestor R l hl)

/-- Under the exact ancestor-injectivity seam, the identity real-radius
cover has canonical raw coordinates in the genuine selected hierarchy. No
external cover map or parent-commutation callback is supplied. -/
def selectedIdentityRestrictionCoordinates
    (T : FiniteScaleSequence
      ((selectedHierarchy R).effectiveRadius 0) depth)
    (A : SelectedAncestorInjective R) :
    SelectedRestrictionCoverCoordinates
      (selectedHierarchy R) (selectedIdentityCoherentCover R) T
      (selectedHierarchyAllGeometry R) where
  lowerCoordinate := fun m _rho _hTauRho _hRhoTheta q =>
    allSelectedAncestor R m.1 (by omega)
      ((Fintype.equivFin (SelectedHierarchyIndex R 0)).symm q.1)
  lowerCoordinate_injective := by
    intro m _rho _hTauRho _hRhoTheta q r hqq
    apply Subtype.ext
    exact (Fintype.equivFin (SelectedHierarchyIndex R 0)).symm.injective
      (A m.1 (by omega) hqq)
  upperCoordinate := fun m _rho _hTauRho _hRhoTheta p =>
    allSelectedAncestor R (m.1 + 1) (by omega)
      ((Fintype.equivFin (SelectedHierarchyIndex R 0)).symm p.1)
  upperCoordinate_injective := by
    intro m _rho _hTauRho _hRhoTheta p q hpq
    apply Subtype.ext
    exact (Fintype.equivFin (SelectedHierarchyIndex R 0)).symm.injective
      (A (m.1 + 1) (by omega) hpq)
  restricted_parent_commutes := by
    intro m rho hTauRho hRhoTheta q
    have hcross :
        (crossParentOfLower (selectedHierarchy R)
          (selectedIdentityCoherentCover R) T m rho hTauRho hRhoTheta q).1 =
          q.1 := by
      rfl
    rw [hcross]
    change
      ((selectedHierarchy R).step m.1 m.2).parentIndex
        (allSelectedAncestor R m.1 (by omega)
          ((Fintype.equivFin (SelectedHierarchyIndex R 0)).symm q.1)).1 =
      (allSelectedAncestor R (m.1 + 1) (by omega)
        ((Fintype.equivFin (SelectedHierarchyIndex R 0)).symm q.1)).1
    have hparent := congrArg Subtype.val
      (hierarchyAncestor_succ
        (selectedHierarchy (selectedHierarchyAllGeometry R))
        m.1 (by omega)
        ⟨(Fintype.equivFin (SelectedHierarchyIndex R 0)).symm q.1,
          Finset.mem_univ _⟩).symm
    simpa only [allSelectedAncestor, selectedHierarchyAll_parent_val] using
      hparent

/-- The identity real-radius cover commutes with every upper endpoint cover
definitionally: all relevant parent maps are the identity on canonical Fin
coordinates. -/
theorem selectedIdentity_parent_compatible
    (T : FiniteScaleSequence
      ((selectedHierarchy R).effectiveRadius 0) depth)
    (m : Fin depth) (rho : NNReal)
    (hTauRho : T.tau m <= rho) (hRhoTheta : rho <= T.theta m)
    (i : SelectedHierarchyIndex R 0)
    (_hi : i ∈ (lowerScaleCover (selectedIdentityCoherentCover R) T m rho
      hTauRho hRhoTheta).activeFine) :
    (upperEndpointCover (selectedIdentityCoherentCover R) T m).parent i =
      (rhoToUpperCover (selectedIdentityCoherentCover R) T m rho
        hTauRho hRhoTheta).parent
        ((lowerScaleCover (selectedIdentityCoherentCover R) T m rho
          hTauRho hRhoTheta).parent i) := by
  rfl

/-! ## Binding the canonical coordinates to the actual selected endpoint -/

/-- The exact level-zero radius compatibility transports to the rebuilt
selected hierarchy because its accumulated buffers, hence effective radii,
are unchanged. -/
theorem selectedHierarchy_levelZeroCanonicalHundredRadiusCompatible
    (K : LevelZeroCanonicalHundredRadiusCompatible H) :
    LevelZeroCanonicalHundredRadiusCompatible (selectedHierarchy R) := by
  simpa only [LevelZeroCanonicalHundredRadiusCompatible,
    selectedHierarchy_effectiveRadius_eq] using K

/-- The actual selected reverse-normalizer endpoint. The hierarchy geometry,
WZ separation, all-radius cover, coordinates, and parent compatibility are
all concrete repository constructions. The sole combinatorial seam is that
the literal ancestor maps do not merge level-zero occurrences. -/
theorem actualReverseParentNormalizerLoss_le_of_selectedIdentityAncestors
    {G : HierarchyRandomMotionGeometry H}
    {hdepth : 0 < depth}
    (Js : HierarchyJointRandomMotionCertificate
      (selectedHierarchy R) (SelectedGeometry G R))
    (T : FiniteScaleSequence
      ((selectedHierarchy R).effectiveRadius 0) depth)
    (A : SelectedAncestorInjective R)
    (K : LevelZeroCanonicalHundredRadiusCompatible H)
    (W : HierarchyLevelWZSeparationData H) :
    actualReverseParentNormalizerLoss (selectedIdentityCoherentCover R) T <=
      hierarchyReverseNormalizerBound
        (hierarchyBranchingBound (selectedHierarchy R))
        (16 * ((levelZeroParentCount (selectedHierarchy R) hdepth *
          commonHundredNeighbourPackingConstant : Nat) : ENNReal)) := by
  exact actualReverseParentNormalizerLoss_le_of_geometry_and_canonicalRadiusCompatible
    (H := selectedHierarchy R) (G := SelectedGeometry G R) (J := Js)
    (X := selectedIdentityRestrictionCoordinates R T A)
    (hdepth := hdepth)
    (selectedHierarchy_levelZeroCanonicalHundredRadiusCompatible R K)
    (selectedHierarchyLevelWZSeparationData (S := R) W)
    (selectedIdentity_parent_compatible R T)

/-- The corresponding arbitrary-radius Sticky endpoint, with the same
parent-count times common-WZ loss as the concrete canonical-coverage theorem. -/
theorem isStickyAtEveryScale_of_selectedIdentityAncestors
    {G : HierarchyRandomMotionGeometry H}
    {epsilon : Real}
    (hdepth : 0 < depth)
    (Js : HierarchyJointRandomMotionCertificate
      (selectedHierarchy R) (SelectedGeometry G R))
    (T : FiniteScaleSequence
      ((selectedHierarchy R).effectiveRadius 0) depth)
    (A : SelectedAncestorInjective R)
    {massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal}
    (D : LargeIntervalLocalGeometry (selectedIdentityCoherentCover R) T epsilon
      massLoss bodyLoss katzTaoLoss)
    (B : DiscreteAllLargeStickyBounds (selectedIdentityCoherentCover R) T epsilon
      frostmanError katzTaoError)
    (K : LevelZeroCanonicalHundredRadiusCompatible H)
    (W : HierarchyLevelWZSeparationData H) :
    (selectedIdentityCoherentCover R).base.IsStickyAtEveryScale
      (hierarchyReverseNormalizerBound
          (hierarchyBranchingBound (selectedHierarchy R))
          (16 * ((levelZeroParentCount (selectedHierarchy R) hdepth *
            commonHundredNeighbourPackingConstant : Nat) : ENNReal)) *
        frostmanError)
      (katzTaoLoss * katzTaoError) := by
  exact isStickyAtEveryScale_of_geometry_and_canonicalRadiusCompatible
    (H := selectedHierarchy R) (G := SelectedGeometry G R) (J := Js)
    (X := selectedIdentityRestrictionCoordinates R T A)
    hdepth D B
    (selectedHierarchyLevelWZSeparationData (S := R) W)
    (selectedHierarchy_levelZeroCanonicalHundredRadiusCompatible R K)

/-! ## Sharp finite seam for extending the coordinates to all radii -/

/-- A genuine two-to-one parent step cannot retain injective coordinates for
the identity real-radius cover. -/
theorem twoToOneParent_has_no_injective_ancestorCoordinate :
    let parent : Fin 2 -> Fin 1 := fun _ => 0
    Function.Surjective parent ∧
      Not (Function.Injective parent) := by
  dsimp
  constructor
  · intro p
    exact ⟨0, Subsingleton.elim _ _⟩
  · intro hinj
    have h := @hinj (0 : Fin 2) (1 : Fin 2)
      (Subsingleton.elim _ _)
    norm_num at h

#print axioms identityRadiusScaleCover
#print axioms identityRadiusCoherentCover
#print axioms identityRadiusCoherentCover_interval_parent
#print axioms StickyScaleCover.ofCoarseTubePartitionReindex
#print axioms selectedAdjacentEndpointCover
#print axioms selectedAdjacentLowerCoordinate
#print axioms selectedAdjacentUpperCoordinate
#print axioms selectedAdjacent_parent_commutes
#print axioms restrictedParentIndex_val_of_restrict
#print axioms hierarchyAncestor
#print axioms hierarchyAncestor_zero
#print axioms hierarchyAncestor_succ
#print axioms selectedHierarchyAllGeometry
#print axioms selectedIdentityCoherentCover
#print axioms allSelectedAncestor
#print axioms selectedHierarchyAll_parent_val
#print axioms SelectedAncestorInjective
#print axioms selectedIdentityRestrictionCoordinates
#print axioms selectedIdentity_parent_compatible
#print axioms selectedHierarchy_levelZeroCanonicalHundredRadiusCompatible
#print axioms actualReverseParentNormalizerLoss_le_of_selectedIdentityAncestors
#print axioms isStickyAtEveryScale_of_selectedIdentityAncestors
#print axioms twoToOneParent_has_no_injective_ancestorCoordinate

end
end FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
