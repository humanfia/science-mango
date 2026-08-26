import FamilyStickyGrounding.FamilyStickyHierarchySelectedSourceNestedRestrictionV1
import FamilyStickyGrounding.FamilyStickyHierarchyWZ2TranslatedSharedHundredHullAncestorBaseZV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyHierarchySelectedLevelZeroDescendantProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1
open FamilyStickyHierarchyTerminalSourceChartBucketProducerV1
open FamilyStickyHierarchySelectedSourceNestedRestrictionV1
open FamilyStickyHierarchyWZ2CollisionCellSourceAdapterV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellCanonicalRowScaleFloorV1
open FamilyStickyHierarchyWZ2TranslatedSharedHundredHullVolumeV1
open FamilyStickyHierarchyWZ2TranslatedSharedHundredHullBaseZNormalizationV1
open FamilyStickyHierarchyWZ2TranslatedSharedHundredHullAncestorBaseZV1

noncomputable section

universe u

/-!
# Selected level-zero descendants for hierarchy collision candidates

The public WZ `L₃` adapter and the Grounding hierarchy currently cannot be
imported in one Lean environment: their import trees contain two modules
which both declare `FamilyStickyTubeParentDirectionCoherenceV1`.  There is no
mathematical mismatch between their level-zero bucket definitions, however.
The first theorem below reduces the Grounding bucket to the literal normal
form appearing in the public adapter, without importing that conflicting
tree.

The main result is independent of that packaging obstruction.  Surjectivity
of every active parent map is iterated backwards to produce a genuine active
level-zero descendant of every selected hierarchy index.  The hierarchy's
existing ancestor theorem then gives the exact effective-carrier inclusion
needed by the WZ2 source-height normalization.
-/

variable {depth : Nat} {nominalRadius : Nat → NNReal}
  {Index : Nat → Type u}
  [∀ l, Fintype (Index l)] [∀ l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}

/-! ## Exact normal form of the level-zero chart bucket -/

/-- A Grounding-side spelling of the literal expression used by
`levelZeroAnalyticChartBucket` in the public WZ `L₃` adapter.  Keeping this
normal form local avoids the duplicate-module import collision described
above. -/
def groundingLevelZeroAnalyticChartBucket (H :
    MultiscaleTubeHierarchy depth nominalRadius Index) (label : Int) :
    Finset (Index 0) :=
  (fixedVerticalChartIndices (H.effectiveFamily 0)
      (H.family 0).refinement.refined).filter fun i =>
    Int.floor
      (projectedTubeGraphC ((H.effectiveFamily 0).tubes i) /
        (((H.effectiveRadius 0 : NNReal) : Real) / 2)) = label

omit [∀ l, Fintype (Index l)] in
/-- The Grounding bucket and the public adapter's literal bucket expression
have exactly the same indices.  This is definitional after unfolding the two
local names for the same floor bucket. -/
theorem levelZeroChartBucketFiber_eq_groundingAnalytic
    (label : Int) :
    levelZeroChartBucketFiber (H := H) label =
      groundingLevelZeroAnalyticChartBucket H label := by
  rfl

/-! ## Generic ancestor-surjectivity -/

omit [∀ l, Fintype (Index l)] in
/-- Every active hierarchy index contains the effective carrier of some
active level-zero descendant.  The proof iterates `parent_surjective`
backwards and composes the literal one-step effective-carrier inclusions. -/
theorem exists_levelZero_descendant_carrier_subset_of_mem_refined
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (l : Nat) (hl : l ≤ depth) (p : Index l)
    (hp : p ∈ (H.family l).refinement.refined) :
    ∃ i : Index 0,
      i ∈ (H.family 0).refinement.refined ∧
        ((H.effectiveFamily 0).tubes i).carrier ⊆
          ((H.effectiveFamily l).tubes p).carrier := by
  induction l with
  | zero =>
      exact ⟨p, hp, Subset.rfl⟩
  | succ l ih =>
      have hstep : l < depth := by omega
      let A := H.step l hstep
      have hpCoarse : p ∈ A.combinatorics.index.coarse := by
        rw [A.combinatorics.coarse_eq_refined]
        exact hp
      obtain ⟨i, hiFine, hiParent⟩ :=
        A.combinatorics.parent_surjective p hpCoarse
      have hiRefined : i ∈ (H.family l).refinement.refined := by
        rw [← A.combinatorics.fine_eq_refined]
        exact hiFine
      obtain ⟨i0, hi0, hsubset⟩ := ih (by omega) i hiRefined
      refine ⟨i0, hi0, hsubset.trans ?_⟩
      have hparent := H.effective_carrier_subset_parent
        l hstep i hiRefined
      have hiParent' : A.parentIndex i = p := by
        simpa only [AdjacentTubeStep.parentIndex, A] using hiParent
      simpa only [A, hiParent'] using hparent

/-! ## Selected hierarchy and literal WZ2 candidate endpoints -/

variable (S : SelectedTerminalSourceChartBucketGeometry (H := H))

/-- Every selected hierarchy index has a genuinely selected level-zero
descendant, and its selected effective carrier is contained in the target
effective carrier. -/
theorem exists_selectedLevelZero_descendant_carrier_subset
    (l : Nat) (hl : l ≤ depth) (p : SelectedHierarchyIndex S l) :
    ∃ i : SelectedHierarchyIndex S 0,
      (((selectedHierarchy S).effectiveFamily 0).tubes i).carrier ⊆
        (((selectedHierarchy S).effectiveFamily l).tubes p).carrier := by
  have hp : p ∈
      ((selectedHierarchy S).family l).refinement.refined := by
    simp only [selectedHierarchy, selectedHierarchyFamily_refined,
      Finset.mem_univ]
  obtain ⟨i, _hi, hsubset⟩ :=
    exists_levelZero_descendant_carrier_subset_of_mem_refined
      (selectedHierarchy S) l hl p hp
  exact ⟨i, hsubset⟩

/-- The exact source normalization inherited from a unit-ball-normalized
selected level-zero analytic family.  It is a source property, not a new
assumption on arbitrary hierarchy levels. -/
def SelectedLevelZeroUnitBallNormalized : Prop :=
  ∀ i : SelectedHierarchyIndex S 0,
    (((selectedHierarchy S).effectiveFamily 0).tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1

/-- Unit-ball containment on the selected indices of the original level-zero
effective family transports without geometric loss to the rebuilt selected
hierarchy. -/
theorem selectedLevelZeroUnitBallNormalized_of_original
    (hunit : ∀ i, i ∈ S.selected →
      ((H.effectiveFamily 0).tubes i).carrier ⊆
        Metric.closedBall (0 : Space) 1) :
    SelectedLevelZeroUnitBallNormalized S := by
  intro i
  change ((H.effectiveFamily 0).tubes i.1).carrier ⊆
    Metric.closedBall (0 : Space) 1
  exact hunit i.1 (by
    simpa only [selectedLevelIndices_zero] using i.2)

/-- Every literal model candidate in a selected hierarchy collision grid
contains the carrier of a unit-ball-normalized selected level-zero tube. -/
theorem exists_unitBall_selectedLevelZero_descendant_of_collisionCandidate
    {G : HierarchyRandomMotionGeometry (selectedHierarchy S)}
    (C : HierarchyJointRandomMotionCertificate (selectedHierarchy S) G)
    (hunit : SelectedLevelZeroUnitBallNormalized S)
    (k : Fin depth) (p : SelectedHierarchyIndex S (k.1 + 1))
    (a : ModelCandidate
      (hierarchyCollisionGrid (selectedHierarchy S) G C k p)) :
    ∃ i : SelectedHierarchyIndex S 0,
      (((selectedHierarchy S).effectiveFamily 0).tubes i).carrier ⊆
          Metric.closedBall (0 : Space) 1 ∧
        (((selectedHierarchy S).effectiveFamily 0).tubes i).carrier ⊆
          ((hierarchyCollisionGrid
            (selectedHierarchy S) G C k p).tube a.1.1).carrier := by
  obtain ⟨i, hsubset⟩ :=
    exists_selectedLevelZero_descendant_carrier_subset S
      k.1 (Nat.le_of_lt k.2) a.1.1
  refine ⟨i, hunit i, ?_⟩
  exact hsubset

/-- The ancestor producer discharges the formerly external descendant
premise of the selected collision-cell source-height theorem. -/
theorem selectedHierarchyCollisionCell_sourceBaseZAbs_le_nine_halves
    {G : HierarchyRandomMotionGeometry (selectedHierarchy S)}
    (C : HierarchyJointRandomMotionCertificate (selectedHierarchy S) G)
    (hunit : SelectedLevelZeroUnitBallNormalized S)
    (k : Fin depth) (p : SelectedHierarchyIndex S (k.1 + 1))
    (a : ModelCandidate
      (hierarchyCollisionGrid (selectedHierarchy S) G C k p))
    (r : Fin
      (FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.repetitions
        G.toDependentSource k)) :
    sourceBaseZAbs
        (hundredTube
          (selectedHierarchyCollisionCell_sharedHundredSourceContainer
            (selectedHierarchy S) G C k p a r).container) ≤
      (9 / 2 : NNReal) := by
  obtain ⟨i, hiUnit, hiSubset⟩ :=
    exists_unitBall_selectedLevelZero_descendant_of_collisionCandidate
      S C hunit k p a
  exact
    selectedHierarchyCollisionCell_sourceBaseZAbs_le_nine_halves_of_unitBall_descendant
      C k p a r
        (((selectedHierarchy S).effectiveFamily 0).tubes i)
        hiUnit hiSubset

/-- End-to-end explicit hull-volume endpoint with the selected descendant
and its unit-ball normalization produced internally. -/
theorem volume_selectedHierarchyCollisionCell_translatedSharedHundredHull_le_nineHalves
    {G : HierarchyRandomMotionGeometry (selectedHierarchy S)}
    (C : HierarchyJointRandomMotionCertificate (selectedHierarchy S) G)
    (hunit : SelectedLevelZeroUnitBallNormalized S)
    (k : Fin depth) (p : SelectedHierarchyIndex S (k.1 + 1))
    (a : ModelCandidate
      (hierarchyCollisionGrid (selectedHierarchy S) G C k p))
    (r : Fin
      (FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.repetitions
        G.toDependentSource k))
    {siteCount : Nat} (hsiteCount : 0 < siteCount) (spacing : Real) :
    volume
        (translatedSharedHundredHullContainer
          (FamilyStickyWZ2ShearParameterPackingV1.shearReducedShift spacing
            (siteCount := siteCount))
          (selectedHierarchyCollisionCellFamily
            (selectedHierarchy S) G C k p a r)
          (selectedHierarchyCollisionCell_sharedHundredSourceContainer
            (selectedHierarchy S) G C k p a r) : Set Space) ≤
      shearGridTubeVolumeBoundAtBaseZCap
        (hundredRadius ((selectedHierarchy S).effectiveRadius k.1))
          spacing siteCount (9 / 2) := by
  obtain ⟨i, hiUnit, hiSubset⟩ :=
    exists_unitBall_selectedLevelZero_descendant_of_collisionCandidate
      S C hunit k p a
  exact
    volume_selectedHierarchyCollisionCell_translatedSharedHundredHull_le_nineHalvesBaseZCap
      C k p a r
        (((selectedHierarchy S).effectiveFamily 0).tubes i)
        hiUnit hiSubset hsiteCount spacing

#print axioms levelZeroChartBucketFiber_eq_groundingAnalytic
#print axioms exists_levelZero_descendant_carrier_subset_of_mem_refined
#print axioms exists_selectedLevelZero_descendant_carrier_subset
#print axioms selectedLevelZeroUnitBallNormalized_of_original
#print axioms exists_unitBall_selectedLevelZero_descendant_of_collisionCandidate
#print axioms selectedHierarchyCollisionCell_sourceBaseZAbs_le_nine_halves
#print axioms volume_selectedHierarchyCollisionCell_translatedSharedHundredHull_le_nineHalves

end
end FamilyStickyHierarchySelectedLevelZeroDescendantProducerV1
