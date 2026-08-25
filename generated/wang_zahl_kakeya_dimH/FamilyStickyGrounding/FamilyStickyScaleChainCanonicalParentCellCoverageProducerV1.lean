import FamilyStickyGrounding.FamilyStickyScaleChainSelectedRestrictionParentPartitionCollisionBindingV1
import FamilyStickyGrounding.FamilyStickyRandomHundredContainerSelectionV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainCanonicalParentCellCoverageProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainArbitraryRadiusInterpolationV1
open FamilyStickyScaleChainArbitraryRadiusBoundsV1
open FamilyStickyScaleChainParentNormalizerReverseProducerV1
open FamilyStickyScaleChainHierarchySiblingRigidityV1
open FamilyStickyScaleChainHierarchySiblingRigidityProducerV1
open FamilyStickyScaleChainSelectedNestedSiblingRigidityProducerV1
open FamilyStickyScaleChainCollisionCellSiblingRigidityProducerV1
open FamilyStickyScaleChainParentPartitionCollisionCellSiblingRigidityProducerV1
open FamilyStickyScaleChainSelectedRestrictionParentPartitionCollisionBindingV1
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomHundredContainerSelectionV1
open FamilyStickyRandomWZCommonNeighbourPackingV1
open FamilyStickyAllParentLayerDataV1
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
open FamilyStickyHierarchyWZ2CollisionCellSourceAdapterV1
open FamilyStickyHierarchyTerminalSourceChartBucketProducerV1

noncomputable section

/-!
# Producing canonical parent-cell coverage from actual hierarchy geometry

The joint random-motion output uses one shared translation at a fixed layer.
Consequently it does not change the relative position of two children in one
parent fibre.  Membership of every child in the canonical base child's
collision cell follows as soon as the corresponding *untranslated* child
carrier lies in the base child's literal `100 T`.

The hierarchy supplies only that every child lies in its common effective
parent tube.  This is not by itself enough.  A genuine sufficient scale
condition is

`4 * parentRadius + childRadius <= 100 * childRadius`.

Indeed the canonical child's axis is contained in both the canonical child
and the common parent.  `TubeCommonSegment` therefore puts the whole parent
tube in the `4 * parentRadius` thickening of the canonical child.  Expanding
the latter child's own radius gives precisely the displayed inequality.

WZ separation is deliberately absent from this production step: it bounds
the cardinality only after a common hundred-fold container has been produced.
The closing two-child model records the sharp logical obstruction: common
parent, pairwise separation, singleton collision loads, and membership in
each child's own cell can all hold while the first child's cell misses the
second child.
-/

universe u

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type u}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  (H : MultiscaleTubeHierarchy depth nominalRadius Index)

/-! ## Exact deterministic content of canonical coverage -/

/-- The weakest deterministic geometric input used below: every literal
level-zero parent fibre lies in the hundred-fold tube about its canonical
base child.  It contains no random choice or collision-load conclusion. -/
def CanonicalLevelZeroSiblingHundredContainment
    (hdepth : 0 < depth) : Prop :=
  forall (p : LevelZeroActiveParent H hdepth) (i : Index 0),
    i ∈ (H.step 0 hdepth).combinatorics.index.fiber p.1 ->
      ((H.effectiveFamily 0).tubes i).carrier ⊆
        (hundredTube
          ((H.effectiveFamily 0).tubes
            (canonicalLevelZeroParentChild (H := H) p).1)).carrier

variable
  {G : HierarchyRandomMotionGeometry H}
  {J : HierarchyJointRandomMotionCertificate H G}

/-- Common translation transports the deterministic sibling containment to
the actual candidate cell.  Grid source membership, candidate, and
repetition are all the concrete definitions from the preceding binding. -/
theorem canonicalLevelZeroParentCellCoverage_of_siblingHundredContainment
    {hdepth : 0 < depth}
    (K : CanonicalLevelZeroSiblingHundredContainment H hdepth) :
    CanonicalLevelZeroParentCellCoverage (H := H) (G := G) (J := J)
      hdepth := by
  intro p i hi
  apply (mem_candidateCollisionFinset _ _ _ _).2
  refine ⟨levelZeroParentChild_mem_collisionGrid
    (H := H) (G := G) (J := J) p i hi, ?_⟩
  let grid := hierarchyCollisionGrid H G J (zeroLayer hdepth) p.1
  let r := canonicalLevelZeroRepetition (G := G) (J := J)
    (hdepth := hdepth)
  let g := (J.output.layerOutput (zeroLayer hdepth)).omega r
  have htranslated := translate_carrier_subset_translate_carrier
    (v := grid.gridVector g) (K p i hi)
  change
    (translateTube ((H.effectiveFamily 0).tubes i)
      (grid.gridVector g)).carrier ⊆
        (hundredTube
          (translateTube
            ((H.effectiveFamily 0).tubes
              (canonicalLevelZeroParentChild (H := H) p).1)
            (grid.gridVector g))).carrier
  simpa only [translateTube_hundredTube] using htranslated

/-! ## An actual adjacent-radius producer -/

/-- Exact scalar inequality sufficient for the common parent carrier to fit
inside the canonical child's hundred-fold tube. -/
def LevelZeroCanonicalHundredRadiusCompatible : Prop :=
  4 * H.effectiveRadius 1 + H.effectiveRadius 0 <=
    hundredRadius (H.effectiveRadius 0)

/-- A generic parent tube containing an equal-child-radius base tube is
contained in the base tube's hundred-fold dilation under the exact `4R+r`
radius inequality. -/
theorem parent_carrier_subset_hundredTube_of_base_subset
    {r R : NNReal} (base : Tube r) (parent : Tube R)
    (hbase : base.carrier ⊆ parent.carrier)
    (hratio : 4 * R + r <= hundredRadius r) :
    parent.carrier ⊆ (hundredTube base).carrier := by
  have hnear : parent.carrier ⊆
      Metric.cthickening (4 * (R : Real)) base.carrier :=
    parent.carrier_subset_four_mul_cthickening_of_commonSegment
      base base.axis
        (base.axis_subset_carrier.trans hbase)
        base.axis_subset_carrier
  refine hnear.trans ?_
  rw [Tube.carrier, hundredTube_carrier,
    cthickening_cthickening (by positivity) (by positivity)]
  apply Metric.cthickening_mono
  exact_mod_cast hratio

/-- The actual hierarchy parent containment plus the scalar ratio produces
the deterministic canonical sibling containment for every active parent. -/
theorem siblingHundredContainment_of_levelZeroRadiusCompatible
    {hdepth : 0 < depth}
    (R : LevelZeroCanonicalHundredRadiusCompatible H) :
    CanonicalLevelZeroSiblingHundredContainment H hdepth := by
  intro p i hi
  let baseIndex := canonicalLevelZeroParentChild (H := H) p
  let base := (H.effectiveFamily 0).tubes baseIndex.1
  let parent := (H.effectiveFamily 1).tubes p.1
  have hiData :=
    ((H.step 0 hdepth).combinatorics.index.mem_fiber i p.1).1 hi
  have hiRef : i ∈ (H.family 0).refinement.refined := by
    rw [← (H.step 0 hdepth).combinatorics.fine_eq_refined]
    exact hiData.1
  have hbaseData :=
    ((H.step 0 hdepth).combinatorics.index.mem_fiber
      baseIndex.1 p.1).1 baseIndex.2
  have hbaseRef : baseIndex.1 ∈ (H.family 0).refinement.refined := by
    rw [← (H.step 0 hdepth).combinatorics.fine_eq_refined]
    exact hbaseData.1
  have hiParentRaw := H.effective_carrier_subset_parent 0 hdepth i hiRef
  have hbaseParentRaw :=
    H.effective_carrier_subset_parent 0 hdepth baseIndex.1 hbaseRef
  have hiParent : ((H.effectiveFamily 0).tubes i).carrier ⊆
      parent.carrier := by
    have hp : (H.step 0 hdepth).parentIndex i = p.1 := by
      simpa [AdjacentTubeStep.parentIndex] using hiData.2
    simpa [parent, hp] using hiParentRaw
  have hbaseParent : base.carrier ⊆ parent.carrier := by
    have hp : (H.step 0 hdepth).parentIndex baseIndex.1 = p.1 := by
      simpa [AdjacentTubeStep.parentIndex] using hbaseData.2
    simpa [base, parent, hp] using hbaseParentRaw
  exact hiParent.trans
    (parent_carrier_subset_hundredTube_of_base_subset base parent
      hbaseParent R)

/-- Combining the true hierarchy geometry with the exact adjacent scale ratio
automatically supplies the previously isolated random coverage proposition. -/
theorem canonicalLevelZeroParentCellCoverage_of_levelZeroRadiusCompatible
    {hdepth : 0 < depth}
    (R : LevelZeroCanonicalHundredRadiusCompatible H) :
    CanonicalLevelZeroParentCellCoverage (H := H) (G := G) (J := J)
      hdepth :=
  canonicalLevelZeroParentCellCoverage_of_siblingHundredContainment
    (H := H) (G := G) (J := J)
    (siblingHundredContainment_of_levelZeroRadiusCompatible H R)

/-- A convenient stronger `20`-to-`1` adjacent effective-radius bound implies
the exact `4R+r <= 100r` condition. -/
theorem levelZeroCanonicalHundredRadiusCompatible_of_parent_le_twenty
    (R : H.effectiveRadius 1 <= 20 * H.effectiveRadius 0) :
    LevelZeroCanonicalHundredRadiusCompatible H := by
  unfold LevelZeroCanonicalHundredRadiusCompatible hundredRadius
  nlinarith [H.effectiveRadius (l := 0).2,
    H.effectiveRadius (l := 1).2]


/-! ## What the random-motion radius fields actually provide -/

/-- At the zero hierarchy step, childRadius_pos is exactly positivity of
the level-zero effective radius. -/
theorem randomMotionGeometry_levelZero_childRadius_pos
    (G : HierarchyRandomMotionGeometry H)
    {hdepth : 0 < depth} :
    0 < H.effectiveRadius 0 := by
  exact G.childRadius_pos (zeroLayer hdepth)

/-- At the zero hierarchy step, childRadius_le_half controls the child
radius effectiveRadius 0; it does not compare the level-one parent radius
to it. -/
theorem randomMotionGeometry_levelZero_childRadius_le_half
    (G : HierarchyRandomMotionGeometry H)
    {hdepth : 0 < depth} :
    H.effectiveRadius 0 <= (2 : NNReal)⁻¹ := by
  exact G.childRadius_le_half (zeroLayer hdepth)

/-- The separate parent field at the zero step supplies only the absolute
bound effectiveRadius 1 <= 1. -/
theorem randomMotionGeometry_levelZero_parentRadius_le_one
    (G : HierarchyRandomMotionGeometry H)
    {hdepth : 0 < depth} :
    H.effectiveRadius 1 <= 1 := by
  simpa [zeroLayer] using G.parentRadius_le_one (zeroLayer hdepth)

/-- The intrinsic hierarchy comparison points from child to parent, the
opposite direction from the upper comparison needed for canonical coverage. -/
theorem hierarchy_levelZero_childRadius_le_parentRadius
    {hdepth : 0 < depth} :
    H.effectiveRadius 0 <= H.effectiveRadius 1 :=
  H.effectiveRadius_step_le 0 hdepth

/-! ## Binding back to the actual reverse and Sticky endpoints -/

variable
  {C : CoherentStickyMultiscaleCover (H.effectiveFamily 0)}
  {S : FiniteScaleSequence (H.effectiveRadius 0) depth}
  {Rsel : SelectedTerminalSourceChartBucketGeometry (H := H)}
  (X : SelectedRestrictionCoverCoordinates H C S Rsel)

include X G J

/-- Actual reverse-normalizer endpoint with no per-parent collision-selection
field: the explicit adjacent radius inequality produces it. -/
theorem actualReverseParentNormalizerLoss_le_of_canonicalRadiusCompatible
    {hdepth : 0 < depth}
    (R : LevelZeroCanonicalHundredRadiusCompatible H)
    (W : HierarchyLevelWZSeparationData H)
    (hdelta : 0 < H.effectiveRadius 0)
    (hhalf : H.effectiveRadius 0 <= (2 : NNReal)⁻¹)
    (hcompat : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
      (i : Index 0),
      i ∈ (lowerScaleCover C S m rho hTauRho hRhoTheta).activeFine ->
      (upperEndpointCover C S m).parent i =
        (rhoToUpperCover C S m rho hTauRho hRhoTheta).parent
          ((lowerScaleCover C S m rho hTauRho hRhoTheta).parent i)) :
    actualReverseParentNormalizerLoss C S <=
      hierarchyReverseNormalizerBound (hierarchyBranchingBound H)
        (16 * ((levelZeroParentCount H hdepth *
          commonHundredNeighbourPackingConstant : Nat) : ENNReal)) := by
  exact actualReverseParentNormalizerLoss_le_parentCount_mul_WZ
    (G := G) (J := J) X
    (canonicalLevelZeroParentCellCoverage_of_levelZeroRadiusCompatible
      (G := G) (J := J) H R)
    W hdelta hhalf hcompat

/-- Arbitrary-radius Sticky endpoint under the same actual hierarchy scale
condition. -/
theorem isStickyAtEveryScale_of_canonicalRadiusCompatible
    {epsilon : Real}
    (hdepth : 0 < depth) (hdelta : 0 < H.effectiveRadius 0)
    (hhalf : H.effectiveRadius 0 <= (2 : NNReal)⁻¹)
    {massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal}
    (D : LargeIntervalLocalGeometry C S epsilon
      massLoss bodyLoss katzTaoLoss)
    (B : DiscreteAllLargeStickyBounds C S epsilon
      frostmanError katzTaoError)
    (W : HierarchyLevelWZSeparationData H)
    (R : LevelZeroCanonicalHundredRadiusCompatible H) :
    C.base.IsStickyAtEveryScale
      (hierarchyReverseNormalizerBound (hierarchyBranchingBound H)
          (16 * ((levelZeroParentCount H hdepth *
            commonHundredNeighbourPackingConstant : Nat) : ENNReal)) *
        frostmanError)
      (katzTaoLoss * katzTaoError) := by
  exact isStickyAtEveryScale_parentCount_mul_WZ
    (G := G) (J := J) X
    hdepth hdelta hhalf D B W
      (canonicalLevelZeroParentCellCoverage_of_levelZeroRadiusCompatible
        (G := G) (J := J) H R)


/-- The actual random-motion geometry already contains positivity and the
half-radius bound. Thus, once the genuinely missing adjacent-radius
comparison is supplied, callers need not repeat either scalar hypothesis. -/
theorem actualReverseParentNormalizerLoss_le_of_geometry_and_canonicalRadiusCompatible
    {hdepth : 0 < depth}
    (R : LevelZeroCanonicalHundredRadiusCompatible H)
    (W : HierarchyLevelWZSeparationData H)
    (hcompat : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
      (i : Index 0),
      i ∈ (lowerScaleCover C S m rho hTauRho hRhoTheta).activeFine ->
      (upperEndpointCover C S m).parent i =
        (rhoToUpperCover C S m rho hTauRho hRhoTheta).parent
          ((lowerScaleCover C S m rho hTauRho hRhoTheta).parent i)) :
    actualReverseParentNormalizerLoss C S <=
      hierarchyReverseNormalizerBound (hierarchyBranchingBound H)
        (16 * ((levelZeroParentCount H hdepth *
          commonHundredNeighbourPackingConstant : Nat) : ENNReal)) := by
  exact actualReverseParentNormalizerLoss_le_of_canonicalRadiusCompatible
    (G := G) (J := J) H X R W
      (randomMotionGeometry_levelZero_childRadius_pos
        (G := G) (hdepth := hdepth) H)
      (randomMotionGeometry_levelZero_childRadius_le_half
        (G := G) (hdepth := hdepth) H)
      hcompat

/-- Corresponding arbitrary-radius Sticky endpoint with the redundant
level-zero positivity and half-radius arguments discharged from G. -/
theorem isStickyAtEveryScale_of_geometry_and_canonicalRadiusCompatible
    {epsilon : Real}
    (hdepth : 0 < depth)
    {massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal}
    (D : LargeIntervalLocalGeometry C S epsilon
      massLoss bodyLoss katzTaoLoss)
    (B : DiscreteAllLargeStickyBounds C S epsilon
      frostmanError katzTaoError)
    (W : HierarchyLevelWZSeparationData H)
    (R : LevelZeroCanonicalHundredRadiusCompatible H) :
    C.base.IsStickyAtEveryScale
      (hierarchyReverseNormalizerBound (hierarchyBranchingBound H)
          (16 * ((levelZeroParentCount H hdepth *
            commonHundredNeighbourPackingConstant : Nat) : ENNReal)) *
        frostmanError)
      (katzTaoLoss * katzTaoError) := by
  exact isStickyAtEveryScale_of_canonicalRadiusCompatible
    (G := G) (J := J) H X hdepth
      (randomMotionGeometry_levelZero_childRadius_pos
        (G := G) (hdepth := hdepth) H)
      (randomMotionGeometry_levelZero_childRadius_le_half
        (G := G) (hdepth := hdepth) H)
      D B W R

/-! ## Sharp obstructions to an unconditional producer -/

omit X G J in
/-- The existing whole-parent compatibility `R <= 100r` is numerically too
weak to center the hundred-fold container at one child: the common-segment
route genuinely pays the parent-to-child recentering cost. -/
theorem parentHundredRadiusCompatibility_does_not_imply_canonicalCompatibility :
    (100 : NNReal) <= hundredRadius 1 ∧
      Not (4 * (100 : NNReal) + 1 <= hundredRadius 1) := by
  norm_num [hundredRadius]


omit X G J in
/-- Even the stronger version in which both adjacent radii satisfy the
random-motion half bound does not yield a relative 20-to-1 comparison.
The values r = 1/100 and R = 1/2 also obey positivity, the hierarchy
forward monotonicity r <= R, and the separate parent bound R <= 1.
This is the exact index/orientation obstruction to using
childRadius_le_half as a canonical-coverage producer. -/
theorem randomMotionAbsoluteBounds_do_not_imply_parent_le_twenty :
    (0 : NNReal) < (100 : NNReal)⁻¹ ∧
      (100 : NNReal)⁻¹ <= (2 : NNReal)⁻¹ ∧
      (2 : NNReal)⁻¹ <= (2 : NNReal)⁻¹ ∧
      (2 : NNReal)⁻¹ <= 1 ∧
      (100 : NNReal)⁻¹ <= (2 : NNReal)⁻¹ ∧
      Not ((2 : NNReal)⁻¹ <= 20 * (100 : NNReal)⁻¹) := by
  refine ⟨by positivity, ?_, le_rfl, by norm_num, ?_, by norm_num⟩
  · exact inv_anti₀ (by norm_num) (by norm_num)
  · exact inv_anti₀ (by norm_num) (by norm_num)

omit X G J in
/-- A two-child finite model simultaneously has one common parent, pairwise
separation, singleton collision loads, and self-cell membership, while the
canonical cell at child zero misses child one.  Thus neither hierarchy
branching, WZ separation, nor the random load bound manufactures coverage. -/
theorem twoSeparatedSameParentChildren_have_noCanonicalCoverage :
    let parent : Fin 2 -> Fin 1 := fun _ => 0
    let cell : Fin 2 -> Fin 2 -> Prop := fun a i => i = a
    (forall i j, parent i = parent j) ∧
      Set.Pairwise (Set.univ : Set (Fin 2)) (fun i j => i ≠ j) ∧
      (forall a i j, cell a i -> cell a j -> i = j) ∧
      (forall i, cell i i) ∧
      Not (forall i, cell 0 i) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intros
    apply Subsingleton.elim
  · intro i _hi j _hj hij
    exact hij
  · intro a i j hi hj
    exact hi.trans hj.symm
  · intro i
    rfl
  · intro h
    have hbad := h (1 : Fin 2)
    norm_num at hbad

#print axioms canonicalLevelZeroParentCellCoverage_of_siblingHundredContainment
#print axioms parent_carrier_subset_hundredTube_of_base_subset
#print axioms siblingHundredContainment_of_levelZeroRadiusCompatible
#print axioms canonicalLevelZeroParentCellCoverage_of_levelZeroRadiusCompatible
#print axioms levelZeroCanonicalHundredRadiusCompatible_of_parent_le_twenty
#print axioms randomMotionGeometry_levelZero_childRadius_pos
#print axioms randomMotionGeometry_levelZero_childRadius_le_half
#print axioms randomMotionGeometry_levelZero_parentRadius_le_one
#print axioms hierarchy_levelZero_childRadius_le_parentRadius
#print axioms actualReverseParentNormalizerLoss_le_of_canonicalRadiusCompatible
#print axioms isStickyAtEveryScale_of_canonicalRadiusCompatible
#print axioms actualReverseParentNormalizerLoss_le_of_geometry_and_canonicalRadiusCompatible
#print axioms isStickyAtEveryScale_of_geometry_and_canonicalRadiusCompatible
#print axioms parentHundredRadiusCompatibility_does_not_imply_canonicalCompatibility
#print axioms randomMotionAbsoluteBounds_do_not_imply_parent_le_twenty
#print axioms twoSeparatedSameParentChildren_have_noCanonicalCoverage

end
end FamilyStickyScaleChainCanonicalParentCellCoverageProducerV1
