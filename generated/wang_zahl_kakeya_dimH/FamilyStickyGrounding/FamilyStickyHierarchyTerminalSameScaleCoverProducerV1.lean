import FamilyStickyGrounding.FamilyStickyHierarchyTerminalWZ2CoefficientBridgeV1
import FamilyStickyCinematicL32ActualGraphSlopeParallelV1

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal

namespace FamilyStickyHierarchyTerminalSameScaleCoverProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyActualTubeTranslationV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualTubeCoefficientSelectionV1
open FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1
open FamilyStickyCinematicL32ActualGraphSlopeParallelV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickySameRadiusTubeContainmentCompatibleV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1.HierarchyJointRandomMotionCertificate
open FamilyStickyHierarchyTerminalCarrierDedupV1
open FamilyStickyHierarchyTerminalEssentialDistinctAdapterV1
open FamilyStickyHierarchyTerminalWZ2CoefficientBridgeV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# The canonical terminal same-scale cover and its sharp obstruction

The hierarchy's packing certificates pack translation vectors in a motion
ball.  They do not contain a parent map from final tubes to same-radius tube
containers.  There is nevertheless a canonical same-scale cover: use one
literal parent for every active tube.

For a WZ2-separated family this tautological construction is optimal.  If
two active tubes had the same cover parent, same-radius carrier rigidity
would identify their carriers, contradicting WZ2 noncontainment.  Hence
every same-radius cover has at least as many parents as active tubes.  In
particular the `3 * 13^3 * Q.count <= card` premise in the current terminal
nonemptiness endpoint is incompatible with `0 < Q.count`; it cannot be
supplied by a better packing construction.

The half-scale parallelity premise has a different source.  Translation
preserves tube directions, so it follows from two honest pre-motion facts:
all level-zero source tubes lie in a nonvertical chart, and they lie in one
half-radius bucket of the omitted graph-`c` coordinate.  The reduced
coefficient distance itself contains only the `a`, `b`, and `d` coordinates,
so the graph-`c` input cannot be discarded.
-/

universe u

/-! ## A canonical identity cover of any finite tube family -/

/-- One same-radius parent for every index.  This construction needs no
geometric or packing input. -/
noncomputable def identityUnivTubeScaleCover
    {delta : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) :
    @TubeScaleCover delta delta iota _ fine Finset.univ where
  count := Fintype.card iota
  tubes := fun q => fine.tubes ((Fintype.equivFin iota).symm q)
  parent := Fintype.equivFin iota
  carrier_subset := by
    intro i _hi
    rw [Equiv.symm_apply_apply]

@[simp]
theorem identityUnivTubeScaleCover_count
    {delta : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) :
    (identityUnivTubeScaleCover fine).count = Fintype.card iota :=
  rfl

/-! ## Every WZ2 same-radius cover has an injective parent map -/

/-- WZ2 separation and same-radius carrier rigidity force the cover-parent
map to be injective on the active family. -/
theorem TubeScaleCover.parent_injectiveOn_of_pairwise_wz2
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    {fine : UniformTubeFamily delta iota} {active : Finset iota}
    (Q : @TubeScaleCover delta delta iota _ fine active)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      WZ2EssentiallyDistinct (fine.tubes i) (fine.tubes j)) :
    Set.InjOn Q.parent (active : Set iota) := by
  intro i hi j hj hparent
  by_contra hij
  have hiSubset : (fine.tubes i).carrier ⊆
      (Q.tubes (Q.parent i)).carrier :=
    Q.carrier_subset i hi
  have hjSubset : (fine.tubes j).carrier ⊆
      (Q.tubes (Q.parent i)).carrier := by
    simpa only [hparent] using Q.carrier_subset j hj
  have hiEq : (fine.tubes i).carrier =
      (Q.tubes (Q.parent i)).carrier :=
    tubeCarrierEqOfSameRadiusCarrierSubset
      (fine.tubes i) (Q.tubes (Q.parent i)) hiSubset
  have hjEq : (fine.tubes j).carrier =
      (Q.tubes (Q.parent i)).carrier :=
    tubeCarrierEqOfSameRadiusCarrierSubset
      (fine.tubes j) (Q.tubes (Q.parent i)) hjSubset
  exact (hpair hi hj hij).carrier_ne (hiEq.trans hjEq.symm)

/-- Consequently every same-radius cover of a WZ2-separated active family
has at least as many parents as active tubes. -/
theorem TubeScaleCover.active_card_le_count_of_pairwise_wz2
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    {fine : UniformTubeFamily delta iota} {active : Finset iota}
    (Q : @TubeScaleCover delta delta iota _ fine active)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      WZ2EssentiallyDistinct (fine.tubes i) (fine.tubes j)) :
    active.card ≤ Q.count := by
  classical
  calc
    active.card = (active.image Q.parent).card := by
      symm
      exact Finset.card_image_iff.mpr fun i hi j hj hEq =>
        FamilyStickyHierarchyTerminalSameScaleCoverProducerV1.TubeScaleCover.parent_injectiveOn_of_pairwise_wz2 Q hpair hi hj hEq
    _ ≤ (Finset.univ : Finset (Fin Q.count)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = Q.count := Fintype.card_fin Q.count

/-! ## Specialization to terminal strong representatives -/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  (C : HierarchyJointRandomMotionCertificate H G)

/-- The canonical, assumption-free terminal same-scale cover. -/
noncomputable def terminalStrongIdentitySameScaleCover :
    TerminalStrongSameScaleCover C :=
  identityUnivTubeScaleCover (terminalStrongTubeFamily C)

@[simp]
theorem terminalStrongIdentitySameScaleCover_count :
    (terminalStrongIdentitySameScaleCover C).count =
      Fintype.card (TerminalStrongIndex C) :=
  rfl

theorem terminalStrongIdentitySameScaleCover_count_eq_representatives_card :
    (terminalStrongIdentitySameScaleCover C).count =
      (terminalStrongRepresentatives C).card := by
  rw [terminalStrongIdentitySameScaleCover_count, Fintype.card_coe]

/-- The identity cover is cardinality-minimal among all terminal strong
same-scale covers. -/
theorem terminalStrong_card_le_sameScaleCover_count
    (Q : TerminalStrongSameScaleCover C) :
    Fintype.card (TerminalStrongIndex C) ≤ Q.count := by
  simpa only [Finset.card_univ] using
    FamilyStickyHierarchyTerminalSameScaleCoverProducerV1.TubeScaleCover.active_card_le_count_of_pairwise_wz2 Q
      (terminalStrongTubeFamily_pairwise_wz2_on_activeUniv C)

theorem terminalStrongIdentitySameScaleCover_count_le
    (Q : TerminalStrongSameScaleCover C) :
    (terminalStrongIdentitySameScaleCover C).count ≤ Q.count := by
  rw [terminalStrongIdentitySameScaleCover_count]
  exact terminalStrong_card_le_sameScaleCover_count C Q

/-! ## The exact pre-motion chart and graph-c bucket input -/

/-- Translation does not change the graph-`c` direction coordinate. -/
@[simp]
theorem projectedTubeGraphC_translateTube
    {delta : NNReal} (T : Tube delta) (v : Space) :
    projectedTubeGraphC (translateTube T v) = projectedTubeGraphC T :=
  rfl

/-- The minimal source-level geometry missing from the hierarchy and its
motion packing certificates.  Both fields concern only the original active
level-zero tubes; all terminal translations are handled automatically. -/
structure TerminalSourceChartBucketGeometry : Prop where
  direction_two_ne_zero : forall i,
    i ∈ (H.family 0).refinement.refined ->
      ((H.effectiveFamily 0).tubes i).axis.direction 2 ≠ 0
  graphC_halfBucket : forall i,
    i ∈ (H.family 0).refinement.refined -> forall j,
    j ∈ (H.family 0).refinement.refined ->
      |projectedTubeGraphC ((H.effectiveFamily 0).tubes i) -
        projectedTubeGraphC ((H.effectiveFamily 0).tubes j)| ≤
          ((H.effectiveRadius 0 : NNReal) : Real) / 2

namespace TerminalSourceChartBucketGeometry

variable (S : TerminalSourceChartBucketGeometry (H := H))
include S

/-- The source chart condition survives every joint random-motion path and
the terminal strong restriction. -/
theorem terminalStrong_direction_two_ne_zero
    (a : TerminalStrongIndex C) :
    ((terminalStrongTubeFamily C).tubes a).axis.direction 2 ≠ 0 := by
  simpa [terminalStrongTubeFamily_tubes,
    HierarchyJointRandomMotionCertificate.finalTube, translateTube,
    translateUnitSegment] using
      TerminalSourceChartBucketGeometry.direction_two_ne_zero S a.1.2.1 a.1.2.2

/-- The source graph-`c` bucket also survives arbitrary, independently
chosen terminal translation paths. -/
theorem terminalStrong_graphC_halfBucket
    (a b : TerminalStrongIndex C) :
    |projectedTubeGraphC ((terminalStrongTubeFamily C).tubes a) -
      projectedTubeGraphC ((terminalStrongTubeFamily C).tubes b)| ≤
        ((H.effectiveRadius 0 : NNReal) : Real) / 2 := by
  simpa only [terminalStrongTubeFamily_tubes,
    HierarchyJointRandomMotionCertificate.finalTube,
    projectedTubeGraphC_translateTube] using
      TerminalSourceChartBucketGeometry.graphC_halfBucket S
        a.1.2.1 a.1.2.2 b.1.2.1 b.1.2.2
/-- The complete half-coefficient direction-parallel premise consumed by
the terminal WZ2 coefficient bridge, produced from source chart/bucket data. -/
theorem terminalStrong_halfCoefficient_parallel
    (j i : TerminalStrongIndex C)
    (hi : i ∈ activeNearCoefficientIndices (terminalStrongTubeFamily C)
      Finset.univ ((terminalStrongTubeFamily C).tubes j)
        (((H.effectiveRadius 0 : NNReal) : Real) / 2)) :
    EssentiallyParallelAtScale
      ((terminalStrongTubeFamily C).tubes i)
      ((terminalStrongTubeFamily C).tubes j) := by
  apply essentiallyParallelAtScale_of_halfCBucket_halfCoefficient
  · exact terminalStrong_direction_two_ne_zero C S i
  · exact terminalStrong_direction_two_ne_zero C S j
  · exact terminalStrong_graphC_halfBucket C S i j
  · exact (Finset.mem_filter.mp hi).2

/-- With the honest source geometry supplied, the bridge's coefficient cap
has no remaining local direction callback. -/
theorem terminalStrong_activeNearCoefficientIndices_card_le_fullCap
    (Q : TerminalStrongSameScaleCover C)
    (hdelta : 0 < H.effectiveRadius 0)
    (center : Tube (H.effectiveRadius 0)) :
    (activeNearCoefficientIndices (terminalStrongTubeFamily C) Finset.univ
      center ((H.effectiveRadius 0 : NNReal) : Real)).card ≤
      actualHalfScaleCoefficientCoverLoss * Q.count := by
  exact
    _root_.FamilyStickyHierarchyTerminalWZ2CoefficientBridgeV1.terminalStrong_activeNearCoefficientIndices_card_le_fullCap
        C Q hdelta (fun j i hi =>
          terminalStrong_halfCoefficient_parallel C S j i hi) center

end TerminalSourceChartBucketGeometry

/-! ## Nonemptiness and the impossible large-family premise -/

/-- Positive depth supplies a terminal strong representative: choose one
literal final occurrence and then use maximal strong-selection coverage. -/
theorem terminalStrongIndex_nonempty_of_depth_pos
    (hdepth : 0 < depth) : Nonempty (TerminalStrongIndex C) := by
  obtain ⟨path⟩ := C.path_nonempty
  obtain ⟨i, hi⟩ :=
    _root_.FamilyStickyHierarchyTranslatedFamilyV1.HierarchyRandomMotionGeometry.activeFine_nonempty_of_depth_pos H hdepth
  let a : C.FinalIndex := (path, ⟨i, hi⟩)
  obtain ⟨b, hb, _hcommon⟩ :=
    exists_strongRepresentative_commonHundredContainer C a
  exact ⟨⟨b, hb⟩⟩

/-- A nonempty terminal strong family gives a positive count for every
same-scale cover. -/
theorem terminalStrong_sameScaleCover_count_pos
    (Q : TerminalStrongSameScaleCover C)
    (hstrong : Nonempty (TerminalStrongIndex C)) :
    0 < Q.count := by
  let a : TerminalStrongIndex C := Classical.choice hstrong
  exact lt_of_le_of_lt (Nat.zero_le _) (Q.parent a).isLt

theorem terminalStrong_sameScaleCover_count_pos_of_depth_pos
    (Q : TerminalStrongSameScaleCover C) (hdepth : 0 < depth) :
    0 < Q.count :=
  terminalStrong_sameScaleCover_count_pos C Q
    (terminalStrongIndex_nonempty_of_depth_pos C hdepth)

/-- The selected coefficient family is nonempty directly from a nonempty
source family.  No cover count, coefficient cap, or three-times-large
hypothesis is needed for mere nonemptiness. -/
theorem terminalStrong_selectedTubes_nonempty_of_index_nonempty
    (hstrong : Nonempty (TerminalStrongIndex C))
    (scale : Real) :
    (selectedTubes
      (activeTubeImage (terminalStrongTubeFamily C) Finset.univ)
      scale).Nonempty := by
  classical
  let a : TerminalStrongIndex C := Classical.choice hstrong
  let family := activeTubeImage (terminalStrongTubeFamily C) Finset.univ
  have ha : (terminalStrongTubeFamily C).tubes a ∈ family := by
    simp [family, activeTubeImage]
  let member : TubeMember family :=
    ⟨(terminalStrongTubeFamily C).tubes a, ha⟩
  let selected := (coefficientSelection family scale).code member
  refine ⟨selected.1.1, ?_⟩
  rw [selectedTubes, Finset.mem_image]
  exact ⟨selected.1, selected.2, rfl⟩

theorem terminalStrong_selectedTubes_nonempty_of_depth_pos
    (hdepth : 0 < depth) (scale : Real) :
    (selectedTubes
      (activeTubeImage (terminalStrongTubeFamily C) Finset.univ)
      scale).Nonempty :=
  terminalStrong_selectedTubes_nonempty_of_index_nonempty C
    (terminalStrongIndex_nonempty_of_depth_pos C hdepth) scale

/-- Sharp obstruction to the current bridge's nonemptiness hypotheses:
same-radius WZ2 rigidity gives `card <= Q.count`, while the requested lower
bound is `3 * 13^3 * Q.count <= card`. -/
theorem terminalStrong_three_fullCaps_large_false
    (Q : TerminalStrongSameScaleCover C)
    (hcount : 0 < Q.count)
    (hlarge :
      3 * (actualHalfScaleCoefficientCoverLoss * Q.count) ≤
        Fintype.card (TerminalStrongIndex C)) : False := by
  have hcollapse :
      3 * (actualHalfScaleCoefficientCoverLoss * Q.count) ≤ Q.count :=
    hlarge.trans (terminalStrong_card_le_sameScaleCover_count C Q)
  norm_num [actualHalfScaleCoefficientCoverLoss] at hcollapse
  omega

theorem terminalStrong_three_fullCaps_large_false_of_depth_pos
    (Q : TerminalStrongSameScaleCover C) (hdepth : 0 < depth)
    (hlarge :
      3 * (actualHalfScaleCoefficientCoverLoss * Q.count) ≤
        Fintype.card (TerminalStrongIndex C)) : False :=
  terminalStrong_three_fullCaps_large_false C Q
    (terminalStrong_sameScaleCover_count_pos_of_depth_pos C Q hdepth) hlarge

theorem not_terminalStrong_three_fullCaps_large
    (Q : TerminalStrongSameScaleCover C) :
    ¬ (0 < Q.count ∧
      3 * (actualHalfScaleCoefficientCoverLoss * Q.count) ≤
        Fintype.card (TerminalStrongIndex C)) := by
  rintro ⟨hcount, hlarge⟩
  exact terminalStrong_three_fullCaps_large_false C Q hcount hlarge

#print axioms identityUnivTubeScaleCover
#print axioms TubeScaleCover.parent_injectiveOn_of_pairwise_wz2
#print axioms TubeScaleCover.active_card_le_count_of_pairwise_wz2
#print axioms terminalStrongIdentitySameScaleCover
#print axioms terminalStrong_card_le_sameScaleCover_count
#print axioms TerminalSourceChartBucketGeometry.terminalStrong_halfCoefficient_parallel
#print axioms TerminalSourceChartBucketGeometry.terminalStrong_activeNearCoefficientIndices_card_le_fullCap
#print axioms terminalStrongIndex_nonempty_of_depth_pos
#print axioms terminalStrong_selectedTubes_nonempty_of_depth_pos
#print axioms terminalStrong_three_fullCaps_large_false
#print axioms terminalStrong_three_fullCaps_large_false_of_depth_pos

end

end FamilyStickyHierarchyTerminalSameScaleCoverProducerV1
