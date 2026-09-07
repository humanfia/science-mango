import Family8Grounding.Family8PaperConflictOwnerGlobalStickyScaleCoverV4

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal BigOperators

namespace Family8PaperConflictOwnerGlobalActiveOwnerStickyScaleCoverV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyAtEveryScaleCoreV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8PaperEssentialDistinctConstantExtractionV2
open Family8PaperEssentialDistinctOwnerClusterRetentionV3
open Family8PaperConflictOwnerParentFrameFiniteCodeV8
open Family8PaperConflictOwnerGlobalCoarseCoverV3

noncomputable section

/-!
# Deduplicated active-owner global coarse cover

Each selected owner occurs only once in the new fine index type.  A chosen
active source owned by that pivot identifies an old parent fibre, hence a
genuine tagged occurrence to which the global V3 cover applies.
-/

/-- Selected owners met by the full old active fine set, with duplicates
removed by the finset image. -/
def ScaleCoverActiveOwner
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho) :=
  ↥(C.sourceOwnerImage S.activeFine)

local instance instFintypeScaleCoverActiveOwner
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho) :
    Fintype (ScaleCoverActiveOwner C S) :=
  Finset.fintypeCoeSort (C.sourceOwnerImage S.activeFine)

local instance instDecidableEqScaleCoverActiveOwner
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho) :
    DecidableEq (ScaleCoverActiveOwner C S) := by
  unfold ScaleCoverActiveOwner
  infer_instance

namespace ScaleCoverActiveOwner

/-- A chosen old active source owned by a deduplicated active owner. -/
noncomputable def source
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho) (b : ScaleCoverActiveOwner C S) : index :=
  Classical.choose (Finset.mem_image.mp b.2)

theorem source_mem_activeFine
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho) (b : ScaleCoverActiveOwner C S) :
    source C S b ∈ S.activeFine := by
  exact (Classical.choose_spec (Finset.mem_image.mp b.2)).1

theorem owner_source_eq
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho) (b : ScaleCoverActiveOwner C S) :
    C.owner (source C S b) = b.1 := by
  exact (Classical.choose_spec (Finset.mem_image.mp b.2)).2

theorem source_mem_parent_fiber
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho) (b : ScaleCoverActiveOwner C S) :
    source C S b ∈ S.fiber (S.parent (source C S b)) :=
  (S.mem_fiber _ _).mpr ⟨source_mem_activeFine C S b, rfl⟩

/-- The canonical tagged occurrence through which the global V3 label is
reused. -/
noncomputable def occurrence
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho) (b : ScaleCoverActiveOwner C S) :
    ScaleCoverOwnerOccurrence C S :=
  ⟨S.parent (source C S b),
    ⟨b.1, Finset.mem_image.mpr
      ⟨source C S b, source_mem_parent_fiber C S b,
        owner_source_eq C S b⟩⟩⟩

@[simp]
theorem occurrence_owner
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho) (b : ScaleCoverActiveOwner C S) :
    (occurrence C S b).owner = b.1 :=
  rfl

end ScaleCoverActiveOwner

/-- The deduplicated fine tube family indexed by active owners. -/
noncomputable def activeOwnerFine
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho) :
    UniformTubeFamily delta (ScaleCoverActiveOwner C S) where
  tubes := fun b => fine.tubes b.1
  refinement := UniformRefinement.ofFinset Finset.univ

@[simp]
theorem activeOwnerFine_tubes
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho) (b : ScaleCoverActiveOwner C S) :
    (activeOwnerFine C S).tubes b = fine.tubes b.1 :=
  rfl

/-- Deduplication retains the paper-essential distinctness of the selected
owner family. -/
theorem activeOwnerFine_pairwise_paper
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho) :
    Set.Pairwise (Set.univ : Set (ScaleCoverActiveOwner C S)) fun b c =>
      PaperEssentiallyDistinct
        ((activeOwnerFine C S).tubes b) ((activeOwnerFine C S).tubes c) := by
  intro b _hb c _hc hbc
  change PaperEssentiallyDistinct (fine.tubes b.1) (fine.tubes c.1)
  have hbSelected : b.1 ∈ C.selected :=
    C.sourceOwnerImage_subset_selected (by simp) b.2
  have hcSelected : c.1 ∈ C.selected :=
    C.sourceOwnerImage_subset_selected (by simp) c.2
  exact C.selected_pairwise_paper hbSelected hcSelected (by
    intro hval
    exact hbc (Subtype.ext hval))

/-- The raw active source loses at most the absolute conflict-cluster factor
when replaced by distinct active owners. -/
theorem activeFine_card_le_constant_mul_activeOwner_card
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho)
    (hdeltaPos : 0 < delta) (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (hpairwise : Set.Pairwise (Set.univ : Set index) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j)) :
    S.activeFine.card ≤
      (paperConflictConstantCodeLoss + 1) *
        Fintype.card (ScaleCoverActiveOwner C S) := by
  have hpairwise' : Set.Pairwise
      (↑(Finset.univ : Finset index) : Set index) fun i j =>
        EssentiallyDistinct (fine.tubes i) (fine.tubes j) := by
    intro i _hi j _hj hij
    exact hpairwise (Set.mem_univ i) (Set.mem_univ j) hij
  have h :=
    Family8PaperEssentialDistinctOwnerClusterRetentionV3.PaperConflictOwnerClustering.source_card_le_constant_mul_ownerImage_card
      C hdeltaPos hdeltaSmall hpairwise' S.activeFine (by simp)
  have hcard : Fintype.card (ScaleCoverActiveOwner C S) =
      (C.sourceOwnerImage S.activeFine).card := by
    exact Fintype.card_coe _
  simpa only [hcard] using h

/-- The V3 global coarse cover descends to the deduplicated active-owner
family.  Only actually occupied labels are active, so parent surjectivity is
literal. -/
theorem exists_activeOwner_stickyScaleCover
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho)
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (hdeltaRho : delta ≤ rho) (hrhoPos : 0 < rho) (hrhoOne : rho ≤ 1) :
    ∃ T : StickyScaleCover (activeOwnerFine C S) (5 * rho),
      T.coarseCard ≤ S.coarseCard * parentFrameCodeCount rho := by
  classical
  obtain ⟨n, coarse0, label, hn, hcontain⟩ :=
    exists_scaleCoverOwnerOccurrence_globalCoarseCover C S hdeltaSmall
      hdeltaRho hrhoPos hrhoOne
  let activeLabel : ScaleCoverActiveOwner C S → Fin n := fun b =>
    label (ScaleCoverActiveOwner.occurrence C S b)
  let occupied : Finset (Fin n) :=
    (Finset.univ : Finset (ScaleCoverActiveOwner C S)).image activeLabel
  let coarse : UniformTubeFamily (5 * rho) (Fin n) :=
    { tubes := coarse0.tubes
      refinement := UniformRefinement.ofFinset occupied }
  let T : StickyScaleCover (activeOwnerFine C S) (5 * rho) :=
    { coarseCard := n
      coarse := coarse
      activeFine := Finset.univ
      activeCoarse := occupied
      parent := activeLabel
      activeFine_eq_refined := by rfl
      activeCoarse_eq_refined := by rfl
      parent_mem := by
        intro b _hb
        exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩
      parent_surjective := by
        intro k hk
        obtain ⟨b, _hb, hbk⟩ := Finset.mem_image.mp hk
        exact ⟨b, Finset.mem_univ b, hbk⟩
      carrier_subset := by
        intro b _hb
        have h := hcontain (ScaleCoverActiveOwner.occurrence C S b)
        simpa only [activeOwnerFine_tubes,
          ScaleCoverActiveOwner.occurrence_owner] using h }
  exact ⟨T, hn⟩

#print axioms activeOwnerFine_pairwise_paper
#print axioms activeFine_card_le_constant_mul_activeOwner_card
#print axioms exists_activeOwner_stickyScaleCover

end
end Family8PaperConflictOwnerGlobalActiveOwnerStickyScaleCoverV5
