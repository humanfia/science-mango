import Family8Grounding.Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
import Family8Grounding.Family8StickyParentHullVolumeBoundV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickySelectedParentGreedyBlockFrostmanV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyAllOccurrenceFrostman
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8StickyParentHullVolumeBoundV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

abbrev ActiveParentIndex (S : StickyScaleCover fine rho) :=
  {k // k ∈ S.activeCoarse}

/-- Original coarse indices represented by an arbitrary selected block of
active-parent subtype indices. -/
def selectedParentValues (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) : Finset (Fin S.coarseCard) :=
  B.map ⟨Subtype.val, Subtype.val_injective⟩

/-- Fine indices whose actual parent belongs to the selected active-parent
block. -/
def selectedParentFineFinset (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) : Finset index :=
  S.activeFine.filter fun i => S.parent i ∈ selectedParentValues S B

abbrev SelectedParentFineIndex (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) :=
  ↥(selectedParentFineFinset S B)

local instance selectedParentFineFintype
    (S : StickyScaleCover fine rho) (B : Finset (ActiveParentIndex S)) :
    Fintype (SelectedParentFineIndex S B) :=
  Finset.fintypeCoeSort (selectedParentFineFinset S B)

local instance selectedParentFineDecidableEq
    (S : StickyScaleCover fine rho) (B : Finset (ActiveParentIndex S)) :
    DecidableEq (SelectedParentFineIndex S B) := Classical.decEq _

namespace SelectedParentFineIndex

theorem data (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (i : SelectedParentFineIndex S B) :
    i.1 ∈ S.activeFine ∧ S.parent i.1 ∈ selectedParentValues S B := by
  exact Finset.mem_filter.mp i.2

/-- The uniquely determined selected active parent of a retained fine
index. -/
theorem exists_blockParent (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (i : SelectedParentFineIndex S B) :
    ∃ p : {p // p ∈ B}, p.1.1 = S.parent i.1 := by
  have hmem := (data S B i).2
  unfold selectedParentValues at hmem
  rcases Finset.mem_map.mp hmem with ⟨p, hp, hval⟩
  exact ⟨⟨p, hp⟩, hval⟩

noncomputable def blockParent (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (i : SelectedParentFineIndex S B) :
    {p // p ∈ B} :=
  Classical.choose (exists_blockParent S B i)

@[simp]
theorem blockParent_value (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (i : SelectedParentFineIndex S B) :
    (blockParent S B i).1.1 = S.parent i.1 :=
  Classical.choose_spec (exists_blockParent S B i)

end SelectedParentFineIndex

/-- The honest restricted fine family; all retained indices are active. -/
noncomputable abbrev selectedParentFineFamily
    (S : StickyScaleCover fine rho) (B : Finset (ActiveParentIndex S)) :
    UniformTubeFamily delta (SelectedParentFineIndex S B) :=
  { tubes := fun i => fine.tubes i.1
    refinement := UniformRefinement.ofFinset Finset.univ }

@[simp]
theorem selectedParentFineFamily_tubes
    (S : StickyScaleCover fine rho) (B : Finset (ActiveParentIndex S))
    (i : SelectedParentFineIndex S B) :
    (selectedParentFineFamily S B).tubes i = fine.tubes i.1 :=
  rfl

/-- Restrict a sticky cover to any selected block of active parents and all
fine indices actually assigned to those parents. -/
noncomputable abbrev selectedParentBlockScaleCover
    (S : StickyScaleCover fine rho) (B : Finset (ActiveParentIndex S)) :
    StickyScaleCover (selectedParentFineFamily S B) rho := by
  classical
  let e : {p // p ∈ B} ≃ Fin B.card := B.equivFin
  let coarse : UniformTubeFamily rho (Fin B.card) :=
    { tubes := fun q => S.coarse.tubes (e.symm q).1.1
      refinement := UniformRefinement.ofFinset Finset.univ }
  exact
    { coarseCard := B.card
      coarse := coarse
      activeFine := Finset.univ
      activeCoarse := Finset.univ
      parent := fun i => e (SelectedParentFineIndex.blockParent S B i)
      activeFine_eq_refined := rfl
      activeCoarse_eq_refined := rfl
      parent_mem := by simp
      parent_surjective := by
        intro q _hq
        let p : {p // p ∈ B} := e.symm q
        have hpActive : p.1.1 ∈ S.activeCoarse := p.1.2
        obtain ⟨i, hiActive, hiParent⟩ :=
          S.parent_surjective p.1.1 hpActive
        have hiSelected : S.parent i ∈ selectedParentValues S B := by
          unfold selectedParentValues
          apply Finset.mem_map.mpr
          exact ⟨p.1, p.2, hiParent.symm⟩
        let ii : SelectedParentFineIndex S B :=
          ⟨i, Finset.mem_filter.mpr ⟨hiActive, hiSelected⟩⟩
        refine ⟨ii, Finset.mem_univ ii, ?_⟩
        have hblock : SelectedParentFineIndex.blockParent S B ii = p := by
          apply Subtype.ext
          apply Subtype.ext
          exact (SelectedParentFineIndex.blockParent_value S B ii).trans
            hiParent
        rw [hblock, e.apply_symm_apply]
      carrier_subset := by
        intro i _hi
        have hsource :=
          S.carrier_subset i.1 (SelectedParentFineIndex.data S B i).1
        change (fine.tubes i.1).carrier ⊆
          (S.coarse.tubes
            (e.symm (e (SelectedParentFineIndex.blockParent S B i))).1.1).carrier
        rw [e.symm_apply_apply,
          SelectedParentFineIndex.blockParent_value]
        exact hsource }

@[simp]
theorem selectedParentBlockScaleCover_coarse_tubes
    (S : StickyScaleCover fine rho) (B : Finset (ActiveParentIndex S))
    (q : Fin B.card) :
    (selectedParentBlockScaleCover S B).coarse.tubes q =
      S.coarse.tubes (B.equivFin.symm q).1.1 :=
  rfl

/-- Active new coarse indices are canonically equivalent to the literal
selected-parent block. -/
noncomputable def activeCoarseEquivSelected
    (S : StickyScaleCover fine rho) (B : Finset (ActiveParentIndex S)) :
    {q // q ∈ (selectedParentBlockScaleCover S B).activeCoarse} ≃
      {p // p ∈ B} :=
  { toFun := fun q => B.equivFin.symm q.1
    invFun := fun p => ⟨B.equivFin p, Finset.mem_univ _⟩
    left_inv := fun q => Subtype.ext (B.equivFin.apply_symm_apply q.1)
    right_inv := fun p => by
      apply Subtype.ext
      exact congrArg Subtype.val (B.equivFin.symm_apply_apply p) }

/-- The equivalence preserves the actual parent body pointwise. -/
@[simp]
theorem activeCoarseFamily_apply_activeCoarseEquivSelected
    (S : StickyScaleCover fine rho) (B : Finset (ActiveParentIndex S))
    (q : {q // q ∈ (selectedParentBlockScaleCover S B).activeCoarse}) :
    (selectedParentBlockScaleCover S B).activeCoarseFamily q =
      selectedCoarseFamily S.activeCoarseFamily B
        (activeCoarseEquivSelected S B q) := by
  rfl

/-- Ordinary contained mass is invariant under a body-preserving finite
reindexing. -/
theorem containedMass_eq_of_bodyPreservingEquiv
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (e : alpha ≃ beta) (F : ConvexFamily alpha) (G : ConvexFamily beta)
    (hbody : ∀ a, F a = G (e a)) (K : ConvexBody Space) :
    containedMass F K = containedMass G K := by
  classical
  unfold containedMass containedIndices
  rw [Finset.sum_filter, Finset.sum_filter]
  change (∑ a : alpha,
      if (F a : Set Space) ⊆ (K : Set Space) then
        volume (F a : Set Space) else 0) =
    ∑ b : beta,
      if (G b : Set Space) ⊆ (K : Set Space) then
        volume (G b : Set Space) else 0
  exact Fintype.sum_equiv e _ _ (fun a => by rw [hbody a])

theorem concentration_eq_of_bodyPreservingEquiv
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (e : alpha ≃ beta) (F : ConvexFamily alpha) (G : ConvexFamily beta)
    (hbody : ∀ a, F a = G (e a)) (K : ConvexBody Space) :
    concentration F K = concentration G K := by
  rw [concentration_eq_containedMass_div,
    concentration_eq_containedMass_div,
    containedMass_eq_of_bodyPreservingEquiv e F G hbody K]

theorem maximalConcentration_eq_of_bodyPreservingEquiv
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (e : alpha ≃ beta) (F : ConvexFamily alpha) (G : ConvexFamily beta)
    (hbody : ∀ a, F a = G (e a)) :
    maximalConcentration F = maximalConcentration G := by
  apply le_antisymm
  · apply iSup_le
    intro K
    rw [concentration_eq_of_bodyPreservingEquiv e F G hbody K]
    exact le_iSup (fun L : ConvexBody Space => concentration G L) K
  · apply iSup_le
    intro K
    rw [← concentration_eq_of_bodyPreservingEquiv e F G hbody K]
    exact le_iSup (fun L : ConvexBody Space => concentration F L) K

/-- The Family 6 canonical scalar is invariant under a body-preserving finite
reindexing. -/
theorem canonicalFrostmanConstant_eq_of_bodyPreservingEquiv
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (e : alpha ≃ beta) (F : ConvexFamily alpha) (G : ConvexFamily beta)
    (hbody : ∀ a, F a = G (e a)) (K : ConvexBody Space) :
    canonicalFrostmanConstant F K = canonicalFrostmanConstant G K := by
  unfold canonicalFrostmanConstant
  rw [maximalConcentration_eq_of_bodyPreservingEquiv e F G hbody,
    containedMass_eq_of_bodyPreservingEquiv e F G hbody K]

/-- Every greedy block of the literal active-parent family produces an
honest restricted sticky cover whose active coarse family has canonical
Frostman constant at most one in the actual winning hull. -/
theorem selectedParentGreedyBlock_canonicalFrostmanConstant_le_one
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length) :
    let B := (blockAt S.activeCoarseFamily P k).fiber
    canonicalFrostmanConstant
        (selectedParentBlockScaleCover S B).activeCoarseFamily
        (blockAt S.activeCoarseFamily P k).body <= 1 := by
  dsimp only
  have hselected : canonicalFrostmanConstant
      (selectedCoarseFamily S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P k).fiber)
      (blockAt S.activeCoarseFamily P k).body <= 1 := by
    apply occurrenceBlock_canonicalFrostmanConstant_le_one
      S.activeCoarseFamily Finset.univ P (fun _ h => h) k
    intro p _hp
    exact (S.coarse.tubes p.1).volume_pos hrho
  rw [canonicalFrostmanConstant_eq_of_bodyPreservingEquiv
    (activeCoarseEquivSelected S
      (blockAt S.activeCoarseFamily P k).fiber)
    (selectedParentBlockScaleCover S
      (blockAt S.activeCoarseFamily P k).fiber).activeCoarseFamily
    (selectedCoarseFamily S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k).fiber)
    (activeCoarseFamily_apply_activeCoarseEquivSelected S
      (blockAt S.activeCoarseFamily P k).fiber)]
  exact hselected

/-- A greedy winning hull is contained in every convex body containing the
base family. -/
theorem blockAt_body_subset_of_base
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (F : ConvexFamily alpha) (base : Finset alpha)
    {active : Finset alpha}
    (P : GreedyDensityPartition F (hullCandidates base)
      (hullContainer F) active)
    (K : ConvexBody Space)
    (hbase : ∀ i ∈ base, (F i : Set Space) ⊆ (K : Set Space)) :
    ∀ k : Fin (blocks F P).length,
      ((blockAt F P k).body : Set Space) ⊆ (K : Set Space) := by
  induction P with
  | empty => intro k; exact Fin.elim0 k
  | @step current choice hfiber tail ih =>
      intro k
      induction k using Fin.cases with
      | zero =>
          have hc := (mem_hullCandidates.mp choice.index_mem)
          simpa [blockAt, blocks] using
            (hullContainer_subset F hc.2 fun i hi => hbase i (hc.1 hi))
      | succ k' =>
          simpa [blockAt, blocks] using ih k'

/-- Transport a canonical bound from a smaller containing hull to a larger
ambient body using only an honest volume-ratio bound. -/
theorem canonicalFrostmanConstant_largerAmbient_le_of_volumeRatio
    {alpha : Type*} [Fintype alpha]
    (F : ConvexFamily alpha) (H K : ConvexBody Space) (A : ENNReal)
    (hcontainedH : ∀ i, (F i : Set Space) ⊆ (H : Set Space))
    (hHK : (H : Set Space) ⊆ (K : Set Space))
    (hvolume : volume (K : Set Space) <= A * volume (H : Set Space))
    (hsmall : canonicalFrostmanConstant F H <= 1) :
    canonicalFrostmanConstant F K <= A := by
  have hcontainedK : ∀ i, (F i : Set Space) ⊆ (K : Set Space) :=
    fun i => (hcontainedH i).trans hHK
  unfold canonicalFrostmanConstant at hsmall ⊢
  rw [containedMass_eq_familyVolume_of_contained F H hcontainedH] at hsmall
  rw [containedMass_eq_familyVolume_of_contained F K hcontainedK]
  calc
    maximalConcentration F * volume (K : Set Space) / familyVolume F <=
        maximalConcentration F * (A * volume (H : Set Space)) /
          familyVolume F := by
      gcongr
    _ = A *
        (maximalConcentration F * volume (H : Set Space) / familyVolume F) := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ <= A * 1 := by gcongr
    _ = A := mul_one A

/-- Flat-prism-ready radius-four transport.  The remaining quantitative
input is the explicit hull-volume lower bound, expressed as the equivalent
volume-ratio inequality; it is not a canonical-Frostman callback. -/
theorem selectedParentGreedyBlock_closedBallFour_canonical_le_of_hullVolume
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length) (A : ENNReal)
    (hHullVolume : volume (closedBallFourBody : Set Space) <=
      A * volume ((blockAt S.activeCoarseFamily P k).body : Set Space)) :
    let B := (blockAt S.activeCoarseFamily P k).fiber
    canonicalFrostmanConstant
        (selectedParentBlockScaleCover S B).activeCoarseFamily
        closedBallFourBody <= A := by
  dsimp only
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let T := selectedParentBlockScaleCover S B
  let H := (blockAt S.activeCoarseFamily P k).body
  have hsmall : canonicalFrostmanConstant T.activeCoarseFamily H <= 1 := by
    exact selectedParentGreedyBlock_canonicalFrostmanConstant_le_one S hrho P k
  have hcontainedH : ∀ q,
      (T.activeCoarseFamily q : Set Space) ⊆ (H : Set Space) := by
    intro q
    rw [activeCoarseFamily_apply_activeCoarseEquivSelected]
    exact (blockAt S.activeCoarseFamily P k).contained
      (activeCoarseEquivSelected S B q).1
      (activeCoarseEquivSelected S B q).2
  have hHB4 : (H : Set Space) ⊆ (closedBallFourBody : Set Space) := by
    apply blockAt_body_subset_of_base S.activeCoarseFamily Finset.univ P
      closedBallFourBody
    intro p _hp
    simpa only [coe_closedBallFourBody] using
      activeCoarseFamily_body_subset_closedBall_four D hD S hrhoOne p
  exact canonicalFrostmanConstant_largerAmbient_le_of_volumeRatio
    T.activeCoarseFamily H closedBallFourBody A hcontainedH hHB4
      hHullVolume hsmall

#print axioms selectedParentValues
#print axioms selectedParentBlockScaleCover
#print axioms activeCoarseEquivSelected
#print axioms activeCoarseFamily_apply_activeCoarseEquivSelected
#print axioms containedMass_eq_of_bodyPreservingEquiv
#print axioms maximalConcentration_eq_of_bodyPreservingEquiv
#print axioms canonicalFrostmanConstant_eq_of_bodyPreservingEquiv
#print axioms selectedParentGreedyBlock_canonicalFrostmanConstant_le_one
#print axioms blockAt_body_subset_of_base
#print axioms canonicalFrostmanConstant_largerAmbient_le_of_volumeRatio
#print axioms
  selectedParentGreedyBlock_closedBallFour_canonical_le_of_hullVolume

end

end Family8StickySelectedParentGreedyBlockFrostmanV3
