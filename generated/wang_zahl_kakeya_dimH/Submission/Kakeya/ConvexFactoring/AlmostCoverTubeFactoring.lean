import Submission.Kakeya.ConvexFactoring.JointTubeFactoring
import Submission.Kakeya.ConvexFactoring.DyadicBranchingBucket

set_option autoImplicit false

/-!
# Tube factoring from an almost cover

This module adapts a Wang--Zahl-style multiple cover by actual coarse tubes to
the unique-parent interface used by `JointTubeFactoring`. Coverage is oriented
to a parent map, while a `Q`-almost incidence bound and the parentwise
`lotsOfUinW` inequality are double-counted to derive aggregate loss `R * Q`.
The aggregate inequality, retained mass, balanced branching, Katz--Tao bound
above, and Frostman bounds below are all theorem conclusions.

The construction uses logarithmic fiber-cardinality bucketing, so it retains
mass within factor `2 * (log₂(card ι) + 1)` and has branching loss two. It
does not construct the initial almost cover or its `lotsOfUinW` estimate from
an arbitrary tube family; that tube-specific geometric step remains upstream.
-/

open Set
open scoped ENNReal NNReal
open MeasureTheory

namespace Submission.Kakeya.ConvexFactoring.AlmostCoverTubeFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open JointTubeFactoring

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]
variable {δ ρ : ℝ≥0}

/-- Candidate coarse parents containing a given fine tube. -/
def candidateParents (fine : UniformTubeFamily δ ι)
    (coarse : UniformTubeFamily ρ κ) (candidates : Finset κ)
    (i : ι) : Finset κ := by
  classical
  exact candidates.filter fun k ↦
    (fine.tubes i).carrier ⊆ (coarse.tubes k).carrier

/-- Multiplicity-counted active fine mass incident to a candidate parent. -/
def incidenceBodyMass (fine : UniformTubeFamily δ ι)
    (coarse : UniformTubeFamily ρ κ) (active : Finset ι)
    (k : κ) : ℝ≥0∞ := by
  classical
  exact ∑ i ∈ active,
    if (fine.tubes i).carrier ⊆ (coarse.tubes k).carrier then
      volume (fine.tubes i).carrier else 0

omit [Fintype ι] [Fintype κ] in
@[simp] theorem mem_candidateParents
    (fine : UniformTubeFamily δ ι) (coarse : UniformTubeFamily ρ κ)
    (candidates : Finset κ) (i : ι) (k : κ) :
    k ∈ candidateParents fine coarse candidates i ↔
      k ∈ candidates ∧
      (fine.tubes i).carrier ⊆ (coarse.tubes k).carrier := by
  classical
  simp [candidateParents]

omit [Fintype ι] [Fintype κ] in
/-- Finite cover data can be oriented to a unique total parent map. -/
theorem exists_parent_assignment
    (fine : UniformTubeFamily δ ι) (coarse : UniformTubeFamily ρ κ)
    (active : Finset ι) (candidates : Finset κ)
    (hactive : active.Nonempty)
    (hcover : ∀ i ∈ active,
      (candidateParents fine coarse candidates i).Nonempty) :
    ∃ parent : ι → κ,
      (∀ i ∈ active, parent i ∈ candidates) ∧
      ∀ i ∈ active,
        (fine.tubes i).carrier ⊆ (coarse.tubes (parent i)).carrier := by
  classical
  obtain ⟨i₀, hi₀⟩ := hactive
  let k₀ := Classical.choose (hcover i₀ hi₀)
  let parent : ι → κ := fun i ↦
    if hi : i ∈ active then Classical.choose (hcover i hi) else k₀
  refine ⟨parent, ?_, ?_⟩
  · intro i hi
    have hmem : Classical.choose (hcover i hi) ∈
        candidateParents fine coarse candidates i :=
      Classical.choose_spec (hcover i hi)
    simpa only [parent, dif_pos hi] using
      (mem_candidateParents fine coarse candidates i _).1 hmem |>.1
  · intro i hi
    have hmem : Classical.choose (hcover i hi) ∈
        candidateParents fine coarse candidates i :=
      Classical.choose_spec (hcover i hi)
    simpa only [parent, dif_pos hi] using
      (mem_candidateParents fine coarse candidates i _).1 hmem |>.2

omit [Fintype ι] [Fintype κ] in
/-- Double-counting the containment incidence graph exchanges the parent and
fine-index summations exactly. -/
theorem sum_incidenceBodyMass_eq
    (fine : UniformTubeFamily δ ι) (coarse : UniformTubeFamily ρ κ)
    (active : Finset ι) (candidates : Finset κ) :
    (∑ k ∈ candidates, incidenceBodyMass fine coarse active k) =
      ∑ i ∈ active,
        ((candidateParents fine coarse candidates i).card : ℝ≥0∞) *
          volume (fine.tubes i).carrier := by
  classical
  unfold incidenceBodyMass candidateParents
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_filter]
  rw [Finset.sum_const]
  simp [nsmul_eq_mul]

omit [Fintype ι] [Fintype κ] in
/-- A `Q`-almost cover bounds total incidence mass by `Q` times active body
mass. -/
theorem sum_incidenceBodyMass_le
    (fine : UniformTubeFamily δ ι) (coarse : UniformTubeFamily ρ κ)
    (active : Finset ι) (candidates : Finset κ) (Q : ℕ)
    (halmost : ∀ i ∈ active,
      (candidateParents fine coarse candidates i).card ≤ Q) :
    (∑ k ∈ candidates, incidenceBodyMass fine coarse active k) ≤
      (Q : ℝ≥0∞) * bodyMassOn fine.bodyFamily active := by
  rw [sum_incidenceBodyMass_eq fine coarse active candidates]
  calc
    (∑ i ∈ active,
        ((candidateParents fine coarse candidates i).card : ℝ≥0∞) *
          volume (fine.tubes i).carrier) ≤
        ∑ i ∈ active, (Q : ℝ≥0∞) *
          volume (fine.tubes i).carrier := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul'
      · exact_mod_cast halmost i hi
      · exact le_rfl
    _ = (Q : ℝ≥0∞) * bodyMassOn fine.bodyFamily active := by
      rw [← Finset.mul_sum]
      simp [bodyMassOn, UniformTubeFamily.bodyFamily, Tube.coe_body]

omit [Fintype ι] [Fintype κ] in
/-- A cover plus `Q`-almost incidence and a `lotsOfUinW` lower-density bound
construct a unique parent assignment and the JointTubeFactoring aggregate
cover cost with loss `R * Q`.  The aggregate inequality is a conclusion, not
an input. -/
theorem exists_parent_with_almostCover_lots_coverCost
    (fine : UniformTubeFamily δ ι) (coarse : UniformTubeFamily ρ κ)
    (active : Finset ι) (candidates : Finset κ)
    (A R : ℝ≥0∞) (Q : ℕ)
    (hactive : active.Nonempty)
    (hcover : ∀ i ∈ active,
      (candidateParents fine coarse candidates i).Nonempty)
    (halmost : ∀ i ∈ active,
      (candidateParents fine coarse candidates i).card ≤ Q)
    (hlots : ∀ k ∈ candidates,
      A * volume (coarse.tubes k).carrier ≤
        R * incidenceBodyMass fine coarse active k)
    (hR0 : R ≠ 0) (hRtop : R ≠ ∞) :
    ∃ parent : ι → κ,
      (∀ i ∈ active, parent i ∈ candidates) ∧
      (∀ i ∈ active,
        (fine.tubes i).carrier ⊆ (coarse.tubes (parent i)).carrier) ∧
      R * (Q : ℝ≥0∞) ≠ 0 ∧
      R * (Q : ℝ≥0∞) ≠ ∞ ∧
      A * (∑ k ∈ occupiedParents active parent,
        volume (coarse.tubes k).carrier) ≤
      (R * (Q : ℝ≥0∞)) * bodyMassOn fine.bodyFamily active := by
  obtain ⟨parent, hparentCandidate, hcontained⟩ :=
    exists_parent_assignment fine coarse active candidates hactive hcover
  have hQpos : 0 < Q := by
    obtain ⟨i, hi⟩ := hactive
    have hneighbors := hcover i hi
    have hone : 1 ≤ (candidateParents fine coarse candidates i).card :=
      Finset.one_le_card.mpr hneighbors
    exact lt_of_lt_of_le Nat.zero_lt_one (hone.trans (halmost i hi))
  have hQcoe0 : (Q : ℝ≥0∞) ≠ 0 := by exact_mod_cast hQpos.ne'
  have hQcoetop : (Q : ℝ≥0∞) ≠ ∞ := by simp
  have hloss0 : R * (Q : ℝ≥0∞) ≠ 0 := mul_ne_zero hR0 hQcoe0
  have hlosstop : R * (Q : ℝ≥0∞) ≠ ∞ :=
    ENNReal.mul_ne_top hRtop hQcoetop
  have hoccupiedSub : occupiedParents active parent ⊆ candidates := by
    intro k hk
    obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hk
    rw [← hik]
    exact hparentCandidate i hi
  have hincidence := sum_incidenceBodyMass_le
    fine coarse active candidates Q halmost
  refine ⟨parent, hparentCandidate, hcontained, hloss0, hlosstop, ?_⟩
  calc
    A * (∑ k ∈ occupiedParents active parent,
        volume (coarse.tubes k).carrier) ≤
        A * (∑ k ∈ candidates,
          volume (coarse.tubes k).carrier) := by
      exact mul_le_mul' le_rfl (Finset.sum_le_sum_of_subset hoccupiedSub)
    _ = ∑ k ∈ candidates,
        A * volume (coarse.tubes k).carrier := by
      rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ candidates,
        R * incidenceBodyMass fine coarse active k := by
      exact Finset.sum_le_sum fun k hk ↦ hlots k hk
    _ = R * (∑ k ∈ candidates,
        incidenceBodyMass fine coarse active k) := by
      rw [Finset.mul_sum]
    _ ≤ R * ((Q : ℝ≥0∞) * bodyMassOn fine.bodyFamily active) :=
      mul_le_mul' le_rfl hincidence
    _ = (R * (Q : ℝ≥0∞)) * bodyMassOn fine.bodyFamily active := by
      ac_rfl

/-- The logarithmic-branching version of joint tube factoring.  This uses the
JointTubeFactoring efficient-parent, KT, and Frostman algebra, but replaces
the exact-cardinality bucket by `DyadicBranchingBucket`. -/
theorem exists_jointTubeFactoring_logBranching
    (fine : UniformTubeFamily δ ι) (coarse : UniformTubeFamily ρ κ)
    (active : Finset ι) (candidates : Finset κ) (parent : ι → κ)
    (A L : ℝ≥0∞)
    (hδ : 0 < δ) (hscale : δ ≤ ρ)
    (hactive : active.Nonempty)
    (hactiveRefined : active ⊆ fine.refinement.refined)
    (hcandidatesRefined : candidates ⊆ coarse.refinement.refined)
    (hparentCandidate : ∀ i ∈ active, parent i ∈ candidates)
    (hcontained : ∀ i ∈ active,
      (fine.tubes i).carrier ⊆ (coarse.tubes (parent i)).carrier)
    (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hL0 : L ≠ 0) (hLtop : L ≠ ∞)
    (hfineKT : IsKatzTaoOn A fine.bodyFamily active)
    (hcoverCost :
      A * (∑ k ∈ occupiedParents active parent,
        volume (coarse.tubes k).carrier) ≤
      L * bodyMassOn fine.bodyFamily active) :
    ∃ (b : Fin (Nat.log 2 (Fintype.card ι) + 1))
        (selected : Finset κ) (selectedFine : Finset ι)
        (fine' : UniformTubeFamily δ ι)
        (coarse' : UniformTubeFamily ρ κ),
      ∃ P : CoarseTubePartition fine' coarse',
        selected =
            efficientLogCardBucket fine coarse active parent A L b ∧
        selectedFine = selectedFineIndices active parent selected ∧
        (∀ i, fine'.tubes i = fine.tubes i) ∧
        (∀ k, coarse'.tubes k = coarse.tubes k) ∧
        fine'.refinement.profile = fine.refinement.profile ∧
        coarse'.refinement.profile = coarse.refinement.profile ∧
        P.index = selectedIndexFactorization active parent selected ∧
        P.branching = logBucketBranching b ∧
        P.branchingLoss = 2 ∧
        WithinFactor (2 * (Nat.log 2 (Fintype.card ι) + 1))
          (bodyMassOn fine.bodyFamily active)
          (bodyMassOn fine'.bodyFamily P.fineIndices) ∧
        selectedFine.Nonempty ∧
        selected.Nonempty ∧
        selectedFine ⊆ active ∧
        selected ⊆ candidates ∧
        (∀ k ∈ P.coarseIndices,
          logBucketBranching b ≤ (P.fiber k).card ∧
          (P.fiber k).card < 2 * logBucketBranching b) ∧
        IsKatzTaoOn (2 * L) coarse'.bodyFamily P.coarseIndices ∧
        ∀ k ∈ P.coarseIndices,
          IsFrostmanOn (2 * L) fine'.bodyFamily (P.fiber k)
            (coarse'.bodyFamily k) := by
  classical
  obtain ⟨b, hretainSum⟩ :=
    exists_efficientLogCardBucket_withinFactor
      fine coarse active parent A L hL0 hLtop hcoverCost
  let selected := efficientLogCardBucket fine coarse active parent A L b
  let selectedFine := selectedFineIndices active parent selected
  have hmassPos := bodyMassOn_pos_of_nonempty fine active hδ hactive
  have hselected : selected.Nonempty := by
    by_contra hnot
    have hempty : selected = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    have hretainSelected :
        WithinFactor (2 * (Nat.log 2 (Fintype.card ι) + 1))
          (bodyMassOn fine.bodyFamily active)
          (∑ k ∈ selected, assignedBodyMass fine active parent k) := by
      simpa [selected] using hretainSum
    unfold WithinFactor at hretainSelected
    rw [hempty] at hretainSelected
    simp at hretainSelected
    exact hmassPos.ne' hretainSelected
  have hselectedEff :
      selected ⊆ efficientParents fine coarse active parent A L := by
    intro k hk
    exact (mem_dyadicFiber
      (efficientParents fine coarse active parent A L)
      (fiberLogCardLabel active parent) b k).1 hk |>.1
  have hselectedOcc : selected ⊆ occupiedParents active parent := by
    intro k hk
    exact (Finset.mem_filter.mp (hselectedEff hk)).1
  have hselectedCandidates : selected ⊆ candidates := by
    intro k hk
    obtain ⟨i, hi, hiparent⟩ := Finset.mem_image.mp (hselectedOcc hk)
    simpa [← hiparent] using hparentCandidate i hi
  have hselectedFineSub : selectedFine ⊆ active :=
    Finset.filter_subset _ _
  have hselectedFineNonempty : selectedFine.Nonempty := by
    obtain ⟨k, hk⟩ := hselected
    obtain ⟨i, hi, hiparent⟩ := Finset.mem_image.mp (hselectedOcc hk)
    refine ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩⟩
    rw [hiparent]
    exact hk
  have hselectedFineRefined :
      selectedFine ⊆ fine.refinement.refined :=
    hselectedFineSub.trans hactiveRefined
  have hselectedCoarseRefined :
      selected ⊆ coarse.refinement.refined :=
    hselectedCandidates.trans hcandidatesRefined
  let fine' : UniformTubeFamily δ ι :=
    restrictUniformTubeFamilyNonempty fine selectedFine
      hselectedFineRefined hselectedFineNonempty
  let coarse' : UniformTubeFamily ρ κ :=
    restrictUniformTubeFamilyNonempty coarse selected
      hselectedCoarseRefined hselected
  have hcontainedBodies : ∀ i ∈ active,
      (fine.bodyFamily i : Set Space) ⊆
        (coarse.bodyFamily (parent i) : Set Space) := by
    intro i hi
    simpa [UniformTubeFamily.bodyFamily, Tube.coe_body] using hcontained i hi
  have hparentSurj : ∀ k ∈ selected,
      ∃ i ∈ selectedFine, parent i = k := by
    intro k hk
    obtain ⟨i, hi, hiparent⟩ := Finset.mem_image.mp (hselectedOcc hk)
    refine ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩, hiparent⟩
    rw [hiparent]
    exact hk
  let P : CoarseTubePartition fine' coarse' :=
    { scale_le := hscale
      index := selectedIndexFactorization active parent selected
      fine_eq_refined := rfl
      coarse_eq_refined := rfl
      coarse_nonempty := hselected
      carrier_subset := by
        intro i hi
        have hiActive : i ∈ active := (Finset.mem_filter.mp hi).1
        simpa [fine', coarse', restrictUniformTubeFamilyNonempty,
          selectedIndexFactorization] using hcontained i hiActive
      parent_surjective := by
        intro k hk
        exact hparentSurj k hk
      branching := logBucketBranching b
      branching_pos := by
        unfold logBucketBranching
        positivity
      branchingLoss := 2
      branchingLoss_pos := by norm_num
      branching_le_loss_mul_fiber := by
        intro k hk
        have hbounds := efficientLogCardBucket_fiber_card_bounds
          fine coarse active parent A L b hk
        rw [selected_fiber_eq_raw_fiber active parent selected hk]
        omega
      fiber_card_le_loss_mul_branching := by
        intro k hk
        have hbounds := efficientLogCardBucket_fiber_card_bounds
          fine coarse active parent A L b hk
        rw [selected_fiber_eq_raw_fiber active parent selected hk]
        exact Nat.le_of_lt hbounds.2 }
  have hretainSelected :
      WithinFactor (2 * (Nat.log 2 (Fintype.card ι) + 1))
        (bodyMassOn fine.bodyFamily active)
        (bodyMassOn fine.bodyFamily selectedFine) := by
    simpa [selected, selectedFine,
      selectedFine_bodyMass_eq_sum_assignedBodyMass] using hretainSum
  have hcoarseKT :
      IsKatzTaoOn (2 * L) coarse.bodyFamily selected :=
    selectedEfficientParents_isKatzTaoOn fine coarse active parent A L
      hA0 hAtop hcontainedBodies hfineKT selected hselectedEff
  have hfineBodyFamily : fine'.bodyFamily = fine.bodyFamily := by
    rfl
  have hcoarseBodyFamily : coarse'.bodyFamily = coarse.bodyFamily := by
    rfl
  refine ⟨b, selected, selectedFine, fine', coarse', P,
    rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, ?_,
    hselectedFineNonempty, hselected, hselectedFineSub,
    hselectedCandidates, ?_, ?_, ?_⟩
  · intro i
    rfl
  · intro k
    rfl
  · rw [hfineBodyFamily]
    simpa [P, selectedFine, CoarseTubePartition.fineIndices] using
      hretainSelected
  · intro k hk
    change logBucketBranching b ≤
        ((selectedIndexFactorization active parent selected).fiber k).card ∧
      ((selectedIndexFactorization active parent selected).fiber k).card <
        2 * logBucketBranching b
    rw [selected_fiber_eq_raw_fiber active parent selected hk]
    exact efficientLogCardBucket_fiber_card_bounds
      fine coarse active parent A L b hk
  · rw [hcoarseBodyFamily]
    simpa [P, CoarseTubePartition.coarseIndices] using hcoarseKT
  · intro k hk
    have hkEff : k ∈ efficientParents fine coarse active parent A L :=
      hselectedEff hk
    have hfrost := efficientParent_isFrostmanOn
      fine coarse active parent A L hcontainedBodies hfineKT hkEff
    rw [hfineBodyFamily, hcoarseBodyFamily]
    simpa [P, CoarseTubePartition.fiber,
      CoarseTubePartition.coarseIndices,
      selected_fiber_eq_raw_fiber active parent selected hk] using hfrost

/-- Paper-facing adapter for a WZ-style multiple tube cover.  Coverage is
oriented to a unique parent map; `Q`-almost incidence and `lotsOfUinW` are
double-counted to derive (rather than assume) aggregate loss `R Q`; efficient
pruning and logarithmic branching then produce the full joint conclusion. -/
theorem exists_jointTubeFactoring_of_almostCover_lots
    (fine : UniformTubeFamily δ ι) (coarse : UniformTubeFamily ρ κ)
    (active : Finset ι) (candidates : Finset κ)
    (A R : ℝ≥0∞) (Q : ℕ)
    (hδ : 0 < δ) (hscale : δ ≤ ρ)
    (hactive : active.Nonempty)
    (hactiveRefined : active ⊆ fine.refinement.refined)
    (hcandidatesRefined : candidates ⊆ coarse.refinement.refined)
    (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hR0 : R ≠ 0) (hRtop : R ≠ ∞)
    (hfineKT : IsKatzTaoOn A fine.bodyFamily active)
    (hcover : ∀ i ∈ active,
      (candidateParents fine coarse candidates i).Nonempty)
    (halmost : ∀ i ∈ active,
      (candidateParents fine coarse candidates i).card ≤ Q)
    (hlots : ∀ k ∈ candidates,
      A * volume (coarse.tubes k).carrier ≤
        R * incidenceBodyMass fine coarse active k) :
    ∃ parent : ι → κ,
      (∀ i ∈ active, parent i ∈ candidates) ∧
      (∀ i ∈ active,
        (fine.tubes i).carrier ⊆ (coarse.tubes (parent i)).carrier) ∧
      ∃ (b : Fin (Nat.log 2 (Fintype.card ι) + 1))
          (selected : Finset κ) (selectedFine : Finset ι)
          (fine' : UniformTubeFamily δ ι)
          (coarse' : UniformTubeFamily ρ κ),
        ∃ P : CoarseTubePartition fine' coarse',
          selected = efficientLogCardBucket fine coarse active parent A
              (R * (Q : ℝ≥0∞)) b ∧
          selectedFine = selectedFineIndices active parent selected ∧
          (∀ i, fine'.tubes i = fine.tubes i) ∧
          (∀ k, coarse'.tubes k = coarse.tubes k) ∧
          fine'.refinement.profile = fine.refinement.profile ∧
          coarse'.refinement.profile = coarse.refinement.profile ∧
          P.index = selectedIndexFactorization active parent selected ∧
          P.branching = logBucketBranching b ∧
          P.branchingLoss = 2 ∧
          WithinFactor (2 * (Nat.log 2 (Fintype.card ι) + 1))
            (bodyMassOn fine.bodyFamily active)
            (bodyMassOn fine'.bodyFamily P.fineIndices) ∧
          selectedFine.Nonempty ∧
          selected.Nonempty ∧
          selectedFine ⊆ active ∧
          selected ⊆ candidates ∧
          (∀ k ∈ P.coarseIndices,
            logBucketBranching b ≤ (P.fiber k).card ∧
            (P.fiber k).card < 2 * logBucketBranching b) ∧
          IsKatzTaoOn (2 * (R * (Q : ℝ≥0∞)))
            coarse'.bodyFamily P.coarseIndices ∧
          ∀ k ∈ P.coarseIndices,
            IsFrostmanOn (2 * (R * (Q : ℝ≥0∞)))
              fine'.bodyFamily (P.fiber k) (coarse'.bodyFamily k) := by
  obtain ⟨parent, hparentCandidate, hcontained, hL0, hLtop, hcost⟩ :=
    exists_parent_with_almostCover_lots_coverCost
      fine coarse active candidates A R Q hactive hcover halmost hlots
        hR0 hRtop
  refine ⟨parent, hparentCandidate, hcontained, ?_⟩
  exact exists_jointTubeFactoring_logBranching
    fine coarse active candidates parent A (R * (Q : ℝ≥0∞))
      hδ hscale hactive hactiveRefined hcandidatesRefined
      hparentCandidate hcontained hA0 hAtop hL0 hLtop hfineKT hcost

end

end Submission.Kakeya.ConvexFactoring.AlmostCoverTubeFactoring
