import Submission.Kakeya.ConvexFactoring.CoarseTubePartition
import Submission.Kakeya.ConvexFactoring.ActiveNonConcentration
import Submission.Kakeya.ConvexFactoring.HeavyParentSelection

open Set
open scoped ENNReal NNReal
open MeasureTheory

/-!
# Joint tube factoring from an efficient tube cover

Given actual uniform fine and coarse tube families, a parent assignment with
carrier containment, a fine Katz--Tao bound, and one global efficient-cover
cost inequality, this module constructs a positive-mass selected coarse
partition.  Balanced branching, Katz--Tao non-concentration above, and
fiberwise Frostman non-concentration below are derived conclusions.

The raw Wang--Zahl efficient tube cover is intentionally not constructed here;
its tube-specific geometric existence is the upstream input isolated by this
module.
-/

namespace Submission.Kakeya.ConvexFactoring.JointTubeFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]
variable {δ ρ : ℝ≥0}

/-- Multiplicity-counted body mass on a finite active set. -/
def bodyMassOn (F : ConvexFamily ι) (s : Finset ι) : ℝ≥0∞ :=
  ∑ i ∈ s, volume (F i : Set Space)

/-- The coarse labels actually occupied by a parent assignment. -/
def occupiedParents (active : Finset ι) (parent : ι → κ) : Finset κ :=
  active.image parent

/-- The raw parent assignment, restricted to its occupied image, is already
an exact finite index factorization. -/
def rawIndexFactorization (active : Finset ι) (parent : ι → κ) :
    IndexFactorization ι κ where
  fine := active
  coarse := occupiedParents active parent
  parent := parent
  parent_mem := by
    intro i hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

/-- Body mass of the fine fiber assigned to `k`. -/
def assignedBodyMass (fine : UniformTubeFamily δ ι)
    (active : Finset ι) (parent : ι → κ) (k : κ) : ℝ≥0∞ :=
  ∑ i ∈ (rawIndexFactorization active parent).fiber k,
    volume (fine.tubes i).carrier

/-- Parents whose individual cover cost is controlled by twice the global
cover loss. -/
def efficientParents (fine : UniformTubeFamily δ ι)
    (coarse : UniformTubeFamily ρ κ) (active : Finset ι)
    (parent : ι → κ) (A L : ℝ≥0∞) : Finset κ :=
  (occupiedParents active parent).filter fun k =>
    A * volume (coarse.tubes k).carrier ≤
      (2 * L) * assignedBodyMass fine active parent k

/-- The complementary inefficient occupied parents. -/
def inefficientParents (fine : UniformTubeFamily δ ι)
    (coarse : UniformTubeFamily ρ κ) (active : Finset ι)
    (parent : ι → κ) (A L : ℝ≥0∞) : Finset κ :=
  (occupiedParents active parent).filter fun k =>
    ¬ A * volume (coarse.tubes k).carrier ≤
      (2 * L) * assignedBodyMass fine active parent k

/-- Fine indices whose parent belongs to a selected coarse set. -/
def selectedFineIndices (active : Finset ι) (parent : ι → κ)
    (selected : Finset κ) : Finset ι :=
  active.filter fun i => parent i ∈ selected

/-- The selected parent assignment remains an exact index factorization. -/
def selectedIndexFactorization (active : Finset ι) (parent : ι → κ)
    (selected : Finset κ) : IndexFactorization ι κ where
  fine := selectedFineIndices active parent selected
  coarse := selected
  parent := parent
  parent_mem := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2

omit [Fintype ι] [Fintype κ] in
@[simp] theorem selectedIndexFactorization_fine
    (active : Finset ι) (parent : ι → κ) (selected : Finset κ) :
    (selectedIndexFactorization active parent selected).fine =
      selectedFineIndices active parent selected := rfl

omit [Fintype ι] [Fintype κ] in
@[simp] theorem selectedIndexFactorization_coarse
    (active : Finset ι) (parent : ι → κ) (selected : Finset κ) :
    (selectedIndexFactorization active parent selected).coarse = selected := rfl

omit [Fintype ι] [Fintype κ] in
/-- On a selected parent, selection does not alter its original fiber. -/
theorem selected_fiber_eq_raw_fiber
    (active : Finset ι) (parent : ι → κ) (selected : Finset κ)
    {k : κ} (hk : k ∈ selected) :
    (selectedIndexFactorization active parent selected).fiber k =
      (rawIndexFactorization active parent).fiber k := by
  ext i
  simp only [IndexFactorization.mem_fiber]
  constructor
  · rintro ⟨hi, hiparent⟩
    exact ⟨(Finset.mem_filter.mp hi).1, hiparent⟩
  · rintro ⟨hi, hiparent⟩
    refine ⟨Finset.mem_filter.mpr ⟨hi, ?_⟩, hiparent⟩
    change parent i = k at hiparent
    rw [hiparent]
    exact hk

/-- Restrict a uniform refinement to a nonempty subset of its selected set,
preserving the original multiscale profile and all its uniform labels.  The
fallback cardinality loss is the size of the original profile family. -/
def restrictUniformRefinementNonempty (R : UniformRefinement ι)
    (s : Finset ι) (hsub : s ⊆ R.refined) (hs : s.Nonempty) :
    UniformRefinement ι where
  profile := R.profile
  refined := s
  refined_subset := hsub.trans R.refined_subset
  uniform := by
    intro r hr
    obtain ⟨level, hlevel⟩ := R.uniform r hr
    exact ⟨level, fun i hi => hlevel i (hsub hi)⟩
  loss := R.profile.family.card
  card_le_loss_mul := by
    exact Nat.le_mul_of_pos_right _ (Finset.card_pos.mpr hs)

/-- Restrict a uniform tube family without changing any geometric tube. -/
def restrictUniformTubeFamilyNonempty (family : UniformTubeFamily δ ι)
    (s : Finset ι) (hsub : s ⊆ family.refinement.refined)
    (hs : s.Nonempty) : UniformTubeFamily δ ι where
  tubes := family.tubes
  refinement := restrictUniformRefinementNonempty family.refinement s hsub hs

omit [Fintype ι] in
@[simp] theorem restrictUniformTubeFamilyNonempty_tubes
    (family : UniformTubeFamily δ ι) (s : Finset ι)
    (hsub : s ⊆ family.refinement.refined) (hs : s.Nonempty) (i : ι) :
    (restrictUniformTubeFamilyNonempty family s hsub hs).tubes i =
      family.tubes i := rfl

omit [Fintype ι] in
@[simp] theorem restrictUniformTubeFamilyNonempty_refined
    (family : UniformTubeFamily δ ι) (s : Finset ι)
    (hsub : s ⊆ family.refinement.refined) (hs : s.Nonempty) :
    (restrictUniformTubeFamilyNonempty family s hsub hs).refinement.refined = s := rfl

omit [Fintype ι] [DecidableEq ι] in
/-- All finite indexed body masses are finite. -/
theorem bodyMassOn_ne_top (F : ConvexFamily ι) (s : Finset ι) :
    bodyMassOn F s ≠ ∞ := by
  apply ENNReal.sum_ne_top.2
  intro i hi
  exact (F i).isCompact.measure_lt_top.ne

omit [Fintype ι] [Fintype κ] in
/-- Every assigned fine-fiber mass is finite. -/
theorem assignedBodyMass_ne_top (fine : UniformTubeFamily δ ι)
    (active : Finset ι) (parent : ι → κ) (k : κ) :
    assignedBodyMass fine active parent k ≠ ∞ := by
  apply ENNReal.sum_ne_top.2
  intro i hi
  exact (fine.tubes i).volume_lt_top.ne

omit [Fintype ι] [Fintype κ] in
/-- Occupied fiber masses sum exactly to the active fine body mass. -/
theorem bodyMassOn_eq_sum_assignedBodyMass
    (fine : UniformTubeFamily δ ι) (active : Finset ι)
    (parent : ι → κ) :
    bodyMassOn fine.bodyFamily active =
      ∑ k ∈ occupiedParents active parent,
        assignedBodyMass fine active parent k := by
  simpa only [bodyMassOn, assignedBodyMass,
    UniformTubeFamily.bodyFamily_apply, Tube.coe_body,
    rawIndexFactorization, occupiedParents] using
    (rawIndexFactorization active parent).sum_fiberwise
      (fun i => volume (fine.tubes i).carrier)

omit [Fintype ι] [Fintype κ] in
/-- Efficient and inefficient occupied parents partition the fine body mass. -/
theorem efficient_add_inefficient_mass
    (fine : UniformTubeFamily δ ι) (coarse : UniformTubeFamily ρ κ)
    (active : Finset ι) (parent : ι → κ) (A L : ℝ≥0∞) :
    (∑ k ∈ efficientParents fine coarse active parent A L,
        assignedBodyMass fine active parent k) +
      (∑ k ∈ inefficientParents fine coarse active parent A L,
        assignedBodyMass fine active parent k) =
      bodyMassOn fine.bodyFamily active := by
  rw [bodyMassOn_eq_sum_assignedBodyMass
    (fine := fine) (active := active) (parent := parent)]
  simpa [efficientParents, inefficientParents] using
    (Finset.sum_filter_add_sum_filter_not (occupiedParents active parent)
      (fun k => A * volume (coarse.tubes k).carrier ≤
        (2 * L) * assignedBodyMass fine active parent k)
      (assignedBodyMass fine active parent))

omit [Fintype ι] [Fintype κ] in
/-- The global efficient-cover inequality forces the efficient parents to
carry at least half of the active fine body mass. -/
theorem bodyMass_le_two_mul_efficient_mass
    (fine : UniformTubeFamily δ ι) (coarse : UniformTubeFamily ρ κ)
    (active : Finset ι) (parent : ι → κ) (A L : ℝ≥0∞)
    (hL0 : L ≠ 0) (hLtop : L ≠ ∞)
    (hcoverCost :
      A * (∑ k ∈ occupiedParents active parent,
        volume (coarse.tubes k).carrier) ≤
      L * bodyMassOn fine.bodyFamily active) :
    bodyMassOn fine.bodyFamily active ≤
      2 * ∑ k ∈ efficientParents fine coarse active parent A L,
        assignedBodyMass fine active parent k := by
  let badMass : ℝ≥0∞ :=
    ∑ k ∈ inefficientParents fine coarse active parent A L,
      assignedBodyMass fine active parent k
  let goodMass : ℝ≥0∞ :=
    ∑ k ∈ efficientParents fine coarse active parent A L,
      assignedBodyMass fine active parent k
  have hbadPiece : ∀ k ∈ inefficientParents fine coarse active parent A L,
      (2 * L) * assignedBodyMass fine active parent k ≤
        A * volume (coarse.tubes k).carrier := by
    intro k hk
    exact le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hk).2)
  have hbadCross : (2 * L) * badMass ≤
      A * (∑ k ∈ inefficientParents fine coarse active parent A L,
        volume (coarse.tubes k).carrier) := by
    simp only [badMass, Finset.mul_sum]
    exact Finset.sum_le_sum fun k hk => hbadPiece k hk
  have hbadVolume :
      (∑ k ∈ inefficientParents fine coarse active parent A L,
        volume (coarse.tubes k).carrier) ≤
      ∑ k ∈ occupiedParents active parent,
        volume (coarse.tubes k).carrier := by
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hbeforeCancel : (2 * badMass) * L ≤
      bodyMassOn fine.bodyFamily active * L := by
    calc
      (2 * badMass) * L = (2 * L) * badMass := by ac_rfl
      _ ≤ A * (∑ k ∈ inefficientParents fine coarse active parent A L,
          volume (coarse.tubes k).carrier) := hbadCross
      _ ≤ A * (∑ k ∈ occupiedParents active parent,
          volume (coarse.tubes k).carrier) := mul_le_mul' le_rfl hbadVolume
      _ ≤ L * bodyMassOn fine.bodyFamily active := hcoverCost
      _ = bodyMassOn fine.bodyFamily active * L := mul_comm _ _
  have htwiceBad : 2 * badMass ≤ bodyMassOn fine.bodyFamily active :=
    (ENNReal.mul_le_mul_iff_left hL0 hLtop).mp hbeforeCancel
  have hbadNeTop : badMass ≠ ∞ := by
    apply ENNReal.sum_ne_top.2
    intro k hk
    exact assignedBodyMass_ne_top fine active parent k
  have hbadLeGood : badMass ≤ goodMass := by
    apply (ENNReal.add_le_add_iff_right hbadNeTop).mp
    calc
      badMass + badMass = 2 * badMass := by simp [two_mul]
      _ ≤ bodyMassOn fine.bodyFamily active := htwiceBad
      _ = goodMass + badMass := by
        simpa [goodMass, badMass] using
          (efficient_add_inefficient_mass fine coarse active parent A L).symm
  calc
    bodyMassOn fine.bodyFamily active = goodMass + badMass := by
      simpa [goodMass, badMass] using
        (efficient_add_inefficient_mass fine coarse active parent A L).symm
    _ ≤ goodMass + goodMass := add_le_add_right hbadLeGood _
    _ = 2 * goodMass := by simp [two_mul]
    _ = 2 * ∑ k ∈ efficientParents fine coarse active parent A L,
        assignedBodyMass fine active parent k := rfl


/-- The exact fiber-cardinality label.  Its finite range has precisely
`card ι + 1` values. -/
def fiberCardLabel (active : Finset ι) (parent : ι → κ) (k : κ) :
    Fin (Fintype.card ι + 1) :=
  ⟨(rawIndexFactorization active parent).fiber k |>.card, by
    apply Nat.lt_succ_of_le
    exact Finset.card_le_card (Finset.subset_univ _)⟩

/-- Exact-cardinality bucketing of the efficient parents. -/
def efficientCardBucket (fine : UniformTubeFamily δ ι)
    (coarse : UniformTubeFamily ρ κ) (active : Finset ι)
    (parent : ι → κ) (A L : ℝ≥0∞) (b : Fin (Fintype.card ι + 1)) :
    Finset κ :=
  dyadicFiber (efficientParents fine coarse active parent A L)
    (fiberCardLabel active parent) b

omit [Fintype κ] in
/-- Efficient-parent selection followed by exact fiber-cardinality bucketing
retains body mass with loss `2 * (card ι + 1)`. -/
theorem exists_efficientCardBucket_withinFactor
    (fine : UniformTubeFamily δ ι) (coarse : UniformTubeFamily ρ κ)
    (active : Finset ι) (parent : ι → κ) (A L : ℝ≥0∞)
    (hL0 : L ≠ 0) (hLtop : L ≠ ∞)
    (hcoverCost :
      A * (∑ k ∈ occupiedParents active parent,
        volume (coarse.tubes k).carrier) ≤
      L * bodyMassOn fine.bodyFamily active) :
    ∃ b : Fin (Fintype.card ι + 1),
      WithinFactor (2 * (Fintype.card ι + 1))
        (bodyMassOn fine.bodyFamily active)
        (∑ k ∈ efficientCardBucket fine coarse active parent A L b,
          assignedBodyMass fine active parent k) := by
  have hgood : WithinFactor 2 (bodyMassOn fine.bodyFamily active)
      (∑ k ∈ efficientParents fine coarse active parent A L,
        assignedBodyMass fine active parent k) := by
    unfold WithinFactor
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using
      bodyMass_le_two_mul_efficient_mass fine coarse active parent A L
        hL0 hLtop hcoverCost
  obtain ⟨b, hb⟩ := HeavyParentSelection.exists_parentLabel_weightedBucket
    (efficientParents fine coarse active parent A L)
    (fiberCardLabel active parent)
    (assignedBodyMass fine active parent)
  refine ⟨b, ?_⟩
  have hbucket : WithinFactor (Fintype.card (Fin (Fintype.card ι + 1)))
      (∑ k ∈ efficientParents fine coarse active parent A L,
        assignedBodyMass fine active parent k)
      (∑ k ∈ efficientCardBucket fine coarse active parent A L b,
        assignedBodyMass fine active parent k) := hb
  simpa [efficientCardBucket] using hgood.trans hbucket

omit [Fintype ι] [Fintype κ] in
/-- The selected fine body mass is exactly the sum of the original masses of
its selected parent fibers. -/
theorem selectedFine_bodyMass_eq_sum_assignedBodyMass
    (fine : UniformTubeFamily δ ι) (active : Finset ι)
    (parent : ι → κ) (selected : Finset κ) :
    bodyMassOn fine.bodyFamily (selectedFineIndices active parent selected) =
      ∑ k ∈ selected, assignedBodyMass fine active parent k := by
  change (∑ i ∈ selectedFineIndices active parent selected,
      volume (fine.tubes i).carrier) = _
  calc
    (∑ i ∈ selectedFineIndices active parent selected,
        volume (fine.tubes i).carrier) =
        ∑ k ∈ selected, ∑ i ∈
          (selectedIndexFactorization active parent selected).fiber k,
            volume (fine.tubes i).carrier := by
      simpa only [selectedIndexFactorization_fine,
        selectedIndexFactorization_coarse] using
        (selectedIndexFactorization active parent selected).sum_fiberwise
          (fun i => volume (fine.tubes i).carrier)
    _ = ∑ k ∈ selected, assignedBodyMass fine active parent k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [selected_fiber_eq_raw_fiber active parent selected hk]
      rfl

omit [Fintype ι] in
/-- A nonempty active family of positive-radius tubes has positive body mass. -/
theorem bodyMassOn_pos_of_nonempty
    (fine : UniformTubeFamily δ ι) (active : Finset ι)
    (hδ : 0 < δ) (hactive : active.Nonempty) :
    0 < bodyMassOn fine.bodyFamily active := by
  rw [bodyMassOn, Finset.sum_pos_iff]
  obtain ⟨i, hi⟩ := hactive
  exact ⟨i, hi, by
    simpa [UniformTubeFamily.bodyFamily, Tube.coe_body] using
      (fine.tubes i).volume_pos hδ⟩

omit [Fintype κ] in
/-- A positive retained mass makes the selected parent bucket nonempty. -/
theorem efficientCardBucket_nonempty_of_withinFactor
    (fine : UniformTubeFamily δ ι) (coarse : UniformTubeFamily ρ κ)
    (active : Finset ι) (parent : ι → κ) (A L : ℝ≥0∞)
    (b : Fin (Fintype.card ι + 1)) (loss : ℕ)
    (hpos : 0 < bodyMassOn fine.bodyFamily active)
    (hretain : WithinFactor loss (bodyMassOn fine.bodyFamily active)
      (∑ k ∈ efficientCardBucket fine coarse active parent A L b,
        assignedBodyMass fine active parent k)) :
    (efficientCardBucket fine coarse active parent A L b).Nonempty := by
  by_contra hnot
  have hempty : efficientCardBucket fine coarse active parent A L b = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hnot
  unfold WithinFactor at hretain
  rw [hempty] at hretain
  simp at hretain
  exact hpos.ne' hretain

omit [Fintype κ] in
/-- Every parent in an exact-cardinality bucket has the advertised fiber
cardinality. -/
theorem efficientCardBucket_fiber_card
    (fine : UniformTubeFamily δ ι) (coarse : UniformTubeFamily ρ κ)
    (active : Finset ι) (parent : ι → κ) (A L : ℝ≥0∞)
    (b : Fin (Fintype.card ι + 1)) {k : κ}
    (hk : k ∈ efficientCardBucket fine coarse active parent A L b) :
    ((rawIndexFactorization active parent).fiber k).card = b.1 := by
  have hlabel := (mem_dyadicFiber
    (efficientParents fine coarse active parent A L)
    (fiberCardLabel active parent) b k).1 hk |>.2
  exact congrArg Fin.val hlabel

omit [Fintype κ] in
/-- A populated exact-cardinality bucket has strictly positive branching. -/
theorem efficientCardBucket_branching_pos
    (fine : UniformTubeFamily δ ι) (coarse : UniformTubeFamily ρ κ)
    (active : Finset ι) (parent : ι → κ) (A L : ℝ≥0∞)
    (b : Fin (Fintype.card ι + 1))
    (hb : (efficientCardBucket fine coarse active parent A L b).Nonempty) :
    0 < b.1 := by
  obtain ⟨k, hk⟩ := hb
  rw [← efficientCardBucket_fiber_card fine coarse active parent A L b hk,
    Finset.card_pos]
  have hkOcc : k ∈ occupiedParents active parent :=
    (Finset.mem_filter.mp
      ((mem_dyadicFiber
        (efficientParents fine coarse active parent A L)
        (fiberCardLabel active parent) b k).1 hk |>.1)).1
  obtain ⟨i, hi, hiparent⟩ := Finset.mem_image.mp hkOcc
  exact ⟨i, (rawIndexFactorization active parent).mem_fiber i k |>.2
    ⟨hi, hiparent⟩⟩


omit [DecidableEq ι] in
/-- If all active bodies lie in `K`, active contained mass is exactly their
multiplicity-counted body mass. -/
theorem containedMassOn_eq_bodyMassOn_of_contained
    (F : ConvexFamily ι) (s : Finset ι) (K : ConvexBody Space)
    (hcontained : ∀ i ∈ s, (F i : Set Space) ⊆ (K : Set Space)) :
    containedMassOn F s K = bodyMassOn F s := by
  classical
  unfold containedMassOn bodyMassOn
  rw [(@Finset.inter_eq_left ι (Classical.decEq ι) _ _).2]
  intro i hi
  exact (mem_containedIndices F K i).2 (hcontained i hi)

omit [Fintype κ] in
/-- Fine mass assigned to parents whose bodies lie in `K` is bounded by the
original fine active contained mass in `K`. -/
theorem selectedAssignedMass_le_containedMassOn
    (fine : UniformTubeFamily δ ι) (coarse : UniformTubeFamily ρ κ)
    (active : Finset ι) (parent : ι → κ)
    (hcontained : ∀ i ∈ active,
      (fine.bodyFamily i : Set Space) ⊆
        (coarse.bodyFamily (parent i) : Set Space))
    (selected : Finset κ) (K : ConvexBody Space)
    (hinside : ∀ k ∈ selected,
      (coarse.bodyFamily k : Set Space) ⊆ (K : Set Space)) :
    (∑ k ∈ selected, assignedBodyMass fine active parent k) ≤
      containedMassOn fine.bodyFamily active K := by
  classical
  rw [← selectedFine_bodyMass_eq_sum_assignedBodyMass]
  unfold bodyMassOn containedMassOn
  apply Finset.sum_le_sum_of_subset
  intro i hi
  have hiParts := Finset.mem_filter.mp hi
  rw [@Finset.mem_inter ι (Classical.decEq ι)]
  refine ⟨hiParts.1, (mem_containedIndices fine.bodyFamily K i).2 ?_⟩
  exact (hcontained i hiParts.1).trans
    (hinside (parent i) hiParts.2)

/-- The global fine Katz--Tao estimate and the efficient-cover inequalities
imply Katz--Tao above on every selected efficient parent set. -/
theorem selectedEfficientParents_isKatzTaoOn
    (fine : UniformTubeFamily δ ι) (coarse : UniformTubeFamily ρ κ)
    (active : Finset ι) (parent : ι → κ) (A L : ℝ≥0∞)
    (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hcontained : ∀ i ∈ active,
      (fine.bodyFamily i : Set Space) ⊆
        (coarse.bodyFamily (parent i) : Set Space))
    (hfineKT : IsKatzTaoOn A fine.bodyFamily active)
    (selected : Finset κ)
    (hselected : selected ⊆ efficientParents fine coarse active parent A L) :
    IsKatzTaoOn (2 * L) coarse.bodyFamily selected := by
  classical
  intro K
  let inside : Finset κ :=
    indicesInside coarse.bodyFamily selected K
  have hinsideCarrier : ∀ k ∈ inside,
      (coarse.bodyFamily k : Set Space) ⊆ (K : Set Space) := by
    intro k hk
    exact (mem_indicesInside coarse.bodyFamily selected K k).1 hk |>.2
  have hinsideEff : inside ⊆
      efficientParents fine coarse active parent A L := by
    intro k hk
    exact hselected ((mem_indicesInside coarse.bodyFamily selected K k).1 hk |>.1)
  have hassigned :
      (∑ k ∈ inside, assignedBodyMass fine active parent k) ≤
        containedMassOn fine.bodyFamily active K :=
    selectedAssignedMass_le_containedMassOn fine coarse active parent
      hcontained inside K hinsideCarrier
  have hcross :
      A * containedMassOn coarse.bodyFamily selected K ≤
        (2 * L) * containedMassOn fine.bodyFamily active K := by
    rw [← massInside_eq_containedMassOn]
    change A * (∑ k ∈ inside,
      volume (coarse.bodyFamily k : Set Space)) ≤ _
    rw [Finset.mul_sum]
    calc
      (∑ k ∈ inside, A * volume (coarse.bodyFamily k : Set Space)) ≤
          ∑ k ∈ inside, (2 * L) *
            assignedBodyMass fine active parent k := by
        apply Finset.sum_le_sum
        intro k hk
        have hgood := (Finset.mem_filter.mp (hinsideEff hk)).2
        simpa [UniformTubeFamily.bodyFamily, Tube.coe_body] using hgood
      _ = (2 * L) *
          (∑ k ∈ inside, assignedBodyMass fine active parent k) := by
        rw [Finset.mul_sum]
      _ ≤ (2 * L) * containedMassOn fine.bodyFamily active K := by
        exact mul_le_mul' le_rfl hassigned
  apply (ENNReal.mul_le_mul_iff_left hA0 hAtop).mp
  calc
    containedMassOn coarse.bodyFamily selected K * A =
        A * containedMassOn coarse.bodyFamily selected K := mul_comm _ _
    _ ≤ (2 * L) * containedMassOn fine.bodyFamily active K := hcross
    _ ≤ (2 * L) * (A * volume (K : Set Space)) := by
      exact mul_le_mul' le_rfl (hfineKT K)
    _ = ((2 * L) * volume (K : Set Space)) * A := by ac_rfl

omit [Fintype κ] in
/-- Every efficient parent carries a genuine Frostman fine fiber.  This is
derived from the original fine Katz--Tao condition and the parent efficiency
inequality; it is not a certificate supplied by the caller. -/
theorem efficientParent_isFrostmanOn
    (fine : UniformTubeFamily δ ι) (coarse : UniformTubeFamily ρ κ)
    (active : Finset ι) (parent : ι → κ) (A L : ℝ≥0∞)
    (hcontained : ∀ i ∈ active,
      (fine.bodyFamily i : Set Space) ⊆
        (coarse.bodyFamily (parent i) : Set Space))
    (hfineKT : IsKatzTaoOn A fine.bodyFamily active)
    {k : κ} (hk : k ∈ efficientParents fine coarse active parent A L) :
    IsFrostmanOn (2 * L) fine.bodyFamily
      ((rawIndexFactorization active parent).fiber k)
      (coarse.bodyFamily k) := by
  classical
  let fiber := (rawIndexFactorization active parent).fiber k
  have hfiberSub : fiber ⊆ active :=
    (rawIndexFactorization active parent).fiber_subset_fine k
  have hfiberContained : ∀ i ∈ fiber,
      (fine.bodyFamily i : Set Space) ⊆
        (coarse.bodyFamily k : Set Space) := by
    intro i hi
    have hiParts := (rawIndexFactorization active parent).mem_fiber i k |>.1 hi
    have hc := hcontained i hiParts.1
    have hiparent : parent i = k := by
      simpa [rawIndexFactorization] using hiParts.2
    simpa [hiparent] using hc
  have hparentMass :
      containedMassOn fine.bodyFamily fiber (coarse.bodyFamily k) =
        assignedBodyMass fine active parent k := by
    rw [containedMassOn_eq_bodyMassOn_of_contained
      fine.bodyFamily fiber (coarse.bodyFamily k) hfiberContained]
    simp [fiber, bodyMassOn, assignedBodyMass,
      UniformTubeFamily.bodyFamily, Tube.coe_body]
  have hgood : A * volume (coarse.bodyFamily k : Set Space) ≤
      (2 * L) * assignedBodyMass fine active parent k := by
    simpa [UniformTubeFamily.bodyFamily, Tube.coe_body] using
      (Finset.mem_filter.mp hk).2
  refine ⟨hfiberContained, ?_⟩
  intro K hK
  have hlocal : containedMassOn fine.bodyFamily fiber K ≤
      A * volume (K : Set Space) :=
    (containedMassOn_mono hfiberSub K).trans (hfineKT K)
  calc
    containedMassOn fine.bodyFamily fiber K *
        volume (coarse.bodyFamily k : Set Space) ≤
      (A * volume (K : Set Space)) *
        volume (coarse.bodyFamily k : Set Space) := by
        exact mul_le_mul' hlocal le_rfl
    _ = (A * volume (coarse.bodyFamily k : Set Space)) *
        volume (K : Set Space) := by ac_rfl
    _ ≤ ((2 * L) * assignedBodyMass fine active parent k) *
        volume (K : Set Space) := by
        exact mul_le_mul' hgood le_rfl
    _ = (2 * L) * containedMassOn fine.bodyFamily fiber
        (coarse.bodyFamily k) * volume (K : Set Space) := by
        rw [hparentMass]


/-- A single raw WZ-style tube cover with a global efficient-cover cost
produces, observably and simultaneously:

* a positive-mass selected fine family and nonempty selected parent family;
* actual tube containment and an exact parent partition;
* exact two-sided branching (loss one after an exact-cardinality bucket);
* Katz--Tao non-concentration above; and
* Frostman non-concentration below in every selected parent.

The caller supplies only the candidate cover data, original fine Katz--Tao
bound, and the one global cover-cost inequality.  No selected-parent KT,
fiber Frostman, balanced branching, or final factorization is assumed. -/
theorem exists_jointTubeFactoring
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
    ∃ (b : Fin (Fintype.card ι + 1)) (selected : Finset κ)
        (selectedFine : Finset ι)
        (fine' : UniformTubeFamily δ ι)
        (coarse' : UniformTubeFamily ρ κ),
      ∃ P : CoarseTubePartition fine' coarse',
        selected =
            efficientCardBucket fine coarse active parent A L b ∧
        selectedFine = selectedFineIndices active parent selected ∧
        (∀ i, fine'.tubes i = fine.tubes i) ∧
        (∀ k, coarse'.tubes k = coarse.tubes k) ∧
        fine'.refinement.profile = fine.refinement.profile ∧
        coarse'.refinement.profile = coarse.refinement.profile ∧
        P.index = selectedIndexFactorization active parent selected ∧
        P.branching = b.1 ∧
        P.branchingLoss = 1 ∧
        WithinFactor (2 * (Fintype.card ι + 1))
          (bodyMassOn fine.bodyFamily active)
          (bodyMassOn fine'.bodyFamily P.fineIndices) ∧
        selectedFine.Nonempty ∧
        selected.Nonempty ∧
        selectedFine ⊆ active ∧
        selected ⊆ candidates ∧
        (∀ k ∈ P.coarseIndices, (P.fiber k).card = b.1) ∧
        IsKatzTaoOn (2 * L) coarse'.bodyFamily P.coarseIndices ∧
        ∀ k ∈ P.coarseIndices,
          IsFrostmanOn (2 * L) fine'.bodyFamily (P.fiber k)
            (coarse'.bodyFamily k) := by
  classical
  obtain ⟨b, hretainSum⟩ :=
    exists_efficientCardBucket_withinFactor fine coarse active parent A L
      hL0 hLtop hcoverCost
  let selected := efficientCardBucket fine coarse active parent A L b
  let selectedFine := selectedFineIndices active parent selected
  have hmassPos := bodyMassOn_pos_of_nonempty fine active hδ hactive
  have hselected : selected.Nonempty :=
    efficientCardBucket_nonempty_of_withinFactor fine coarse active parent
      A L b (2 * (Fintype.card ι + 1)) hmassPos hretainSum
  have hselectedEff :
      selected ⊆ efficientParents fine coarse active parent A L := by
    intro k hk
    exact (mem_dyadicFiber
      (efficientParents fine coarse active parent A L)
      (fiberCardLabel active parent) b k).1 hk |>.1
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
  have hbranchPos : 0 < b.1 :=
    efficientCardBucket_branching_pos fine coarse active parent A L b hselected
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
          selectedIndexFactorization] using
          hcontained i hiActive
      parent_surjective := by
        intro k hk
        exact hparentSurj k hk
      branching := b.1
      branching_pos := hbranchPos
      branchingLoss := 1
      branchingLoss_pos := by simp
      branching_le_loss_mul_fiber := by
        intro k hk
        have hcard :
            ((selectedIndexFactorization active parent selected).fiber k).card =
              b.1 := by
          rw [selected_fiber_eq_raw_fiber active parent selected hk]
          exact efficientCardBucket_fiber_card
            fine coarse active parent A L b hk
        simp [hcard]
      fiber_card_le_loss_mul_branching := by
        intro k hk
        have hcard :
            ((selectedIndexFactorization active parent selected).fiber k).card =
              b.1 := by
          rw [selected_fiber_eq_raw_fiber active parent selected hk]
          exact efficientCardBucket_fiber_card
            fine coarse active parent A L b hk
        simp [hcard] }
  have hretainSelected : WithinFactor (2 * (Fintype.card ι + 1))
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
    change ((selectedIndexFactorization active parent selected).fiber k).card =
      b.1
    rw [selected_fiber_eq_raw_fiber active parent selected hk]
    exact efficientCardBucket_fiber_card fine coarse active parent A L b hk
  · rw [hcoarseBodyFamily]
    simpa [P, CoarseTubePartition.coarseIndices] using hcoarseKT
  · intro k hk
    have hkEff : k ∈ efficientParents fine coarse active parent A L :=
      hselectedEff hk
    have hfrost := efficientParent_isFrostmanOn fine coarse active parent A L
      hcontainedBodies hfineKT hkEff
    rw [hfineBodyFamily, hcoarseBodyFamily]
    simpa [P, CoarseTubePartition.fiber,
      CoarseTubePartition.coarseIndices,
      selected_fiber_eq_raw_fiber active parent selected hk]
      using hfrost

end

end Submission.Kakeya.ConvexFactoring.JointTubeFactoring
