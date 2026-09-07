import Family8Grounding.Family8StickyDensityAwareLogBranchingCoverLossV4
import Submission.Kakeya.ConvexFactoring.DyadicBranchingBucket
import Mathlib.Tactic

/-!
# Shading-aware logarithmic parent selection

The body-mass logarithmic selector need not retain an arbitrary shading.
This successor uses the actual assigned shading mass both in the efficient
cover loss and in the logarithmic weighted pigeonhole.  Its selected parents
are automatically efficient for the existing body-mass definition because
every shading carrier lies in its tube body.  Thus the geometric coarse and
fiber conclusions remain reusable, while source shading mass is genuinely
retained.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyShadingAwareLogBucketSelectionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8StickyDensityAwareLogBranchingCoverLossV4
open Family8StickyJointExactUniformCoverCostV4
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

variable {delta rho : NNReal} {index : Type*}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Multiplicity-counted shading mass on an arbitrary finite fine set. -/
def shadingMassOn (Y : Shading fine.bodyFamily) (s : Finset index) : ENNReal :=
  ∑ i ∈ s, volume (Y.carrier i)

/-- Actual shading mass assigned to one parent fiber. -/
def assignedShadingMass (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily) (k : Fin S.coarseCard) : ENNReal :=
  ∑ i ∈ (rawIndexFactorization S.activeFine S.parent).fiber k,
    volume (Y.carrier i)

theorem shadingMassOn_ne_top
    (Y : Shading fine.bodyFamily) (s : Finset index) :
    shadingMassOn Y s ≠ ∞ := by
  unfold shadingMassOn
  apply ENNReal.sum_ne_top.2
  intro i hi
  exact (shadingPiece_volume_lt_top Y i).ne

theorem assignedShadingMass_ne_top
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (k : Fin S.coarseCard) :
    assignedShadingMass S Y k ≠ ∞ := by
  unfold assignedShadingMass
  apply ENNReal.sum_ne_top.2
  intro i hi
  exact (shadingPiece_volume_lt_top Y i).ne

theorem assignedShadingMass_le_assignedBodyMass
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (k : Fin S.coarseCard) :
    assignedShadingMass S Y k ≤
      assignedBodyMass fine S.activeFine S.parent k := by
  unfold assignedShadingMass assignedBodyMass
  apply Finset.sum_le_sum
  intro i hi
  exact measure_mono (Y.carrier_subset i)

/-- Actual active shading mass is the sum of its assigned parent masses. -/
theorem shadingMassOn_eq_sum_assignedShadingMass
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) :
    shadingMassOn Y S.activeFine =
      ∑ k ∈ occupiedParents S.activeFine S.parent,
        assignedShadingMass S Y k := by
  simpa only [shadingMassOn, assignedShadingMass, rawIndexFactorization,
    occupiedParents] using
    (rawIndexFactorization S.activeFine S.parent).sum_fiberwise
      (fun i => volume (Y.carrier i))

/-- The exact global cover cost per unit of actual active shading mass. -/
def stickyShadingAwareCoverLoss
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) : ENNReal :=
  (A * familyVolume S.activeCoarseFamily) /
    shadingMassOn Y S.activeFine

/-- Parents whose coarse cover cost is paid directly by their assigned
shading mass. -/
def shadingEfficientParents
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A L : ENNReal) : Finset (Fin S.coarseCard) :=
  (occupiedParents S.activeFine S.parent).filter fun k =>
    A * volume (S.coarse.tubes k).carrier ≤
      (2 * L) * assignedShadingMass S Y k

def shadingInefficientParents
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A L : ENNReal) : Finset (Fin S.coarseCard) :=
  (occupiedParents S.activeFine S.parent).filter fun k =>
    ¬ A * volume (S.coarse.tubes k).carrier ≤
      (2 * L) * assignedShadingMass S Y k

theorem shadingEfficient_add_inefficient_mass
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A L : ENNReal) :
    (∑ k ∈ shadingEfficientParents S Y A L,
        assignedShadingMass S Y k) +
      (∑ k ∈ shadingInefficientParents S Y A L,
        assignedShadingMass S Y k) =
      shadingMassOn Y S.activeFine := by
  rw [shadingMassOn_eq_sum_assignedShadingMass S Y]
  simpa [shadingEfficientParents, shadingInefficientParents] using
    (Finset.sum_filter_add_sum_filter_not
      (occupiedParents S.activeFine S.parent)
      (fun k => A * volume (S.coarse.tubes k).carrier ≤
        (2 * L) * assignedShadingMass S Y k)
      (assignedShadingMass S Y))

private theorem activeCoarseFamilyVolume_pos
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    0 < familyVolume S.activeCoarseFamily := by
  obtain ⟨i, hi⟩ := hactive
  have hk : S.parent i ∈ S.activeCoarse := S.parent_mem i hi
  unfold familyVolume
    FamilyStickyAtEveryScaleCoreV1.StickyScaleCover.activeCoarseFamily
  rw [Finset.sum_pos_iff]
  exact ⟨⟨S.parent i, hk⟩, Finset.mem_univ _, by
    simpa only [UniformTubeFamily.bodyFamily, Tube.coe_body] using
      (S.coarse.tubes (S.parent i)).volume_pos hrho⟩

theorem stickyShadingAwareCoverLoss_ne_zero
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    {A : ENNReal} (hA0 : A ≠ 0) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    stickyShadingAwareCoverLoss S Y A ≠ 0 := by
  unfold stickyShadingAwareCoverLoss
  apply ENNReal.div_ne_zero.mpr
  exact ⟨mul_ne_zero hA0
      (activeCoarseFamilyVolume_pos S hrho hactive).ne',
    shadingMassOn_ne_top Y S.activeFine⟩

theorem stickyShadingAwareCoverLoss_ne_top
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    {A : ENNReal} (hAtop : A ≠ ∞)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    stickyShadingAwareCoverLoss S Y A ≠ ∞ := by
  unfold stickyShadingAwareCoverLoss
  apply ENNReal.div_ne_top
  · exact ENNReal.mul_ne_top hAtop
      (familyVolume_ne_top S.activeCoarseFamily)
  · exact hmass

theorem stickyShadingAwareCoverCost
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    A * (∑ k ∈ occupiedParents S.activeFine S.parent,
        volume (S.coarse.tubes k).carrier) ≤
      stickyShadingAwareCoverLoss S Y A *
        shadingMassOn Y S.activeFine := by
  rw [sum_occupiedParentVolume_eq_activeCoarseFamilyVolume]
  unfold stickyShadingAwareCoverLoss
  rw [ENNReal.div_mul_cancel hmass
    (shadingMassOn_ne_top Y S.activeFine)]

/-- The shading-efficient parents retain at least half of the actual active
shading mass. -/
theorem shadingMassOn_le_two_mul_shadingEfficient_mass
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A L : ENNReal) (hL0 : L ≠ 0) (hLtop : L ≠ ∞)
    (hcover : A * (∑ k ∈ occupiedParents S.activeFine S.parent,
        volume (S.coarse.tubes k).carrier) ≤
      L * shadingMassOn Y S.activeFine) :
    shadingMassOn Y S.activeFine ≤
      2 * ∑ k ∈ shadingEfficientParents S Y A L,
        assignedShadingMass S Y k := by
  let badMass : ENNReal :=
    ∑ k ∈ shadingInefficientParents S Y A L,
      assignedShadingMass S Y k
  let goodMass : ENNReal :=
    ∑ k ∈ shadingEfficientParents S Y A L,
      assignedShadingMass S Y k
  have hbadPiece : ∀ k ∈ shadingInefficientParents S Y A L,
      (2 * L) * assignedShadingMass S Y k ≤
        A * volume (S.coarse.tubes k).carrier := by
    intro k hk
    exact le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hk).2)
  have hbadCross : (2 * L) * badMass ≤
      A * (∑ k ∈ shadingInefficientParents S Y A L,
        volume (S.coarse.tubes k).carrier) := by
    simp only [badMass, Finset.mul_sum]
    exact Finset.sum_le_sum fun k hk => hbadPiece k hk
  have hbadVolume :
      (∑ k ∈ shadingInefficientParents S Y A L,
        volume (S.coarse.tubes k).carrier) ≤
      ∑ k ∈ occupiedParents S.activeFine S.parent,
        volume (S.coarse.tubes k).carrier := by
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hbeforeCancel : (2 * badMass) * L ≤
      shadingMassOn Y S.activeFine * L := by
    calc
      (2 * badMass) * L = (2 * L) * badMass := by ac_rfl
      _ ≤ A * (∑ k ∈ shadingInefficientParents S Y A L,
          volume (S.coarse.tubes k).carrier) := hbadCross
      _ ≤ A * (∑ k ∈ occupiedParents S.activeFine S.parent,
          volume (S.coarse.tubes k).carrier) := mul_le_mul' le_rfl hbadVolume
      _ ≤ L * shadingMassOn Y S.activeFine := hcover
      _ = shadingMassOn Y S.activeFine * L := mul_comm _ _
  have htwiceBad : 2 * badMass ≤ shadingMassOn Y S.activeFine :=
    (ENNReal.mul_le_mul_iff_left hL0 hLtop).mp hbeforeCancel
  have hbadTop : badMass ≠ ∞ := by
    apply ENNReal.sum_ne_top.2
    intro k hk
    exact assignedShadingMass_ne_top S Y k
  have hbadLeGood : badMass ≤ goodMass := by
    apply (ENNReal.add_le_add_iff_right hbadTop).mp
    calc
      badMass + badMass = 2 * badMass := by simp [two_mul]
      _ ≤ shadingMassOn Y S.activeFine := htwiceBad
      _ = goodMass + badMass := by
        simpa only [goodMass, badMass] using
          (shadingEfficient_add_inefficient_mass S Y A L).symm
  calc
    shadingMassOn Y S.activeFine = goodMass + badMass := by
      simpa only [goodMass, badMass] using
        (shadingEfficient_add_inefficient_mass S Y A L).symm
    _ ≤ goodMass + goodMass := add_le_add_right hbadLeGood _
    _ = 2 * goodMass := by simp [two_mul]
    _ = 2 * ∑ k ∈ shadingEfficientParents S Y A L,
        assignedShadingMass S Y k := rfl

/-- Shading efficiency is stronger than the existing body efficiency. -/
theorem shadingEfficientParents_subset_efficientParents
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A L : ENNReal) :
    shadingEfficientParents S Y A L ⊆
      efficientParents fine S.coarse S.activeFine S.parent A L := by
  intro k hk
  have hk' := Finset.mem_filter.mp hk
  apply Finset.mem_filter.mpr
  refine ⟨hk'.1, hk'.2.trans ?_⟩
  exact mul_le_mul' le_rfl
    (assignedShadingMass_le_assignedBodyMass S Y k)

/-- One fiber-cardinality logarithmic bucket of shading-efficient parents. -/
def shadingEfficientLogCardBucket
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A L : ENNReal)
    (b : Fin (Nat.log 2 (Fintype.card index) + 1)) :
    Finset (Fin S.coarseCard) :=
  dyadicFiber (shadingEfficientParents S Y A L)
    (fiberLogCardLabel S.activeFine S.parent) b

theorem exists_shadingEfficientLogCardBucket_withinFactor
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A L : ENNReal) (hL0 : L ≠ 0) (hLtop : L ≠ ∞)
    (hcover : A * (∑ k ∈ occupiedParents S.activeFine S.parent,
        volume (S.coarse.tubes k).carrier) ≤
      L * shadingMassOn Y S.activeFine) :
    ∃ b : Fin (Nat.log 2 (Fintype.card index) + 1),
      WithinFactor (2 * (Nat.log 2 (Fintype.card index) + 1))
        (shadingMassOn Y S.activeFine)
        (∑ k ∈ shadingEfficientLogCardBucket S Y A L b,
          assignedShadingMass S Y k) := by
  have hgood : WithinFactor 2 (shadingMassOn Y S.activeFine)
      (∑ k ∈ shadingEfficientParents S Y A L,
        assignedShadingMass S Y k) := by
    unfold WithinFactor
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using
      shadingMassOn_le_two_mul_shadingEfficient_mass
        S Y A L hL0 hLtop hcover
  obtain ⟨b, hb⟩ := exists_parentLabel_weightedBucket
    (shadingEfficientParents S Y A L)
    (fiberLogCardLabel S.activeFine S.parent)
    (assignedShadingMass S Y)
  refine ⟨b, ?_⟩
  have hbucket : WithinFactor
      (Fintype.card (Fin (Nat.log 2 (Fintype.card index) + 1)))
      (∑ k ∈ shadingEfficientParents S Y A L,
        assignedShadingMass S Y k)
      (∑ k ∈ shadingEfficientLogCardBucket S Y A L b,
        assignedShadingMass S Y k) := hb
  simpa [shadingEfficientLogCardBucket] using hgood.trans hbucket

/-- The selected fine shading mass is exactly the selected parent sum. -/
theorem selectedFine_shadingMass_eq_sum_assignedShadingMass
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (selected : Finset (Fin S.coarseCard)) :
    shadingMassOn Y
        (selectedFineIndices S.activeFine S.parent selected) =
      ∑ k ∈ selected, assignedShadingMass S Y k := by
  change (∑ i ∈ selectedFineIndices S.activeFine S.parent selected,
      volume (Y.carrier i)) = _
  calc
    (∑ i ∈ selectedFineIndices S.activeFine S.parent selected,
        volume (Y.carrier i)) =
        ∑ k ∈ selected, ∑ i ∈
          (selectedIndexFactorization
            S.activeFine S.parent selected).fiber k,
            volume (Y.carrier i) := by
      simpa only [selectedIndexFactorization_fine,
        selectedIndexFactorization_coarse] using
        (selectedIndexFactorization
          S.activeFine S.parent selected).sum_fiberwise
            (fun i => volume (Y.carrier i))
    _ = ∑ k ∈ selected, assignedShadingMass S Y k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [selected_fiber_eq_raw_fiber S.activeFine S.parent selected hk]
      rfl

theorem shadingEfficientLogCardBucket_subset_efficientLogCardBucket
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A L : ENNReal)
    (b : Fin (Nat.log 2 (Fintype.card index) + 1)) :
    shadingEfficientLogCardBucket S Y A L b ⊆
      efficientLogCardBucket fine S.coarse S.activeFine S.parent A L b := by
  intro k hk
  have hk' := (mem_dyadicFiber
    (shadingEfficientParents S Y A L)
    (fiberLogCardLabel S.activeFine S.parent) b k).1 hk
  apply (mem_dyadicFiber
    (efficientParents fine S.coarse S.activeFine S.parent A L)
    (fiberLogCardLabel S.activeFine S.parent) b k).2
  exact ⟨shadingEfficientParents_subset_efficientParents S Y A L hk'.1,
    hk'.2⟩

/-- Complete honest selector certificate, with an explicit zero-mass branch.
The positive branch simultaneously retains actual shading mass and every
body-efficient/balanced-branching field used by the existing partition. -/
theorem shadingAwareLogBucket_zero_or_exists_certificate
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty) :
    shadingMassOn Y S.activeFine = 0 ∨
      ∃ b : Fin (Nat.log 2 (Fintype.card index) + 1),
        let L := stickyShadingAwareCoverLoss S Y A
        let selected := shadingEfficientLogCardBucket S Y A L b
        let selectedFine :=
          selectedFineIndices S.activeFine S.parent selected
        WithinFactor (2 * (Nat.log 2 (Fintype.card index) + 1))
            (shadingMassOn Y S.activeFine)
            (shadingMassOn Y selectedFine) ∧
          shadingMassOn Y S.activeFine /
              (2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) ≤
            shadingMassOn Y selectedFine ∧
          selected.Nonempty ∧ selectedFine.Nonempty ∧
          selected ⊆ S.activeCoarse ∧
          selectedFine ⊆ S.activeFine ∧
          selected ⊆
            efficientParents fine S.coarse S.activeFine S.parent A L ∧
          (∀ k ∈ selected,
            logBucketBranching b ≤
                ((rawIndexFactorization S.activeFine S.parent).fiber k).card ∧
              ((rawIndexFactorization S.activeFine S.parent).fiber k).card <
                2 * logBucketBranching b) := by
  by_cases hmass : shadingMassOn Y S.activeFine = 0
  · exact Or.inl hmass
  · right
    let L := stickyShadingAwareCoverLoss S Y A
    have hL0 : L ≠ 0 :=
      stickyShadingAwareCoverLoss_ne_zero S Y hA0 hrho hactive
    have hLtop : L ≠ ∞ :=
      stickyShadingAwareCoverLoss_ne_top S Y hAtop hmass
    have hcover := stickyShadingAwareCoverCost S Y A hmass
    obtain ⟨b, hretainParents⟩ :=
      exists_shadingEfficientLogCardBucket_withinFactor
        S Y A L hL0 hLtop (by simpa only [L] using hcover)
    let selected := shadingEfficientLogCardBucket S Y A L b
    let selectedFine :=
      selectedFineIndices S.activeFine S.parent selected
    have hmassEq : shadingMassOn Y selectedFine =
        ∑ k ∈ selected, assignedShadingMass S Y k := by
      simpa only [selectedFine] using
        selectedFine_shadingMass_eq_sum_assignedShadingMass S Y selected
    have hretain : WithinFactor
        (2 * (Nat.log 2 (Fintype.card index) + 1))
        (shadingMassOn Y S.activeFine) (shadingMassOn Y selectedFine) := by
      rw [hmassEq]
      simpa only [selected] using hretainParents
    have hselectedMass : shadingMassOn Y selectedFine ≠ 0 := by
      intro hzero
      unfold WithinFactor at hretain
      rw [hzero] at hretain
      simp at hretain
      exact hmass hretain
    have hselected : selected.Nonempty := by
      by_contra hnot
      have hempty : selected = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
      apply hselectedMass
      rw [hmassEq, hempty]
      simp
    have hselectedFine : selectedFine.Nonempty := by
      by_contra hnot
      have hempty : selectedFine = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hnot
      apply hselectedMass
      rw [hempty]
      simp [shadingMassOn]
    have hsourceFloor : shadingMassOn Y S.activeFine /
          (2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) ≤
        shadingMassOn Y selectedFine := by
      apply (ENNReal.div_le_iff_le_mul (Or.inl (by norm_num))
        (Or.inl (by finiteness))).2
      unfold WithinFactor at hretain
      simpa only [nsmul_eq_mul, ENNReal.coe_natCast, mul_comm] using hretain
    refine ⟨b, ?_⟩
    dsimp only
    refine ⟨hretain, hsourceFloor, hselected, hselectedFine, ?_, ?_, ?_, ?_⟩
    · intro k hk
      have hkOcc : k ∈ occupiedParents S.activeFine S.parent :=
        (Finset.mem_filter.mp
          ((mem_dyadicFiber
            (shadingEfficientParents S Y A L)
            (fiberLogCardLabel S.activeFine S.parent) b k).1 hk |>.1)).1
      obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hkOcc
      simpa [← hik] using S.parent_mem i hi
    · exact Finset.filter_subset _ _
    · intro k hk
      exact shadingEfficientLogCardBucket_subset_efficientLogCardBucket
        S Y A L b hk |>
          (mem_dyadicFiber
            (efficientParents fine S.coarse S.activeFine S.parent A L)
            (fiberLogCardLabel S.activeFine S.parent) b k).1 |>.1
    · intro k hk
      exact efficientLogCardBucket_fiber_card_bounds
        fine S.coarse S.activeFine S.parent A L b
          (shadingEfficientLogCardBucket_subset_efficientLogCardBucket
            S Y A L b hk)

#print axioms shadingMassOn_eq_sum_assignedShadingMass
#print axioms stickyShadingAwareCoverCost
#print axioms shadingMassOn_le_two_mul_shadingEfficient_mass
#print axioms exists_shadingEfficientLogCardBucket_withinFactor
#print axioms shadingAwareLogBucket_zero_or_exists_certificate

end
end Family8StickyShadingAwareLogBucketSelectionV1
