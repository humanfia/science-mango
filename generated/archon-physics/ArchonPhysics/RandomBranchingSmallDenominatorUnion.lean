import ArchonPhysics.FiniteHistorySmallDenominatorUnionBound
import ArchonPhysics.FreeFPUTBranchingNonresonantOrderBound

/-!
# A fixed finite index for random branching-history denominators

For a frozen random mass sample, the values in a branching Duhamel
denominator list vary with the sample, but the list always has a deterministic
factorial/exponential capacity.  This file pads the list by a safe default and
thereby indexes every possible denominator by one fixed finite type.

Combining this construction with the finite-union theorem gives the explicit
all-order estimate

`P(irregular tree) <= tree.order! * (2 ^ tree.order - 1) * oneGapBudget`.

The only probabilistic input left visible is the scalar bound for each padded
coordinate.  No independence, RPA, Markov property, or positive-time
re-randomization is assumed.
-/

namespace ArchonPhysics.RandomBranchingSmallDenominatorUnion

open MeasureTheory
open ArchonPhysics
open ArchonPhysics.FiniteHistorySmallDenominatorUnionBound
open ArchonPhysics.FreeFPUTBranchingHistoryDenominatorEnumeration
open ArchonPhysics.FreeFPUTBranchingNonresonantOrderBound
open ArchonPhysics.FreeFPUTBranchingOscillatoryShuffle
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A list of sample-dependent scalar denominators, padded to a deterministic
capacity. -/
def paddedRandomListCoordinate
    (values : Omega → List Real) (capacity : Nat) (defaultValue : Real)
    (i : Fin capacity) (omega : Omega) : Real :=
  (values omega).getD i.val defaultValue

omit [MeasurableSpace Omega] in
/-- If the padding value lies outside the open small-gap interval, a short
list has a small entry exactly when one of its padded finite coordinates is
small. -/
theorem exists_mem_small_iff_exists_paddedRandomListCoordinate_small
    (values : Omega → List Real) (capacity : Nat) (defaultValue gamma : Real)
    (hcapacity : ∀ omega, (values omega).length ≤ capacity)
    (hdefault : gamma ≤ |defaultValue|) (omega : Omega) :
    (∃ delta ∈ values omega, |delta| < gamma) ↔
      ∃ i : Fin capacity,
        |paddedRandomListCoordinate values capacity defaultValue i omega| <
          gamma := by
  constructor
  · rintro ⟨delta, hmem, hsmall⟩
    rw [List.mem_iff_getElem] at hmem
    rcases hmem with ⟨index, hindex, rfl⟩
    let i : Fin capacity :=
      ⟨index, lt_of_lt_of_le hindex (hcapacity omega)⟩
    refine ⟨i, ?_⟩
    change |(values omega).getD index defaultValue| < gamma
    rw [List.getD_eq_getElem (values omega) defaultValue hindex]
    exact hsmall
  · rintro ⟨i, hsmall⟩
    have hindex : i.val < (values omega).length := by
      by_contra hnot
      have hle : (values omega).length ≤ i.val := Nat.le_of_not_gt hnot
      have hdefaultEq :
          paddedRandomListCoordinate values capacity defaultValue i omega =
            defaultValue := by
        exact List.getD_eq_default (values omega) defaultValue hle
      rw [hdefaultEq] at hsmall
      exact (not_lt_of_ge hdefault) hsmall
    refine ⟨paddedRandomListCoordinate values capacity defaultValue i omega,
      ?_, hsmall⟩
    have hget :
        paddedRandomListCoordinate values capacity defaultValue i omega =
          (values omega)[i.val] := by
      exact List.getD_eq_getElem (values omega) defaultValue hindex
    rw [hget]
    exact List.getElem_mem _

/-- A uniform small-ball estimate for the fixed padded coordinates controls
the event that a random list has any small entry. -/
theorem measure_exists_mem_small_le_capacity_mul
    (mu : Measure Omega) (values : Omega → List Real)
    (capacity : Nat) (defaultValue gamma : Real)
    (hcapacity : ∀ omega, (values omega).length ≤ capacity)
    (hdefault : gamma ≤ |defaultValue|) (budget : ENNReal)
    (hone : ∀ i : Fin capacity,
      mu {omega |
        |paddedRandomListCoordinate values capacity defaultValue i omega| <
          gamma} ≤ budget) :
    mu {omega | ∃ delta ∈ values omega, |delta| < gamma} ≤
      (capacity : ENNReal) * budget := by
  have hevent :
      {omega | ∃ delta ∈ values omega, |delta| < gamma} =
        finiteSmallDenominatorEvent
          (paddedRandomListCoordinate values capacity defaultValue) gamma := by
    ext omega
    change (∃ delta ∈ values omega, |delta| < gamma) ↔ _
    rw [mem_finiteSmallDenominatorEvent_iff]
    exact exists_mem_small_iff_exists_paddedRandomListCoordinate_small
      values capacity defaultValue gamma hcapacity hdefault omega
  rw [hevent]
  simpa using
    (measure_finiteSmallDenominatorEvent_le_card_mul
      mu (paddedRandomListCoordinate values capacity defaultValue)
        gamma budget hone)

/-- Deterministic capacity for every complete denominator list of a branching
tree of the supplied shape. -/
def branchingDenominatorCapacity (tree : BinaryInteractionTree) : Nat :=
  tree.order.factorial * (2 ^ tree.order - 1)

theorem length_branchingHistoryDenominators_le_capacity
    (tree : BinaryInteractionTree)
    (assignment : BinaryInteractionTreePhaseAssignment tree) :
    (branchingHistoryDenominators tree assignment).length ≤
      branchingDenominatorCapacity tree := by
  rw [length_branchingHistoryDenominators]
  unfold branchingDenominatorCapacity
  exact Nat.mul_le_mul_right _
    (length_branchingPhaseLinearExtensions_le_factorial tree assignment)

/-- The precise finite coordinate random variable whose one-gap small-ball
law is needed for an all-order random branching history. -/
def randomBranchingDenominatorCoordinate
    (tree : BinaryInteractionTree)
    (assignment : Omega → BinaryInteractionTreePhaseAssignment tree)
    (defaultValue : Real)
    (i : Fin (branchingDenominatorCapacity tree)) (omega : Omega) : Real :=
  paddedRandomListCoordinate
    (fun sample => branchingHistoryDenominators tree (assignment sample))
    (branchingDenominatorCapacity tree) defaultValue i omega

/-- Exact handoff from scalar one-gap estimates to an all-order branching
irregularity probability. -/
theorem measure_not_fullyNonresonantBranchingHistory_le_capacity_mul
    (mu : Measure Omega) (tree : BinaryInteractionTree)
    (assignment : Omega → BinaryInteractionTreePhaseAssignment tree)
    (defaultValue gamma : Real) (hdefault : gamma ≤ |defaultValue|)
    (budget : ENNReal)
    (hone : ∀ i : Fin (branchingDenominatorCapacity tree),
      mu {omega |
        |randomBranchingDenominatorCoordinate
          tree assignment defaultValue i omega| < gamma} ≤ budget) :
    mu {omega |
      ¬ FullyNonresonantBranchingHistory gamma tree (assignment omega)} ≤
      (branchingDenominatorCapacity tree : ENNReal) * budget := by
  have hevent :
      {omega |
        ¬ FullyNonresonantBranchingHistory gamma tree (assignment omega)} =
      {omega | ∃ delta ∈
        branchingHistoryDenominators tree (assignment omega),
          |delta| < gamma} := by
    ext omega
    exact
      not_fullyNonresonantBranchingHistory_iff_exists_small_denominator
        gamma tree (assignment omega)
  rw [hevent]
  exact measure_exists_mem_small_le_capacity_mul
    mu (fun omega => branchingHistoryDenominators tree (assignment omega))
      (branchingDenominatorCapacity tree) defaultValue gamma
      (fun omega =>
        length_branchingHistoryDenominators_le_capacity tree (assignment omega))
      hdefault budget hone

end

end ArchonPhysics.RandomBranchingSmallDenominatorUnion
