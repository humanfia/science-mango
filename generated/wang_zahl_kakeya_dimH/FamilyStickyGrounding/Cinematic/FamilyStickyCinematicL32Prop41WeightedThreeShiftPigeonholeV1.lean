import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ThreeShiftPigeonholeV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1

open FamilyStickyCinematicL32Prop41ThreeShiftPigeonholeV1

noncomputable section

universe u

/-!
# Weighted three-shift pigeonhole

This is the mass-preserving analogue of `exists_uniform_threeShift_fiber`.
The pointwise valid label is chosen first, exactly as in the cardinal theorem.
Among the occupied labels we then maximize an arbitrary `ENNReal` weight.
Restricting the maximization to occupied labels keeps the returned fibre
nonempty even when every weight is zero.
-/

/-- The total weight of a finite carrier. -/
def finiteENNRealWeight
    {alpha : Type u} [DecidableEq alpha]
    (items : Finset alpha) (weight : alpha -> ENNReal) : ENNReal :=
  ∑ a ∈ items, weight a

/-- The total weight in one fibre of a three-shift labelling. -/
def threeShiftFiberWeight
    {alpha : Type u} [DecidableEq alpha]
    (items : Finset alpha) (label : alpha -> Fin 3)
    (weight : alpha -> ENNReal) (k : Fin 3) : ENNReal :=
  ∑ a ∈ threeShiftFiber items label k, weight a

/-- The three fibres give a lossless partition of the input weight. -/
theorem finiteENNRealWeight_eq_sum_threeShiftFiberWeight
    {alpha : Type u} [DecidableEq alpha]
    (items : Finset alpha) (label : alpha -> Fin 3)
    (weight : alpha -> ENNReal) :
    finiteENNRealWeight items weight =
      ∑ k : Fin 3, threeShiftFiberWeight items label weight k := by
  rw [finiteENNRealWeight]
  symm
  simpa only [threeShiftFiberWeight, threeShiftFiber] using
    (Finset.sum_fiberwise items label weight)

/-- One pointwise-valid label retains at least one third of an arbitrary
nonnegative extended-real weight.  The selected fibre is nonempty whenever
the input carrier is nonempty, including in the zero-total-mass case. -/
theorem exists_uniform_threeShift_weighted_fiber
    {alpha : Type u} [DecidableEq alpha]
    (items : Finset alpha) (good : alpha -> Fin 3 -> Prop)
    (weight : alpha -> ENNReal)
    (hitems : items.Nonempty)
    (hgood : forall i, i ∈ items -> ∃ k : Fin 3, good i k) :
    ∃ k : Fin 3,
      let fiber := threeShiftFiber items
        (chosenThreeShiftLabel items good hgood) k
      fiber.Nonempty ∧ fiber ⊆ items ∧
        finiteENNRealWeight items weight ≤
          3 * finiteENNRealWeight fiber weight ∧
        forall i, i ∈ fiber -> good i k := by
  let label := chosenThreeShiftLabel items good hgood
  let occupied : Finset (Fin 3) := items.image label
  let fiberWeight : Fin 3 -> ENNReal := fun k =>
    threeShiftFiberWeight items label weight k
  have hoccupied : occupied.Nonempty := by
    obtain ⟨i, hi⟩ := hitems
    exact ⟨label i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
  obtain ⟨k, hkOccupied, hmax⟩ :=
    Finset.exists_max_image occupied fiberWeight hoccupied
  have hfiberNonempty : (threeShiftFiber items label k).Nonempty := by
    obtain ⟨i, hiItems, hiLabel⟩ := Finset.mem_image.mp hkOccupied
    refine ⟨i, ?_⟩
    exact (mem_threeShiftFiber_iff items label k i).mpr
      ⟨hiItems, hiLabel⟩
  have hfiberSubset : threeShiftFiber items label k ⊆ items := by
    intro i hi
    exact (mem_threeShiftFiber_iff items label k i).mp hi |>.1
  have hlabelMax : forall j : Fin 3, fiberWeight j ≤ fiberWeight k := by
    intro j
    by_cases hj : j ∈ occupied
    · exact hmax j hj
    · have hfiberEmpty : threeShiftFiber items label j = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨i, hi⟩
        have hiData := (mem_threeShiftFiber_iff items label j i).mp hi
        exact hj (Finset.mem_image.mpr ⟨i, hiData.1, hiData.2⟩)
      simp only [fiberWeight, threeShiftFiberWeight, hfiberEmpty,
        Finset.sum_empty]
      exact bot_le
  have hweight : finiteENNRealWeight items weight ≤
      3 * threeShiftFiberWeight items label weight k := by
    rw [finiteENNRealWeight_eq_sum_threeShiftFiberWeight]
    calc
      (∑ j : Fin 3, threeShiftFiberWeight items label weight j) ≤
          ∑ _j : Fin 3, threeShiftFiberWeight items label weight k := by
        exact Finset.sum_le_sum fun j _hj => hlabelMax j
      _ = 3 * threeShiftFiberWeight items label weight k := by
        norm_num [Fin.sum_univ_succ]
  refine ⟨k, ?_, ?_, ?_, ?_⟩
  · simpa only [label] using hfiberNonempty
  · simpa only [label] using hfiberSubset
  · simpa only [finiteENNRealWeight, threeShiftFiberWeight, label] using hweight
  · intro i hi
    have hi' : i ∈ threeShiftFiber items label k := by
      simpa only [label] using hi
    have hiData := (mem_threeShiftFiber_iff items label k i).mp hi'
    have hchosen := chosenThreeShiftLabel_good items good hgood hiData.1
    simpa only [label, hiData.2] using hchosen

#print axioms finiteENNRealWeight_eq_sum_threeShiftFiberWeight
#print axioms exists_uniform_threeShift_weighted_fiber

end

end FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1
