import ArchonPhysics.PeriodicPolynomialWindowGeometricInterior

/-!
# Exact reduction of a periodic polynomial-kernel row sum to one fixed window

For a common polynomial propagation radius `R`, the cyclic translate of the
odd window `Fin (2 * R + 1)` contains every column which can contribute to a
fixed row.  Columns in the complementary `Fin m` block are proved to vanish
from nearest-neighbour walk geometry.  Reindexing the complete finite sum
therefore gives an exact sum of fixed-window three-leg observables, with all
three legs sharing the same right endpoint.
-/

namespace ArchonPhysics.PeriodicPolynomialWindowRowSum

open ArchonPhysics
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.PeriodicPolynomialWindowGeometricInterior
open ArchonPhysics.PeriodicPolynomialWindowReindex
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.PolynomialMarkedLegWindowStrongLaw
open ArchonPhysics.RegularizedMarkedLegPolynomialLocality

noncomputable section

/-- The cyclic translate of the split-coordinate equivalence. -/
def translatedSplitEquiv {n m : Nat} [NeZero (n + m)]
    (shift : Fin (n + m)) : (Fin n ⊕ Fin m) ≃ Fin (n + m) :=
  finSumFinEquiv.trans (finCycleTranslation shift)

@[simp] theorem translatedSplitEquiv_apply_inl
    {n m : Nat} [NeZero (n + m)] (shift : Fin (n + m)) (i : Fin n) :
    translatedSplitEquiv shift (Sum.inl i) =
      finCycleTranslation shift (Fin.castAdd m i) := by
  rfl

@[simp] theorem translatedSplitEquiv_apply_inr
    {n m : Nat} [NeZero (n + m)] (shift : Fin (n + m)) (i : Fin m) :
    translatedSplitEquiv shift (Sum.inr i) =
      finCycleTranslation shift (Fin.natAdd n i) := by
  rfl

/-- A polynomial kernel from the centered row to the complementary split
block is zero.  This is derived from actual comparison-walk geometry. -/
theorem splitPolynomialKernelEntry_inr_eq_zero
    {m windowRadius : Nat} [NeZero m]
    (w : Fin ((2 * windowRadius + 1) + m) → Real)
    (degree : Nat) (coefficient : Nat → Real)
    (hdegree : degree + 1 ≤ windowRadius) (j : Fin m) :
    zeroConstantMatrixPolynomialUpTo degree coefficient
        (splitFinWeightedCycleLaplacian w)
        (Sum.inl (centeredWindowIndex windowRadius)) (Sum.inr j) = 0 := by
  apply zeroConstantMatrixPolynomialUpTo_apply_eq_zero_of_not_reachableWithin
    (splitFinWeightedCycleLaplacian_supportedOn_comparison w)
    degree coefficient
  intro hreach
  rcases hreach with ⟨steps, hsteps, hwalk⟩
  obtain ⟨b, hbad, _hleft, _hright⟩ :=
    matrixWalk_inl_natBounds_of_localStep
      (splitComparisonStep w)
      (splitComparisonStep_inl_of_interior (by omega) w)
      windowRadius (centeredWindowIndex windowRadius)
      (by simp) (by simp; omega)
      (le_trans hsteps hdegree) hwalk
  cases hbad

/-- After an arbitrary cyclic translation, every column in the complementary
block still has zero polynomial entry from the translated centered row. -/
theorem translatedPolynomialKernelEntry_inr_eq_zero
    {m windowRadius : Nat} [NeZero m]
    (w : Fin ((2 * windowRadius + 1) + m) → Real)
    (shift : Fin ((2 * windowRadius + 1) + m))
    (degree : Nat) (coefficient : Nat → Real)
    (hdegree : degree + 1 ≤ windowRadius) (j : Fin m) :
    zeroConstantMatrixPolynomialUpTo degree coefficient
        (finWeightedCycleLaplacian w)
        (finCycleTranslation shift
          (Fin.castAdd m (centeredWindowIndex windowRadius)))
        (finCycleTranslation shift
          (Fin.natAdd (2 * windowRadius + 1) j)) = 0 := by
  rw [← zeroConstantPolynomial_finWeightedCycle_translate]
  calc
    _ = zeroConstantMatrixPolynomialUpTo degree coefficient
          (splitFinWeightedCycleLaplacian (translateFinWeights w shift))
          (Sum.inl (centeredWindowIndex windowRadius)) (Sum.inr j) := by
        symm
        unfold splitFinWeightedCycleLaplacian
        rw [zeroConstantMatrixPolynomialUpTo_reindex_apply
          finSumFinEquiv.symm
          (finWeightedCycleLaplacian (translateFinWeights w shift))]
        simp only [Equiv.symm_symm, finSumFinEquiv_apply_left,
          finSumFinEquiv_apply_right]
    _ = 0 := splitPolynomialKernelEntry_inr_eq_zero
      (translateFinWeights w shift) degree coefficient hdegree j

/-- Site-indexed vanishing theorem for every leg outside the translated
fixed window. -/
theorem polynomialKernelEntry_eq_zero_on_centeredWindowComplement
    {m windowRadius : Nat} [NeZero m]
    (w : Fin ((2 * windowRadius + 1) + m) → Real)
    (target : Fin ((2 * windowRadius + 1) + m))
    (degree : Nat) (coefficient : Nat → Real)
    (hdegree : degree + 1 ≤ windowRadius) (j : Fin m) :
    let centerBig := Fin.castAdd m (centeredWindowIndex windowRadius)
    let shift := finCenteringShift centerBig target
    zeroConstantMatrixPolynomialUpTo degree coefficient
        (finWeightedCycleLaplacian w) target
        (translatedSplitEquiv shift (Sum.inr j)) = 0 := by
  dsimp only
  simpa using translatedPolynomialKernelEntry_inr_eq_zero
    w (finCenteringShift
      (Fin.castAdd m (centeredWindowIndex windowRadius)) target)
    degree coefficient hdegree j

/-- Three polynomial legs at one large-chain site and one translated-window
column equal the fixed-window product with the same right endpoint `b`. -/
theorem threeLegPolynomialKernelProduct_eq_centeredWindowProduct
    {m windowRadius : Nat} [NeZero m]
    (x : Fin ((2 * windowRadius + 1) + m) → Real)
    (target : Fin ((2 * windowRadius + 1) + m))
    (degree : Fin 3 → Nat)
    (coefficient : Fin 3 → Nat → Real)
    (hdegree : ∀ r, degree r + 1 ≤ windowRadius)
    (b : Fin (2 * windowRadius + 1)) :
    let center := centeredWindowIndex windowRadius
    let centerBig := Fin.castAdd m center
    let shift := finCenteringShift centerBig target
    (∏ r : Fin 3,
      zeroConstantMatrixPolynomialUpTo (degree r) (coefficient r)
        (finWeightedCycleLaplacian (inverseClippedWindow x)) target
        (translatedSplitEquiv shift (Sum.inl b))) =
      threeLegPolynomialWindowProduct degree coefficient
        (fun _ ↦ center) (fun _ ↦ b) (translatedMassWindow x shift) := by
  dsimp only
  unfold threeLegPolynomialWindowProduct
  apply Finset.prod_congr rfl
  intro r _hr
  exact periodicPolynomialKernelEntry_eq_centeredMassWindow_atSite
    x target (degree r) (coefficient r) (hdegree r) b

/-- Exact row-sum reduction.  The right endpoint is shared by all three legs
both before and after reindexing. -/
theorem threeLegPolynomialKernelRowSum_eq_centeredWindowSum
    {m windowRadius : Nat} [NeZero m]
    (x : Fin ((2 * windowRadius + 1) + m) → Real)
    (target : Fin ((2 * windowRadius + 1) + m))
    (degree : Fin 3 → Nat)
    (coefficient : Fin 3 → Nat → Real)
    (hdegree : ∀ r, degree r + 1 ≤ windowRadius) :
    let center := centeredWindowIndex windowRadius
    let centerBig := Fin.castAdd m center
    let shift := finCenteringShift centerBig target
    (∑ l : Fin ((2 * windowRadius + 1) + m),
      ∏ r : Fin 3,
        zeroConstantMatrixPolynomialUpTo (degree r) (coefficient r)
          (finWeightedCycleLaplacian (inverseClippedWindow x)) target l) =
      ∑ b : Fin (2 * windowRadius + 1),
        threeLegPolynomialWindowProduct degree coefficient
          (fun _ ↦ center) (fun _ ↦ b)
          (translatedMassWindow x shift) := by
  dsimp only
  let shift := finCenteringShift
    (Fin.castAdd m (centeredWindowIndex windowRadius)) target
  let F : Fin ((2 * windowRadius + 1) + m) → Real := fun l ↦
    ∏ r : Fin 3,
      zeroConstantMatrixPolynomialUpTo (degree r) (coefficient r)
        (finWeightedCycleLaplacian (inverseClippedWindow x)) target l
  calc
    (∑ l, F l) =
        ∑ u : Fin (2 * windowRadius + 1) ⊕ Fin m,
          F (translatedSplitEquiv shift u) := by
      exact (Equiv.sum_comp (translatedSplitEquiv shift) F).symm
    _ = (∑ b : Fin (2 * windowRadius + 1),
          F (translatedSplitEquiv shift (Sum.inl b))) +
        ∑ j : Fin m, F (translatedSplitEquiv shift (Sum.inr j)) := by
      exact Fintype.sum_sum_type _
    _ = (∑ b : Fin (2 * windowRadius + 1),
          threeLegPolynomialWindowProduct degree coefficient
            (fun _ ↦ centeredWindowIndex windowRadius) (fun _ ↦ b)
            (translatedMassWindow x shift)) + 0 := by
      congr 1
      · apply Finset.sum_congr rfl
        intro b _hb
        exact threeLegPolynomialKernelProduct_eq_centeredWindowProduct
          x target degree coefficient hdegree b
      · apply Finset.sum_eq_zero
        intro j _hj
        unfold F
        have hzero (r : Fin 3) :
            zeroConstantMatrixPolynomialUpTo (degree r) (coefficient r)
                (finWeightedCycleLaplacian (inverseClippedWindow x)) target
                (translatedSplitEquiv shift (Sum.inr j)) = 0 := by
          exact polynomialKernelEntry_eq_zero_on_centeredWindowComplement
            (inverseClippedWindow x) target (degree r) (coefficient r)
              (hdegree r) j
        simp_rw [hzero]
        simp
    _ = ∑ b : Fin (2 * windowRadius + 1),
          threeLegPolynomialWindowProduct degree coefficient
            (fun _ ↦ centeredWindowIndex windowRadius) (fun _ ↦ b)
            (translatedMassWindow x shift) := by
      rw [add_zero]

end
end ArchonPhysics.PeriodicPolynomialWindowRowSum
