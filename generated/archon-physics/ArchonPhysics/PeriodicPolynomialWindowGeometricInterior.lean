import ArchonPhysics.PeriodicPolynomialWindowReindex

/-!
# Geometric discharge of periodic polynomial-window interior conditions

This module turns the exact walk-based premise from
`PeriodicPolynomialWindowReindex` into an elementary natural-coordinate
margin condition.  In particular, an odd window of width `2 * R + 1`
centered at coordinate `R` works for every zero-constant polynomial whose
propagation radius is at most `R`, at every cyclic translate of the large
periodic chain.
-/

namespace ArchonPhysics.PeriodicPolynomialWindowGeometricInterior

open ArchonPhysics
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.PeriodicPolynomialWindowReindex
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.PolynomialMarkedLegWindowStrongLaw
open ArchonPhysics.RandomMassHarmonicSecondMoment
open ArchonPhysics.RegularizedMarkedLegPolynomialLocality
open ArchonPhysics.SingleMassRankOnePerturbation

noncomputable section

theorem finCycleEdgeVector_zero_apply_eq_zero_of_interior
    {N : Nat} [NeZero N] (i : Fin N)
    (hi0 : 0 < i.val) (hiN : i.val + 1 < N) :
    finCycleEdgeVector (0 : Fin N) i = 0 := by
  unfold finCycleEdgeVector cycleMassPerturbationVector differenceMatrix
  have hzero : (siteEquivFin N).symm (0 : Fin N) ≠
      (siteEquivFin N).symm i := by
    intro h
    have hv := congrArg ZMod.val h
    rw [val_siteEquivFin_symm, val_siteEquivFin_symm] at hv
    simp at hv
    omega
  have hsucc : (siteEquivFin N).symm (0 : Fin N) ≠
      (siteEquivFin N).symm i + 1 := by
    intro h
    have hv := congrArg ZMod.val h
    have hNtwo : 1 < N := by omega
    have hone : (1 : ZMod N).val = 1 := by
      simpa using (ZMod.val_natCast_of_lt (n := N) (a := 1) hNtwo)
    rw [val_siteEquivFin_symm, ZMod.val_add, val_siteEquivFin_symm,
      hone, Nat.mod_eq_of_lt hiN] at hv
    simp at hv
  rw [if_neg hsucc, if_neg hzero]
  simp

/-- An ordinary natural-coordinate interior row is outside the support of all
four exact cut-bond updates. -/
theorem not_isSplitBoundaryRow_inl_of_interior
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (i : Fin n) (hi0 : 0 < i.val) (hiN : i.val + 1 < n) :
    ¬ IsSplitBoundaryRow (Sum.inl i : Fin n ⊕ Fin m) := by
  unfold IsSplitBoundaryRow
  push Not
  have hn : 0 < n := NeZero.pos n
  have hm : 0 < m := NeZero.pos m
  constructor
  · unfold splitFullEdgeVector
    rw [finSumFinEquiv_apply_left]
    apply finCycleEdgeVector_zero_apply_eq_zero_of_interior
    · simpa
    · simp only [Fin.val_castAdd]
      omega
  constructor
  · unfold splitFullEdgeVector
    rw [finSumFinEquiv_apply_left]
    rw [finCycleEdgeVector_apply_of_ne_zero]
    · have hcast : (Fin.castAdd m i).val = i.val := rfl
      have hnat : (Fin.natAdd n (0 : Fin m)).val = n := by simp
      have hindex : Fin.natAdd n (0 : Fin m) ≠ Fin.castAdd m i := by
        intro h
        have hv := congrArg Fin.val h
        rw [hcast, hnat] at hv
        omega
      have hsucc : ¬(Fin.natAdd n (0 : Fin m)).val =
          (Fin.castAdd m i).val + 1 := by
        rw [hcast, hnat]
        exact Nat.ne_of_gt hiN
      rw [if_neg hsucc, if_neg hindex]
      simp
    · intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
  constructor
  · unfold leftBlockEdgeVector
    rw [Sum.elim_inl]
    exact finCycleEdgeVector_zero_apply_eq_zero_of_interior i hi0 hiN
  · simp [rightBlockEdgeVector]

/-- A nonzero weighted-cycle entry leaving an ordinary interior row is at
the same natural coordinate or one coordinate to either side. -/
theorem finWeightedCycleLaplacian_step_of_interior
    {N : Nat} [NeZero N] (hN : 3 ≤ N) (w : Fin N → Real)
    (i j : Fin N) (hi0 : 0 < i.val) (hiN : i.val + 1 < N)
    (hij : finWeightedCycleLaplacian w i j ≠ 0) :
    j.val = i.val ∨ j.val = i.val + 1 ∨ j.val + 1 = i.val := by
  have hs : periodicCycleStep ((siteEquivFin N).symm i)
      ((siteEquivFin N).symm j) := by
    apply weightedCycleLaplacian_supportedOn_periodicCycleStep hN
      (weightsOfCoordinates w)
    simpa [finWeightedCycleLaplacian, Matrix.reindex_apply,
      Matrix.submatrix_apply] using hij
  rcases hs with hdiag | hnext | hprev
  · left
    exact congrArg Fin.val (Equiv.injective (siteEquivFin N).symm hdiag)
  · right; left
    have hj0 : j ≠ 0 := by
      intro hj
      subst j
      have hv := congrArg ZMod.val hnext
      have hone : (1 : ZMod N).val = 1 := by
        simpa using (ZMod.val_natCast_of_lt (n := N) (a := 1) (by omega))
      rw [val_siteEquivFin_symm, ZMod.val_add, val_siteEquivFin_symm,
        hone, Nat.mod_eq_of_lt hiN] at hv
      simp at hv
    exact (finCycle_successor_iff_of_ne_zero i j hj0).mp hnext
  · right; right
    have hi0fin : i ≠ 0 := by
      intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_zero] at hv
      omega
    have hback : (siteEquivFin N).symm i =
        (siteEquivFin N).symm j + 1 := by
      simpa [sub_eq_add_neg, add_assoc] using
        (congrArg (fun x : Lattice.Site N ↦ x + 1) hprev).symm
    exact (finCycle_successor_iff_of_ne_zero j i hi0fin).mp hback |>.symm

/-- A comparison step from an ordinary interior row remains in the left
window and changes its natural coordinate by at most one. -/
theorem splitComparisonStep_inl_of_interior
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (hn3 : 3 ≤ n) (w : Fin (n + m) → Real)
    (i : Fin n) (v : Fin n ⊕ Fin m)
    (hi0 : 0 < i.val) (hiN : i.val + 1 < n)
    (hstep : splitComparisonStep w (Sum.inl i) v) :
    ∃ j : Fin n, v = Sum.inl j ∧
      (j.val = i.val ∨ j.val = i.val + 1 ∨ j.val + 1 = i.val) := by
  rcases hstep with hlarge | hblock
  · cases v with
    | inl j =>
        refine ⟨j, rfl, ?_⟩
        have hsupport := finWeightedCycleLaplacian_step_of_interior
          (N := n + m) (by omega) w
          (Fin.castAdd m i) (Fin.castAdd m j) (by simpa) (by
            simp only [Fin.val_castAdd]
            omega) (by
              simpa [splitFinWeightedCycleLaplacian, Matrix.reindex_apply,
                Matrix.submatrix_apply] using hlarge)
        simpa only [Fin.val_castAdd] using hsupport
    | inr j =>
        have hsupport := finWeightedCycleLaplacian_step_of_interior
          (N := n + m) (by omega) w
          (Fin.castAdd m i) (Fin.natAdd n j) (by simpa) (by
            simp only [Fin.val_castAdd]
            omega) (by
              simpa [splitFinWeightedCycleLaplacian, Matrix.reindex_apply,
                Matrix.submatrix_apply] using hlarge)
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hsupport
        omega
  · cases v with
    | inl j =>
        refine ⟨j, rfl, ?_⟩
        apply finWeightedCycleLaplacian_step_of_interior hn3
          (leftWeights w) i j hi0 hiN
        simpa [splitBlockCycleLaplacian] using hblock
    | inr j =>
        simp [splitBlockCycleLaplacian] at hblock

/-- Iterating a nearest-neighbour local relation for at most `radius` steps
keeps a centered row in the left block and within the corresponding natural
coordinate interval. -/
theorem matrixWalk_inl_natBounds_of_localStep
    {n m : Nat} (step : (Fin n ⊕ Fin m) → (Fin n ⊕ Fin m) → Prop)
    (hlocal : ∀ (i : Fin n) (v : Fin n ⊕ Fin m),
      0 < i.val → i.val + 1 < n → step (Sum.inl i) v →
        ∃ j : Fin n, v = Sum.inl j ∧
          (j.val = i.val ∨ j.val = i.val + 1 ∨ j.val + 1 = i.val))
    (radius : Nat) (a : Fin n)
    (haLeft : radius ≤ a.val) (haRight : a.val + radius < n)
    {r : Nat} (hr : r ≤ radius) {u : Fin n ⊕ Fin m}
    (hwalk : MatrixWalk step r (Sum.inl a) u) :
    ∃ b : Fin n, u = Sum.inl b ∧
      a.val ≤ b.val + r ∧ b.val ≤ a.val + r := by
  induction r generalizing u with
  | zero =>
      change Sum.inl a = u at hwalk
      subst u
      exact ⟨a, rfl, by omega, by omega⟩
  | succ r ih =>
      change ∃ k, MatrixWalk step r (Sum.inl a) k ∧ step k u at hwalk
      rcases hwalk with ⟨k, hwalk, hku⟩
      obtain ⟨b, rfl, habLeft, habRight⟩ := ih (by omega) hwalk
      have hb0 : 0 < b.val := by omega
      have hbN : b.val + 1 < n := by omega
      obtain ⟨c, rfl, hbc⟩ := hlocal b u hb0 hbN hku
      refine ⟨c, rfl, ?_, ?_⟩ <;> omega

/-- Concrete discharge rule for the abstract walk-based interior premise:
ordinary left and right natural-coordinate margins of `radius` suffice. -/
theorem isSplitInteriorWithin_of_fin_margins
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (hn3 : 3 ≤ n) (w : Fin (n + m) → Real)
    (radius : Nat) (a : Fin n)
    (haLeft : radius ≤ a.val) (haRight : a.val + radius < n) :
    IsSplitInteriorWithin w radius (Sum.inl a) := by
  intro r hr u hwalk
  obtain ⟨b, rfl, habLeft, habRight⟩ :=
    matrixWalk_inl_natBounds_of_localStep
      (splitComparisonStep w)
      (splitComparisonStep_inl_of_interior hn3 w)
      radius a haLeft haRight (Nat.le_of_lt hr) hwalk
  apply not_isSplitBoundaryRow_inl_of_interior
  · omega
  · omega

/-- Center coordinate of an odd window of width `2 * radius + 1`. -/
def centeredWindowIndex (radius : Nat) : Fin (2 * radius + 1) :=
  ⟨radius, by omega⟩

@[simp] theorem centeredWindowIndex_val (radius : Nat) :
    (centeredWindowIndex radius).val = radius := rfl

/-- Any propagation radius no larger than a positive centered-window radius
automatically satisfies the exact split-interior premise. -/
theorem centeredWindow_isSplitInteriorWithin
    {m windowRadius : Nat} [NeZero m]
    (hwindow : 0 < windowRadius)
    (w : Fin ((2 * windowRadius + 1) + m) → Real)
    (kernelRadius : Nat) (hkernel : kernelRadius ≤ windowRadius) :
    IsSplitInteriorWithin w kernelRadius
      (Sum.inl (centeredWindowIndex windowRadius)) := by
  apply isSplitInteriorWithin_of_fin_margins (by omega)
  · simpa using hkernel
  · simp only [centeredWindowIndex_val]
    omega

/-- Fully instantiated exact local-kernel identity on an odd centered window.
There is no residual graph-interior premise: `degree + 1 ≤ windowRadius` is
the ordinary numerical propagation condition. -/
theorem periodicPolynomialKernelEntry_eq_centeredTranslatedMassWindow
    {m windowRadius : Nat} [NeZero m]
    (x : Fin ((2 * windowRadius + 1) + m) → Real)
    (shift : Fin ((2 * windowRadius + 1) + m))
    (degree : Nat) (coefficient : Nat → Real)
    (hdegree : degree + 1 ≤ windowRadius)
    (b : Fin (2 * windowRadius + 1)) :
    zeroConstantMatrixPolynomialUpTo degree coefficient
        (finWeightedCycleLaplacian (inverseClippedWindow x))
        (finCycleTranslation shift
          (Fin.castAdd m (centeredWindowIndex windowRadius)))
        (finCycleTranslation shift (Fin.castAdd m b)) =
      polynomialWindowKernelEntry degree coefficient
        (centeredWindowIndex windowRadius) b
        (translatedMassWindow x shift) := by
  apply periodicPolynomialKernelEntry_eq_translatedMassWindow
  exact centeredWindow_isSplitInteriorWithin (by omega)
    (translateFinWeights (inverseClippedWindow x) shift)
    (degree + 1) hdegree

/-- The cyclic shift which sends `center` to the prescribed target site. -/
def finCenteringShift {N : Nat} [NeZero N]
    (center target : Fin N) : Fin N :=
  siteEquivFin N
    ((siteEquivFin N).symm target - (siteEquivFin N).symm center)

@[simp] theorem finCycleTranslation_centeringShift_apply
    {N : Nat} [NeZero N] (center target : Fin N) :
    finCycleTranslation (finCenteringShift center target) center = target := by
  apply (siteEquivFin N).symm.injective
  simp [finCycleTranslation, finCenteringShift, siteTranslation,
    sub_eq_add_neg, add_assoc]

/-- Site-indexed version: every site of the large periodic chain is the
center of an exact translated fixed-window polynomial observable. -/
theorem periodicPolynomialKernelEntry_eq_centeredMassWindow_atSite
    {m windowRadius : Nat} [NeZero m]
    (x : Fin ((2 * windowRadius + 1) + m) → Real)
    (target : Fin ((2 * windowRadius + 1) + m))
    (degree : Nat) (coefficient : Nat → Real)
    (hdegree : degree + 1 ≤ windowRadius)
    (b : Fin (2 * windowRadius + 1)) :
    let centerBig := Fin.castAdd m (centeredWindowIndex windowRadius)
    let shift := finCenteringShift centerBig target
    zeroConstantMatrixPolynomialUpTo degree coefficient
        (finWeightedCycleLaplacian (inverseClippedWindow x)) target
        (finCycleTranslation shift (Fin.castAdd m b)) =
      polynomialWindowKernelEntry degree coefficient
        (centeredWindowIndex windowRadius) b
        (translatedMassWindow x shift) := by
  dsimp only
  simpa using periodicPolynomialKernelEntry_eq_centeredTranslatedMassWindow
    x (finCenteringShift
      (Fin.castAdd m (centeredWindowIndex windowRadius)) target)
    degree coefficient hdegree b

end
end ArchonPhysics.PeriodicPolynomialWindowGeometricInterior
