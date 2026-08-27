import ArchonPhysics.MeasurableHarmonicData

/-!
# Exact trace of the random-mass harmonic matrix

For every periodic chain with at least two sites, each column of the forward
difference matrix has squared norm two.  It follows that the trace of the
mass-weighted harmonic matrix is exactly twice the sum of the inverse masses.

This is a finite-volume identity.  It does not assert a density-of-states,
localization, collision-kernel, kinetic, or thermalization limit.
-/

open scoped Matrix

namespace ArchonPhysics.RandomMassHarmonicTrace

open ArchonPhysics
open ArchonPhysics.HarmonicModes

noncomputable section

/-- On a periodic lattice with at least two sites, translation by one has no
fixed site. -/
theorem zmod_add_one_ne_self {N : Nat} (hN : 2 ≤ N)
    (i : Lattice.Site N) : i + 1 ≠ i := by
  intro h
  have hone : (1 : ZMod N) = 0 := by
    apply add_left_cancel (a := i)
    simpa using h
  have : N = 1 := ZMod.one_eq_zero_iff.mp hone
  omega

/-- Every column of the periodic forward-difference matrix has squared
Euclidean norm two. -/
theorem differenceMatrix_column_sq_sum {N : Nat} [NeZero N]
    (hN : 2 ≤ N) (i : Lattice.Site N) :
    ∑ j, differenceMatrix j i ^ 2 = 2 := by
  have hne : i - 1 ≠ i := by
    intro h
    have h' := congrArg (fun x : Lattice.Site N ↦ x + 1) h
    have hone : i ≠ i + 1 := (zmod_add_one_ne_self hN i).symm
    apply hone
    simpa [sub_eq_add_neg, add_assoc] using h'
  have hdifference (j : Lattice.Site N) :
      differenceMatrix j i =
        if j = i - 1 then 1 else if j = i then -1 else 0 := by
    unfold differenceMatrix
    have hiff : i = j + 1 ↔ j = i - 1 := by
      constructor
      · intro hij
        rw [hij]
        simp
      · intro hji
        rw [hji]
        simp
    rw [if_congr hiff rfl rfl]
    by_cases hj : j = i - 1
    · have hij : i ≠ j := by
        rw [hj]
        exact hne.symm
      rw [if_pos hj, if_neg hij, if_pos hj]
      simp
    · by_cases hji : j = i
      · subst j
        simp [hj]
      · have hij : i ≠ j := Ne.symm hji
        simp [hj, hji, hij]
  simp_rw [hdifference]
  calc
    (∑ j, (if j = i - 1 then (1 : Real) else
        if j = i then (-1 : Real) else 0) ^ 2) =
        ∑ j, ((if j = i - 1 then (1 : Real) else 0) +
          (if j = i then (1 : Real) else 0)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hleft : j = i - 1
      · have hright : j ≠ i := by
          intro hright
          rw [hright] at hleft
          exact hne.symm hleft
        simp only [if_pos hleft, if_neg hright]
        norm_num
      · by_cases hright : j = i
        · simp only [if_neg hleft, if_pos hright]
          norm_num
        · simp only [if_neg hleft, if_neg hright]
          norm_num
    _ = 2 := by
      rw [Finset.sum_add_distrib]
      simp
      norm_num

/-- Exact finite-volume trace identity for the mass-weighted harmonic matrix. -/
theorem massWeightedHarmonicMatrix_trace_eq_inverseMassSum
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (m : Lattice.PositiveMassConfig N) :
    Matrix.trace (massWeightedHarmonicMatrix m) =
      ∑ i, 2 * (m.mass i)⁻¹ := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply]
  simp_rw [
    ArchonPhysics.MeasurableHarmonicData.massWeightedHarmonicMatrix_apply]
  simp_rw [
    ArchonPhysics.MeasurableHarmonicData.massWeightedDifferenceMatrix_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  calc
    (∑ k, (differenceMatrix k i * (Real.sqrt (m.mass i))⁻¹) *
        (differenceMatrix k i * (Real.sqrt (m.mass i))⁻¹)) =
        (Real.sqrt (m.mass i))⁻¹ ^ 2 *
          ∑ k, differenceMatrix k i ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ = (Real.sqrt (m.mass i))⁻¹ ^ 2 * 2 := by
      rw [differenceMatrix_column_sq_sum hN i]
    _ = 2 * (m.mass i)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (m.mass_pos i).le]
      ring

/-- Normalized form of the exact trace identity. -/
theorem massWeightedHarmonicMatrix_normalizedTrace_eq_inverseMassMean
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (m : Lattice.PositiveMassConfig N) :
    Matrix.trace (massWeightedHarmonicMatrix m) / (N : Real) =
      2 * ((∑ i, (m.mass i)⁻¹) / (N : Real)) := by
  rw [massWeightedHarmonicMatrix_trace_eq_inverseMassSum hN m]
  rw [← Finset.mul_sum]
  ring

end

end ArchonPhysics.RandomMassHarmonicTrace
