import ArchonPhysics.RandomMassHarmonicTrace
import ArchonPhysics.MassWeightedCycleBridge

/-!
# Exact second spectral moment of the random-mass harmonic matrix

For every periodic chain of size at least three, this module computes
`trace(H_m * H_m)` exactly as a sum of one-site and nearest-neighbour
reciprocal-mass observables.  This is the finite-volume locality input for a
later strong law for the second moment of the harmonic spectral measure.

No full density-of-states, localization, collision-kernel, kinetic, or
thermalization limit is asserted here.
-/

open scoped Matrix

namespace ArchonPhysics.RandomMassHarmonicSecondMoment

open ArchonPhysics
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedCycleBridge

noncomputable section

/-- Entry formula for the edge-space weighted cycle Laplacian. -/
theorem weightedCycleLaplacian_apply
    {N : Nat} [NeZero N] (w : Lattice.Configuration N)
    (i j : Lattice.Site N) :
    weightedCycleLaplacian w i j =
      w (i + 1) *
          ((if j = i then 1 else 0) - (if j = i + 1 then 1 else 0)) +
        w i *
          ((if j = i then 1 else 0) - (if j = i - 1 then 1 else 0)) := by
  unfold weightedCycleLaplacian
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp_rw [Matrix.diagonal_mul]
  simp only [Matrix.transpose_apply, differenceMatrix]
  simp_rw [sub_mul, mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, add_left_inj]
  have hprev : j + 1 = i ↔ j = i - 1 := by
    constructor
    · intro h
      calc
        j = (j + 1) - 1 := by simp
        _ = i - 1 := by rw [h]
    · intro h
      rw [h]
      simp
  rw [if_congr hprev rfl rfl]
  split_ifs <;> simp_all [sub_eq_add_neg]

theorem zmod_two_ne_zero {N : Nat} (hN : 3 ≤ N) :
    (2 : ZMod N) ≠ 0 := by
  intro h
  have hcast : ((2 : Nat) : ZMod N) = ((0 : Nat) : ZMod N) := by
    simpa using h
  have hmod := (ZMod.natCast_eq_natCast_iff 2 0 N).mp hcast
  have heq : 2 = 0 :=
    hmod.eq_of_lt_of_lt (by omega) (by omega)
  omega

/-- For `N ≥ 3`, a row has exactly the diagonal and two distinct neighbour
entries. -/
theorem weightedCycleLaplacian_apply_piecewise
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (w : Lattice.Configuration N) (i j : Lattice.Site N) :
    weightedCycleLaplacian w i j =
      if j = i then w (i + 1) + w i
      else if j = i + 1 then -w (i + 1)
      else if j = i - 1 then -w i
      else 0 := by
  have hplus : i + 1 ≠ i :=
    ArchonPhysics.RandomMassHarmonicTrace.zmod_add_one_ne_self
      (by omega) i
  have hminus : i - 1 ≠ i := by
    intro h
    have hshift := congrArg (fun x : Lattice.Site N ↦ x + 1) h
    apply hplus.symm
    simpa [sub_eq_add_neg, add_assoc] using hshift
  have hneighbors : i - 1 ≠ i + 1 := by
    intro h
    have hnegone : (-1 : ZMod N) = 1 := by
      apply add_left_cancel (a := i)
      simpa [sub_eq_add_neg] using h
    have hzeroTwo := congrArg (fun x : ZMod N ↦ x + 1) hnegone
    apply zmod_two_ne_zero hN
    calc
      (2 : ZMod N) = 1 + 1 := by norm_num
      _ = (-1 : ZMod N) + 1 := hzeroTwo.symm
      _ = 0 := by simp
  have hone : (1 : ZMod N) ≠ 0 := by
    intro h
    have : N = 1 := ZMod.one_eq_zero_iff.mp h
    omega
  rw [weightedCycleLaplacian_apply]
  by_cases hzero : j = i
  · subst j
    simp [hone, hminus.symm]
  · by_cases hnext : j = i + 1
    · subst j
      simp [hplus, hneighbors.symm]
    · by_cases hprev : j = i - 1
      · subst j
        simp [hminus, hneighbors]
      · simp [hzero, hnext, hprev]

/-- Exact squared Euclidean norm of one weighted-cycle row. -/
theorem weightedCycleLaplacian_row_sq_sum
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (w : Lattice.Configuration N) (i : Lattice.Site N) :
    ∑ j, weightedCycleLaplacian w i j ^ 2 =
      (w (i + 1) + w i) ^ 2 + w (i + 1) ^ 2 + w i ^ 2 := by
  classical
  simp_rw [weightedCycleLaplacian_apply_piecewise hN w i]
  have hplus : i + 1 ≠ i :=
    ArchonPhysics.RandomMassHarmonicTrace.zmod_add_one_ne_self
      (by omega) i
  have hminus : i - 1 ≠ i := by
    intro h
    have hshift := congrArg (fun x : Lattice.Site N ↦ x + 1) h
    apply hplus.symm
    simpa [sub_eq_add_neg, add_assoc] using hshift
  have hneighbors : i - 1 ≠ i + 1 := by
    intro h
    have hnegone : (-1 : ZMod N) = 1 := by
      apply add_left_cancel (a := i)
      simpa [sub_eq_add_neg] using h
    have hzeroTwo := congrArg (fun x : ZMod N ↦ x + 1) hnegone
    apply zmod_two_ne_zero hN
    calc
      (2 : ZMod N) = 1 + 1 := by norm_num
      _ = (-1 : ZMod N) + 1 := hzeroTwo.symm
      _ = 0 := by simp
  have hone : (1 : ZMod N) ≠ 0 := by
    intro h
    have : N = 1 := ZMod.one_eq_zero_iff.mp h
    omega
  calc
    (∑ j, (if j = i then w (i + 1) + w i
      else if j = i + 1 then -w (i + 1)
      else if j = i - 1 then -w i
      else 0) ^ 2) =
        ∑ j, ((if j = i then (w (i + 1) + w i) ^ 2 else 0) +
          (if j = i + 1 then w (i + 1) ^ 2 else 0) +
          (if j = i - 1 then w i ^ 2 else 0)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hzero : j = i
      · simp [hzero, hplus.symm, hminus.symm]
      · by_cases hnext : j = i + 1
        · simp [hnext, hneighbors.symm, hone]
        · by_cases hprev : j = i - 1
          · simp [hprev, hone, hneighbors]
          · simp [hzero, hnext, hprev]
    _ = (w (i + 1) + w i) ^ 2 + w (i + 1) ^ 2 + w i ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp

theorem weightedCycleLaplacian_isHermitian_local
    {N : Nat} [NeZero N] (w : Lattice.Configuration N) :
    (weightedCycleLaplacian w).IsHermitian := by
  unfold weightedCycleLaplacian Matrix.IsHermitian
  simp [Matrix.mul_assoc]

/-- Exact second trace moment of a weighted periodic cycle. -/
theorem trace_weightedCycleLaplacian_sq
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (w : Lattice.Configuration N) :
    Matrix.trace (weightedCycleLaplacian w * weightedCycleLaplacian w) =
      4 * ∑ i, w i ^ 2 + 2 * ∑ i, w i * w (i + 1) := by
  classical
  have hsymm := weightedCycleLaplacian_isHermitian_local w
  have hshift :
      (∑ i : Lattice.Site N, w (i + 1) ^ 2) =
        ∑ i : Lattice.Site N, w i ^ 2 := by
    exact Fintype.sum_equiv (Equiv.addRight 1)
      (fun i ↦ w (i + 1) ^ 2) (fun i ↦ w i ^ 2) (fun _ ↦ rfl)
  calc
    Matrix.trace (weightedCycleLaplacian w * weightedCycleLaplacian w) =
        ∑ i, ∑ j, weightedCycleLaplacian w i j ^ 2 := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      have hij : weightedCycleLaplacian w j i =
          weightedCycleLaplacian w i j := by
        simpa using hsymm.apply i j
      rw [hij, pow_two]
    _ = ∑ i, ((w (i + 1) + w i) ^ 2 +
          w (i + 1) ^ 2 + w i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact weightedCycleLaplacian_row_sq_sum hN w i
    _ = 4 * ∑ i, w i ^ 2 + 2 * ∑ i, w i * w (i + 1) := by
      simp_rw [add_sq]
      repeat rw [Finset.sum_add_distrib]
      rw [hshift]
      have hcross : (∑ i, w (i + 1) * w i) =
          ∑ i, w i * w (i + 1) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      rw [hcross]
      ring

/-- Squared Gram and cogram matrices have the same trace. -/
theorem trace_gram_sq_eq_trace_cogram_sq
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι Real) :
    Matrix.trace ((Matrix.transpose A * A) * (Matrix.transpose A * A)) =
      Matrix.trace ((A * Matrix.transpose A) *
        (A * Matrix.transpose A)) := by
  calc
    Matrix.trace ((Matrix.transpose A * A) * (Matrix.transpose A * A)) =
        Matrix.trace
          (Matrix.transpose A * (A * Matrix.transpose A) * A) := by
      congr 1
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace
        ((A * Matrix.transpose A) * (A * Matrix.transpose A)) := by
      exact Matrix.trace_mul_cycle (Matrix.transpose A)
        (A * Matrix.transpose A) A

/-- Exact finite-volume second spectral moment of the physical random-mass
harmonic matrix. -/
theorem massWeightedHarmonicMatrix_trace_sq
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (m : Lattice.PositiveMassConfig N) :
    Matrix.trace
        (massWeightedHarmonicMatrix m * massWeightedHarmonicMatrix m) =
      4 * ∑ i, (m.mass i)⁻¹ ^ 2 +
        2 * ∑ i, (m.mass i)⁻¹ * (m.mass (i + 1))⁻¹ := by
  let A := massWeightedDifferenceMatrix m
  calc
    Matrix.trace
        (massWeightedHarmonicMatrix m * massWeightedHarmonicMatrix m) =
      Matrix.trace ((Matrix.transpose A * A) * (Matrix.transpose A * A)) := by
        rfl
    _ = Matrix.trace ((A * Matrix.transpose A) *
        (A * Matrix.transpose A)) :=
      trace_gram_sq_eq_trace_cogram_sq A
    _ = Matrix.trace
        (weightedCycleLaplacian (fun i ↦ (m.mass i)⁻¹) *
          weightedCycleLaplacian (fun i ↦ (m.mass i)⁻¹)) := by
      rw [show A * Matrix.transpose A =
        weightedCycleLaplacian (fun i ↦ (m.mass i)⁻¹) by
          exact massWeighted_selfTranspose_eq_weightedCycleLaplacian m]
    _ = 4 * ∑ i, (m.mass i)⁻¹ ^ 2 +
        2 * ∑ i, (m.mass i)⁻¹ * (m.mass (i + 1))⁻¹ :=
      trace_weightedCycleLaplacian_sq hN _

end

end ArchonPhysics.RandomMassHarmonicSecondMoment
