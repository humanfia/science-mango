import ArchonPhysics.FrozenCollisionMassQuantitativeLowerBound
import ArchonPhysics.RandomMassHarmonicSecondMoment

/-!
# Extensive lower bound for the frozen cubic interaction tensor

Finite Fubini and Parseval identify the full Hilbert--Schmidt square of the
cubic physical interaction tensor with the entrywise cube sum of the
edge-space weighted cycle Laplacian.  For a cycle of length at least three,
that cube sum is exactly

`3 * sum_i w_i * w_(i+1) * (w_i + w_(i+1))`.

Thus inverse masses bounded below by one positive constant give a tensor
square lower bound linear in the volume.  No resonance or thermodynamic
limit is asserted.
-/

namespace ArchonPhysics.FrozenInteractionTensorExtensiveLowerBound

open ArchonPhysics
open ArchonPhysics.FrozenCollisionMassQuantitativeLowerBound
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedCycleBridge
open ArchonPhysics.ModeCoupling
open ArchonPhysics.RandomMassHarmonicSecondMoment
open scoped InnerProductSpace RealInnerProductSpace

noncomputable section

/-- Finite Fubini identity for the Hilbert--Schmidt square of a tensor
obtained by summing products of one-leg coefficients. -/
theorem sum_sq_sum_prod_factorization
    {mode leg bond : Type*}
    [Fintype mode] [Fintype leg] [DecidableEq leg] [Fintype bond]
    (coefficient : bond → mode → Real) :
    (∑ modes : leg → mode,
        (∑ j, ∏ r, coefficient j (modes r)) ^ 2) =
      ∑ j : bond, ∑ l : bond, ∏ _r : leg, ∑ k : mode,
        coefficient j k * coefficient l k := by
  calc
    (∑ modes : leg → mode,
        (∑ j, ∏ r, coefficient j (modes r)) ^ 2) =
        ∑ modes : leg → mode, ∑ j : bond, ∑ l : bond,
          ∏ r, coefficient j (modes r) * coefficient l (modes r) := by
      apply Finset.sum_congr rfl
      intro modes _hmodes
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _hl
      rw [← Finset.prod_mul_distrib]
    _ = ∑ j : bond, ∑ l : bond, ∑ modes : leg → mode,
          ∏ r, coefficient j (modes r) * coefficient l (modes r) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.sum_comm]
    _ = ∑ j : bond, ∑ l : bond, ∏ _r : leg, ∑ k : mode,
          coefficient j k * coefficient l k := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro l _hl
      rw [Fintype.prod_sum]

/-- A matrix row, regarded as a vector in the Euclidean domain. -/
def matrixRowEuclidean {mode bond : Type*} [Fintype mode]
    (B : Matrix bond mode Real) (j : bond) : EuclideanSpace Real mode :=
  WithLp.toLp 2 (B j)

/-- Parseval for two rows after multiplication by an arbitrary finite real
orthonormal basis. -/
theorem sum_mulVec_orthonormalBasis_mul
    {mode bond : Type*} [Fintype mode]
    (B : Matrix bond mode Real)
    (b : OrthonormalBasis mode Real (EuclideanSpace Real mode))
    (j l : bond) :
    (∑ k, Matrix.mulVec B (b k) j * Matrix.mulVec B (b k) l) =
      (B * Matrix.transpose B) j l := by
  calc
    (∑ k, Matrix.mulVec B (b k) j * Matrix.mulVec B (b k) l) =
        ∑ k, ⟪matrixRowEuclidean B j, b k⟫_ℝ *
          ⟪b k, matrixRowEuclidean B l⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro k _hk
      simp [matrixRowEuclidean, Matrix.mulVec, dotProduct,
        PiLp.inner_apply, mul_comm]
    _ = ⟪matrixRowEuclidean B j, matrixRowEuclidean B l⟫_ℝ :=
      b.sum_inner_mul_inner _ _
    _ = (B * Matrix.transpose B) j l := by
      simp [matrixRowEuclidean, PiLp.inner_apply, Matrix.mul_apply, mul_comm]

/-- Exact full tensor-square identity in terms of the edge-space cogram. -/
theorem sum_interactionTensor_three_sq_eq_cogram_entry_cube
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    (∑ modes : Fin 3 → Lattice.Site N,
        (interactionTensor m 3 modes) ^ 2) =
      ∑ j, ∑ l,
        (massWeightedDifferenceMatrix m *
          Matrix.transpose (massWeightedDifferenceMatrix m)) j l ^ 3 := by
  let B := massWeightedDifferenceMatrix m
  calc
    (∑ modes : Fin 3 → Lattice.Site N,
        (interactionTensor m 3 modes) ^ 2) =
        ∑ j, ∑ l, ∏ _r : Fin 3, ∑ k,
          bondModeCoefficient m j k * bondModeCoefficient m l k := by
      simpa [interactionTensor] using
        (sum_sq_sum_prod_factorization
          (leg := Fin 3)
          (coefficient := fun j k ↦ bondModeCoefficient m j k))
    _ = ∑ j, ∑ l, ∏ _r : Fin 3, (B * Matrix.transpose B) j l := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro l _hl
      apply Finset.prod_congr rfl
      intro r _hr
      exact sum_mulVec_orthonormalBasis_mul B (normalModeBasis m) j l
    _ = ∑ j, ∑ l, (B * Matrix.transpose B) j l ^ 3 := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro l _hl
      rw [Fin.prod_univ_three]
      ring

/-- The cube sum of one weighted-cycle row consists of its diagonal and two
neighbour entries. -/
theorem weightedCycleLaplacian_row_cube_sum
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (w : Lattice.Configuration N) (i : Lattice.Site N) :
    ∑ j, weightedCycleLaplacian w i j ^ 3 =
      (w (i + 1) + w i) ^ 3 + (-w (i + 1)) ^ 3 + (-w i) ^ 3 := by
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
      else 0) ^ 3) =
        ∑ j, ((if j = i then (w (i + 1) + w i) ^ 3 else 0) +
          (if j = i + 1 then (-w (i + 1)) ^ 3 else 0) +
          (if j = i - 1 then (-w i) ^ 3 else 0)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hzero : j = i
      · simp [hzero, hplus.symm, hminus.symm]
      · by_cases hnext : j = i + 1
        · simp [hnext, hneighbors.symm, hone]
        · by_cases hprev : j = i - 1
          · simp [hprev, hone, hneighbors]
          · simp [hzero, hnext, hprev]
    _ = (w (i + 1) + w i) ^ 3 + (-w (i + 1)) ^ 3 + (-w i) ^ 3 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp

/-- Exact entrywise cube sum of a weighted periodic cycle. -/
theorem sum_weightedCycleLaplacian_entry_cube
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (w : Lattice.Configuration N) :
    (∑ i, ∑ j, weightedCycleLaplacian w i j ^ 3) =
      3 * ∑ i, w i * w (i + 1) * (w i + w (i + 1)) := by
  calc
    (∑ i, ∑ j, weightedCycleLaplacian w i j ^ 3) =
        ∑ i, ((w (i + 1) + w i) ^ 3 +
          (-w (i + 1)) ^ 3 + (-w i) ^ 3) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact weightedCycleLaplacian_row_cube_sum hN w i
    _ = 3 * ∑ i, w i * w (i + 1) * (w i + w (i + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring

/-- Exact extensive formula for the full cubic tensor Hilbert--Schmidt
square. -/
theorem sum_interactionTensor_three_sq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) (hN : 3 ≤ N) :
    (∑ modes : Fin 3 → Lattice.Site N,
        (interactionTensor m 3 modes) ^ 2) =
      3 * ∑ i, (m.mass i)⁻¹ * (m.mass (i + 1))⁻¹ *
        ((m.mass i)⁻¹ + (m.mass (i + 1))⁻¹) := by
  rw [sum_interactionTensor_three_sq_eq_cogram_entry_cube]
  rw [massWeighted_selfTranspose_eq_weightedCycleLaplacian]
  exact sum_weightedCycleLaplacian_entry_cube hN _

/-- A common positive lower bound on all inverse masses gives a tensor-square
lower bound linear in the number of sites. -/
theorem six_mul_card_mul_cube_le_sum_interactionTensor_three_sq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) (hN : 3 ≤ N)
    (wLower : Real) (hwLower : 0 ≤ wLower)
    (hw : ∀ i, wLower ≤ (m.mass i)⁻¹) :
    6 * (N : Real) * wLower ^ 3 ≤
      ∑ modes : Fin 3 → Lattice.Site N,
        (interactionTensor m 3 modes) ^ 2 := by
  rw [sum_interactionTensor_three_sq m hN]
  have hterm (i : Lattice.Site N) :
      6 * wLower ^ 3 ≤
        3 * ((m.mass i)⁻¹ * (m.mass (i + 1))⁻¹ *
          ((m.mass i)⁻¹ + (m.mass (i + 1))⁻¹)) := by
    have hiNonneg : 0 ≤ (m.mass i)⁻¹ := inv_nonneg.mpr (m.mass_pos i).le
    have hnextNonneg : 0 ≤ (m.mass (i + 1))⁻¹ :=
      inv_nonneg.mpr (m.mass_pos (i + 1)).le
    have hproduct : wLower * wLower ≤
        (m.mass i)⁻¹ * (m.mass (i + 1))⁻¹ :=
      mul_le_mul (hw i) (hw (i + 1)) hwLower hiNonneg
    have hsum : 2 * wLower ≤
        (m.mass i)⁻¹ + (m.mass (i + 1))⁻¹ := by
      linarith [hw i, hw (i + 1)]
    have hmul := mul_le_mul hproduct hsum
      (mul_nonneg (by norm_num) hwLower)
      (mul_nonneg hiNonneg hnextNonneg)
    nlinarith
  calc
    6 * (N : Real) * wLower ^ 3 =
        ∑ _i : Lattice.Site N, 6 * wLower ^ 3 := by
      simp [Lattice.Site]
      ring
    _ ≤ ∑ i, 3 * ((m.mass i)⁻¹ * (m.mass (i + 1))⁻¹ *
          ((m.mass i)⁻¹ + (m.mass (i + 1))⁻¹)) :=
      Finset.sum_le_sum fun i _hi ↦ hterm i
    _ = 3 * ∑ i, (m.mass i)⁻¹ * (m.mass (i + 1))⁻¹ *
          ((m.mass i)⁻¹ + (m.mass (i + 1))⁻¹) := by
      rw [Finset.mul_sum]

/-- Frozen IID masses give the explicit extensive lower bound
`(125/36) * N`. -/
theorem iid_tensorSquare_extensive_lower
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega) (hN : 3 ≤ N) :
    (125 / 36 : Real) * N ≤
      ∑ modes : Fin 3 → Lattice.Site N,
        (interactionTensor
          (ensemble.restrictPositiveMass (N := N) omega) 3 modes) ^ 2 := by
  let m := ensemble.restrictPositiveMass (N := N) omega
  have hw : ∀ i, (5 / 6 : Real) ≤ (m.mass i)⁻¹ := by
    intro i
    have hupper : m.mass i ≤ (6 / 5 : Real) := by
      simpa [m, RandomEnsemble.massUpper] using
        (ensemble.mass_mem_support i.val omega).2
    simpa using
      ((inv_le_inv₀ (by norm_num : (0 : Real) < 6 / 5) (m.mass_pos i)).2 hupper)
  have hbound := six_mul_card_mul_cube_le_sum_interactionTensor_three_sq
    m hN (5 / 6) (by norm_num) hw
  calc
    (125 / 36 : Real) * N = 6 * (N : Real) * (5 / 6 : Real) ^ 3 := by
      norm_num
      ring
    _ ≤ _ := hbound

end

end ArchonPhysics.FrozenInteractionTensorExtensiveLowerBound
