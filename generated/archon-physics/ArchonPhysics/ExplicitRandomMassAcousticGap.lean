import ArchonPhysics.UniformMassGaugeCoercivity
import ArchonPhysics.RandomMassHarmonicTransferMatrix

/-!
# An explicit coarse acoustic lower edge

This module proves a fully explicit finite-cycle Poincare estimate by
telescoping along natural representatives of `ZMod N` and applying the finite
Cauchy--Schwarz inequality.  The resulting constant `4 * N^3` is deliberately
coarse, but it is uniform and polynomial in the chain length.

Ordinary centering preserves bond differences.  In the mass-weighted gauge it
also controls the mass-weighted square sum using only a coordinatewise upper
mass bound.  Combining this with the exact generalized eigenmode energy
identity gives

`(4 * mUpper * N^3)⁻¹ ≤ lambda`

for every nonzero generalized mode with `lambda > 0` and `m_i ≤ mUpper`.
No sharp sine law, density-of-states, coupling, connectivity, localization,
probability, or thermalization statement is asserted.
-/

namespace ArchonPhysics.ExplicitRandomMassAcousticGap

open ArchonPhysics
open ArchonPhysics.HarmonicModes
open ArchonPhysics.RandomMassHarmonicTransferMatrix
open ArchonPhysics.TranslationReducedCoercivity
open ArchonPhysics.UniformMassGaugeCoercivity

noncomputable section

/-- Squared `l2` bond seminorm. -/
def bondSquareSum {N : Nat} [NeZero N] (q : Lattice.Configuration N) : Real :=
  ∑ i, Lattice.forwardDifference q i ^ 2

/-- Squared mass-weighted physical norm. -/
def massSquareSum {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (q : Lattice.Configuration N) : Real :=
  ∑ i, m.mass i * q i ^ 2

/-- Forward differences telescope along the natural representatives of
periodic sites. -/
theorem sum_range_forwardDifference {N : Nat} [NeZero N]
    (q : Lattice.Configuration N) (k : Nat) :
    (∑ r ∈ Finset.range k,
      Lattice.forwardDifference q (r : Lattice.Site N)) =
      q (k : Lattice.Site N) - q 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Lattice.forwardDifference_apply, Nat.cast_add, Nat.cast_one]
      ring

/-- Every individual squared bond is bounded by the total bond-square sum. -/
theorem forwardDifference_sq_le_bondSquareSum {N : Nat} [NeZero N]
    (q : Lattice.Configuration N) (i : Lattice.Site N) :
    Lattice.forwardDifference q i ^ 2 ≤ bondSquareSum q := by
  exact Finset.single_le_sum (fun j _ => sq_nonneg (Lattice.forwardDifference q j))
    (Finset.mem_univ i)

/-- A site differs from the zero site by at most the coarse squared path
bound `N² * bondSquareSum`. -/
theorem sub_zeroSite_sq_le {N : Nat} [NeZero N]
    (q : Lattice.Configuration N) (i : Lattice.Site N) :
    (q i - q 0) ^ 2 ≤ (N : Real) ^ 2 * bondSquareSum q := by
  let k := i.val
  have htel : q i - q 0 =
      ∑ r ∈ Finset.range k,
        Lattice.forwardDifference q (r : Lattice.Site N) := by
    simpa [k] using (sum_range_forwardDifference q k).symm
  have hE : 0 ≤ bondSquareSum q := by
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have hsum :
      (∑ r ∈ Finset.range k,
        Lattice.forwardDifference q (r : Lattice.Site N) ^ 2) ≤
        (k : Real) * bondSquareSum q := by
    calc
      (∑ r ∈ Finset.range k,
          Lattice.forwardDifference q (r : Lattice.Site N) ^ 2) ≤
          ∑ _r ∈ Finset.range k, bondSquareSum q := by
        apply Finset.sum_le_sum
        intro r _hr
        exact forwardDifference_sq_le_bondSquareSum q (r : Lattice.Site N)
      _ = (k : Real) * bondSquareSum q := by simp
  have hcauchy :
      (∑ r ∈ Finset.range k,
        Lattice.forwardDifference q (r : Lattice.Site N)) ^ 2 ≤
        (k : Real) *
          ∑ r ∈ Finset.range k,
            Lattice.forwardDifference q (r : Lattice.Site N) ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := Finset.range k)
      (f := fun r => Lattice.forwardDifference q (r : Lattice.Site N)))
  have hk : (k : Real) ≤ (N : Real) := by
    exact_mod_cast Nat.le_of_lt (ZMod.val_lt i)
  have hk0 : 0 ≤ (k : Real) := Nat.cast_nonneg k
  have hN0 : 0 ≤ (N : Real) := Nat.cast_nonneg N
  have hkSq : (k : Real) ^ 2 ≤ (N : Real) ^ 2 := by
    exact (sq_le_sq₀ hk0 hN0).2 hk
  rw [htel]
  calc
    (∑ r ∈ Finset.range k,
        Lattice.forwardDifference q (r : Lattice.Site N)) ^ 2 ≤
        (k : Real) *
          ∑ r ∈ Finset.range k,
            Lattice.forwardDifference q (r : Lattice.Site N) ^ 2 := hcauchy
    _ ≤ (k : Real) * ((k : Real) * bondSquareSum q) :=
      mul_le_mul_of_nonneg_left hsum hk0
    _ = (k : Real) ^ 2 * bondSquareSum q := by ring
    _ ≤ (N : Real) ^ 2 * bondSquareSum q :=
      mul_le_mul_of_nonneg_right hkSq hE

/-- Explicit coarse Poincare estimate on the ordinary zero-mean gauge. -/
theorem zeroMean_sum_sq_le_four_mul_cube_bondSquareSum
    {N : Nat} [NeZero N] (q : Lattice.Configuration N)
    (hmean : ∑ i, q i = 0) :
    (∑ i, q i ^ 2) ≤
      4 * (N : Real) ^ 3 * bondSquareSum q := by
  let d : Lattice.Configuration N := fun i => q i - q 0
  have hE : 0 ≤ bondSquareSum q := by
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have hd (i : Lattice.Site N) :
      d i ^ 2 ≤ (N : Real) ^ 2 * bondSquareSum q := by
    exact sub_zeroSite_sq_le q i
  have hsumd : ∑ i, d i = -(N : Real) * q 0 := by
    unfold d
    rw [Finset.sum_sub_distrib, hmean]
    simp [ZMod.card, nsmul_eq_mul]
  have hsumdSq :
      (∑ i, d i ^ 2) ≤
        (N : Real) * ((N : Real) ^ 2 * bondSquareSum q) := by
    calc
      (∑ i, d i ^ 2) ≤
          ∑ _i : Lattice.Site N,
            ((N : Real) ^ 2 * bondSquareSum q) :=
        Finset.sum_le_sum fun i _ => hd i
      _ = (N : Real) * ((N : Real) ^ 2 * bondSquareSum q) := by
        simp [ZMod.card]
  have hcauchy :
      (∑ i, d i) ^ 2 ≤ (N : Real) * ∑ i, d i ^ 2 := by
    simpa [ZMod.card] using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Lattice.Site N))) (f := d))
  have hN0 : 0 ≤ (N : Real) := Nat.cast_nonneg N
  have hcombined :
      (∑ i, d i) ^ 2 ≤
        (N : Real) *
          ((N : Real) * ((N : Real) ^ 2 * bondSquareSum q)) :=
    hcauchy.trans (mul_le_mul_of_nonneg_left hsumdSq hN0)
  rw [hsumd] at hcombined
  have hNpos : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hN2pos : 0 < (N : Real) ^ 2 := sq_pos_of_pos hNpos
  have hq0 : q 0 ^ 2 ≤ (N : Real) ^ 2 * bondSquareSum q := by
    apply (mul_le_mul_iff_right₀ hN2pos).mp
    calc
      (N : Real) ^ 2 * q 0 ^ 2 = (-(N : Real) * q 0) ^ 2 := by ring
      _ ≤ (N : Real) *
          ((N : Real) * ((N : Real) ^ 2 * bondSquareSum q)) := hcombined
      _ = (N : Real) ^ 2 *
          ((N : Real) ^ 2 * bondSquareSum q) := by ring
  have hpoint (i : Lattice.Site N) :
      q i ^ 2 ≤ 4 * (N : Real) ^ 2 * bondSquareSum q := by
    have hsplit : q i ^ 2 ≤ 2 * d i ^ 2 + 2 * q 0 ^ 2 := by
      change q i ^ 2 ≤ 2 * (q i - q 0) ^ 2 + 2 * q 0 ^ 2
      nlinarith [sq_nonneg (q i - 2 * q 0)]
    calc
      q i ^ 2 ≤ 2 * d i ^ 2 + 2 * q 0 ^ 2 := hsplit
      _ ≤ 2 * ((N : Real) ^ 2 * bondSquareSum q) +
          2 * ((N : Real) ^ 2 * bondSquareSum q) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hd i) (by norm_num))
          (mul_le_mul_of_nonneg_left hq0 (by norm_num))
      _ = 4 * (N : Real) ^ 2 * bondSquareSum q := by ring
  calc
    (∑ i, q i ^ 2) ≤
        ∑ _i : Lattice.Site N,
          (4 * (N : Real) ^ 2 * bondSquareSum q) :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = 4 * (N : Real) ^ 3 * bondSquareSum q := by
      simp [ZMod.card]
      ring

/-- Subtracting the ordinary mean cannot decrease the mass-weighted square
sum when the original configuration is in the mass-weighted gauge. -/
theorem massSquareSum_le_centered_of_massGauge
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (q : Lattice.Configuration N)
    (hgauge : ∑ i, m.mass i * q i = 0) :
    massSquareSum m q ≤
      massSquareSum m (centeredConfiguration q) := by
  let c := configurationMean q
  have hmassNonneg : 0 ≤ ∑ i : Lattice.Site N, m.mass i :=
    Finset.sum_nonneg fun i _ => (m.mass_pos i).le
  calc
    massSquareSum m q ≤
        massSquareSum m q + c ^ 2 * ∑ i, m.mass i := by
      exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg c) hmassNonneg)
    _ = massSquareSum m (centeredConfiguration q) := by
      unfold massSquareSum centeredConfiguration
      change (∑ i, m.mass i * q i ^ 2) +
          c ^ 2 * ∑ i, m.mass i =
        ∑ i, m.mass i * (q i - c) ^ 2
      calc
        (∑ i, m.mass i * q i ^ 2) +
            c ^ 2 * ∑ i, m.mass i =
            (∑ i, m.mass i * q i ^ 2) -
              2 * c * (∑ i, m.mass i * q i) +
                c ^ 2 * ∑ i, m.mass i := by rw [hgauge]; ring
        _ = ∑ i, (m.mass i * q i ^ 2 -
              2 * c * (m.mass i * q i) + c ^ 2 * m.mass i) := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.mul_sum]
        _ = ∑ i, m.mass i * (q i - c) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _hi
          ring

/-- The explicit zero-mean estimate and centering give a deterministic
mass-weighted Poincare inequality with a coordinatewise mass upper bound. -/
theorem massSquareSum_le_four_massUpper_mul_cube_bondSquareSum
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (mUpper : Real) (hmUpper : 0 ≤ mUpper)
    (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (q : Lattice.Configuration N)
    (hgauge : ∑ i, m.mass i * q i = 0) :
    massSquareSum m q ≤
      4 * mUpper * (N : Real) ^ 3 * bondSquareSum q := by
  let r := centeredConfiguration q
  have hrMean : ∑ i, r i = 0 := by
    exact (mem_zeroMeanSubspace_iff r).mp
      (centeredConfiguration_zeroMean q)
  have hP : (∑ i, r i ^ 2) ≤
      4 * (N : Real) ^ 3 * bondSquareSum q := by
    have h := zeroMean_sum_sq_le_four_mul_cube_bondSquareSum r hrMean
    simpa [r, bondSquareSum, forwardDifference_centeredConfiguration] using h
  have hmass :
      massSquareSum m r ≤ mUpper * ∑ i, r i ^ 2 := by
    calc
      massSquareSum m r = ∑ i, m.mass i * r i ^ 2 := rfl
      _ ≤ ∑ i, mUpper * r i ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        exact mul_le_mul_of_nonneg_right (hmassUpper i) (sq_nonneg (r i))
      _ = mUpper * ∑ i, r i ^ 2 := by rw [Finset.mul_sum]
  calc
    massSquareSum m q ≤ massSquareSum m r := by
      exact massSquareSum_le_centered_of_massGauge m q hgauge
    _ ≤ mUpper * ∑ i, r i ^ 2 := hmass
    _ ≤ mUpper * (4 * (N : Real) ^ 3 * bondSquareSum q) :=
      mul_le_mul_of_nonneg_left hP hmUpper
    _ = 4 * mUpper * (N : Real) ^ 3 * bondSquareSum q := by ring

/-- The physical Gram quadratic form is the bond-square sum, so a generalized
mode satisfies the exact energy identity. -/
theorem generalizedEigenmode_bondSquareSum_eq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (lambda : Real) (q : Lattice.Configuration N)
    (hmode : IsGeneralizedHarmonicEigenmode m lambda q) :
    bondSquareSum q = lambda * massSquareSum m q := by
  calc
    bondSquareSum q =
        (Matrix.mulVec differenceMatrix q) ⬝ᵥ
          (Matrix.mulVec differenceMatrix q) := by
      rw [differenceMatrix_mulVec]
      simp [bondSquareSum, dotProduct, pow_two]
    _ = q ⬝ᵥ Matrix.mulVec (Matrix.transpose differenceMatrix)
          (Matrix.mulVec differenceMatrix q) := by
      exact (Matrix.dotProduct_transpose_mulVec differenceMatrix q
        (Matrix.mulVec differenceMatrix q)).symm
    _ = q ⬝ᵥ Matrix.mulVec physicalCycleHarmonicMatrix q := by
      rw [physicalCycleHarmonicMatrix, ← Matrix.mulVec_mulVec]
    _ = q ⬝ᵥ (lambda • Lattice.massAction m q) := by rw [hmode]
    _ = lambda * massSquareSum m q := by
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Lattice.massAction,
        massSquareSum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring

/-- The physical cycle Laplacian has zero coordinate sum. -/
theorem sum_physicalCycleHarmonicMatrix_mulVec_eq_zero
    {N : Nat} [NeZero N] (q : Lattice.Configuration N) :
    ∑ i, Matrix.mulVec physicalCycleHarmonicMatrix q i = 0 := by
  rw [physicalCycleHarmonicMatrix_mulVec]
  have hprev : (∑ i : Lattice.Site N, q (i - 1)) = ∑ i, q i := by
    exact Fintype.sum_equiv (Equiv.addRight (-1))
      (fun i => q (i - 1)) q (fun i => by simp [sub_eq_add_neg])
  have hnext : (∑ i : Lattice.Site N, q (i + 1)) = ∑ i, q i := by
    exact Fintype.sum_equiv (Equiv.addRight 1)
      (fun i => q (i + 1)) q (fun _ => rfl)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  rw [hprev, hnext]
  ring

/-- Every generalized eigenmode with positive eigenvalue automatically lies
in the mass-weighted translation gauge. -/
theorem generalizedEigenmode_massGauge_of_pos
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (lambda : Real) (q : Lattice.Configuration N)
    (hmode : IsGeneralizedHarmonicEigenmode m lambda q)
    (hlambda : 0 < lambda) :
    ∑ i, m.mass i * q i = 0 := by
  have hsum := congrArg (fun x : Lattice.Configuration N => ∑ i, x i) hmode
  have hright :
      (∑ i, (lambda • Lattice.massAction m q) i) =
        lambda * ∑ i, m.mass i * q i := by
    simp only [Pi.smul_apply, smul_eq_mul, Lattice.massAction]
    rw [Finset.mul_sum]
  have hprod : lambda * ∑ i, m.mass i * q i = 0 := by
    rw [← hright, ← hsum]
    exact sum_physicalCycleHarmonicMatrix_mulVec_eq_zero q
  exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hlambda)

/-- A nonzero configuration has strictly positive mass-weighted square sum. -/
theorem massSquareSum_pos_of_ne_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (q : Lattice.Configuration N) (hq : q ≠ 0) :
    0 < massSquareSum m q := by
  have hcoord : ∃ i : Lattice.Site N, q i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hq (funext h)
  obtain ⟨i, hi⟩ := hcoord
  have hterm : 0 < m.mass i * q i ^ 2 :=
    mul_pos (m.mass_pos i) (sq_pos_of_ne_zero hi)
  have hle : m.mass i * q i ^ 2 ≤ massSquareSum m q := by
    exact Finset.single_le_sum
      (fun j _ => mul_nonneg (m.mass_pos j).le (sq_nonneg (q j)))
      (Finset.mem_univ i)
  exact hterm.trans_le hle

/-- Explicit deterministic lower edge for every nonzero positive generalized
mode.  The constant is coarse but polynomial and uniform under `m_i ≤ mUpper`. -/
theorem generalizedPositiveMode_lowerBound
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (mUpper : Real) (hmUpper : 0 < mUpper)
    (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (lambda : Real) (q : Lattice.Configuration N)
    (hmode : IsGeneralizedHarmonicEigenmode m lambda q)
    (hlambda : 0 < lambda) (hq : q ≠ 0) :
    (4 * mUpper * (N : Real) ^ 3)⁻¹ ≤ lambda := by
  have hgauge := generalizedEigenmode_massGauge_of_pos
    m lambda q hmode hlambda
  have hP := massSquareSum_le_four_massUpper_mul_cube_bondSquareSum
    m mUpper hmUpper.le hmassUpper q hgauge
  have henergy := generalizedEigenmode_bondSquareSum_eq
    m lambda q hmode
  have hmassPos := massSquareSum_pos_of_ne_zero m q hq
  have hNpos : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hCpos : 0 < 4 * mUpper * (N : Real) ^ 3 := by positivity
  have hbound :
      massSquareSum m q ≤
        (4 * mUpper * (N : Real) ^ 3) *
          (lambda * massSquareSum m q) := by
    calc
      massSquareSum m q ≤
          4 * mUpper * (N : Real) ^ 3 * bondSquareSum q := hP
      _ = (4 * mUpper * (N : Real) ^ 3) *
          (lambda * massSquareSum m q) := by rw [henergy]
  have hone :
      1 ≤ (4 * mUpper * (N : Real) ^ 3) * lambda := by
    apply (mul_le_mul_iff_right₀ hmassPos).mp
    calc
      massSquareSum m q * 1 = massSquareSum m q := mul_one _
      _ ≤ (4 * mUpper * (N : Real) ^ 3) *
          (lambda * massSquareSum m q) := hbound
      _ = massSquareSum m q *
          ((4 * mUpper * (N : Real) ^ 3) * lambda) := by ring
  apply (mul_le_mul_iff_right₀ hCpos).mp
  rw [mul_inv_cancel₀ (ne_of_gt hCpos)]
  exact hone

end

end ArchonPhysics.ExplicitRandomMassAcousticGap
