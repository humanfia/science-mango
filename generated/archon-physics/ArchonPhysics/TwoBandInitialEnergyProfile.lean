import ArchonPhysics.SoftSectorL1Control

/-!
# A macroscopic two-band non-equilibrium initial profile

This profile puts total energy `(1 + a) / 2` in the lower half of the ordered
positive modes and `(1 - a) / 2` in the upper half.  Unlike a checkerboard
profile, it has a direct step-function thermodynamic interpretation.  It is
uniformly separated from equipartition while assigning only `O(1 / M)` energy
to every individual mode, so an `o(M)` acoustic layer has `o(1)` energy.

The file freezes the modal energy spectrum only.  A measurable random
eigenbasis/phase adapter into microscopic positions and momenta is still a
separate obligation.
-/

namespace ArchonPhysics.TwoBandInitialEnergyProfile

open Filter
open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.SoftSectorL1Control

noncomputable section

/-- Lower half of the ordered positive-mode ranks. -/
def lowerBand (M : Nat) : Finset (Fin M) :=
  Finset.univ.filter fun i ↦ i.val < M / 2

/-- Upper half, including the middle rank when `M` is odd. -/
def upperBand (M : Nat) : Finset (Fin M) :=
  Finset.univ.filter fun i ↦ ¬ i.val < M / 2

theorem card_lowerBand (M : Nat) : (lowerBand M).card = M / 2 := by
  simpa [lowerBand, Nat.min_eq_right (Nat.div_le_self M 2)] using
    (Fin.card_filter_val_lt (n := M) (m := M / 2))

theorem card_upperBand (M : Nat) : (upperBand M).card = M - M / 2 := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin M))) (fun i ↦ i.val < M / 2)
  rw [show (Finset.univ.filter fun i : Fin M ↦ i.val < M / 2) =
      lowerBand M by rfl,
    show (Finset.univ.filter fun i : Fin M ↦ ¬ i.val < M / 2) =
      upperBand M by rfl,
    card_lowerBand, Finset.card_univ, Fintype.card_fin] at h
  omega

/-- The macroscopic two-band probability profile. -/
def initialEnergyProfile (M : Nat) (a : Real) (i : Fin M) : Real :=
  if i.val < M / 2 then
    (1 + a) / (2 * (M / 2 : Nat) : Real)
  else
    (1 - a) / (2 * (M - M / 2 : Nat) : Real)

/-- For at least two modes, both band sizes are positive. -/
theorem bandCounts_pos {M : Nat} (hM : 2 ≤ M) :
    0 < M / 2 ∧ 0 < M - M / 2 := by
  constructor <;> omega

theorem initialEnergyProfile_nonneg {M : Nat} (hM : 2 ≤ M)
    {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (i : Fin M) :
    0 ≤ initialEnergyProfile M a i := by
  have hcounts := bandCounts_pos hM
  rw [initialEnergyProfile]
  split_ifs
  · positivity
  · exact div_nonneg (by linarith) (by positivity)

/-- The lower band carries exactly `(1 + a) / 2` of the energy. -/
theorem sum_lowerBand_initialEnergyProfile {M : Nat} (hM : 2 ≤ M)
    (a : Real) :
    (∑ i ∈ lowerBand M, initialEnergyProfile M a i) = (1 + a) / 2 := by
  have hkNat : M / 2 ≠ 0 := ne_of_gt (bandCounts_pos hM).1
  have hk : (((M / 2 : Nat) : Real)) ≠ 0 := Nat.cast_ne_zero.mpr hkNat
  calc
    (∑ i ∈ lowerBand M, initialEnergyProfile M a i) =
        ∑ _i ∈ lowerBand M,
          (1 + a) / (2 * (M / 2 : Nat) : Real) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [initialEnergyProfile, if_pos]
      simpa [lowerBand] using hi
    _ = ((M / 2 : Nat) : Real) *
        ((1 + a) / (2 * (M / 2 : Nat) : Real)) := by
      simp only [Finset.sum_const, card_lowerBand, nsmul_eq_mul]
    _ = (1 + a) / 2 := by
      field_simp [hk]

/-- The upper band carries exactly `(1 - a) / 2` of the energy. -/
theorem sum_upperBand_initialEnergyProfile {M : Nat} (hM : 2 ≤ M)
    (a : Real) :
    (∑ i ∈ upperBand M, initialEnergyProfile M a i) = (1 - a) / 2 := by
  have hlNat : M - M / 2 ≠ 0 := ne_of_gt (bandCounts_pos hM).2
  have hl : (((M - M / 2 : Nat) : Real)) ≠ 0 := Nat.cast_ne_zero.mpr hlNat
  calc
    (∑ i ∈ upperBand M, initialEnergyProfile M a i) =
        ∑ _i ∈ upperBand M,
          (1 - a) / (2 * (M - M / 2 : Nat) : Real) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [initialEnergyProfile, if_neg]
      simpa [upperBand] using hi
    _ = ((M - M / 2 : Nat) : Real) *
        ((1 - a) / (2 * (M - M / 2 : Nat) : Real)) := by
      simp only [Finset.sum_const, card_upperBand, nsmul_eq_mul]
    _ = (1 - a) / 2 := by
      field_simp [hl]

/-- The two bands partition all positive ranks. -/
theorem lowerBand_union_upperBand (M : Nat) :
    lowerBand M ∪ upperBand M = Finset.univ := by
  ext i
  simp only [lowerBand, upperBand, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · exact fun _ ↦ True.intro
  · exact fun _ ↦ Classical.em (i.val < M / 2)

theorem disjoint_lowerBand_upperBand (M : Nat) :
    Disjoint (lowerBand M) (upperBand M) := by
  rw [Finset.disjoint_left]
  simp [lowerBand, upperBand]

/-- The two-band profile has total energy one. -/
theorem sum_initialEnergyProfile_eq_one {M : Nat} (hM : 2 ≤ M)
    (a : Real) :
    (∑ i : Fin M, initialEnergyProfile M a i) = 1 := by
  have hpartition := lowerBand_union_upperBand M
  have hsum := Finset.sum_union (f := initialEnergyProfile M a)
    (disjoint_lowerBand_upperBand M)
  rw [hpartition] at hsum
  rw [hsum, sum_lowerBand_initialEnergyProfile hM,
    sum_upperBand_initialEnergyProfile hM]
  ring

/-- The profile is separated from uniform energy by a fixed amount. -/
theorem half_amplitude_le_l1Distance_uniform {M : Nat} (hM : 2 ≤ M)
    {a : Real} (ha0 : 0 ≤ a) :
    a / 2 ≤ l1Distance (initialEnergyProfile M a)
      (uniformWeights : Fin M → Real) := by
  have hMpos : 0 < (M : Real) := by positivity
  have hk_le : ((M / 2 : Nat) : Real) / (M : Real) ≤ 1 / 2 := by
    rw [div_le_iff₀ hMpos]
    have hkNat : 2 * (M / 2) ≤ M := by
      simpa [mul_comm] using Nat.div_mul_le_self M 2
    have hkCast : (2 : Real) * ((M / 2 : Nat) : Real) ≤ (M : Real) := by
      exact_mod_cast hkNat
    nlinarith
  have hsector :=
    abs_sectorWeight_sub_le_sectorL1Contribution (lowerBand M)
      (initialEnergyProfile M a) (uniformWeights : Fin M → Real)
  rw [show sectorWeight (lowerBand M) (initialEnergyProfile M a) =
      (1 + a) / 2 by exact sum_lowerBand_initialEnergyProfile hM a,
    sectorWeight_uniformWeights, card_lowerBand, Fintype.card_fin] at hsector
  have hgap : a / 2 ≤
      |(1 + a) / 2 - ((M / 2 : Nat) : Real) / (M : Real)| := by
    rw [abs_of_nonneg]
    · linarith
    · linarith
  exact hgap.trans (hsector.trans
    (sectorL1Contribution_le_l1Distance (lowerBand M)
      (initialEnergyProfile M a) (uniformWeights : Fin M → Real)))

/-- Every mode carries at most `3 / M` energy in the frozen amplitude range. -/
theorem initialEnergyProfile_le_three_div {M : Nat} (hM : 2 ≤ M)
    {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4) (i : Fin M) :
    initialEnergyProfile M a i ≤ 3 / (M : Real) := by
  have hMpos : 0 < (M : Real) := by positivity
  have hkpos := (bandCounts_pos hM).1
  have hlpos := (bandCounts_pos hM).2
  rw [initialEnergyProfile]
  split_ifs with hi
  · have hM_le : M ≤ 2 * (M / 2) + 1 := by omega
    have hk_one : 1 ≤ M / 2 := hkpos
    apply (div_le_div_iff₀
      (by positivity : 0 < (2 * (M / 2 : Nat) : Real)) hMpos).2
    have hM_le_cast : (M : Real) ≤ 2 * ((M / 2 : Nat) : Real) + 1 := by
      exact_mod_cast hM_le
    have hk_one_cast : (1 : Real) ≤ ((M / 2 : Nat) : Real) := by
      exact_mod_cast hk_one
    nlinarith
  · have hM_le : M ≤ 2 * (M - M / 2) := by omega
    apply (div_le_div_iff₀
      (by positivity : 0 < (2 * (M - M / 2 : Nat) : Real)) hMpos).2
    have hnum : 1 - a ≤ 1 := by linarith
    have hM_le_cast : (M : Real) ≤
        2 * ((M - M / 2 : Nat) : Real) := by
      exact_mod_cast hM_le
    nlinarith

/-- A soft subset carries at most three times its fraction of all modes. -/
theorem sum_softSubset_le {M : Nat} (hM : 2 ≤ M)
    {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (soft : Finset (Fin M)) :
    (∑ i ∈ soft, initialEnergyProfile M a i) ≤
      3 * (soft.card : Real) / (M : Real) := by
  calc
    (∑ i ∈ soft, initialEnergyProfile M a i) ≤
        ∑ _i ∈ soft, 3 / (M : Real) :=
      Finset.sum_le_sum fun i _ ↦
        initialEnergyProfile_le_three_div hM ha0 ha1 i
    _ = 3 * (soft.card : Real) / (M : Real) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Any `o(M)` soft layer has vanishing energy under the macroscopic profile. -/
theorem softLayer_energy_tendsto_zero
    (a : Nat → Real) (ha0 : ∀ M, 0 ≤ a M) (ha1 : ∀ M, a M ≤ 1 / 4)
    (soft : ∀ M, Finset (Fin (M + 2)))
    (hsoft : Tendsto
      (fun M ↦ (soft M).card / ((M + 2 : Nat) : Real))
      atTop (nhds 0)) :
    Tendsto
      (fun M ↦ ∑ i ∈ soft M, initialEnergyProfile (M + 2) (a M) i)
      atTop (nhds 0) := by
  have hupper : Tendsto
      (fun M ↦ 3 * ((soft M).card / ((M + 2 : Nat) : Real)))
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hsoft)
  refine squeeze_zero (fun M ↦ Finset.sum_nonneg fun i hi ↦ ?_)
      (fun M ↦ ?_) hupper
  · exact initialEnergyProfile_nonneg (by omega) (ha0 M)
      ((ha1 M).trans (by norm_num)) i
  · simpa [mul_div_assoc] using
      sum_softSubset_le (by omega) (ha0 M) (ha1 M) (soft M)

end

end ArchonPhysics.TwoBandInitialEnergyProfile
