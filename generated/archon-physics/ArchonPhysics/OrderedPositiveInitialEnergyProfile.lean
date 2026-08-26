import ArchonPhysics.TwoBandInitialEnergyProfile
import ArchonPhysics.OrderedTranslationLastMode

/-!
# A deterministic nonequilibrium profile on all ordered harmonic indices

Because the translation zero mode is the fixed last ordered index, a profile
on `Fin (N - 1)` can be lifted to all `Fin N` ordered indices by assigning
zero energy to the last index.  The lift is deterministic: it does not depend
on the random masses and therefore introduces no measurable-selection issue.

The profile remains nonnegative, has total energy one, and retains the exact
`l1` separation from positive-mode equipartition proved in
`TwoBandInitialEnergyProfile`.
-/

namespace ArchonPhysics.OrderedPositiveInitialEnergyProfile

open ArchonPhysics
open ArchonPhysics.TwoBandInitialEnergyProfile
open ArchonPhysics.OrderedTranslationLastMode
open scoped BigOperators

noncomputable section

/-- Lift the frozen profile from the first `N - 1` ordered modes to all
ordered modes, assigning zero to the final translation mode. -/
def orderedPositiveInitialEnergyProfile
    (N : Nat) (a : Real) (k : Fin N) : Real :=
  if hk : k.val < N - 1 then
    initialEnergyProfile (N - 1) a ⟨k.val, hk⟩
  else 0

/-- Uniform weight on the first `N - 1` modes and zero on the final
translation mode. -/
def orderedPositiveUniformWeight (N : Nat) (k : Fin N) : Real :=
  if k.val < N - 1 then ((N - 1 : Nat) : Real)⁻¹ else 0

/-- The last site-ordered index, represented directly in `Fin N`. -/
def lastSiteOrderedIndex (N : Nat) [NeZero N] : Fin N :=
  ⟨N - 1, by have := NeZero.ne N; omega⟩

/-- A non-last ordered index canonically becomes an index of `Fin (N - 1)`. -/
def dropLastOrderedIndex {N : Nat} [NeZero N]
    (k : Fin N)
    (hk : k ≠ lastSiteOrderedIndex N) : Fin (N - 1) :=
  ⟨k.val, by
    have hkval : k.val ≠ N - 1 := by
      intro heq
      apply hk
      apply Fin.ext
      simpa [lastSiteOrderedIndex] using heq
    omega⟩

/-- Away from the last mode, the lifted profile is exactly the original
`Fin (N - 1)` profile at the canonical dropped index. -/
theorem orderedPositiveInitialEnergyProfile_of_ne_last
    {N : Nat} [NeZero N] (a : Real) (k : Fin N)
    (hk : k ≠ lastSiteOrderedIndex N) :
    orderedPositiveInitialEnergyProfile N a k =
      initialEnergyProfile (N - 1) a (dropLastOrderedIndex k hk) := by
  have hklt : k.val < N - 1 := (dropLastOrderedIndex k hk).isLt
  rw [orderedPositiveInitialEnergyProfile, dif_pos hklt]
  rfl

/-- The deterministic last ordered mode receives exactly zero energy. -/
@[simp] theorem orderedPositiveInitialEnergyProfile_last
    {N : Nat} [NeZero N] (a : Real) :
    orderedPositiveInitialEnergyProfile N a
      (lastSiteOrderedIndex N) = 0 := by
  simp [orderedPositiveInitialEnergyProfile, lastSiteOrderedIndex]

/-- The positive uniform mask also vanishes at the translation mode. -/
@[simp] theorem orderedPositiveUniformWeight_last
    {N : Nat} [NeZero N] :
    orderedPositiveUniformWeight N
      (lastSiteOrderedIndex N) = 0 := by
  simp [orderedPositiveUniformWeight, lastSiteOrderedIndex]

/-- Nonnegativity is inherited from the two-band positive-mode profile. -/
theorem orderedPositiveInitialEnergyProfile_nonneg
    {N : Nat} (hN : 3 ≤ N) {a : Real}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4) (k : Fin N) :
    0 ≤ orderedPositiveInitialEnergyProfile N a k := by
  unfold orderedPositiveInitialEnergyProfile
  split_ifs with hk
  · exact initialEnergyProfile_nonneg (by omega) ha0
      (ha1.trans (by norm_num)) _
  · exact le_rfl

/-- The lifted profile has total energy exactly one. -/
theorem sum_orderedPositiveInitialEnergyProfile_eq_one
    {N : Nat} (hN : 3 ≤ N) (a : Real) :
    (∑ k : Fin N, orderedPositiveInitialEnergyProfile N a k) = 1 := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  rw [Fin.sum_univ_castSucc]
  have hsum :
      (∑ k : Fin M,
        orderedPositiveInitialEnergyProfile M.succ a k.castSucc) =
        ∑ k : Fin M, initialEnergyProfile M a k := by
    apply Finset.sum_congr rfl
    intro k _hk
    have hklt : k.castSucc.val < M.succ - 1 := by simp
    rw [orderedPositiveInitialEnergyProfile, dif_pos hklt]
    rfl
  have hlast : orderedPositiveInitialEnergyProfile M.succ a (Fin.last M) = 0 := by
    unfold orderedPositiveInitialEnergyProfile
    rw [dif_neg]
    simp
  rw [hsum, hlast, add_zero]
  exact sum_initialEnergyProfile_eq_one (by omega) a

/-- The lifted `l1` distance from positive-mode uniformity is exactly the
original `Fin (N - 1)` distance. -/
theorem orderedPositive_l1_eq_initialEnergyProfile_l1
    {N : Nat} [NeZero N] (a : Real) :
    (∑ k : Fin N,
      |orderedPositiveInitialEnergyProfile N a k -
        orderedPositiveUniformWeight N k|) =
      ∑ i : Fin (N - 1),
        |initialEnergyProfile (N - 1) a i -
          1 / ((N - 1 : Nat) : Real)| := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  rw [Fin.sum_univ_castSucc]
  have hsum :
      (∑ k : Fin M,
        |orderedPositiveInitialEnergyProfile M.succ a k.castSucc -
          orderedPositiveUniformWeight M.succ k.castSucc|) =
        ∑ k : Fin M,
          |initialEnergyProfile M a k - 1 / (M : Real)| := by
    apply Finset.sum_congr rfl
    intro k _hk
    simp [orderedPositiveInitialEnergyProfile,
      orderedPositiveUniformWeight, k.isLt]
  rw [hsum]
  simp [orderedPositiveInitialEnergyProfile, orderedPositiveUniformWeight]

/-- At the frozen amplitude `1/4`, the lifted profile stays uniformly away
from equipartition on the positive modes. -/
theorem quarterAmplitude_orderedPositive_l1_lower
    {N : Nat} (hN : 3 ≤ N) :
    (1 / 8 : Real) ≤
      ∑ k : Fin N,
        |orderedPositiveInitialEnergyProfile N (1 / 4) k -
          orderedPositiveUniformWeight N k| := by
  have hne : NeZero N := ⟨by omega⟩
  let _ : NeZero N := hne
  rw [orderedPositive_l1_eq_initialEnergyProfile_l1]
  have h := half_amplitude_le_l1Distance_uniform
    (M := N - 1) (by omega) (a := (1 / 4 : Real)) (by norm_num)
  norm_num at h ⊢
  simpa [EquipartitionEntropy.l1Distance,
    EquipartitionEntropy.uniformWeights, one_div] using h

end

end ArchonPhysics.OrderedPositiveInitialEnergyProfile
