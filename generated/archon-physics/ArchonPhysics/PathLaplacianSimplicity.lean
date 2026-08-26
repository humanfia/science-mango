import ArchonPhysics.PathLaplacianSpecialization

namespace ArchonPhysics.PathLaplacianSimplicity

open ArchonPhysics.PathLaplacianSpecialization
open ArchonPhysics.GenericSpectrumResultant

noncomputable section

/-- An eigenvector of the broken-cycle path Laplacian is determined by its
first coordinate.  In particular, if that coordinate is zero, the vector is
zero. -/
theorem path_eigenvector_zero_of_zero_first
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (q : Lattice.Configuration N) (lambda : Real)
    (heigen : Matrix.mulVec (weightedCycleLaplacian pathWeight) q = lambda • q)
    (hq0 : q 0 = 0) : q = 0 := by
  have hone : (1 : Lattice.Site N) ≠ 0 := by
    rw [Ne, ZMod.one_eq_zero_iff]
    omega
  have hq1 : q (1 : Lattice.Site N) = 0 := by
    have hrow := congrFun heigen (0 : Lattice.Site N)
    rw [weightedCycleLaplacian_mulVec] at hrow
    simp [pathWeight, hone, hq0] at hrow
    linarith
  have hall : ∀ k : Nat, k < N → q (k : Lattice.Site N) = 0 := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero =>
        intro _
        simpa using hq0
    | one =>
        intro _
        simpa using hq1
    | more k hk hk1 =>
        intro hk2N
        have hkN : k < N := by omega
        have hk1N : k + 1 < N := by omega
        have hk0 : ((k + 1 : Nat) : Lattice.Site N) ≠ 0 := by
          change ((k + 1 : Nat) : ZMod N) ≠ 0
          rw [Ne, ZMod.natCast_eq_zero_iff]
          exact Nat.not_dvd_of_pos_of_lt (by omega) hk1N
        have hk20 : ((k + 2 : Nat) : Lattice.Site N) ≠ 0 := by
          change ((k + 2 : Nat) : ZMod N) ≠ 0
          rw [Ne, ZMod.natCast_eq_zero_iff]
          exact Nat.not_dvd_of_pos_of_lt (by omega) hk2N
        have hprev :
            (((k + 1 : Nat) : Lattice.Site N) - 1) = (k : Lattice.Site N) := by
          push_cast
          ring
        have hnext :
            (((k + 1 : Nat) : Lattice.Site N) + 1) =
              ((k + 2 : Nat) : Lattice.Site N) := by
          push_cast
          ring
        have hrow := congrFun heigen ((k + 1 : Nat) : Lattice.Site N)
        rw [weightedCycleLaplacian_mulVec] at hrow
        change
          pathWeight (((k + 1 : Nat) : Lattice.Site N) + 1) *
              (q ((k + 1 : Nat) : Lattice.Site N) -
                q (((k + 1 : Nat) : Lattice.Site N) + 1)) +
            pathWeight ((k + 1 : Nat) : Lattice.Site N) *
              (q ((k + 1 : Nat) : Lattice.Site N) -
                q (((k + 1 : Nat) : Lattice.Site N) - 1)) =
            lambda * q ((k + 1 : Nat) : Lattice.Site N) at hrow
        rw [hprev, hnext] at hrow
        have hqk := hk hkN
        have hqk1 := hk1 hk1N
        simp only [pathWeight] at hrow
        rw [if_neg hk20, if_neg hk0, hqk, hqk1] at hrow
        norm_num at hrow
        simpa only [Nat.cast_add, Nat.cast_ofNat] using hrow
  ext i
  have hi : i.val < N := i.val_lt
  have hz := hall i.val hi
  simpa [ZMod.natCast_zmod_val] using hz

end

end ArchonPhysics.PathLaplacianSimplicity
