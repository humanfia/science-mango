import ArchonPhysics.ActualSixSiteNearResonantModularCompanionCertificate

/-! A kernel-clean characteristic-quintic certificate for the modular companion. -/

open scoped Matrix

namespace ArchonPhysics.ActualSixSiteNearResonantModularCompanionQuintic

open ArchonPhysics.ActualSixSiteNearResonantModularCertificate
open ArchonPhysics.ActualSixSiteNearResonantModularCompanionCertificate

def matrixQuintic103 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (ZMod 103)) : Matrix ι ι (ZMod 103) :=
  M ^ 5 + (92 : ZMod 103) • M ^ 4 + (20 : ZMod 103) • M ^ 3 +
    (14 : ZMod 103) • M ^ 2 + (80 : ZMod 103) • M + (76 : ZMod 103) • 1

/-- The quotient companion is annihilated by its defining quintic.  The
proof checks only the origin column and transports it through the cyclic
basis, rather than deciding equality of all entries of all matrix powers. -/
theorem matrixQuintic103_companion103 : matrixQuintic103 companion103 = 0 := by
  have horigin : ∀ i : Fin 5, matrixQuintic103 companion103 i 0 = 0 := by
    intro i
    simp only [matrixQuintic103, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply]
    rw [companion103_pow_column_eq_reducedPower ⟨5, by omega⟩ i,
      companion103_pow_column_eq_reducedPower ⟨4, by omega⟩ i,
      companion103_pow_column_eq_reducedPower ⟨3, by omega⟩ i,
      companion103_pow_column_eq_reducedPower ⟨2, by omega⟩ i]
    fin_cases i <;>
      simp [reducedPower103, reducedPowerArray103, companion103] <;> reduce_mod_char
  have hpow (j : Fin 5) (n : Nat) :
      companion103 ^ n * companion103 ^ j.val =
        companion103 ^ j.val * companion103 ^ n := by
    rw [← pow_add, ← pow_add, add_comm n j.val]
  have hcomm (j : Fin 5) :
      matrixQuintic103 companion103 * companion103 ^ j.val =
        companion103 ^ j.val * matrixQuintic103 companion103 := by
    unfold matrixQuintic103
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
    rw [hpow j 5, hpow j 4, hpow j 3, hpow j 2]
    have hone : companion103 * companion103 ^ j.val =
        companion103 ^ j.val * companion103 := by
      simpa only [pow_one] using hpow j 1
    rw [hone]
    simp
  apply funext
  intro i
  apply funext
  intro j
  calc
    matrixQuintic103 companion103 i j =
        (matrixQuintic103 companion103 * companion103 ^ j.val) i 0 := by
      rw [Matrix.mul_apply']
      have hcol : (fun k => (companion103 ^ j.val) k 0) = Pi.single j 1 := by
        funext k
        simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using
          companion103_pow_column_origin j k
      rw [hcol, dotProduct_single_one]
    _ = (companion103 ^ j.val * matrixQuintic103 companion103) i 0 := by
      rw [hcomm j]
    _ = 0 := by
      rw [Matrix.mul_apply]
      simp_rw [horigin]
      simp
    _ = (0 : Matrix (Fin 5) (Fin 5) (ZMod 103)) i j := rfl

end ArchonPhysics.ActualSixSiteNearResonantModularCompanionQuintic
