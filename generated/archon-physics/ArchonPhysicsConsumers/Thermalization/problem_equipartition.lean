import Mathlib
import ArchonPhysics
import Physlib.StatisticalMechanics.CanonicalEnsemble.Basic

/-! Finite monitored-mode observables for approximate equipartition. -/

namespace ArchonPhysics.Generated.Equipartition

noncomputable section

/-- A nonnegative modal-energy vector. -/
structure ModalEnergies (ι : Type*) where
  energy : ι → ℝ
  nonneg : ∀ k, 0 ≤ energy k

/-- The average energy of mode `k` over the late-time window `[μT,T]`. -/
def lateWindowAverage {ι : Type*} (E : ℝ → ι → ℝ) (μ T : ℝ) (k : ι) : ℝ :=
  ((1 - μ) * T)⁻¹ * ∫ t in μ * T..T, E t k

/-- The total energy in a finite monitored set. -/
def totalEnergy {ι : Type*} [Fintype ι] (e : ι → ℝ) : ℝ :=
  ∑ k, e k

/-- Normalized modal weights, defined when the total monitored energy is nonzero. -/
def normalizedWeight {ι : Type*} [Fintype ι] (e : ι → ℝ) (k : ι) : ℝ :=
  e k / totalEnergy e

/-- The `ℓ¹` distance of modal weights to the uniform distribution. -/
def equipartitionDistance {ι : Type*} [Fintype ι] (e : ι → ℝ) : ℝ :=
  ∑ k, |normalizedWeight e k - (Fintype.card ι : ℝ)⁻¹|

/-- Approximate equipartition at tolerance `δ`. -/
def ApproximatelyEquipartitioned {ι : Type*} [Fintype ι] (e : ι → ℝ) (tolerance : ℝ) : Prop :=
  equipartitionDistance e ≤ tolerance

/-- Normalization and an elementary `ℓ¹` bound for the finite monitored modes. -/
theorem equipartition_physics_formalization_target
    {ι : Type*} [Fintype ι] [Nonempty ι] (e : ModalEnergies ι)
    (htotal : totalEnergy e.energy ≠ 0) :
    (∑ k, normalizedWeight e.energy k) = 1 ∧
      0 ≤ equipartitionDistance e.energy ∧
        equipartitionDistance e.energy ≤ 2 := by
  have htotal_nonneg : 0 ≤ totalEnergy e.energy := by
    unfold totalEnergy
    exact Finset.sum_nonneg fun k _ => e.nonneg k
  have htotal_pos : 0 < totalEnergy e.energy :=
    lt_of_le_of_ne htotal_nonneg (Ne.symm htotal)
  have hweight_nonneg : ∀ k, 0 ≤ normalizedWeight e.energy k := by
    intro k
    exact div_nonneg (e.nonneg k) (le_of_lt htotal_pos)
  have hsum : (∑ k, normalizedWeight e.energy k) = 1 := by
    calc
      (∑ k, normalizedWeight e.energy k) =
          (∑ k, e.energy k) / totalEnergy e.energy := by
            simp only [normalizedWeight, Finset.sum_div]
      _ = totalEnergy e.energy / totalEnergy e.energy := by rfl
      _ = 1 := div_self htotal
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have huniform : ∑ _k : ι, (Fintype.card ι : ℝ)⁻¹ = 1 := by
    calc
      (∑ _k : ι, (Fintype.card ι : ℝ)⁻¹) =
          (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ)⁻¹ := by simp
      _ = 1 := mul_inv_cancel₀ hcard
  refine ⟨hsum, ?_, ?_⟩
  · unfold equipartitionDistance
    exact Finset.sum_nonneg fun k _ => abs_nonneg _
  · calc
      equipartitionDistance e.energy =
          ∑ k, |normalizedWeight e.energy k - (Fintype.card ι : ℝ)⁻¹| := rfl
      _ ≤ ∑ k, (normalizedWeight e.energy k + (Fintype.card ι : ℝ)⁻¹) := by
        exact Finset.sum_le_sum fun k _ => by
          calc
            |normalizedWeight e.energy k - (Fintype.card ι : ℝ)⁻¹| ≤
                |normalizedWeight e.energy k| + |(Fintype.card ι : ℝ)⁻¹| :=
              calc
                |normalizedWeight e.energy k - (Fintype.card ι : ℝ)⁻¹| =
                    |normalizedWeight e.energy k + -(Fintype.card ι : ℝ)⁻¹| := by
                      rw [sub_eq_add_neg]
                _ ≤ |normalizedWeight e.energy k| + |-(Fintype.card ι : ℝ)⁻¹| :=
                  abs_add_le _ _
                _ = |normalizedWeight e.energy k| + |(Fintype.card ι : ℝ)⁻¹| := by
                  rw [abs_neg]
            _ = normalizedWeight e.energy k + (Fintype.card ι : ℝ)⁻¹ := by
              rw [abs_of_nonneg (hweight_nonneg k),
                abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))]
      _ = (∑ k, normalizedWeight e.energy k) +
          ∑ k, (Fintype.card ι : ℝ)⁻¹ := Finset.sum_add_distrib
      _ = 2 := by rw [hsum, huniform]; norm_num

end

end ArchonPhysics.Generated.Equipartition
