import Mathlib
import ArchonPhysics
import Physlib.StatisticalMechanics.CanonicalEnsemble.Basic

/-! Spectral entropy and participation observables for finite modal energies. -/

namespace ArchonPhysics.Generated.Entropy

noncomputable section

/-- The `0 \cdot \log 0 = 0` entropy summand. -/
def entropySummand (x : ℝ) : ℝ :=
  if x = 0 then 0 else -x * Real.log x

/-- Spectral entropy of a finite normalized modal-energy vector. -/
def spectralEntropy {ι : Type*} [Fintype ι] (w : ι → ℝ) : ℝ :=
  ∑ k, entropySummand (w k)

/-- Entropy deficit relative to the uniform distribution on the monitored modes. -/
def entropyDeficit {ι : Type*} [Fintype ι] (w : ι → ℝ) : ℝ :=
  Real.log (Fintype.card ι) - spectralEntropy w

/-- The inverse participation number, with zero value for the zero vector. -/
def participationNumber {ι : Type*} [Fintype ι] (w : ι → ℝ) : ℝ :=
  (∑ k, w k ^ 2)⁻¹

/-- The uniform modal-energy vector. -/
def uniformWeight (ι : Type*) [Fintype ι] : ι → ℝ :=
  fun _ => (Fintype.card ι : ℝ)⁻¹

/-- Elementary entropy facts promised for finite nonnegative normalized weights. -/
theorem entropy_physics_formalization_target
    {ι : Type*} [Fintype ι] [Nonempty ι] (w : ι → ℝ)
    (hnonneg : ∀ k, 0 ≤ w k) (hnorm : (∑ k, w k) = 1) :
    0 ≤ spectralEntropy w ∧
      spectralEntropy (uniformWeight ι) = Real.log (Fintype.card ι) := by
  constructor
  · unfold spectralEntropy
    apply Finset.sum_nonneg
    intro k _
    unfold entropySummand
    split_ifs with hk
    · positivity
    · have hk_le_sum : w k ≤ ∑ i, w i :=
        Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ k)
      rw [hnorm] at hk_le_sum
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (hnonneg k))
        (Real.log_nonpos (hnonneg k) hk_le_sum)
  · have hcard_pos : (0 : ℝ) < Fintype.card ι := by
      exact_mod_cast Fintype.card_pos
    have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hcard_pos
    rw [spectralEntropy]
    simp only [uniformWeight]
    simp [entropySummand, hcard_ne, Real.log_inv, Finset.sum_const,
      Finset.card_univ]

end

end ArchonPhysics.Generated.Entropy
