import ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge

/-!
# Localization of direct-branch near resonances

The direct continuum four-wave mismatch factors into the product of the two
pairing distances in sine coordinates.  This module turns that exact
factorization into a quantitative statement: away from the acoustic endpoint
factor, a sufficiently near-resonant direct interaction must lie close to at
least one of the two trivial pairing lines.

The conclusion is deterministic and finite-scale.  It does not estimate the
Umklapp branch and does not assert a kinetic limit.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTDirectNearResonanceLocalization

open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry

noncomputable section

/-- Absolute-value form of the exact direct-branch factorization. -/
theorem abs_directReducedFourWaveMismatch_factor
    (k₀ k₁ k₂ : Real) :
    |directReducedFourWaveMismatch k₀ k₁ k₂| =
      8 * |Real.sin ((k₀ + k₁) / 4)| *
        |Real.sin ((k₂ - k₀) / 4)| *
          |Real.sin ((k₂ - k₁) / 4)| := by
  rw [directReducedFourWaveMismatch_factor]
  simp only [abs_mul]
  norm_num

/-- If the acoustic sum factor is at least `s` and the direct mismatch is at
most `Delta`, then below the displayed threshold one of the two pairing sine
coordinates is smaller than `rho`. -/
theorem directNearResonance_localizes_to_pairing_sine
    {k₀ k₁ k₂ s rho Delta : Real}
    (hs : s ≤ |Real.sin ((k₀ + k₁) / 4)|)
    (hs0 : 0 ≤ s) (hrho : 0 ≤ rho)
    (hnear : |directReducedFourWaveMismatch k₀ k₁ k₂| ≤ Delta)
    (hthreshold : Delta < 8 * s * rho ^ 2) :
    |Real.sin ((k₂ - k₀) / 4)| < rho ∨
      |Real.sin ((k₂ - k₁) / 4)| < rho := by
  let A : Real := |Real.sin ((k₀ + k₁) / 4)|
  let B : Real := |Real.sin ((k₂ - k₀) / 4)|
  let C : Real := |Real.sin ((k₂ - k₁) / 4)|
  have hA0 : 0 ≤ A := abs_nonneg _
  have hB0 : 0 ≤ B := abs_nonneg _
  have hC0 : 0 ≤ C := abs_nonneg _
  by_contra hpairing
  simp only [not_or, not_lt] at hpairing
  have hrhoC : rho * rho ≤ rho * C :=
    mul_le_mul_of_nonneg_left hpairing.2 hrho
  have hrhoBC : rho * C ≤ B * C :=
    mul_le_mul_of_nonneg_right hpairing.1 hC0
  have hrhoSqBC : rho ^ 2 ≤ B * C := by
    rw [pow_two]
    exact hrhoC.trans hrhoBC
  have hsBC : s * (B * C) ≤ A * (B * C) :=
    mul_le_mul_of_nonneg_right hs (mul_nonneg hB0 hC0)
  have hsrhoSq : s * rho ^ 2 ≤ s * (B * C) :=
    mul_le_mul_of_nonneg_left hrhoSqBC hs0
  have heightrhoSq : 8 * (s * rho ^ 2) ≤ 8 * (s * (B * C)) :=
    mul_le_mul_of_nonneg_left hsrhoSq (by norm_num)
  have heightBC : 8 * (s * (B * C)) ≤ 8 * (A * (B * C)) :=
    mul_le_mul_of_nonneg_left hsBC (by norm_num)
  have hlower : 8 * s * rho ^ 2 ≤ 8 * A * B * C := by
    calc
      8 * s * rho ^ 2 = 8 * (s * rho ^ 2) := by ring
      _ ≤ 8 * (s * (B * C)) := heightrhoSq
      _ ≤ 8 * (A * (B * C)) := heightBC
      _ = 8 * A * B * C := by ring
  have habs : |directReducedFourWaveMismatch k₀ k₁ k₂| =
      8 * A * B * C := by
    simpa [A, B, C] using
      abs_directReducedFourWaveMismatch_factor k₀ k₁ k₂
  rw [habs] at hnear
  linarith

/-- Equivalent contrapositive: separation from both pairing lines forces a
strict mismatch lower bound. -/
theorem directMismatch_gt_of_pairing_sine_separated
    {k₀ k₁ k₂ s rho : Real}
    (hs : s ≤ |Real.sin ((k₀ + k₁) / 4)|)
    (hs0 : 0 ≤ s) (hrho : 0 ≤ rho)
    (hleft : rho ≤ |Real.sin ((k₂ - k₀) / 4)|)
    (hright : rho ≤ |Real.sin ((k₂ - k₁) / 4)|) :
    8 * s * rho ^ 2 ≤
      |directReducedFourWaveMismatch k₀ k₁ k₂| := by
  let A : Real := |Real.sin ((k₀ + k₁) / 4)|
  let B : Real := |Real.sin ((k₂ - k₀) / 4)|
  let C : Real := |Real.sin ((k₂ - k₁) / 4)|
  have hB0 : 0 ≤ B := abs_nonneg _
  have hC0 : 0 ≤ C := abs_nonneg _
  have hrhoC : rho * rho ≤ rho * C :=
    mul_le_mul_of_nonneg_left hright hrho
  have hrhoBC : rho * C ≤ B * C :=
    mul_le_mul_of_nonneg_right hleft hC0
  have hrhoSqBC : rho ^ 2 ≤ B * C := by
    rw [pow_two]
    exact hrhoC.trans hrhoBC
  have hsBC : s * (B * C) ≤ A * (B * C) :=
    mul_le_mul_of_nonneg_right hs (mul_nonneg hB0 hC0)
  have hsrhoSq : s * rho ^ 2 ≤ s * (B * C) :=
    mul_le_mul_of_nonneg_left hrhoSqBC hs0
  have heightrhoSq : 8 * (s * rho ^ 2) ≤ 8 * (s * (B * C)) :=
    mul_le_mul_of_nonneg_left hsrhoSq (by norm_num)
  have heightBC : 8 * (s * (B * C)) ≤ 8 * (A * (B * C)) :=
    mul_le_mul_of_nonneg_left hsBC (by norm_num)
  rw [abs_directReducedFourWaveMismatch_factor]
  change 8 * s * rho ^ 2 ≤ 8 * A * B * C
  calc
    8 * s * rho ^ 2 = 8 * (s * rho ^ 2) := by ring
    _ ≤ 8 * (s * (B * C)) := heightrhoSq
    _ ≤ 8 * (A * (B * C)) := heightBC
    _ = 8 * A * B * C := by ring

end

end ArchonPhysics.EqualMassPeriodicFPUTDirectNearResonanceLocalization
