import ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell

/-!
# Continuum four-wave geometry of the equal-mass FPUT dispersion

In the thermodynamic parametrization `k ∈ (0, 2π)`, the acoustic dispersion
is `2 sin (k / 2)`.  Eliminating the fourth momentum before or after a
Brillouin-zone wrap gives two different analytic branches.

This module proves exact trigonometric factorizations for both branches.  On
the direct (non-Umklapp) branch, zero mismatch is equivalent to one of the two
trivial pairings.  Hence every genuinely nontrivial continuum resonance must
come from the Umklapp branch, whose explicit formula and transverse
derivative are also recorded.

No Riemann-sum estimate, collision measure, or kinetic limit is asserted.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry

noncomputable section

/-- Continuum acoustic frequency on the principal Brillouin interval. -/
def continuumAcousticFrequency (k : Real) : Real :=
  2 * Real.sin (k / 2)

/-- Four-wave mismatch before wrapping the eliminated fourth momentum. -/
def directReducedFourWaveMismatch (k₀ k₁ k₂ : Real) : Real :=
  continuumAcousticFrequency k₀ + continuumAcousticFrequency k₁ -
    continuumAcousticFrequency k₂ -
      continuumAcousticFrequency (k₀ + k₁ - k₂)

/-- Four-wave mismatch after one Brillouin-zone wrap.  Since shifting the
unwrapped fourth half-angle by `π` reverses its sine, its contribution has
the displayed plus sign. -/
def umklappReducedFourWaveMismatch (k₀ k₁ k₂ : Real) : Real :=
  continuumAcousticFrequency k₀ + continuumAcousticFrequency k₁ -
    continuumAcousticFrequency k₂ +
      continuumAcousticFrequency (k₀ + k₁ - k₂)

private theorem sin_direct_four_wave_factor (x y z : Real) :
    Real.sin x + Real.sin y - Real.sin z - Real.sin (x + y - z) =
      4 * Real.sin ((x + y) / 2) * Real.sin ((z - x) / 2) *
        Real.sin ((z - y) / 2) := by
  calc
    Real.sin x + Real.sin y - Real.sin z - Real.sin (x + y - z) =
        (Real.sin x + Real.sin y) -
          (Real.sin z + Real.sin (x + y - z)) := by ring
    _ = 2 * Real.sin ((x + y) / 2) * Real.cos ((x - y) / 2) -
        2 * Real.sin ((z + (x + y - z)) / 2) *
          Real.cos ((z - (x + y - z)) / 2) := by
      rw [Real.sin_add_sin, Real.sin_add_sin]
    _ = 2 * Real.sin ((x + y) / 2) *
        (Real.cos ((x - y) / 2) -
          Real.cos ((2 * z - x - y) / 2)) := by ring
    _ = 4 * Real.sin ((x + y) / 2) * Real.sin ((z - x) / 2) *
        Real.sin ((z - y) / 2) := by
      rw [Real.cos_sub_cos]
      ring_nf
      rw [show x * (1 / 2 : Real) + z * (-1 / 2 : Real) =
        -(x * (-1 / 2 : Real) + z * (1 / 2 : Real)) by ring,
        Real.sin_neg]
      ring

private theorem sin_umklapp_four_wave_factor (x y z : Real) :
    Real.sin x + Real.sin y - Real.sin z + Real.sin (x + y - z) =
      2 * (Real.sin ((x + y) / 2) * Real.cos ((x - y) / 2) -
        Real.cos ((x + y) / 2) * Real.sin (z - (x + y) / 2)) := by
  calc
    Real.sin x + Real.sin y - Real.sin z + Real.sin (x + y - z) =
        (Real.sin x + Real.sin y) -
          (Real.sin z - Real.sin (x + y - z)) := by ring
    _ = 2 * Real.sin ((x + y) / 2) * Real.cos ((x - y) / 2) -
        2 * Real.sin ((z - (x + y - z)) / 2) *
          Real.cos ((z + (x + y - z)) / 2) := by
      rw [Real.sin_add_sin, Real.sin_sub_sin]
    _ = 2 * (Real.sin ((x + y) / 2) * Real.cos ((x - y) / 2) -
        Real.cos ((x + y) / 2) * Real.sin (z - (x + y) / 2)) := by
      ring

/-- Exact factorization of the direct reduced four-wave mismatch. -/
theorem directReducedFourWaveMismatch_factor
    (k₀ k₁ k₂ : Real) :
    directReducedFourWaveMismatch k₀ k₁ k₂ =
      8 * Real.sin ((k₀ + k₁) / 4) *
        Real.sin ((k₂ - k₀) / 4) *
          Real.sin ((k₂ - k₁) / 4) := by
  unfold directReducedFourWaveMismatch continuumAcousticFrequency
  have h := sin_direct_four_wave_factor (k₀ / 2) (k₁ / 2) (k₂ / 2)
  convert congrArg (fun value : Real ↦ 2 * value) h using 1 <;> ring

/-- Exact analytic equation of the one-wrap Umklapp branch. -/
theorem umklappReducedFourWaveMismatch_factor
    (k₀ k₁ k₂ : Real) :
    umklappReducedFourWaveMismatch k₀ k₁ k₂ =
      4 * (Real.sin ((k₀ + k₁) / 4) *
          Real.cos ((k₀ - k₁) / 4) -
        Real.cos ((k₀ + k₁) / 4) *
          Real.sin ((2 * k₂ - k₀ - k₁) / 4)) := by
  unfold umklappReducedFourWaveMismatch continuumAcousticFrequency
  have h := sin_umklapp_four_wave_factor
    (k₀ / 2) (k₁ / 2) (k₂ / 2)
  convert congrArg (fun value : Real ↦ 2 * value) h using 1 <;> ring

/-- Inside the open Brillouin zone, the direct branch has only the two
pairing resonances `k₂ = k₀` and `k₂ = k₁`. -/
theorem directReducedFourWaveMismatch_eq_zero_iff_pairing
    {k₀ k₁ k₂ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hk₂0 : 0 < k₂) (hk₂2pi : k₂ < 2 * Real.pi) :
    directReducedFourWaveMismatch k₀ k₁ k₂ = 0 ↔
      k₂ = k₀ ∨ k₂ = k₁ := by
  rw [directReducedFourWaveMismatch_factor]
  have hsum0 : 0 < (k₀ + k₁) / 4 := by positivity
  have hsumpi : (k₀ + k₁) / 4 < Real.pi := by linarith
  have hsumSin : Real.sin ((k₀ + k₁) / 4) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hsum0 hsumpi)
  have h20lower : -Real.pi < (k₂ - k₀) / 4 := by linarith
  have h20upper : (k₂ - k₀) / 4 < Real.pi := by linarith
  have h21lower : -Real.pi < (k₂ - k₁) / 4 := by linarith
  have h21upper : (k₂ - k₁) / 4 < Real.pi := by linarith
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with hprefix | h21
    · rcases mul_eq_zero.mp hprefix with hprefix | h20
      · rcases mul_eq_zero.mp hprefix with h8 | hsum
        · norm_num at h8
        · exact False.elim (hsumSin hsum)
      · left
        have := (Real.sin_eq_zero_iff_of_lt_of_lt
          h20lower h20upper).mp h20
        linarith
    · right
      have := (Real.sin_eq_zero_iff_of_lt_of_lt
        h21lower h21upper).mp h21
      linarith
  · intro hpairing
    rcases hpairing with rfl | rfl <;> simp

/-- Derivative of the Umklapp mismatch in the eliminated free momentum. -/
theorem hasDerivAt_umklappReducedFourWaveMismatch_k₂
    (k₀ k₁ k₂ : Real) :
    HasDerivAt (fun z ↦ umklappReducedFourWaveMismatch k₀ k₁ z)
      (-Real.cos (k₂ / 2) -
        Real.cos ((k₀ + k₁ - k₂) / 2)) k₂ := by
  have hk₂ : HasDerivAt
      (fun z : Real ↦ continuumAcousticFrequency z)
      (Real.cos (k₂ / 2)) k₂ := by
    unfold continuumAcousticFrequency
    have hhalf : HasDerivAt (fun z : Real ↦ z / 2) (1 / 2) k₂ :=
      (hasDerivAt_id k₂).div_const 2
    have h := ((Real.hasDerivAt_sin (k₂ / 2)).comp k₂ hhalf).const_mul 2
    have h' := h.congr_deriv (by ring)
    apply h'.congr_of_eventuallyEq
    filter_upwards [] with z
    rfl
  have hinner : HasDerivAt
      (fun z : Real ↦ (k₀ + k₁ - z) / 2) (-1 / 2) k₂ := by
    have h := ((hasDerivAt_const k₂ (k₀ + k₁)).sub
      (hasDerivAt_id k₂)).div_const 2
    simpa only [Pi.sub_apply, id_eq, zero_sub] using h
  have hwrapped : HasDerivAt
      (fun z : Real ↦ continuumAcousticFrequency (k₀ + k₁ - z))
      (-Real.cos ((k₀ + k₁ - k₂) / 2)) k₂ := by
    unfold continuumAcousticFrequency
    have h := ((Real.hasDerivAt_sin ((k₀ + k₁ - k₂) / 2)).comp
      k₂ hinner).const_mul 2
    have h' : HasDerivAt
        (fun y : Real ↦ 2 *
          (Real.sin ∘ fun z : Real ↦ (k₀ + k₁ - z) / 2) y)
        (-Real.cos ((k₀ + k₁ - k₂) / 2)) k₂ :=
      h.congr_deriv (by ring)
    apply h'.congr_of_eventuallyEq
    filter_upwards [] with z
    rfl
  have htotal :=
    ((((hasDerivAt_const k₂ (continuumAcousticFrequency k₀)).add
      (hasDerivAt_const k₂ (continuumAcousticFrequency k₁))).sub hk₂).add
        hwrapped)
  unfold umklappReducedFourWaveMismatch
  have hevent :
      (fun z : Real ↦ continuumAcousticFrequency k₀ +
        continuumAcousticFrequency k₁ - continuumAcousticFrequency z +
          continuumAcousticFrequency (k₀ + k₁ - z)) =ᶠ[nhds k₂]
        ((((fun _ : Real ↦ continuumAcousticFrequency k₀) +
          (fun _ : Real ↦ continuumAcousticFrequency k₁)) -
          (fun z : Real ↦ continuumAcousticFrequency z)) +
          (fun z : Real ↦ continuumAcousticFrequency (k₀ + k₁ - z))) := by
    filter_upwards [] with z
    rfl
  exact (htotal.congr_of_eventuallyEq hevent).congr_deriv (by ring)

end

end ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
