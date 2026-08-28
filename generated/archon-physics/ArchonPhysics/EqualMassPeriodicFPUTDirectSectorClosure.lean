import ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge
import ArchonPhysics.EqualMassPeriodicFPUTTrivialPairingCollisionCancellation

/-!
# Equal-mass periodic FPUT: closure of the direct four-wave sector

The continuum direct mismatch has only the two pairing zeros whenever the
sum of its two incoming principal-zone wave numbers is positive.  The sole
endpoint exception to that continuum statement is `k₀ = k₁ = 0`; on the
finite Fourier grid, the exact no-wrap branch identity forces `k₂ = 0` in
that case as well.

Consequently every exactly resonant finite-grid quartet carrying an explicit
direct/no-wrap branch certificate is a trivial pairing, and its four-wave
collision flux vanishes for every action profile.  A final disjunction keeps
the global bridge honest: a zero-mismatch finite configuration is either such
a zero-flux pairing or is identified with the Umklapp analytic branch.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTDirectSectorClosure

open ArchonPhysics
open ArchonPhysics.Lattice
open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell
open ArchonPhysics.EqualMassPeriodicFPUTTrivialPairingCollisionCancellation

noncomputable section

/-! ## Principal-grid endpoint facts -/

@[simp] theorem gridWaveNumber_zero (N : Nat) [NeZero N] :
    gridWaveNumber N (0 : Site N) = 0 := by
  simp [gridWaveNumber]

theorem gridWaveNumber_nonneg
    (N : Nat) [NeZero N] (k : Site N) :
    0 ≤ gridWaveNumber N k := by
  unfold gridWaveNumber
  positivity

theorem gridWaveNumber_pos_of_ne_zero
    {N : Nat} [NeZero N] {k : Site N} (hk : k ≠ 0) :
    0 < gridWaveNumber N k := by
  have hN : (0 : Real) < (N : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hkval : 0 < k.val := Nat.pos_of_ne_zero (by
    intro hval
    apply hk
    apply ZMod.val_injective N
    simp [hval])
  unfold gridWaveNumber
  positivity

theorem gridWaveNumber_lt_two_pi
    (N : Nat) [NeZero N] (k : Site N) :
    gridWaveNumber N k < 2 * Real.pi := by
  have hN : (0 : Real) < (N : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hklt : (k.val : Real) < (N : Real) := by exact_mod_cast k.val_lt
  have hratio : (k.val : Real) / (N : Real) < 1 :=
    (div_lt_one hN).2 hklt
  unfold gridWaveNumber
  calc
    2 * Real.pi * (k.val : Real) / (N : Real) =
        (2 * Real.pi) * ((k.val : Real) / (N : Real)) := by ring
    _ < (2 * Real.pi) * 1 :=
      mul_lt_mul_of_pos_left hratio (by positivity)
    _ = 2 * Real.pi := by ring

@[simp] theorem gridWaveNumber_eq_zero_iff
    {N : Nat} [NeZero N] {k : Site N} :
    gridWaveNumber N k = 0 ↔ k = 0 := by
  constructor
  · intro hgrid
    by_contra hk
    exact (ne_of_gt (gridWaveNumber_pos_of_ne_zero hk)) hgrid
  · rintro rfl
    exact gridWaveNumber_zero N

theorem gridWaveNumber_injective
    (N : Nat) [NeZero N] : Function.Injective (gridWaveNumber N) := by
  intro left right hgrid
  have hN : (0 : Real) < (N : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hscale : (0 : Real) < 2 * Real.pi / (N : Real) := by positivity
  have hscaled :
      (2 * Real.pi / (N : Real)) * (left.val : Real) =
        (2 * Real.pi / (N : Real)) * (right.val : Real) := by
    calc
      (2 * Real.pi / (N : Real)) * (left.val : Real) =
          gridWaveNumber N left := by unfold gridWaveNumber; ring
      _ = gridWaveNumber N right := hgrid
      _ = (2 * Real.pi / (N : Real)) * (right.val : Real) := by
        unfold gridWaveNumber
        ring
  have hvalReal : (left.val : Real) = (right.val : Real) :=
    mul_left_cancel₀ (ne_of_gt hscale) hscaled
  apply ZMod.val_injective N
  exact_mod_cast hvalReal

/-! ## Direct continuum rigidity with the lower endpoint included -/

/-- On the half-open principal zone, the direct mismatch has only the two
pairing zeros as soon as the incoming wave-number sum is positive. -/
theorem directReducedFourWaveMismatch_eq_zero_iff_pairing_of_sum_pos
    {k₀ k₁ k₂ : Real}
    (hk₀0 : 0 ≤ k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 ≤ k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hk₂0 : 0 ≤ k₂) (hk₂2pi : k₂ < 2 * Real.pi)
    (hsum : 0 < k₀ + k₁) :
    directReducedFourWaveMismatch k₀ k₁ k₂ = 0 ↔
      k₂ = k₀ ∨ k₂ = k₁ := by
  rw [directReducedFourWaveMismatch_factor]
  have hsum0 : 0 < (k₀ + k₁) / 4 := by positivity
  have hsumpi : (k₀ + k₁) / 4 < Real.pi := by linarith
  have hsumSin : Real.sin ((k₀ + k₁) / 4) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hsum0 hsumpi)
  have h20lower : -Real.pi < (k₂ - k₀) / 4 := by
    linarith [Real.pi_pos]
  have h20upper : (k₂ - k₀) / 4 < Real.pi := by
    linarith [Real.pi_pos]
  have h21lower : -Real.pi < (k₂ - k₁) / 4 := by
    linarith [Real.pi_pos]
  have h21upper : (k₂ - k₁) / 4 < Real.pi := by
    linarith [Real.pi_pos]
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with hprefix | h21
    · rcases mul_eq_zero.mp hprefix with hprefix | h20
      · rcases mul_eq_zero.mp hprefix with h8 | hsumZero
        · norm_num at h8
        · exact False.elim (hsumSin hsumZero)
      · left
        have hroot := (Real.sin_eq_zero_iff_of_lt_of_lt
          h20lower h20upper).mp h20
        linarith
    · right
      have hroot := (Real.sin_eq_zero_iff_of_lt_of_lt
        h21lower h21upper).mp h21
      linarith
  · rintro (rfl | rfl) <;> simp

/-! ## Finite direct-sector closure and collision cancellation -/

/-- Explicit certificate that eliminating the fourth finite momentum caused
no Brillouin-zone wrap. -/
def FiniteDirectTwoToTwoBranch
    {N : Nat} [NeZero N] (k₀ k₁ k₂ : Site N) : Prop :=
  gridWaveNumber N (k₀ + k₁ - k₂) =
    gridWaveNumber N k₀ + gridWaveNumber N k₁ - gridWaveNumber N k₂

/-- Every exactly resonant finite configuration with a direct/no-wrap
certificate is one of the two trivial pairings, including the zero-mode
endpoint case. -/
theorem finite_direct_zeroMismatch_iff_pairing
    {N : Nat} [NeZero N] (k₀ k₁ k₂ : Site N)
    (hdirect : FiniteDirectTwoToTwoBranch k₀ k₁ k₂) :
    reducedTwoToTwoMismatch k₀ k₁ k₂ = 0 ↔
      k₂ = k₀ ∨ k₂ = k₁ := by
  constructor
  · intro hzero
    by_cases hboth : k₀ = 0 ∧ k₁ = 0
    · rcases hboth with ⟨rfl, rfl⟩
      have hdirect' :
          gridWaveNumber N (-k₂) = -gridWaveNumber N k₂ := by
        simpa [FiniteDirectTwoToTwoBranch] using hdirect
      have hleftNonneg : 0 ≤ gridWaveNumber N (-k₂) :=
        gridWaveNumber_nonneg N (-k₂)
      have hrightNonneg : 0 ≤ gridWaveNumber N k₂ :=
        gridWaveNumber_nonneg N k₂
      have hk₂Grid : gridWaveNumber N k₂ = 0 := by linarith
      have hk₂ : k₂ = 0 := gridWaveNumber_eq_zero_iff.mp hk₂Grid
      exact Or.inl hk₂
    · have hsum :
          0 < gridWaveNumber N k₀ + gridWaveNumber N k₁ := by
        by_cases hk₀ : k₀ = 0
        · have hk₁ : k₁ ≠ 0 := by
            intro hk₁
            exact hboth ⟨hk₀, hk₁⟩
          rw [hk₀, gridWaveNumber_zero]
          simpa using gridWaveNumber_pos_of_ne_zero hk₁
        · exact add_pos_of_pos_of_nonneg
            (gridWaveNumber_pos_of_ne_zero hk₀)
            (gridWaveNumber_nonneg N k₁)
      have hcontinuum :
          directReducedFourWaveMismatch
            (gridWaveNumber N k₀) (gridWaveNumber N k₁)
              (gridWaveNumber N k₂) = 0 := by
        rw [← reducedTwoToTwoMismatch_eq_direct_of_grid_eq
          k₀ k₁ k₂ hdirect]
        exact hzero
      have hpairGrid :=
        (directReducedFourWaveMismatch_eq_zero_iff_pairing_of_sum_pos
          (gridWaveNumber_nonneg N k₀) (gridWaveNumber_lt_two_pi N k₀)
          (gridWaveNumber_nonneg N k₁) (gridWaveNumber_lt_two_pi N k₁)
          (gridWaveNumber_nonneg N k₂) (gridWaveNumber_lt_two_pi N k₂)
          hsum).mp hcontinuum
      rcases hpairGrid with hleft | hright
      · exact Or.inl ((gridWaveNumber_injective N) hleft)
      · exact Or.inr ((gridWaveNumber_injective N) hright)
  · intro hpair
    rcases hpair with hk₂ | hk₂
    · subst k₂
      exact reducedTwoToTwoMismatch_pairing_left k₀ k₁
    · subst k₂
      exact reducedTwoToTwoMismatch_pairing_right k₀ k₁

/-- The direct exactly resonant sector has identically zero collision flux
for every action profile. -/
theorem reducedTwoToTwoCollisionFlux_eq_zero_of_direct_of_zeroMismatch
    {N : Nat} [NeZero N] (action : Site N → Real)
    (k₀ k₁ k₂ : Site N)
    (hdirect : FiniteDirectTwoToTwoBranch k₀ k₁ k₂)
    (hzero : reducedTwoToTwoMismatch k₀ k₁ k₂ = 0) :
    reducedTwoToTwoCollisionFlux action k₀ k₁ k₂ = 0 := by
  rcases (finite_direct_zeroMismatch_iff_pairing k₀ k₁ k₂ hdirect).mp hzero with
    hk₂ | hk₂
  · subst k₂
    exact reducedTwoToTwoCollisionFlux_pairing_left action k₀ k₁
  · subst k₂
    exact reducedTwoToTwoCollisionFlux_pairing_right action k₀ k₁

/-- Honest global branch disjunction: an exact finite resonance is either a
direct trivial pairing or its finite mismatch is represented by the
one-wrap Umklapp analytic branch. -/
theorem zeroMismatch_pairing_or_eq_umklapp
    {N : Nat} [NeZero N] (k₀ k₁ k₂ : Site N)
    (hzero : reducedTwoToTwoMismatch k₀ k₁ k₂ = 0) :
    (k₂ = k₀ ∨ k₂ = k₁) ∨
      reducedTwoToTwoMismatch k₀ k₁ k₂ =
        umklappReducedFourWaveMismatch
          (gridWaveNumber N k₀) (gridWaveNumber N k₁)
            (gridWaveNumber N k₂) := by
  rcases grid_fourth_eq_direct_or_one_wrap k₀ k₁ k₂ with
    hdirect | hlower | hupper
  · exact Or.inl ((finite_direct_zeroMismatch_iff_pairing
      k₀ k₁ k₂ hdirect).mp hzero)
  · exact Or.inr (reducedTwoToTwoMismatch_eq_umklapp_of_grid_eq_add_two_pi
      k₀ k₁ k₂ hlower)
  · exact Or.inr (reducedTwoToTwoMismatch_eq_umklapp_of_grid_eq_sub_two_pi
      k₀ k₁ k₂ hupper)

/-- Flux form of the same honest dichotomy. -/
theorem zeroMismatch_zeroFlux_or_eq_umklapp
    {N : Nat} [NeZero N] (action : Site N → Real)
    (k₀ k₁ k₂ : Site N)
    (hzero : reducedTwoToTwoMismatch k₀ k₁ k₂ = 0) :
    reducedTwoToTwoCollisionFlux action k₀ k₁ k₂ = 0 ∨
      reducedTwoToTwoMismatch k₀ k₁ k₂ =
        umklappReducedFourWaveMismatch
          (gridWaveNumber N k₀) (gridWaveNumber N k₁)
            (gridWaveNumber N k₂) := by
  rcases zeroMismatch_pairing_or_eq_umklapp k₀ k₁ k₂ hzero with
    hpair | humklapp
  · left
    rcases hpair with rfl | rfl <;> simp
  · exact Or.inr humklapp

end

end ArchonPhysics.EqualMassPeriodicFPUTDirectSectorClosure
