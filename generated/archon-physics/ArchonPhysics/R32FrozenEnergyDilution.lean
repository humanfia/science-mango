import ArchonPhysics.FrozenTwoBandUnitTwistGain

/-!
# R32: deterministic dilution of the frozen two-band energy profile

The frozen v0.3 initial state uses contrast `1 / 4` on the first `N - 1`
ordered modes and assigns zero energy to the final translation mode.  This
file packages the exact deterministic estimates needed by volume-counting
arguments:

* total energy is exactly one;
* every ordered-mode energy is at most `3 / (N - 1)`;
* the squared `l2` mass of the energy vector is at most the same envelope;
* the corresponding square-root amplitudes have squared `l2` mass one and
  sup norm at most `sqrt (3 / (N - 1))`.

All substantive profile facts are reused from the existing exact two-band
lemmas.  No randomness, dynamics, limiting argument, or thermalization claim
is introduced here.
-/

namespace ArchonPhysics.R32FrozenEnergyDilution

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.FrozenTwoBandUnitTwistGain
open ArchonPhysics.OrderedPositiveInitialEnergyProfile
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPositiveCollisionData

noncomputable section

/-- The deterministic frozen-quarter energy on every ordered mode, including
the zero-energy translation mode. -/
def frozenTwoBandEnergy
    (N : Nat) [NeZero N] (mode : OrderedModeIndex N) : Real :=
  orderedTargetEnergy N (1 / 4) mode

/-- The nonnegative scalar amplitude whose square is the prescribed modal
energy. -/
def frozenTwoBandAmplitude
    (N : Nat) [NeZero N] (mode : OrderedModeIndex N) : Real :=
  Real.sqrt (frozenTwoBandEnergy N mode)

/-- Every coordinate of the frozen profile is nonnegative. -/
theorem frozenTwoBandEnergy_nonneg
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (mode : OrderedModeIndex N) :
    0 <= frozenTwoBandEnergy N mode := by
  unfold frozenTwoBandEnergy orderedTargetEnergy
  exact orderedPositiveInitialEnergyProfile_nonneg hN (by norm_num)
    (by norm_num) _

/-- The complete frozen profile, with the translation coordinate included,
has exactly unit total energy. -/
theorem sum_frozenTwoBandEnergy_eq_one
    {N : Nat} [NeZero N] (hN : 3 <= N) :
    (∑ mode : OrderedModeIndex N, frozenTwoBandEnergy N mode) = 1 := by
  simpa [frozenTwoBandEnergy] using
    (sum_orderedTargetEnergy_eq_one hN (1 / 4 : Real))

/-- Exact inverse-volume envelope for each frozen ordered-mode energy. -/
theorem frozenTwoBandEnergy_le_three_div_pred
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (mode : OrderedModeIndex N) :
    frozenTwoBandEnergy N mode <=
      3 / (((N - 1 : Nat) : Real)) := by
  simpa [frozenTwoBandEnergy] using
    (orderedTargetEnergy_le_three_div_pred hN
      (by norm_num : (0 : Real) <= 1 / 4)
      (by norm_num : (1 / 4 : Real) <= 1 / 4) mode)

/-- The energy vector's squared `l2` mass gains one inverse volume. -/
theorem sum_sq_frozenTwoBandEnergy_le_three_div_pred
    {N : Nat} [NeZero N] (hN : 3 <= N) :
    (∑ mode : OrderedModeIndex N, (frozenTwoBandEnergy N mode) ^ 2) <=
      3 / (((N - 1 : Nat) : Real)) := by
  have hpoint : ∀ mode : OrderedModeIndex N,
      (frozenTwoBandEnergy N mode) ^ 2 <=
        (3 / (((N - 1 : Nat) : Real))) *
          frozenTwoBandEnergy N mode := by
    intro mode
    have hnonneg := frozenTwoBandEnergy_nonneg hN mode
    have hupper := frozenTwoBandEnergy_le_three_div_pred hN mode
    simpa [pow_two] using mul_le_mul_of_nonneg_right hupper hnonneg
  calc
    (∑ mode : OrderedModeIndex N, (frozenTwoBandEnergy N mode) ^ 2) <=
        ∑ mode : OrderedModeIndex N,
          (3 / (((N - 1 : Nat) : Real))) *
            frozenTwoBandEnergy N mode :=
      Finset.sum_le_sum fun mode _hmode => hpoint mode
    _ = (3 / (((N - 1 : Nat) : Real))) *
        ∑ mode : OrderedModeIndex N, frozenTwoBandEnergy N mode := by
      rw [Finset.mul_sum]
    _ = 3 / (((N - 1 : Nat) : Real)) := by
      rw [sum_frozenTwoBandEnergy_eq_one hN, mul_one]

/-- Square-root form of the energy-vector `l2` dilution bound. -/
theorem sqrt_sum_sq_frozenTwoBandEnergy_le
    {N : Nat} [NeZero N] (hN : 3 <= N) :
    Real.sqrt
        (∑ mode : OrderedModeIndex N,
          (frozenTwoBandEnergy N mode) ^ 2) <=
      Real.sqrt (3 / (((N - 1 : Nat) : Real))) := by
  exact Real.sqrt_le_sqrt
    (sum_sq_frozenTwoBandEnergy_le_three_div_pred hN)

/-- The maximum energy coordinate, represented by the finite-function sup
norm, obeys the same inverse-volume envelope. -/
theorem norm_frozenTwoBandEnergy_le_three_div_pred
    {N : Nat} [NeZero N] (hN : 3 <= N) :
    ‖frozenTwoBandEnergy N‖ <=
      3 / (((N - 1 : Nat) : Real)) := by
  have henvelope : 0 <= 3 / (((N - 1 : Nat) : Real)) := by
    positivity
  refine (pi_norm_le_iff_of_nonneg henvelope).2 ?_
  intro mode
  rw [Real.norm_eq_abs, abs_of_nonneg (frozenTwoBandEnergy_nonneg hN mode)]
  exact frozenTwoBandEnergy_le_three_div_pred hN mode

/-- Frozen square-root amplitudes are nonnegative. -/
theorem frozenTwoBandAmplitude_nonneg
    {N : Nat} [NeZero N] (mode : OrderedModeIndex N) :
    0 <= frozenTwoBandAmplitude N mode := by
  exact Real.sqrt_nonneg _

/-- Each square-root amplitude squares back to the exact frozen energy. -/
theorem frozenTwoBandAmplitude_sq
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (mode : OrderedModeIndex N) :
    (frozenTwoBandAmplitude N mode) ^ 2 =
      frozenTwoBandEnergy N mode := by
  exact Real.sq_sqrt (frozenTwoBandEnergy_nonneg hN mode)

/-- The amplitude vector has exactly unit squared `l2` norm. -/
theorem sum_sq_frozenTwoBandAmplitude_eq_one
    {N : Nat} [NeZero N] (hN : 3 <= N) :
    (∑ mode : OrderedModeIndex N,
      (frozenTwoBandAmplitude N mode) ^ 2) = 1 := by
  calc
    (∑ mode : OrderedModeIndex N,
        (frozenTwoBandAmplitude N mode) ^ 2) =
        ∑ mode : OrderedModeIndex N, frozenTwoBandEnergy N mode := by
      apply Finset.sum_congr rfl
      intro mode _hmode
      exact frozenTwoBandAmplitude_sq hN mode
    _ = 1 := sum_frozenTwoBandEnergy_eq_one hN

/-- Every square-root amplitude is diluted by the square root of the
inverse-volume energy envelope. -/
theorem frozenTwoBandAmplitude_le_sqrt_three_div_pred
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (mode : OrderedModeIndex N) :
    frozenTwoBandAmplitude N mode <=
      Real.sqrt (3 / (((N - 1 : Nat) : Real))) := by
  exact Real.sqrt_le_sqrt
    (frozenTwoBandEnergy_le_three_div_pred hN mode)

/-- Max-amplitude dilution, expressed as the sup norm of the complete finite
amplitude vector. -/
theorem norm_frozenTwoBandAmplitude_le_sqrt_three_div_pred
    {N : Nat} [NeZero N] (hN : 3 <= N) :
    ‖frozenTwoBandAmplitude N‖ <=
      Real.sqrt (3 / (((N - 1 : Nat) : Real))) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 ?_
  intro mode
  rw [Real.norm_eq_abs,
    abs_of_nonneg (frozenTwoBandAmplitude_nonneg mode)]
  exact frozenTwoBandAmplitude_le_sqrt_three_div_pred hN mode

end

end ArchonPhysics.R32FrozenEnergyDilution
