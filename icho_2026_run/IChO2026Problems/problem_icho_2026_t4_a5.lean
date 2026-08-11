import Mathlib

/-!
# IChO 2026, Theory Problem T4 — subquestion 4.5: neutron moderation in water

## Source

58th International Chemistry Olympiad (Tashkent, Uzbekistan, 2026), Theory
Problem T4 ("The nuclear past of Uzbekistan"), subquestion 4.5 (2 points):

> Determine the average number of collisions required, n_c, to slow a neutron
> from 2 MeV to 0.012 eV, using water as the moderator. ξ(water) = 0.948.

The shared problem text defines the *logarithmic energy decrement*

  ξ = ln(E_initial / E_final),

the average decrease per collision in the logarithm of the neutron energy
(`E_initial`, `E_final` are the initial and final neutron energies per
collision), and states that ξ is a constant for each type of material and
does not depend on the initial neutron energy.  The shared context also
states that fission neutrons are produced with an average energy of 2 MeV.

## Assumption / target split

Assumptions (carried by `Moderator`, `SlowingTrajectory`, and the sourced
numerical constants below):

* per collision, the logarithm of the neutron energy decreases on average by
  the moderator's constant decrement ξ (`SlowingTrajectory.per_collision`);
* neutron energies are positive (`SlowingTrajectory.energy_pos`), so every
  energy ratio lies in the domain of `Real.log`;
* sourced constants: ξ(water) = 0.948 (`water`), the mean fission-neutron
  energy 2 MeV (`fissionNeutronEnergy`, read out in eV), and the final
  energy 0.012 eV (`finalNeutronEnergy`).

Targets:

* the aggregate moderation law `log_ratio_after_collisions`: over `n`
  collisions the total logarithmic energy drop is `n * ξ`;
* the endpoint formula `collisions_eq_averageCollisions`: a trajectory's
  collision count is determined by its endpoint energies alone, through
  `ln(E_initial / E_final) / ξ`;
* the requested numerical answer `number_of_collisions_water`: for water,
  n_c ≈ 19.97, i.e. about 20 collisions.  (Recorded rubric answer, used only
  as validation guidance: `n_c = ln(E_initial/E_final)/ξ = 19.97 ≈ 20`.)

## Units convention

Following the shared IChO 2026 convention, physical quantities are
represented by their real numerical readouts in the source's units.  The
energy ratio `E_initial / E_final` is dimensionless only when both energies
are read out in the same unit, so the 2 MeV initial energy appears in eV as
`2 * 10 ^ 6`.
-/

namespace IChO2026.T4.A5

/-- A moderator material for neutron slowing, characterized by its
logarithmic energy decrement `ξ`: the average decrease of `Real.log` of the
neutron energy per collision.  The source states that `ξ` is a constant for
each type of material and does not depend on the initial neutron energy.
Positivity records that the material genuinely slows neutrons (and makes
division by `ξ` meaningful). -/
structure Moderator where
  /-- The logarithmic energy decrement `ξ` (dimensionless). -/
  ξ : ℝ
  /-- Moderators reduce neutron energy on average, so `ξ` is positive. -/
  ξ_pos : 0 < ξ

/-- The per-collision logarithmic energy decrement from the source text,
`ξ = ln(E_initial / E_final)` for one collision taking the neutron energy
from `EInitial` to `EFinal`. -/
noncomputable def logDecrement (EInitial EFinal : ℝ) : ℝ :=
  Real.log (EInitial / EFinal)

/-- A neutron slowing-down trajectory in a moderator: neutron energies
indexed by collision count, all positive, such that every single-collision
logarithmic decrement equals the moderator's constant `ξ`.  Requiring one
and the same `ξ` at every step encodes the source's statement that `ξ` does
not depend on the neutron energy. -/
structure SlowingTrajectory (M : Moderator) where
  /-- Neutron energy after `k` collisions, in the chosen common energy unit. -/
  energy : ℕ → ℝ
  /-- Energies stay positive, keeping every logarithm in its domain. -/
  energy_pos : ∀ k, 0 < energy k
  /-- Per-collision logarithmic decrement law (the source's definition of `ξ`). -/
  per_collision : ∀ k, logDecrement (energy k) (energy (k + 1)) = M.ξ

/-- Aggregate moderation law: after `n` collisions the total logarithmic
energy drop equals `n * ξ`.  This is the telescoped form of the
per-collision law (via `Real.log_div` and `Finset.sum_range_sub`). -/
theorem log_ratio_after_collisions (M : Moderator) (tr : SlowingTrajectory M) (n : ℕ) :
    Real.log (tr.energy 0 / tr.energy n) = (n : ℝ) * M.ξ := by
  -- Each single-collision logarithmic decrement equals the moderator's `ξ`.
  have hstep : ∀ k, Real.log (tr.energy k) - Real.log (tr.energy (k + 1)) = M.ξ := by
    intro k
    have hk := tr.per_collision k
    unfold logDecrement at hk
    rwa [Real.log_div (tr.energy_pos k).ne' (tr.energy_pos (k + 1)).ne'] at hk
  -- Telescope the per-collision decrements over `n` collisions.
  have hsum := Finset.sum_range_sub' (fun k => Real.log (tr.energy k)) n
  simp only [hstep] at hsum
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  rw [Real.log_div (tr.energy_pos 0).ne' (tr.energy_pos n).ne']
  linarith [hsum]

/-- The average number of collisions needed to slow a neutron from energy
`EInitial` to energy `EFinal` in a moderator: the real-valued count `n_c`
solving the aggregate moderation law `n_c * ξ = ln(EInitial / EFinal)`. -/
noncomputable def averageCollisions (M : Moderator) (EInitial EFinal : ℝ) : ℝ :=
  Real.log (EInitial / EFinal) / M.ξ

/-- Endpoint formula for collision counts: the number of collisions of any
slowing trajectory equals `averageCollisions` evaluated at its endpoint
energies, so the count depends on the endpoints alone — the quantitative
content of the source's energy-independence of `ξ`. -/
theorem collisions_eq_averageCollisions (M : Moderator) (tr : SlowingTrajectory M) (n : ℕ) :
    (n : ℝ) = averageCollisions M (tr.energy 0) (tr.energy n) := by
  have hξ : M.ξ ≠ 0 := M.ξ_pos.ne'
  unfold averageCollisions
  rw [log_ratio_after_collisions M tr n, mul_div_cancel_right₀ _ hξ]

/-- Water as the moderator of subquestion 4.5: the source gives
`ξ(water) = 0.948`. -/
def water : Moderator where
  ξ := 0.948
  ξ_pos := by norm_num

/-- Mean energy of a freshly produced fission neutron: the shared problem
text gives 2 MeV, read out here in eV as `2 * 10 ^ 6` so that the ratio with
the final energy is a ratio of like-unit readouts. -/
def fissionNeutronEnergy : ℝ :=
  2 * 10 ^ 6

/-- Target final neutron energy of subquestion 4.5: `0.012` eV. -/
def finalNeutronEnergy : ℝ :=
  0.012

/-- **Target of IChO 2026 T4.5.**  The average number of collisions `n_c`
required to slow a neutron from 2 MeV to 0.012 eV with water as the
moderator is `ln(2·10⁶ / 0.012) / 0.948`, which is approximately `19.97`,
i.e. about 20 collisions (the recorded rubric answer `19.97 ≈ 20`). -/
theorem number_of_collisions_water :
    19.965 < averageCollisions water fissionNeutronEnergy finalNeutronEnergy ∧
    averageCollisions water fissionNeutronEnergy finalNeutronEnergy < 19.975 ∧
    round (averageCollisions water fissionNeutronEnergy finalNeutronEnergy) = 20 := by
  -- `exp` of a natural number is a power of `exp 1`.
  have hexp_nat : ∀ m : ℕ, Real.exp (m : ℝ) = Real.exp 1 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      push_cast
      rw [Real.exp_add, ih, pow_succ]
  have he1_lo : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have he1_hi : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
  -- Upper bound: `exp 18.92682 = e^19 / exp 0.07318 ≤ e^19 / 1.07318 < 5·10⁸/3`,
  -- using `1 + x ≤ exp x` at `x = 0.07318`.
  have hexp07318 : (1.07318 : ℝ) ≤ Real.exp 0.07318 := by
    have h := Real.add_one_le_exp (0.07318 : ℝ)
    linarith
  have hUpper : Real.exp 18.92682 < 500000000 / 3 := by
    have e1 : Real.exp 18.92682 = Real.exp 1 ^ 19 / Real.exp 0.07318 := by
      rw [show (18.92682 : ℝ) = ((19 : ℕ) : ℝ) - 0.07318 by norm_num, Real.exp_sub,
        hexp_nat 19]
    have h19 : Real.exp 1 ^ 19 ≤ (2.7182818286 : ℝ) ^ 19 :=
      pow_le_pow_left₀ (Real.exp_nonneg 1) he1_hi.le 19
    have hdiv : Real.exp 1 ^ 19 / Real.exp 0.07318 ≤ (2.7182818286 : ℝ) ^ 19 / 1.07318 :=
      div_le_div₀ (pow_nonneg (by norm_num) 19) h19 (by norm_num) hexp07318
    rw [e1]
    exact lt_of_le_of_lt hdiv (by norm_num)
  -- Lower bound: `exp 0.0637 ≤ 0.9363⁻¹` (from `1 - x ≤ exp (-x)`), hence
  -- `exp 18.93630 = e^18 · e / exp 0.0637 ≥ e^19 · 0.9363 > 5·10⁸/3`.
  have h00637 : Real.exp 0.0637 ≤ (0.9363 : ℝ)⁻¹ := by
    have h := Real.add_one_le_exp (-0.0637 : ℝ)
    rw [Real.exp_neg] at h
    have h' : (0.9363 : ℝ) ≤ (Real.exp 0.0637)⁻¹ := by linarith
    have h'' := inv_anti₀ (show (0 : ℝ) < 0.9363 by norm_num) h'
    rwa [inv_inv] at h''
  have h09363 : (2.7182818283 : ℝ) * 0.9363 ≤ Real.exp 1 / Real.exp 0.0637 := by
    have h2 : Real.exp 1 / (0.9363 : ℝ)⁻¹ ≤ Real.exp 1 / Real.exp 0.0637 :=
      div_le_div_of_nonneg_left (Real.exp_nonneg 1) (Real.exp_pos 0.0637) h00637
    rw [div_inv_eq_mul] at h2
    exact (mul_le_mul_of_nonneg_right he1_lo.le (by norm_num)).trans h2
  have hLower : (500000000 / 3 : ℝ) < Real.exp 18.93630 := by
    have e2 : Real.exp 18.93630 = Real.exp 1 ^ 18 * (Real.exp 1 / Real.exp 0.0637) := by
      rw [show (18.93630 : ℝ) = ((18 : ℕ) : ℝ) + (1 - 0.0637) by norm_num, Real.exp_add,
        Real.exp_sub, hexp_nat 18]
    have h18 : (2.7182818283 : ℝ) ^ 18 ≤ Real.exp 1 ^ 18 :=
      pow_le_pow_left₀ (by norm_num) he1_lo.le 18
    have hmul := mul_le_mul h18 h09363 (by norm_num : (0 : ℝ) ≤ 2.7182818283 * 0.9363)
      (pow_nonneg (Real.exp_nonneg 1) 18)
    rw [e2]
    exact (by norm_num : (500000000 / 3 : ℝ) <
      2.7182818283 ^ 18 * (2.7182818283 * 0.9363)).trans_le hmul
  -- Convert the `exp` bounds into `log` bounds for `2·10⁶ / 0.012 = 5·10⁸/3`.
  have hpos : (0 : ℝ) < 2 * 10 ^ 6 / 0.012 := by norm_num
  have hratio : (2 * 10 ^ 6 / (0.012 : ℝ)) = 500000000 / 3 := by norm_num
  have hL_lo : 18.92682 < Real.log (2 * 10 ^ 6 / (0.012 : ℝ)) := by
    rw [Real.lt_log_iff_exp_lt hpos, hratio]
    exact hUpper
  have hL_hi : Real.log (2 * 10 ^ 6 / (0.012 : ℝ)) < 18.93630 := by
    rw [Real.log_lt_iff_lt_exp hpos, hratio]
    exact hLower
  -- Divide by `ξ(water) = 0.948`: `19.965·0.948 = 18.92682`, `19.975·0.948 = 18.93630`.
  have h948 : (0 : ℝ) < 0.948 := by norm_num
  have hb1 : 19.965 < Real.log (2 * 10 ^ 6 / (0.012 : ℝ)) / 0.948 := by
    rw [lt_div_iff₀ h948, show (19.965 : ℝ) * 0.948 = 18.92682 by norm_num]
    exact hL_lo
  have hb2 : Real.log (2 * 10 ^ 6 / (0.012 : ℝ)) / 0.948 < 19.975 := by
    rw [div_lt_iff₀ h948, show (19.975 : ℝ) * 0.948 = 18.93630 by norm_num]
    exact hL_hi
  have hval : averageCollisions water fissionNeutronEnergy finalNeutronEnergy
      = Real.log (2 * 10 ^ 6 / (0.012 : ℝ)) / 0.948 := rfl
  rw [hval]
  refine ⟨hb1, hb2, ?_⟩
  rw [round_eq, Int.floor_eq_iff]
  constructor <;> push_cast <;> linarith [hb1, hb2]

end IChO2026.T4.A5
