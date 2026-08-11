import Mathlib

/-!
# IChO 2026, Theory Problem T7 (Nitrogen Fixation), Subquestion 7.3

## Source

58th International Chemistry Olympiad, Tashkent 2026, problem T7 "Nitrogen
Fixation", subquestion 7.3 (problem PDF page 64, printed page Q7-2;
`T7_page-2.png`, `T7_page-1.png`).

A model of a real Haber–Bosch reaction system includes recirculation of
reagents.  An open system operates in a cyclic mode; each cycle consists of
four steps:

1. A stoichiometric N₂ : H₂ = 1 : 3 mixture with a total amount of `n₀` mol
   is fed into the reactor after each cycle.
2. The reaction N₂ + 3H₂ ⇌ 2NH₃ proceeds with a constant per-pass yield
   `η = 0.150`.
3. Ammonia is separated by liquification (complete removal of the product).
4. Unreacted gases (N₂ and H₂, still in the ratio 1 : 3) are returned into
   the reactor.

The cycle is repeated until the required overall yield is reached.

## Current subquestion

* **(a)** Calculate the amount of nitrogen (N₂), present in the system after
  the 58th cycle (before the addition of the 59th portion of mixture), if
  `n₀ = 4` mol.  Provide 4 decimal places.
* **(b)** Calculate the number of cycles needed to increase the overall yield
  from 15.0 % to 97.0 %.

## Assumption / target split

**Assumptions (model, encoded as definitions):**

* `stoichCoeffN2`, `stoichCoeffH2`: the stoichiometric coefficients 1 and 3
  of the feed mixture, from which the N₂ feed fraction `1 / (1 + 3)` derives;
* `nitrogenAfterCycle n₀ η n`: moles of N₂ in the reactor after the reaction
  step of cycle `n` (after NH₃ separation, before feeding portion `n + 1`),
  defined by the governing recurrence of the recirculation model
  `f 0 = 0`, `f (n + 1) = (f n + n₀ · 1/4) (1 - η)` — each cycle adds a fresh
  portion of `n₀/4` mol N₂ to the recycled unreacted N₂, and a fraction `η`
  of the N₂ present is converted to NH₃ and removed by liquification;
* `overallYield n₀ η n`: the cumulative (overall) yield after `n` cycles,
  i.e. the fraction of all N₂ fed so far that has been converted,
  `1 - f n / (n · n₀/4)`.

**Targets (recorded answers appear only here, never in the definitions):**

* `nitrogenAfterCycle_eq_geom_sum` / `nitrogenAfterCycle_eq_closed`: the
  geometric-progression closed form of the recurrence (the hint of part (a));
* `overallYield_first_cycle`: the overall yield after one cycle equals `η`
  (the "from 15.0 %" baseline of part (b));
* `nitrogen_after_58_cycles`: part (a) — with `n₀ = 4`, `η = 0.150` the N₂
  amount after the 58th cycle rounds to `5.6662` mol at 4 decimal places;
* `cycles_needed_for_overall_yield_97`: part (b) — `189` is the least number
  of cycles at which the overall yield reaches `97.0 %`.

Only the physical side conditions `0 < η < 1` and `0 < n₀` are used from the
problem data; the theorems below carry exactly the hypotheses they need
(`η ≠ 0` for division in the closed form, `n₀ ≠ 0` for the yield baseline).
-/

namespace IChO2026.T7.A3

/-- Stoichiometric coefficient of N₂ in the fresh feed mixture
(N₂ : H₂ = 1 : 3), as given by step 1 of the cycle. -/
def stoichCoeffN2 : ℝ := 1

/-- Stoichiometric coefficient of H₂ in the fresh feed mixture
(N₂ : H₂ = 1 : 3), as given by step 1 of the cycle. -/
def stoichCoeffH2 : ℝ := 3

/-- Mole fraction of N₂ in the fresh stoichiometric feed mixture:
`1 / (1 + 3) = 1/4`.  Kept as a quotient of the two stoichiometric
coefficients so the 1 : 3 ratio of the source is preserved explicitly. -/
noncomputable def n2FeedFraction : ℝ := stoichCoeffN2 / (stoichCoeffN2 + stoichCoeffH2)

/-- Moles of N₂ contained in one fresh feed portion: the N₂ fraction of the
total `n₀` mol of stoichiometric mixture fed after each cycle. -/
noncomputable def freshN2PerCycle (n₀ : ℝ) : ℝ := n₀ * n2FeedFraction

/-- Moles of N₂ present in the reactor after the reaction step of cycle `n`
(and after the NH₃ separation of step 3), i.e. before portion `n + 1` of the
fresh mixture is added.  This is the governing recurrence of the
recirculation model: the unreacted N₂ of the previous cycle is returned to
the reactor (step 4), a fresh portion `n₀/4` is added (step 1), and a
fraction `η` of the total is converted to NH₃ and removed (steps 2–3):

`f 0 = 0`,  `f (n + 1) = (f n + n₀/4) · (1 - η)`. -/
noncomputable def nitrogenAfterCycle (n₀ η : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (nitrogenAfterCycle n₀ η n + freshN2PerCycle n₀) * (1 - η)

/-- The reactor is empty before the first cycle. -/
theorem nitrogenAfterCycle_zero (n₀ η : ℝ) :
    nitrogenAfterCycle n₀ η 0 = 0 :=
  rfl

/-- The per-cycle recurrence relation of the model (rubric equation):
after cycle `n + 1`, the N₂ present is the unconverted fraction `1 - η` of
the N₂ available at the start of that cycle (recycled plus fresh feed). -/
theorem nitrogenAfterCycle_succ (n₀ η : ℝ) (n : ℕ) :
    nitrogenAfterCycle n₀ η (n + 1)
      = (nitrogenAfterCycle n₀ η n + freshN2PerCycle n₀) * (1 - η) :=
  rfl

/-- Geometric-progression form of the solution (the hint of part (a)):
the N₂ amount after cycle `n` is the feed portion times the geometric sum
`∑_{i=1}^{n} (1 - η)^i`.

Proof sketch for the prover stage: induction on `n` using
`nitrogenAfterCycle_succ` and `Finset.sum_range_succ`, then `ring`. -/
theorem nitrogenAfterCycle_eq_geom_sum (n₀ η : ℝ) (n : ℕ) :
    nitrogenAfterCycle n₀ η n
      = freshN2PerCycle n₀ * ∑ i ∈ Finset.range n, (1 - η) ^ (i + 1) := by
  induction n with
  | zero => simp [nitrogenAfterCycle]
  | succ k ih =>
    -- Reindex the tail sum: shifting each exponent by one pulls out a
    -- factor of `1 - η`, turning the step into a pure ring identity.
    have hsum : (∑ i ∈ Finset.range k, (1 - η) ^ (i + 1 + 1))
        = (∑ i ∈ Finset.range k, (1 - η) ^ (i + 1)) * (1 - η) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => pow_succ _ _
    rw [nitrogenAfterCycle_succ, ih, Finset.sum_range_succ', hsum]
    ring

/-- Closed form of the recurrence via the geometric-series formula
(`geom_sum_eq`, valid since `1 - η ≠ 1` when `η ≠ 0`):
`f n = (n₀/4) · (1/η - 1) · (1 - (1 - η)^n)`.

Proof sketch: rewrite with `nitrogenAfterCycle_eq_geom_sum`, apply
`geom_sum_eq` to `r = 1 - η`, and simplify `(1 - η) / η = 1 / η - 1` by
`field_simp`. -/
theorem nitrogenAfterCycle_eq_closed (n₀ η : ℝ) (hη : η ≠ 0) (n : ℕ) :
    nitrogenAfterCycle n₀ η n
      = freshN2PerCycle n₀ * (1 / η - 1) * (1 - (1 - η) ^ n) := by
  rw [nitrogenAfterCycle_eq_geom_sum]
  have hr : (1 : ℝ) - η ≠ 1 := by
    intro h
    exact hη (by linarith)
  have hr1 : (1 : ℝ) - η - 1 ≠ 0 := by
    intro h
    exact hη (by linarith)
  -- Pull one factor of `1 - η` out of the geometric sum so that
  -- `geom_sum_eq` applies to `∑ (1 - η) ^ i`.
  have hsum : (∑ i ∈ Finset.range n, (1 - η) ^ (i + 1))
      = (1 - η) * ∑ i ∈ Finset.range n, (1 - η) ^ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => pow_succ' _ _
  rw [hsum, geom_sum_eq hr]
  field_simp
  ring

/-- Overall (cumulative) yield after `n` cycles: the fraction of all N₂ fed
into the system that has been converted to NH₃.  Over `n` cycles the total
amount of N₂ fed is `n · n₀/4` mol, of which `f n` mol remains unreacted in
the reactor, so the overall yield is `1 - f n / (n · n₀/4)`. -/
noncomputable def overallYield (n₀ η : ℝ) (n : ℕ) : ℝ :=
  1 - nitrogenAfterCycle n₀ η n / ((n : ℝ) * freshN2PerCycle n₀)

/-- Baseline of part (b): after a single cycle the overall yield equals the
per-pass yield `η` (for `η = 0.150` this is the initial "15.0 %").
Requires a nonempty feed (`n₀ ≠ 0`) to cancel the feed portion.

Proof sketch: unfold the definitions, use `nitrogenAfterCycle_succ`,
`n2FeedFraction`, and `field_simp` with `n₀ ≠ 0`. -/
theorem overallYield_first_cycle (n₀ η : ℝ) (h₀ : n₀ ≠ 0) :
    overallYield n₀ η 1 = η := by
  have hc : freshN2PerCycle n₀ = n₀ / 4 := by
    unfold freshN2PerCycle n2FeedFraction stoichCoeffN2 stoichCoeffH2
    ring
  have hn0 : (n₀ / 4 : ℝ) ≠ 0 := div_ne_zero h₀ (by norm_num)
  have hf1 : nitrogenAfterCycle n₀ η 1 = freshN2PerCycle n₀ * (1 - η) := by
    simpa [nitrogenAfterCycle_zero] using nitrogenAfterCycle_succ n₀ η 0
  unfold overallYield
  rw [hf1, hc]
  simp only [Nat.cast_one, one_mul]
  field_simp [hn0]
  ring

/-- **Part (a).** With `n₀ = 4` mol of fresh mixture per cycle and per-pass
yield `η = 0.150`, the amount of N₂ present in the system after the 58th
cycle (before the addition of the 59th portion) is `5.6662` mol to four
decimal places, i.e. the exact value differs from `5.6662` by strictly less
than half a unit of the fourth decimal place.

Proof sketch: `nitrogenAfterCycle_eq_closed` gives
`f 58 = (17/3) (1 - 0.85^58)`; with `0.85^58 ≈ 8.06·10⁻⁵` this is
`≈ 5.66621`, within `5·10⁻⁵` of `5.6662` (`norm_num`/`interval` bounds on
`0.85^58`). -/
theorem nitrogen_after_58_cycles :
    |nitrogenAfterCycle 4 0.15 58 - 5.6662| < 0.00005 := by
  have hc : freshN2PerCycle 4 = 1 := by
    unfold freshN2PerCycle n2FeedFraction stoichCoeffN2 stoichCoeffH2
    norm_num
  rw [nitrogenAfterCycle_eq_closed 4 0.15 (by norm_num) 58, hc, abs_lt]
  -- Both sides are exact rational comparisons after evaluating
  -- `(1 - 0.15) ^ 58 = (17 / 20) ^ 58`; `norm_num` decides them.
  constructor <;> norm_num

/-- **Part (b).** Starting from the single-cycle overall yield of 15.0 %
(`overallYield_first_cycle`), the least number of cycles after which the
overall yield reaches 97.0 % is `189`.  (Solving
`1 - 0.97 = (17/3) (1 - 0.85^n) / n` over the reals gives `n ≈ 188.9`;
since whole cycles are counted, the answer is the ceiling, `189`.)

Proof sketch: membership — evaluate `overallYield 4 0.15 189 ≥ 0.97` via the
closed form (`0.85^189` is negligible, `norm_num` bounds); minimality — show
`overallYield 4 0.15 n` is strictly increasing in `n ≥ 1` (the unreacted
amount `f n` increases while the feed `n` grows linearly) and that
`overallYield 4 0.15 188 < 0.97`, so no `n ≤ 188` qualifies. -/
theorem cycles_needed_for_overall_yield_97 :
    IsLeast {n : ℕ | 1 ≤ n ∧ 0.97 ≤ overallYield 4 0.15 n} 189 := by
  have hc : freshN2PerCycle 4 = 1 := by
    unfold freshN2PerCycle n2FeedFraction stoichCoeffN2 stoichCoeffH2
    norm_num
  -- Closed form of the recurrence for this problem's data (`n₀ = 4`, `η = 0.15`):
  -- after cycle `n` the reactor holds `(17/3) (1 - 0.85 ^ n)` mol of N₂.
  have hcl : ∀ n : ℕ, nitrogenAfterCycle 4 0.15 n
      = (17 / 3 : ℝ) * (1 - (1 - 0.15 : ℝ) ^ n) := by
    intro n
    rw [nitrogenAfterCycle_eq_closed 4 0.15 (by norm_num) n, hc]
    have e : (1 : ℝ) / 0.15 - 1 = 17 / 3 := by norm_num
    rw [e, one_mul]
  -- Auxiliary Bernoulli-type bound: `0.85 ^ n · (0.15 · n + 1) ≤ 1`
  -- (the factor decreases because `0.85 · (0.15 (k+1) + 1) ≤ 0.15 k + 1`).
  have haux : ∀ n : ℕ, (1 - 0.15 : ℝ) ^ n * (0.15 * (n : ℝ) + 1) ≤ 1 := by
    intro n
    induction n with
    | zero => norm_num
    | succ k ih =>
      have hk : (0 : ℝ) ≤ (1 - 0.15 : ℝ) ^ k := by positivity
      have hstep : (1 - 0.15 : ℝ) * (0.15 * (k : ℝ) + 0.15 + 1) ≤ 0.15 * (k : ℝ) + 1 := by
        have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        nlinarith
      have hgoal : (1 - 0.15 : ℝ) ^ (k + 1) * (0.15 * ((k + 1 : ℕ) : ℝ) + 1)
          = (1 - 0.15 : ℝ) ^ k * ((1 - 0.15) * (0.15 * (k : ℝ) + 0.15 + 1)) := by
        push_cast
        rw [pow_succ]
        ring
      rw [hgoal]
      exact le_trans (mul_le_mul_of_nonneg_left hstep hk) ih
  -- The overall yield is increasing for `n ≥ 1`: the unreacted N₂ share per
  -- fed mole `f n / n` decreases, which by the closed form is exactly `haux`.
  have hmono : ∀ n : ℕ, 1 ≤ n → overallYield 4 0.15 n ≤ overallYield 4 0.15 (n + 1) := by
    intro n hn
    have hn1 : (0 : ℝ) < (n : ℝ) := by
      have h : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hn2 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
      have h : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      push_cast
      linarith
    unfold overallYield
    rw [hcl n, hcl (n + 1), hc]
    simp only [mul_one]
    rw [sub_le_sub_iff_left, div_le_div_iff₀ hn2 hn1, pow_succ]
    push_cast
    nlinarith [haux n]
  -- After 188 cycles the yield is still below 97 %:
  -- `(17/3) (1 - 0.85 ^ 188) > 0.03 · 188 = 5.64`, since
  -- `0.85 ^ 188 ≤ 0.85 ^ 40 < 8 / 1700`.
  have h188 : overallYield 4 0.15 188 < 0.97 := by
    have h40 : (1 - 0.15 : ℝ) ^ 40 < 8 / 1700 := by norm_num
    have hsplit : (1 - 0.15 : ℝ) ^ 188 = (1 - 0.15 : ℝ) ^ 40 * (1 - 0.15 : ℝ) ^ 148 := by
      rw [← pow_add]
    have h148 : (1 - 0.15 : ℝ) ^ 148 ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have hx : (1 - 0.15 : ℝ) ^ 188 < 8 / 1700 := by
      calc (1 - 0.15 : ℝ) ^ 188 = (1 - 0.15 : ℝ) ^ 40 * (1 - 0.15 : ℝ) ^ 148 := hsplit
        _ ≤ (1 - 0.15 : ℝ) ^ 40 * 1 :=
            mul_le_mul_of_nonneg_left h148 (by positivity)
        _ = (1 - 0.15 : ℝ) ^ 40 := mul_one _
        _ < 8 / 1700 := h40
    have h1x : (1 : ℝ) - 8 / 1700 < 1 - (1 - 0.15 : ℝ) ^ 188 := sub_lt_sub_left hx 1
    have hv : (17 / 3 : ℝ) * (1 - 8 / 1700) < (17 / 3) * (1 - (1 - 0.15 : ℝ) ^ 188) :=
      mul_lt_mul_of_pos_left h1x (by norm_num)
    have hval : (17 / 3 : ℝ) * (1 - 8 / 1700) = 5.64 := by norm_num
    rw [hval] at hv
    unfold overallYield
    rw [hcl 188, hc]
    simp only [mul_one]
    push_cast
    have h03 : (0.03 : ℝ) < (17 / 3 : ℝ) * (1 - (1 - 0.15 : ℝ) ^ 188) / 188 := by
      rw [lt_div_iff₀ (by norm_num)]
      linarith [hv]
    linarith [h03]
  -- After 189 cycles the yield reaches 97 %: the unreacted N₂ is bounded by
  -- the geometric limit `17/3`, and `(17/3) / 189 = 17/567 ≤ 0.03`.
  have h189 : (0.97 : ℝ) ≤ overallYield 4 0.15 189 := by
    have hx0 : (0 : ℝ) < (1 - 0.15 : ℝ) ^ 189 := by positivity
    have hv : (17 / 3 : ℝ) * (1 - (1 - 0.15 : ℝ) ^ 189) < 17 / 3 := by
      have h1 : (1 : ℝ) - (1 - 0.15 : ℝ) ^ 189 < 1 := by linarith
      calc (17 / 3 : ℝ) * (1 - (1 - 0.15 : ℝ) ^ 189) < (17 / 3) * 1 :=
            mul_lt_mul_of_pos_left h1 (by norm_num)
        _ = 17 / 3 := mul_one _
    have hdiv : (17 / 3 : ℝ) * (1 - (1 - 0.15 : ℝ) ^ 189) / 189 ≤ 17 / 567 := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 189)]
      have e : (17 / 567 : ℝ) * 189 = 17 / 3 := by norm_num
      rw [e]
      exact le_of_lt hv
    unfold overallYield
    rw [hcl 189, hc]
    simp only [mul_one]
    push_cast
    linarith [hdiv]
  refine ⟨⟨by norm_num, h189⟩, ?_⟩
  intro m hm
  obtain ⟨hm1, hm2⟩ := hm
  by_contra h
  push Not at h
  have hm188 : m ≤ 188 := by omega
  -- Any qualifying `m ≤ 188` would beat the monotone bound at 188.
  have hle : overallYield 4 0.15 m ≤ overallYield 4 0.15 188 :=
    Nat.le_induction (le_refl _)
      (fun k hmk ih => le_trans ih (hmono k (le_trans hm1 hmk))) 188 hm188
  linarith [hle, h188, hm2]

end IChO2026.T7.A3
