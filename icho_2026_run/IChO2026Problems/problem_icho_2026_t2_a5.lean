import Mathlib
import IChO2026Chem
import IChO2026Chem.Kinetics.BelousovZhabotinsky

/-!
# IChO 2026 T2-A5: period of the BZ oscillation

All scalar concentrations in this file are their numerical values in the
source's molar (`M`) scale and times are numerical values in seconds.  The
model is deliberately local: the two values obtained in T2-A2 and T2-A3 are
recorded as the source-authorized branch data rather than imported from those
generated problem files.
-/

namespace IChO2026Problems.T2A5

open IChO2026Chem.Kinetics.BelousovZhabotinsky

/--
The Process-B data for the period calculation.  The `period` field is an
unknown measured in seconds, not a supplied answer.  The Process-C field is
the net bromide-production contribution; setting it to zero is precisely the
source's `Ce(IV) approximately zero` approximation during Process B.
-/
structure BromidePeriodData where
  parameters : KineticParameters
  state : State
  bromideMax : ℝ
  bromideCritical : ℝ
  period : ℝ
  processCNetBromideRate : ℝ
  k4_positive : 0 < parameters.k4
  k5_positive : 0 < parameters.k5
  hbro2B_positive : 0 < state .hbro2
  proton_positive : 0 < state .proton
  bromate_positive : 0 < state .bromate
  bromideMax_positive : 0 < bromideMax
  bromideCritical_positive : 0 < bromideCritical
  bromideCritical_lt_max : bromideCritical < bromideMax
  period_nonnegative : 0 ≤ period
  processC_neglected : processCNetBromideRate = 0

/-- Bromide consumption rate from Process-B elementary step (4). -/
def processBStep4BromideLoss (data : BromidePeriodData)
    (bromide : ℝ) : ℝ :=
  rate4 data.parameters (Function.update data.state .bromide bromide)

/-- Bromide consumption rate from Process-B elementary step (5). -/
def processBStep5BromideLoss (data : BromidePeriodData)
    (bromide : ℝ) : ℝ :=
  rate5 data.parameters (Function.update data.state .bromide bromide)

/-- The two Process-B bromide loss terms retained after Process C is neglected. -/
def processBromideLossRate (data : BromidePeriodData)
    (bromide : ℝ) : ℝ :=
  processBStep4BromideLoss data bromide + processBStep5BromideLoss data bromide

/-- The Process-B net bromide rate, retaining the separately named Process-C term. -/
def processBNetBromideRate (data : BromidePeriodData)
    (bromide : ℝ) : ℝ :=
  data.processCNetBromideRate - processBromideLossRate data bromide

/--
The first-order coefficient obtained by factoring bromide from the two
Process-B loss terms.  Its numerical unit is `s⁻¹`.
-/
def effectiveDecayRate (data : BromidePeriodData) : ℝ :=
  data.parameters.k4 * data.state .hbro2 * data.state .proton +
    data.parameters.k5 * data.state .bromate * data.state .proton ^ 2

/--
The Process-B kinetic law after the source's Process-C-neglect approximation:
the negative net bromide rate is `k_* [Br⁻]`.
-/
def firstOrderProcessBLaw (data : BromidePeriodData)
    (bromide : ℝ) : Prop :=
  -processBNetBromideRate data bromide = effectiveDecayRate data * bromide

/--
The first-order law together with its exponential solution at the switching
time.  This is an explicit equation, not an opaque assertion of the requested
period.
-/
def BromidePeriodData.reachesCriticalByDecay (data : BromidePeriodData) : Prop :=
  (∀ bromide : ℝ, firstOrderProcessBLaw data bromide) ∧
    data.bromideCritical =
      data.bromideMax * Real.exp (-effectiveDecayRate data * data.period)

/-- A bromide-concentration trajectory governed by the Process-B first-order
ODE.  The endpoint fields are source observations; the exponential solution is
not assumed and is instead derived below from the differential equation. -/
structure BromideDecayTrajectory (data : BromidePeriodData) where
  concentration : ℝ → ℝ
  initial : concentration 0 = data.bromideMax
  switching : concentration data.period = data.bromideCritical
  obeysRateLaw : ∀ t : ℝ,
    HasDerivAt concentration (-effectiveDecayRate data * concentration t) t

/-- The official values supplied or obtained in the preceding source parts. -/
def BromidePeriodData.matchesOfficialData (data : BromidePeriodData) : Prop :=
  data.parameters.k4 = 2 * 10 ^ 9 ∧
    data.parameters.k5 = 21 / 10 ∧
    data.state .hbro2 = 504 / 10 ^ 13 ∧
    data.state .proton = 4 / 5 ∧
    data.state .bromate = 3 / 50 ∧
    data.bromideMax = 7 / 10000 ∧
    data.bromideCritical = 3 / 10 ^ 7

/--
The explicitly permitted fallback values.  Only the two prior-part results
change; all printed Process-B constants and the maximum bromide concentration
are retained.
-/
def BromidePeriodData.matchesFallbackData (data : BromidePeriodData) : Prop :=
  data.parameters.k4 = 2 * 10 ^ 9 ∧
    data.parameters.k5 = 21 / 10 ∧
    data.state .hbro2 = 1 / 10 ^ 10 ∧
    data.state .proton = 4 / 5 ∧
    data.state .bromate = 3 / 50 ∧
    data.bromideMax = 7 / 10000 ∧
    data.bromideCritical = 1 / 10 ^ 7

/-- Factoring the retained Process-B loss terms gives the effective rate. -/
lemma processBromideLossRate_factor
    (data : BromidePeriodData) (bromide : ℝ) :
    processBromideLossRate data bromide = effectiveDecayRate data * bromide := by
  rw [processBromideLossRate, processBStep4BromideLoss,
    processBStep5BromideLoss, rate4_update_bromide, rate5_update_bromide]
  unfold effectiveDecayRate
  ring

/-- The Process-C-neglect approximation makes the net Process-B law first order. -/
lemma firstOrderProcessBLaw_of_processC_neglected
    (data : BromidePeriodData) (bromide : ℝ) :
    firstOrderProcessBLaw data bromide := by
  unfold firstOrderProcessBLaw processBNetBromideRate
  rw [data.processC_neglected, zero_sub, neg_neg,
    processBromideLossRate_factor]

/-- Solving the first-order Process-B ODE with an integrating factor gives the
exponential switching relation used in the official calculation. -/
theorem reachesCriticalByDecay_of_trajectory
    (data : BromidePeriodData) (trajectory : BromideDecayTrajectory data) :
    data.reachesCriticalByDecay := by
  constructor
  · exact firstOrderProcessBLaw_of_processC_neglected data
  · let weighted : ℝ → ℝ := fun t ↦
      trajectory.concentration t * Real.exp (effectiveDecayRate data * t)
    have hweighted : ∀ t : ℝ, HasDerivAt weighted 0 t := by
      intro t
      have hexp : HasDerivAt
          (fun s : ℝ ↦ Real.exp (effectiveDecayRate data * s))
          (Real.exp (effectiveDecayRate data * t) * effectiveDecayRate data) t :=
        (Real.hasDerivAt_exp _).comp t (hasDerivAt_const_mul _)
      have hmul := (trajectory.obeysRateLaw t).mul hexp
      have hzero :
          -effectiveDecayRate data * trajectory.concentration t *
              Real.exp (effectiveDecayRate data * t) +
            trajectory.concentration t *
              (Real.exp (effectiveDecayRate data * t) * effectiveDecayRate data) = 0 := by
        ring
      rw [hzero] at hmul
      exact hmul
    have hconstant : weighted data.period = weighted 0 := by
      apply is_const_of_deriv_eq_zero
      · exact fun t ↦ (hweighted t).differentiableAt
      · exact fun t ↦ (hweighted t).deriv
    dsimp [weighted] at hconstant
    rw [trajectory.switching, trajectory.initial] at hconstant
    simp only [mul_zero, Real.exp_zero, mul_one] at hconstant
    calc
      data.bromideCritical =
          data.bromideMax / Real.exp (effectiveDecayRate data * data.period) := by
            exact (eq_div_iff (ne_of_gt (Real.exp_pos _))).2 hconstant
      _ = data.bromideMax * Real.exp (-effectiveDecayRate data * data.period) := by
            rw [show -effectiveDecayRate data * data.period =
                -(effectiveDecayRate data * data.period) by ring, Real.exp_neg]
            rfl

/--
Positive source data and the exponential switching relation yield the exact
period formula.  No numerical branch values occur in this derivation.
-/
theorem period_formula
    (data : BromidePeriodData)
    (hdecay : data.reachesCriticalByDecay) :
    data.period =
      Real.log (data.bromideMax / data.bromideCritical) / effectiveDecayRate data := by
  have hrate_pos : 0 < effectiveDecayRate data := by
    unfold effectiveDecayRate
    apply add_pos
    · exact mul_pos (mul_pos data.k4_positive data.hbro2B_positive)
        data.proton_positive
    · exact mul_pos (mul_pos data.k5_positive data.bromate_positive)
        (sq_pos_of_pos data.proton_positive)
  have hrate_ne : effectiveDecayRate data ≠ 0 := ne_of_gt hrate_pos
  have hmax_ne : data.bromideMax ≠ 0 := ne_of_gt data.bromideMax_positive
  have hcritical_ne : data.bromideCritical ≠ 0 :=
    ne_of_gt data.bromideCritical_positive
  have hratio : data.bromideCritical / data.bromideMax =
      Real.exp (-effectiveDecayRate data * data.period) := by
    rw [hdecay.2]
    field_simp
  have hlog : Real.log (data.bromideCritical / data.bromideMax) =
      -effectiveDecayRate data * data.period := by
    rw [hratio, Real.log_exp]
  have hlog_inv : Real.log (data.bromideMax / data.bromideCritical) =
      -Real.log (data.bromideCritical / data.bromideMax) := by
    rw [Real.log_div hmax_ne hcritical_ne,
      Real.log_div hcritical_ne hmax_ne]
    ring
  rw [eq_div_iff hrate_ne]
  nlinarith [hlog, hlog_inv]

/--
For the official preceding-part inputs, the effective rate, exact logarithmic
period, and the source's nearest-second report are all recorded.  The
half-second inequality represents the reported integer `48` faithfully.
-/
theorem official_oscillation_period
    (data : BromidePeriodData)
    (hdata : data.matchesOfficialData)
    (trajectory : BromideDecayTrajectory data) :
    effectiveDecayRate data = (504 : ℝ) / 3125 ∧
      data.period =
        Real.log ((7 / 10000 : ℝ) / (3 / 10 ^ 7)) / ((504 : ℝ) / 3125) ∧
      |data.period - 48| < (1 : ℝ) / 2 := by
  have hdecay := reachesCriticalByDecay_of_trajectory data trajectory
  rcases hdata with ⟨hk4, hk5, hhbro2, hproton, hbromate, hmax, hcritical⟩
  have heffective : effectiveDecayRate data = (504 : ℝ) / 3125 := by
    norm_num [effectiveDecayRate, hk4, hk5, hhbro2, hproton, hbromate]
  have hperiod : data.period =
      Real.log ((7 / 10000 : ℝ) / (3 / 10 ^ 7)) / ((504 : ℝ) / 3125) := by
    calc
      data.period = Real.log (data.bromideMax / data.bromideCritical) /
          effectiveDecayRate data := period_formula data hdecay
      _ = Real.log ((7 / 10000 : ℝ) / (3 / 10 ^ 7)) /
          ((504 : ℝ) / 3125) := by rw [hmax, hcritical, heffective]
  refine ⟨heffective, hperiod, ?_⟩
  have hratio_pos : 0 < (7 / 10000 : ℝ) / (3 / 10 ^ 7) := by norm_num
  have he_one_upper : Real.exp 1 < (68 : ℝ) / 25 :=
    lt_trans Real.exp_one_lt_d9 (by norm_num)
  have he_seven_upper : Real.exp 7 < ((68 : ℝ) / 25) ^ 7 := by
    calc
      Real.exp 7 = Real.exp 1 ^ 7 := by
        convert Real.exp_nat_mul (1 : ℝ) 7 using 1 <;> norm_num
      _ < ((68 : ℝ) / 25) ^ 7 := by gcongr
  have hfrac_lower_upper : Real.exp ((413 : ℝ) / 6250) ≤
      1 / (1 - (413 : ℝ) / 6250) :=
    Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
  have hfrac_upper : Real.exp ((413 : ℝ) / 625) ≤
      (1 / (1 - (413 : ℝ) / 6250)) ^ 10 := by
    calc
      Real.exp ((413 : ℝ) / 625) = Real.exp ((413 : ℝ) / 6250) ^ 10 := by
        convert Real.exp_nat_mul ((413 : ℝ) / 6250) 10 using 1 <;> norm_num
      _ ≤ (1 / (1 - (413 : ℝ) / 6250)) ^ 10 := by gcongr
  have hlog_lower : (4788 : ℝ) / 625 <
      Real.log ((7 / 10000 : ℝ) / (3 / 10 ^ 7)) := by
    rw [Real.lt_log_iff_exp_lt hratio_pos]
    calc
      Real.exp ((4788 : ℝ) / 625) =
          Real.exp 7 * Real.exp ((413 : ℝ) / 625) := by
        rw [← Real.exp_add]
        congr 1
        norm_num
      _ < ((68 : ℝ) / 25) ^ 7 * Real.exp ((413 : ℝ) / 625) := by
        exact mul_lt_mul_of_pos_right he_seven_upper (Real.exp_pos _)
      _ ≤ ((68 : ℝ) / 25) ^ 7 *
          (1 / (1 - (413 : ℝ) / 6250)) ^ 10 := by
        gcongr
      _ < (7 / 10000 : ℝ) / (3 / 10 ^ 7) := by norm_num
  have he_one_lower : (271 : ℝ) / 100 < Real.exp 1 :=
    lt_trans (by norm_num) Real.exp_one_gt_d9
  have he_seven_lower : ((271 : ℝ) / 100) ^ 7 < Real.exp 7 := by
    calc
      ((271 : ℝ) / 100) ^ 7 < Real.exp 1 ^ 7 := by gcongr
      _ = Real.exp 7 := by
        convert (Real.exp_nat_mul (1 : ℝ) 7).symm using 1 <;> norm_num
  have hfrac_lower_base : 1 + (2569 : ℝ) / 31250 ≤
      Real.exp ((2569 : ℝ) / 31250) := by
    simpa [add_comm] using Real.add_one_le_exp ((2569 : ℝ) / 31250)
  have hfrac_lower : (1 + (2569 : ℝ) / 31250) ^ 10 ≤
      Real.exp ((2569 : ℝ) / 3125) := by
    calc
      (1 + (2569 : ℝ) / 31250) ^ 10 ≤
          Real.exp ((2569 : ℝ) / 31250) ^ 10 := by gcongr
      _ = Real.exp ((2569 : ℝ) / 3125) := by
        convert (Real.exp_nat_mul ((2569 : ℝ) / 31250) 10).symm using 1 <;> norm_num
  have hlog_upper : Real.log ((7 / 10000 : ℝ) / (3 / 10 ^ 7)) <
      (24444 : ℝ) / 3125 := by
    rw [Real.log_lt_iff_lt_exp hratio_pos]
    calc
      (7 / 10000 : ℝ) / (3 / 10 ^ 7) <
          ((271 : ℝ) / 100) ^ 7 * (1 + (2569 : ℝ) / 31250) ^ 10 := by
        norm_num
      _ ≤ Real.exp 7 * Real.exp ((2569 : ℝ) / 3125) := by
        exact mul_le_mul he_seven_lower.le hfrac_lower (by positivity) (by positivity)
      _ = Real.exp ((24444 : ℝ) / 3125) := by
        rw [← Real.exp_add]
        congr 1
        norm_num
  rw [hperiod, abs_lt]
  constructor <;> nlinarith

/--
For the source-authorized fallback inputs, the separate effective rate,
logarithmic period, and nearest-second report are recorded.  This branch does
not alter the official data branch.
-/
theorem fallback_oscillation_period
    (data : BromidePeriodData)
    (hdata : data.matchesFallbackData)
    (trajectory : BromideDecayTrajectory data) :
    effectiveDecayRate data = (752 : ℝ) / 3125 ∧
      data.period =
        Real.log ((7 / 10000 : ℝ) / (1 / 10 ^ 7)) / ((752 : ℝ) / 3125) ∧
      |data.period - 37| < (1 : ℝ) / 2 := by
  have hdecay := reachesCriticalByDecay_of_trajectory data trajectory
  rcases hdata with ⟨hk4, hk5, hhbro2, hproton, hbromate, hmax, hcritical⟩
  have heffective : effectiveDecayRate data = (752 : ℝ) / 3125 := by
    norm_num [effectiveDecayRate, hk4, hk5, hhbro2, hproton, hbromate]
  have hperiod : data.period =
      Real.log ((7 / 10000 : ℝ) / (1 / 10 ^ 7)) / ((752 : ℝ) / 3125) := by
    calc
      data.period = Real.log (data.bromideMax / data.bromideCritical) /
          effectiveDecayRate data := period_formula data hdecay
      _ = Real.log ((7 / 10000 : ℝ) / (1 / 10 ^ 7)) /
          ((752 : ℝ) / 3125) := by rw [hmax, hcritical, heffective]
  refine ⟨heffective, hperiod, ?_⟩
  have hratio_pos : 0 < (7 / 10000 : ℝ) / (1 / 10 ^ 7) := by norm_num
  have he_one_upper : Real.exp 1 < (68 : ℝ) / 25 :=
    lt_trans Real.exp_one_lt_d9 (by norm_num)
  have he_eight_upper : Real.exp 8 < ((68 : ℝ) / 25) ^ 8 := by
    calc
      Real.exp 8 = Real.exp 1 ^ 8 := by
        convert Real.exp_nat_mul (1 : ℝ) 8 using 1 <;> norm_num
      _ < ((68 : ℝ) / 25) ^ 8 := by gcongr
  have hfrac_base_upper : Real.exp ((1224 : ℝ) / 15625) ≤
      1 / (1 - (1224 : ℝ) / 15625) :=
    Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
  have hfrac_upper : Real.exp ((2448 : ℝ) / 3125) ≤
      (1 / (1 - (1224 : ℝ) / 15625)) ^ 10 := by
    calc
      Real.exp ((2448 : ℝ) / 3125) = Real.exp ((1224 : ℝ) / 15625) ^ 10 := by
        convert Real.exp_nat_mul ((1224 : ℝ) / 15625) 10 using 1 <;> norm_num
      _ ≤ (1 / (1 - (1224 : ℝ) / 15625)) ^ 10 := by gcongr
  have hlog_lower : (27448 : ℝ) / 3125 <
      Real.log ((7 / 10000 : ℝ) / (1 / 10 ^ 7)) := by
    rw [Real.lt_log_iff_exp_lt hratio_pos]
    calc
      Real.exp ((27448 : ℝ) / 3125) =
          Real.exp 8 * Real.exp ((2448 : ℝ) / 3125) := by
        rw [← Real.exp_add]
        congr 1
        norm_num
      _ < ((68 : ℝ) / 25) ^ 8 * Real.exp ((2448 : ℝ) / 3125) := by
        exact mul_lt_mul_of_pos_right he_eight_upper (Real.exp_pos _)
      _ ≤ ((68 : ℝ) / 25) ^ 8 *
          (1 / (1 - (1224 : ℝ) / 15625)) ^ 10 := by
        gcongr
      _ < (7 / 10000 : ℝ) / (1 / 10 ^ 7) := by norm_num
  have he_one_lower : (271 : ℝ) / 100 < Real.exp 1 :=
    lt_trans (by norm_num) Real.exp_one_gt_d9
  have he_nine_lower : ((271 : ℝ) / 100) ^ 9 < Real.exp 9 := by
    calc
      ((271 : ℝ) / 100) ^ 9 < Real.exp 1 ^ 9 := by gcongr
      _ = Real.exp 9 := by
        convert (Real.exp_nat_mul (1 : ℝ) 9).symm using 1 <;> norm_num
  have hlog_upper : Real.log ((7 / 10000 : ℝ) / (1 / 10 ^ 7)) <
      (1128 : ℝ) / 125 := by
    rw [Real.log_lt_iff_lt_exp hratio_pos]
    calc
      (7 / 10000 : ℝ) / (1 / 10 ^ 7) < ((271 : ℝ) / 100) ^ 9 := by norm_num
      _ < Real.exp 9 := he_nine_lower
      _ < Real.exp ((1128 : ℝ) / 125) := by
        rw [Real.exp_lt_exp]
        norm_num
  rw [hperiod, abs_lt]
  constructor <;> nlinarith

/--
The T2-A5 result exposes both source-authorized branches.  Their hypotheses
contain only data and the first-order decay law, never either requested answer.
-/
theorem oscillation_periods :
    (∀ data : BromidePeriodData,
      data.matchesOfficialData → BromideDecayTrajectory data →
        effectiveDecayRate data = (504 : ℝ) / 3125 ∧
          data.period =
            Real.log ((7 / 10000 : ℝ) / (3 / 10 ^ 7)) / ((504 : ℝ) / 3125) ∧
          |data.period - 48| < (1 : ℝ) / 2) ∧
      (∀ data : BromidePeriodData,
        data.matchesFallbackData → BromideDecayTrajectory data →
          effectiveDecayRate data = (752 : ℝ) / 3125 ∧
            data.period =
              Real.log ((7 / 10000 : ℝ) / (1 / 10 ^ 7)) / ((752 : ℝ) / 3125) ∧
            |data.period - 37| < (1 : ℝ) / 2) := by
  constructor
  · intro data hdata hdecay
    exact official_oscillation_period data hdata hdecay
  · intro data hdata hdecay
    exact fallback_oscillation_period data hdata hdecay

end IChO2026Problems.T2A5
