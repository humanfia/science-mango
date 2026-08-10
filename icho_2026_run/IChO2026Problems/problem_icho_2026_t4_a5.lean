import IChO2026Chem

/-!
# IChO 2026 T4, subproblem 4.5

The numerical energies in this file are expressed in electronvolts (eV).
Accordingly, the source's `2 MeV` is represented by `2_000_000` eV.  The
collision count is a real-valued average, rather than a natural-number count.
-/

namespace IChO2026Problems.T4A5

/-- A neutron energy readout expressed in electronvolts. -/
abbrev EnergyEV := ℝ

/-- An average number of neutron-moderator collisions. -/
abbrev AverageCollisionCount := ℝ

/-- The moderator identity relevant to the supplied T4-A5 datum. -/
inductive Moderator where
  | water
  deriving DecidableEq

/-- The numerical moderation quantities occurring in T4-A5.

The positivity and nonnegativity fields retain the domain conditions needed
for the energy ratio, its logarithm, and an average collision count. -/
structure NeutronModerationData where
  moderator : Moderator
  initialEnergy : EnergyEV
  finalEnergy : EnergyEV
  logarithmicEnergyDecrement : ℝ
  averageCollisions : AverageCollisionCount
  initialEnergy_pos : 0 < initialEnergy
  finalEnergy_pos : 0 < finalEnergy
  logarithmicEnergyDecrement_pos : 0 < logarithmicEnergyDecrement
  averageCollisions_nonneg : 0 ≤ averageCollisions

/-- The cumulative moderation law: each collision contributes the same mean
logarithmic decrement, so the total decrement is the logarithm of the total
energy ratio. -/
def NeutronModerationData.satisfiesModerationLaw
    (data : NeutronModerationData) : Prop :=
  data.averageCollisions * data.logarithmicEnergyDecrement =
    Real.log (data.initialEnergy / data.finalEnergy)

/-- The empirical water-moderation inputs supplied in T4-A5.  In particular,
the first equality records the conversion `2 MeV = 2_000_000 eV`; it does not
assume a collision-count answer. -/
def NeutronModerationData.matchesWaterData
    (data : NeutronModerationData) : Prop :=
  data.moderator = .water ∧
  data.initialEnergy = 2_000_000 ∧
  data.finalEnergy = 0.012 ∧
  data.logarithmicEnergyDecrement = 0.948

/-- The cumulative law uniquely determines the average collision count because
the logarithmic energy decrement is positive. -/
lemma collision_count_formula
    (data : NeutronModerationData)
    (hlaw : data.satisfiesModerationLaw) :
    data.averageCollisions =
      Real.log (data.initialEnergy / data.finalEnergy) /
        data.logarithmicEnergyDecrement := by
  rw [NeutronModerationData.satisfiesModerationLaw] at hlaw
  exact (eq_div_iff data.logarithmicEnergyDecrement_pos.ne').mpr hlaw

/-- For the water values supplied by the question, the exact average-count
readout has the stated logarithmic form, agrees with the reported decimal
`19.97` to four decimal places, and is within one half of the reported nearest
integer `20`. -/
theorem water_collision_count
    (data : NeutronModerationData)
    (hwater : data.matchesWaterData)
    (hlaw : data.satisfiesModerationLaw) :
    data.averageCollisions = Real.log (2_000_000 / 0.012) / 0.948 ∧
      |data.averageCollisions - (1997 / 100 : ℝ)| < (1 / 10000 : ℝ) ∧
      |data.averageCollisions - 20| < (1 / 2 : ℝ) := by
  rcases hwater with ⟨hmoderator, hinitial, hfinal, hdecrement⟩
  have hformula := collision_count_formula data hlaw
  have hcount : data.averageCollisions = Real.log (2_000_000 / 0.012) / 0.948 := by
    rw [hformula, hinitial, hfinal, hdecrement]
  have hlog2_lower : (693147 : ℝ) / 1000000 < Real.log 2 := by
    have h := Real.sum_range_le_log_div (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 20
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hlog2_upper : Real.log 2 < (693148 : ℝ) / 1000000 := by
    have h := Real.log_div_le_sum_range_add (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 20
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hlog3_lower : (1098612 : ℝ) / 1000000 < Real.log 3 := by
    have h := Real.sum_range_le_log_div (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) 20
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hlog3_upper : Real.log 3 < (1098613 : ℝ) / 1000000 := by
    have h := Real.log_div_le_sum_range_add (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) 20
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hlog5_lower : (1609437 : ℝ) / 1000000 < Real.log 5 := by
    have h := Real.sum_range_le_log_div (x := (2 / 3 : ℝ)) (by norm_num) (by norm_num) 20
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hlog5_upper : Real.log 5 < (1609438 : ℝ) / 1000000 := by
    have h := Real.log_div_le_sum_range_add (x := (2 / 3 : ℝ)) (by norm_num) (by norm_num) 22
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hlog : (199699 : ℝ) / 10000 * 0.948 < Real.log (2_000_000 / 0.012) ∧
      Real.log (2_000_000 / 0.012) < (199701 : ℝ) / 10000 * 0.948 := by
    have hlog_ratio : Real.log (2_000_000 / 0.012) =
        8 * Real.log 2 + 9 * Real.log 5 - Real.log 3 := by
      calc
        Real.log (2_000_000 / 0.012) = Real.log (((2 : ℝ) ^ 8 * 5 ^ 9) / 3) := by
          norm_num
        _ = Real.log ((2 : ℝ) ^ 8 * 5 ^ 9) - Real.log 3 := by
          rw [Real.log_div] <;> norm_num
        _ = 8 * Real.log 2 + 9 * Real.log 5 - Real.log 3 := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
          ring
    rw [hlog_ratio]
    constructor <;> linarith
  have hdecrement_pos : (0 : ℝ) < 0.948 := by norm_num
  have hcount_lower : (1997 / 100 : ℝ) - 1 / 10000 <
      Real.log (2_000_000 / 0.012) / 0.948 := by
    apply (lt_div_iff₀ hdecrement_pos).mpr
    norm_num at hlog ⊢
    exact hlog.1
  have hcount_upper : Real.log (2_000_000 / 0.012) / 0.948 <
      (1997 / 100 : ℝ) + 1 / 10000 := by
    apply (div_lt_iff₀ hdecrement_pos).mpr
    norm_num at hlog ⊢
    exact hlog.2
  constructor
  · exact hcount
  constructor
  · rw [hcount, abs_lt]
    constructor <;> linarith
  · rw [hcount, abs_lt]
    constructor <;> linarith

/-- T4-A5 asks for the average collision count for a water moderator.  Its
reported integer is therefore retained as a rounding bound, not as an exact
equality of the physical average to `20`. -/
theorem average_collisions_for_water
    (data : NeutronModerationData)
    (hwater : data.matchesWaterData)
    (hlaw : data.satisfiesModerationLaw) :
    |data.averageCollisions - (1997 / 100 : ℝ)| < (1 / 10000 : ℝ) ∧
      |data.averageCollisions - 20| < (1 / 2 : ℝ) := by
  exact (water_collision_count data hwater hlaw).2

end IChO2026Problems.T4A5
