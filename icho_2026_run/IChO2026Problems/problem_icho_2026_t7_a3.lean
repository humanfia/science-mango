import IChO2026Chem
import CRNT.Basic.Reaction
import Mathlib

/-!
# IChO 2026 T7-A3: recirculating Haber--Bosch synthesis

The source models a reactor operated in cycles.  A fresh stoichiometric
`N₂ : H₂ = 1 : 3` gas feed is added after every cycle, a fixed fraction of the
nitrogen entering the reactor reacts, liquid ammonia is separated, and the
unreacted nitrogen and hydrogen are returned as gases.  Amounts below are
numerical values in mol; the chemical species and phases are nevertheless
kept explicit where the recycling model distinguishes them.
-/

namespace IChO2026Problems.T7A3

/-- The three species in the Haber--Bosch synthesis cycle. -/
private inductive HaberBoschSpecies where
  | dinitrogen
  | dihydrogen
  | ammonia
  deriving DecidableEq, Fintype

/-- The phases relevant to the feed, recycle stream, and liquefied product. -/
private inductive ChemicalPhase where
  | gas
  | liquid
  deriving DecidableEq

/-- A numerical amount of one species in one specified phase, measured in mol. -/
private structure PhaseAmount (species : HaberBoschSpecies) (phase : ChemicalPhase) where
  moles : ℝ

/-- The balanced reaction `N₂(g) + 3 H₂(g) → 2 NH₃(l)`.  The liquid phase in
the product records the separation by liquefaction specified in the source. -/
private def haberBoschSynthesis : CRNT.Reaction HaberBoschSpecies where
  source
    | .dinitrogen => 1
    | .dihydrogen => 3
    | .ammonia => 0
  target
    | .dinitrogen => 0
    | .dihydrogen => 0
    | .ammonia => 2

/-- One fresh gas feed having the stoichiometric `N₂ : H₂ = 1 : 3` composition.
The total amount is retained separately because the question supplies it as
`n₀`. -/
private structure StoichiometricGasFeed where
  dinitrogen : PhaseAmount .dinitrogen .gas
  dihydrogen : PhaseAmount .dihydrogen .gas
  totalMoles : ℝ
  dinitrogen_nonnegative : 0 ≤ dinitrogen.moles
  dihydrogen_nonnegative : 0 ≤ dihydrogen.moles
  total_eq_sum : totalMoles = dinitrogen.moles + dihydrogen.moles
  dinitrogen_quarter : dinitrogen.moles = totalMoles / 4
  dihydrogen_three_quarters : dihydrogen.moles = 3 * totalMoles / 4

/-- The constant-yield reactor together with its recurring fresh feed.  The
yield is the fraction of the nitrogen entering a cycle that reacts in that
cycle, so the bounds retain its interpretation as a fraction. -/
private structure CyclicHaberBoschSystem where
  reaction : CRNT.Reaction HaberBoschSpecies
  reaction_is_haber_bosch : reaction = haberBoschSynthesis
  freshFeed : StoichiometricGasFeed
  reactionYield : ℝ
  yield_nonnegative : 0 ≤ reactionYield
  yield_le_one : reactionYield ≤ 1

/-- Nitrogen remaining in the reactor after `cycleCount` completed cycles and
before the next fresh feed is added.  At cycle zero the reactor contains no
residual gas. -/
private def residualNitrogen (system : CyclicHaberBoschSystem) : ℕ → ℝ
  | 0 => 0
  | cycleCount + 1 =>
      (system.freshFeed.dinitrogen.moles + residualNitrogen system cycleCount) *
        (1 - system.reactionYield)

/-- Hydrogen remaining after the same cycle.  Stoichiometric feeding and the
reaction coefficient `3` preserve the `H₂ : N₂ = 3 : 1` ratio in the returned
gas stream. -/
private def residualHydrogen (system : CyclicHaberBoschSystem) (cycleCount : ℕ) : ℝ :=
  3 * residualNitrogen system cycleCount

/-- The recycled dinitrogen stream is a gas stream; it is precisely the
nitrogen amount present in the system before the next feed. -/
private def recycledDinitrogen (system : CyclicHaberBoschSystem) (cycleCount : ℕ) :
    PhaseAmount .dinitrogen .gas :=
  ⟨residualNitrogen system cycleCount⟩

/-- The recycled dihydrogen stream is returned as gas with the stoichiometric
three-to-one ratio to recycled dinitrogen. -/
private def recycledDihydrogen (system : CyclicHaberBoschSystem) (cycleCount : ℕ) :
    PhaseAmount .dihydrogen .gas :=
  ⟨residualHydrogen system cycleCount⟩

/-- The ammonia produced during one cycle is collected as liquid.  Each mole
of nitrogen consumed yields two moles of ammonia by `haberBoschSynthesis`. -/
private def separatedAmmonia (system : CyclicHaberBoschSystem) : ℕ →
    PhaseAmount .ammonia .liquid
  | 0 => ⟨0⟩
  | cycleCount + 1 =>
      ⟨2 * (system.freshFeed.dinitrogen.moles +
        residualNitrogen system cycleCount) * system.reactionYield⟩

/-- The total amount of nitrogen introduced in the first `cycleCount` fresh
feeds.  This is the denominator in the overall nitrogen conversion. -/
private def totalNitrogenFed (system : CyclicHaberBoschSystem) (cycleCount : ℕ) : ℝ :=
  (cycleCount : ℝ) * system.freshFeed.dinitrogen.moles

/-- Overall nitrogen conversion after a positive number of cycles: nitrogen
fed minus nitrogen still present, divided by nitrogen fed.  The later theorem
only invokes this quantity for positive cycle counts. -/
private noncomputable def overallNitrogenConversion
    (system : CyclicHaberBoschSystem) (cycleCount : ℕ) : ℝ :=
  (totalNitrogenFed system cycleCount - residualNitrogen system cycleCount) /
    totalNitrogenFed system cycleCount

/-- The recurrence printed in the official solution. -/
private theorem residual_nitrogen_recurrence
    (system : CyclicHaberBoschSystem) (cycleCount : ℕ) :
    residualNitrogen system (cycleCount + 1) =
      (system.freshFeed.dinitrogen.moles + residualNitrogen system cycleCount) *
        (1 - system.reactionYield) := by
  rfl

/-- The geometric-series form of the residual-nitrogen recurrence.  This is
the relation suggested in part (a), before substituting the supplied values. -/
private theorem residual_nitrogen_eq_geometric_sum
    (system : CyclicHaberBoschSystem) (cycleCount : ℕ) :
    residualNitrogen system cycleCount =
      system.freshFeed.dinitrogen.moles *
        ∑ i ∈ Finset.range cycleCount, (1 - system.reactionYield) ^ (i + 1) := by
  let a : ℝ := system.freshFeed.dinitrogen.moles
  let q : ℝ := 1 - system.reactionYield
  have hres : ∀ n : ℕ,
      residualNitrogen system n = a * q * ∑ i ∈ Finset.range n, q ^ i := by
    intro n
    induction n with
    | zero =>
        simp [residualNitrogen]
    | succ n ih =>
        rw [residual_nitrogen_recurrence, ih]
        have hgeom : q * (∑ i ∈ Finset.range n, q ^ i) + 1 =
            (∑ i ∈ Finset.range n, q ^ i) + q ^ n := by
          nlinarith [geom_sum_mul q n]
        calc
          (a + a * q * ∑ i ∈ Finset.range n, q ^ i) * q =
              a * q * (q * (∑ i ∈ Finset.range n, q ^ i) + 1) := by ring
          _ = a * q * ((∑ i ∈ Finset.range n, q ^ i) + q ^ n) := by rw [hgeom]
          _ = a * q * ∑ i ∈ Finset.range (n + 1), q ^ i := by
            exact congrArg (fun x : ℝ => a * q * x)
              (Finset.sum_range_succ (fun i => q ^ i) n).symm
  rw [hres cycleCount]
  have hshift : (∑ i ∈ Finset.range cycleCount, q ^ (i + 1)) =
      q * ∑ i ∈ Finset.range cycleCount, q ^ i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_succ']
  rw [hshift]
  simp only [a]
  ring

/-- The closed geometric-series expression used in the official calculation.
The nonzero-yield condition is the denominator side condition for this form. -/
private theorem residual_nitrogen_eq_geometric_closed_form
    (system : CyclicHaberBoschSystem) (cycleCount : ℕ)
    (hyield_ne_zero : system.reactionYield ≠ 0) :
    residualNitrogen system cycleCount =
      system.freshFeed.dinitrogen.moles * (1 - system.reactionYield) /
        system.reactionYield *
        (1 - (1 - system.reactionYield) ^ cycleCount) := by
  have hsum : ∑ i ∈ Finset.range cycleCount, (1 - system.reactionYield) ^ i =
      (1 - (1 - system.reactionYield) ^ cycleCount) / system.reactionYield := by
    apply (eq_div_iff hyield_ne_zero).2
    simpa using geom_sum_mul_neg (1 - system.reactionYield) cycleCount
  rw [residual_nitrogen_eq_geometric_sum]
  have hshift : (∑ i ∈ Finset.range cycleCount,
      (1 - system.reactionYield) ^ (i + 1)) =
      (1 - system.reactionYield) *
        ∑ i ∈ Finset.range cycleCount, (1 - system.reactionYield) ^ i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_succ']
  rw [hshift, hsum]
  ring

/-- The two numerical data supplied for T7-A3: `n₀ = 4 mol` and a constant
per-cycle yield `η = 0.150`.  The requested numerical answers are deliberately
not fields of this predicate. -/
private def MatchesT7A3SourceData (system : CyclicHaberBoschSystem) : Prop :=
  system.freshFeed.totalMoles = 4 ∧ system.reactionYield = 3 / 20

/-- Part (a): the nitrogen amount after the 58th completed cycle rounds to
`5.6662 mol` at four decimal places.  The strict half-unit-in-the-last-place
bound states the rounding guarantee rather than treating the displayed answer
as an exact measured quantity. -/
theorem nitrogen_amount_after_fifty_eighth_cycle
    (system : CyclicHaberBoschSystem)
    (hsource : MatchesT7A3SourceData system) :
    |residualNitrogen system 58 - (56662 : ℝ) / 10000| < (1 : ℝ) / 20000 := by
  rcases hsource with ⟨htotal, hyield⟩
  have hnitrogen : system.freshFeed.dinitrogen.moles = 1 := by
    rw [system.freshFeed.dinitrogen_quarter, htotal]
    norm_num
  norm_num [residualNitrogen, hnitrogen, hyield]

/-- Part (b): the first cycle has the stated 15.0% overall yield, and 189 is
the least positive whole number of cycles for which the overall conversion
reaches 97.0%. -/
theorem cycles_needed_for_ninety_seven_percent_overall_yield
    (system : CyclicHaberBoschSystem)
    (hsource : MatchesT7A3SourceData system) :
    overallNitrogenConversion system 1 = 3 / 20 ∧
      97 / 100 ≤ overallNitrogenConversion system 189 ∧
        ∀ cycleCount : ℕ, 0 < cycleCount → cycleCount < 189 →
          overallNitrogenConversion system cycleCount < 97 / 100 := by
  rcases hsource with ⟨htotal, hyield⟩
  have hnitrogen : system.freshFeed.dinitrogen.moles = 1 := by
    rw [system.freshFeed.dinitrogen_quarter, htotal]
    norm_num
  have hresidual_formula : ∀ n : ℕ,
      residualNitrogen system n = (17 : ℝ) / 3 * (1 - ((17 : ℝ) / 20) ^ n) := by
    intro n
    induction n with
    | zero =>
        norm_num [residualNitrogen]
    | succ n ih =>
        rw [residual_nitrogen_recurrence, ih, hnitrogen, hyield, pow_succ]
        ring
  constructor
  · norm_num [overallNitrogenConversion, totalNitrogenFed, hnitrogen,
      hresidual_formula]
  constructor
  · norm_num [overallNitrogenConversion, totalNitrogenFed, hnitrogen,
      hresidual_formula]
  · intro cycleCount hpositive hbefore
    by_cases hsmall : cycleCount < 34
    · interval_cases cycleCount <;>
        norm_num [overallNitrogenConversion, totalNitrogenFed, residualNitrogen,
          hnitrogen, hyield] at hpositive hbefore ⊢
    · have hthirty_four_le : 34 ≤ cycleCount := by omega
      have hresidual_upper : ∀ n : ℕ, residualNitrogen system n < (17 : ℝ) / 3 := by
        intro n
        rw [hresidual_formula]
        have hpow_pos : 0 < ((17 : ℝ) / 20) ^ n := pow_pos (by norm_num) n
        nlinarith
      have hresidual_step : ∀ n : ℕ,
          residualNitrogen system n ≤ residualNitrogen system (n + 1) := by
        intro n
        rw [residual_nitrogen_recurrence, hnitrogen, hyield]
        nlinarith [hresidual_upper n]
      have hresidual_mono : Monotone (residualNitrogen system) :=
        monotone_nat_of_le_succ hresidual_step
      have hcycle_upper : cycleCount ≤ 188 := by omega
      have hresidual_at_thirty_four : (141 : ℝ) / 25 < residualNitrogen system 34 := by
        norm_num [hresidual_formula]
      have hresidual_lower : (141 : ℝ) / 25 < residualNitrogen system cycleCount :=
        lt_of_lt_of_le hresidual_at_thirty_four (hresidual_mono hthirty_four_le)
      have hcycle_positive_real : 0 < (cycleCount : ℝ) := by
        exact_mod_cast hpositive
      have hcycle_upper_real : (cycleCount : ℝ) ≤ 188 := by
        exact_mod_cast hcycle_upper
      rw [overallNitrogenConversion, totalNitrogenFed, hnitrogen]
      norm_num only [mul_one]
      apply (div_lt_iff₀ hcycle_positive_real).2
      nlinarith

/-- T7-A3 exposes both requested outputs: the four-decimal nitrogen amount in
part (a), and the least cycle count attaining 97% overall conversion in part
(b). -/
theorem recirculating_haber_bosch_answers :
    (∀ system : CyclicHaberBoschSystem,
      MatchesT7A3SourceData system →
        |residualNitrogen system 58 - (56662 : ℝ) / 10000| < (1 : ℝ) / 20000) ∧
    (∀ system : CyclicHaberBoschSystem,
      MatchesT7A3SourceData system →
        overallNitrogenConversion system 1 = 3 / 20 ∧
          97 / 100 ≤ overallNitrogenConversion system 189 ∧
            ∀ cycleCount : ℕ, 0 < cycleCount → cycleCount < 189 →
              overallNitrogenConversion system cycleCount < 97 / 100) := by
  constructor
  · exact nitrogen_amount_after_fifty_eighth_cycle
  · exact cycles_needed_for_ninety_seven_percent_overall_yield

end IChO2026Problems.T7A3
