import Mathlib
import IChO2026Chem
import IChO2026Chem.Kinetics.BelousovZhabotinsky

/-!
# IChO 2026 T2-A3: critical bromide concentration in the BZ reaction

The scalar quantities below use the numerical units printed in the source:
concentrations are in `M` and the two rate constants are in `M⁻² s⁻¹`.
The species labels are retained separately from their numerical concentrations.
-/

namespace IChO2026Problems.T2A3

open IChO2026Chem.Kinetics.BelousovZhabotinsky

/--
The supplied constants and the concentrations at one switching point.
The exact source values are data.  In contrast, the critical bromide
concentration is not fixed here: it remains a component to be determined from
the switching-rate equality.
-/
structure BZSwitchingData where
  parameters : KineticParameters
  state : State
  rateConstant1_value : parameters.k1 = 10 ^ 4
  rateConstant4_value : parameters.k4 = 2 * 10 ^ 9
  bromate_value : state .bromate = 0.06
  concentrations_nonnegative : ∀ species, 0 ≤ state species
  bromousAcid_positive : 0 < state .hbro2
  proton_positive : 0 < state .proton

/-- Rate of elementary step (1), `HBrO₂ + BrO₃⁻ + H⁺ → 2 BrO₂• + H₂O`. -/
def processARate (data : BZSwitchingData) : ℝ :=
  rate1 data.parameters data.state

/-- Rate of elementary step (4), `HBrO₂ + Br⁻ + H⁺ → 2 HBrO`. -/
def processBRate (data : BZSwitchingData) : ℝ :=
  rate4 data.parameters data.state

/--
At a switch, equality of the rates of steps (1) and (4) lets the positive
common concentrations of `HBrO₂` and `H⁺` be cancelled.
-/
theorem switching_rate_balance
    (data : BZSwitchingData)
    (hswitch : processARate data = processBRate data) :
    data.parameters.k1 * data.state .bromate =
      data.parameters.k4 * data.state .bromide := by
  apply rate1_eq_rate4_of_positive data.parameters data.state
    data.bromousAcid_positive data.proton_positive
  exact hswitch

/--
The rate balance at the A/B switch gives the source formula and its numerical
critical bromide concentration, `3.0 × 10⁻⁷ M`.  No concentration conclusion
from T2-A2 is assumed.
-/
theorem critical_bromide_concentration
    (data : BZSwitchingData)
    (hswitch : processARate data = processBRate data) :
    data.state .bromide =
        (data.parameters.k1 / data.parameters.k4) * data.state .bromate ∧
      data.state .bromide = (3 : ℝ) / 10 ^ 7 := by
  have hbalance := switching_rate_balance data hswitch
  have hk4_ne : data.parameters.k4 ≠ 0 := by
    rw [data.rateConstant4_value]
    norm_num
  constructor
  · rw [div_mul_eq_mul_div]
    apply (eq_div_iff hk4_ne).mpr
    simpa [mul_comm] using hbalance.symm
  · rw [data.rateConstant1_value, data.rateConstant4_value, data.bromate_value] at hbalance
    norm_num at hbalance ⊢
    linarith

end IChO2026Problems.T2A3
