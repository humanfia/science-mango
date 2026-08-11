import Mathlib
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026, Theory Problem T4, part 4.8 — Urtabulak blowout: daily combustion energy

58th International Chemistry Olympiad, Tashkent 2026, Problem T4
("The Nuclear Past of Uzbekistan"), subquestion 4.8 (2 points).

## Source contract

> **Assume** that methane is flowing out the well at 101.325 kPa and 298 K with
> volumetric flow `Q = 2.2 × 10⁵ m³` per day before it catches fire.
>
> **4.8. Calculate** the total energy released per day, `E`, (in J day⁻¹) by
> complete isothermic combustion of methane at `T = 2000 K`.

The marking scheme reads the volumetric flow as a *daily* volume
(`n = PV/RT = 101325 Pa × 2.2 × 10⁵ m³ / (8.314 J mol⁻¹ K⁻¹ × 298 K)
= 9.00 × 10⁶ mol day⁻¹`), uses the Part-4.7 enthalpy
`ΔrH°₂₀₀₀ = −781.9 kJ mol⁻¹` (computed there from the sourced formation
enthalpies and heat capacities via Kirchhoff's law), and records
`E = 7.04 × 10¹² J day⁻¹`.  The source also licenses the fallback branch
`ΔH₂₀₀₀ = −700 kJ mol⁻¹` ("if you did not get an answer for 4.7"), for which
the recorded answer is `E = 6.30 × 10¹² J day⁻¹`.

## Assumption / target split

*Assumptions* (structure `UrtabulakBlowout`): the sourced data `P`, `T`, `Q`,
`R`, the isothermal combustion temperature `2000 K`, and the two governing
relations — the ideal-gas law `P·Q = n·R·T` at the well conditions and the
energy balance `E = −n·ΔrH₂₀₀₀·1000` for complete isothermal combustion.
The Part-4.7 conclusion is a natural-language prerequisite
(`natural_language_prerequisite_only`): it enters only as the explicit
hypothesis `hreactionEnthalpy` of the main theorem, never as a definition.
The fallback value `−700 kJ mol⁻¹` is the alternative branch printed in the
source; both branches are preserved as separate theorems.

*Targets*: the molar flow `n ≈ 9.00 × 10⁶ mol day⁻¹` (marking-scheme
intermediate), and the requested daily energy `E ≈ 7.04 × 10¹² J day⁻¹`
(main) resp. `E ≈ 6.30 × 10¹² J day⁻¹` (fallback).  All numerical readouts
are reals in the documented SI units; each approximation is stated as a
two-sided bound at the precision the data support (the scheme's intermediate
rounding `n = 9.00 × 10⁶` and the direct evaluation differ by less than the
stated tolerance).
-/

namespace IChO2026.T4.A8

/-! ## Unit-carrying numerical readouts

Following the project convention (`IChO2026Chem.Kinetics.BelousovZhabotinsky`),
physical quantities are represented by their real numerical readouts in the
corresponding source units. -/

/-- A pressure readout in pascal (Pa). -/
abbrev PressurePa := ℝ

/-- A temperature readout in kelvin (K). -/
abbrev TemperatureK := ℝ

/-- A volumetric flow readout in m³ day⁻¹. -/
abbrev VolumeFlowM3PerDay := ℝ

/-- A molar flow readout in mol day⁻¹. -/
abbrev MolarFlowMolPerDay := ℝ

/-- A molar reaction enthalpy readout in kJ mol⁻¹. -/
abbrev MolarEnthalpyKJPerMol := ℝ

/-- An energy flow readout in J day⁻¹. -/
abbrev EnergyFlowJPerDay := ℝ

/-- A gas constant readout in J mol⁻¹ K⁻¹. -/
abbrev GasConstantSI := ℝ

/-! ## Species and the combustion reaction -/

/-- The species of the methane combustion; per the source (parts 4.6–4.8) all
species are gaseous, including the water produced at 2000 K. -/
inductive Species where
  /-- Methane, CH₄(g): the fuel flowing out of the Urtabulak well. -/
  | methane
  /-- Dioxygen, O₂(g): the oxidant. -/
  | oxygen
  /-- Carbon dioxide, CO₂(g): combustion product. -/
  | carbonDioxide
  /-- Water vapour, H₂O(g): combustion product. -/
  | water
  deriving DecidableEq, Repr

deriving instance Fintype for Species

/-- The complete combustion of methane with all species gaseous,
`CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g)`, as a CRNT reaction.  One firing of
this reaction is the "one mole of methane combustion reaction" to which the
molar reaction enthalpies of parts 4.6–4.8 refer. -/
def methaneCombustion : CRNT.Reaction Species where
  source := fun
    | .methane => 1
    | .oxygen => 2
    | _ => 0
  target := fun
    | .carbonDioxide => 1
    | .water => 2
    | _ => 0

/-! ## The data bundle and governing relations -/

/-- The Urtabulak well-blowout data bundle for part 4.8: the sourced numerical
data, the two governing relations assumed by the source, and the derived
quantities they pin down.

The two law fields are exactly the relations the marking scheme uses:
the ideal-gas law at the well conditions (where the volumetric flow is
metered) and the isothermal-combustion energy balance at 2000 K. -/
structure UrtabulakBlowout where
  /-- Well-exit pressure `P` (source: 101.325 kPa = 101325 Pa). -/
  pressure : PressurePa
  /-- Temperature at which the volumetric flow is metered (source: 298 K). -/
  flowTemperature : TemperatureK
  /-- Volumetric methane flow `Q` at the well (source: 2.2 × 10⁵ m³ day⁻¹). -/
  volumeFlow : VolumeFlowM3PerDay
  /-- Universal gas constant `R` (marking scheme: 8.314 J mol⁻¹ K⁻¹). -/
  gasConstant : GasConstantSI
  /-- Molar methane flow `n` determined by the ideal-gas law. -/
  molarFlow : MolarFlowMolPerDay
  /-- Temperature of the isothermal combustion (source: `T = 2000 K`). -/
  combustionTemperature : TemperatureK
  /-- Standard molar enthalpy `ΔrH°₂₀₀₀` of `methaneCombustion` at the
  combustion temperature, per mole of CH₄; negative because combustion is
  exothermic.  Its value is the Part-4.7 conclusion (or the printed
  fallback), supplied as a hypothesis of the theorems below. -/
  reactionEnthalpy : MolarEnthalpyKJPerMol
  /-- Total energy released per day `E` by the combustion. -/
  energyPerDay : EnergyFlowJPerDay
  /-- Source data: the well pressure is 101.325 kPa. -/
  pressure_value : pressure = 101325
  /-- Source data: the flow is metered at 298 K. -/
  flowTemperature_value : flowTemperature = 298
  /-- Source data: the volumetric flow is 2.2 × 10⁵ m³ day⁻¹. -/
  volumeFlow_value : volumeFlow = 2.2 * 10 ^ 5
  /-- Marking-scheme constant: `R = 8.314 J mol⁻¹ K⁻¹`. -/
  gasConstant_value : gasConstant = 8.314
  /-- Source condition: the combustion is isothermal at `T = 2000 K`. -/
  combustionTemperature_value : combustionTemperature = 2000
  /-- Governing relation (ideal gas at the well conditions): `P·Q = n·R·T`. -/
  ideal_gas_law : pressure * volumeFlow = molarFlow * gasConstant * flowTemperature
  /-- Governing relation (complete isothermal combustion at 2000 K): each mole
  of methane releases `−ΔrH°₂₀₀₀`; with the kJ → J conversion the daily energy
  is `E = −n·ΔrH°₂₀₀₀·1000`. -/
  energy_balance : energyPerDay = - (molarFlow * reactionEnthalpy * 1000)

namespace UrtabulakBlowout

/-- The molar flow pinned down by the ideal-gas law: `n = P·Q / (R·T)`. -/
theorem molarFlow_eq (w : UrtabulakBlowout) :
    w.molarFlow = w.pressure * w.volumeFlow / (w.gasConstant * w.flowTemperature) := by
  have hRT : w.gasConstant * w.flowTemperature ≠ 0 := by
    rw [w.gasConstant_value, w.flowTemperature_value]
    norm_num
  rw [eq_div_iff_mul_eq hRT]
  linear_combination -w.ideal_gas_law

/-- Marking-scheme intermediate: the molar methane flow is
`9.00 × 10⁶ mol day⁻¹` at the precision of the data
(direct evaluation gives `8.997 × 10⁶`). -/
theorem molarFlow_value (w : UrtabulakBlowout) :
    |w.molarFlow - 9.00 * 10 ^ 6| ≤ 3 * 10 ^ 4 := by
  rw [w.molarFlow_eq, w.pressure_value, w.volumeFlow_value, w.gasConstant_value,
    w.flowTemperature_value]
  norm_num [abs_le]

/-- **T4-A8, main branch.**  With the Part-4.7 result
`ΔrH°₂₀₀₀ = −781.9 kJ mol⁻¹` (a reusable previous-part conclusion, restated
here as an explicit hypothesis per the `natural_language_prerequisite_only`
policy), the total energy released per day by the complete isothermal
combustion of the methane at 2000 K is `7.04 × 10¹² J day⁻¹` at the precision
of the data. -/
theorem energyPerDay_value (w : UrtabulakBlowout)
    (hreactionEnthalpy : w.reactionEnthalpy = -781.9) :
    |w.energyPerDay - 7.04 * 10 ^ 12| ≤ 1 * 10 ^ 10 := by
  have hbal := w.energy_balance
  rw [hreactionEnthalpy] at hbal
  rw [hbal, w.molarFlow_eq, w.pressure_value, w.volumeFlow_value,
    w.gasConstant_value, w.flowTemperature_value]
  norm_num [abs_le]

/-- **T4-A8, fallback branch.**  The source licenses the substitute value
`ΔH₂₀₀₀ = −700 kJ mol⁻¹` "if you did not get an answer for 4.7"; the recorded
daily energy is then `6.30 × 10¹² J day⁻¹` at the precision of the data. -/
theorem energyPerDay_fallback (w : UrtabulakBlowout)
    (hreactionEnthalpy : w.reactionEnthalpy = -700) :
    |w.energyPerDay - 6.30 * 10 ^ 12| ≤ 2 * 10 ^ 9 := by
  have hbal := w.energy_balance
  rw [hreactionEnthalpy] at hbal
  rw [hbal, w.molarFlow_eq, w.pressure_value, w.volumeFlow_value,
    w.gasConstant_value, w.flowTemperature_value]
  norm_num [abs_le]

end UrtabulakBlowout

end IChO2026.T4.A8
