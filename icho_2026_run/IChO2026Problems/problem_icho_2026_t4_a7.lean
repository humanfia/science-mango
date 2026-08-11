import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Theory Problem 4, part 4.7 — combustion enthalpy of methane at 2000 K

Source: 58th International Chemistry Olympiad, Tashkent 2026, Theory Problem T4
("The Nuclear Past of Uzbekistan"), question 4.7 (problem PDF page 39, printed
page Q4-3; thermodynamic data table printed on page Q4-2).

## Question

Calculate `Δ_r H_2000` (kJ mol⁻¹) per mole of methane combustion reaction at
2000 K.  Assume all species are gaseous.

## Assumption / target split

Assumptions (all carried as explicit structure fields or hypotheses below):

* the balanced equation concluded in part 4.6 and reused here as a natural
  language prerequisite (policy `natural_language_prerequisite_only`):
  `CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g)`;
* the part-4.6 result `Δ_r H°_298 = -802.3 kJ mol⁻¹`, restated as the anchor
  hypothesis `anchor` of the main theorem (never as a definition);
* the source-supplied heat capacities, assumed temperature-independent:
  `C_P(CH₄) = 35`, `C_P(H₂O, g) = 34`, `C_P(O₂) = 29`, `C_P(CO₂) = 37`
  (numerical readouts in J mol⁻¹ K⁻¹, exactly as printed in the Q4-2 table);
* the side condition that every species is gaseous;
* Kirchhoff's law under the constant-heat-capacity assumption,
  `ΔH(T) = ΔH(298 K) + ΔC_P · (T − 298 K)`, with the J → kJ conversion
  (`/ 1000`) made explicit, since the table mixes J and kJ.

Requested conclusions (rubric: 1 point for `ΔC_P`, 1 point for `Δ_r H_2000`):

* `ΔC_P = 12 J mol⁻¹ K⁻¹` (`deltaHeatCapacity_value`);
* `Δ_r H_2000 = -781.876 kJ mol⁻¹`, reported as `-781.9 kJ mol⁻¹`
  (`reactionEnthalpy_2000`, `reactionEnthalpy_2000_rounded`);
* the sanctioned alternative branch using the part-4.6 fallback value
  `ΔH_298 = -750 kJ mol⁻¹`, giving `-729.576 kJ mol⁻¹` ≈ `-729.6 kJ mol⁻¹`
  (`reactionEnthalpy_2000_fallback`, `reactionEnthalpy_2000_fallback_rounded`).

The 4.7 question box also prints "If you did not get an answer for 4.7, use
`ΔH_2000 = -700 kJ mol⁻¹` for further calculations."  That fallback concerns
later parts (4.8) only; it is not derivable from the 4.7 data and is therefore
recorded only in this comment, not as a Lean declaration.

Blueprint target: `thm:physics:icho_2026_t4_a7:target`.
-/

namespace IChO2026T4A7

/-- The four chemical species of the methane combustion reaction
`CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g)` of IChO 2026 T4, parts 4.6–4.7.
Water appears as the vapour, matching the table row `C_P(H₂O, gas)`. -/
inductive Species where
  | methane
  | oxygen
  | carbonDioxide
  | waterVapor
  deriving DecidableEq, Repr

deriving instance Fintype for Species

/-- The phases the problem statement distinguishes; part 4.7 fixes every
species in the gas phase. -/
inductive Phase where
  | gas
  | liquid
  | solid
  deriving DecidableEq, Repr

/-- Signed stoichiometric coefficients of the balanced combustion equation
`CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g)`, products positive and reactants
negative, per mole of methane.  The balanced equation is the reusable
conclusion of part 4.6. -/
def stoichiometricCoefficient : Species → ℝ
  | .methane => -1
  | .oxygen => -2
  | .carbonDioxide => 1
  | .waterVapor => 2

/-- The thermodynamic data supplied for parts 4.6–4.7: a phase assignment
witnessing the "all species are gaseous" side condition, and the printed
molar heat capacities (numerical readouts in J mol⁻¹ K⁻¹), which the marking
scheme treats as constant between 298 K and 2000 K. -/
structure ThermodynamicData where
  /-- Phase of each species. -/
  phase : Species → Phase
  /-- Side condition of part 4.7: all species are gaseous. -/
  phase_all_gas : ∀ s : Species, phase s = .gas
  /-- Molar heat capacity at constant pressure, readout in J mol⁻¹ K⁻¹,
  assumed independent of temperature over the range used. -/
  heatCapacity : Species → ℝ
  /-- Printed table value `C_P(CH₄) = 35 J mol⁻¹ K⁻¹`. -/
  heatCapacity_methane : heatCapacity .methane = 35
  /-- Printed table value `C_P(O₂) = 29 J mol⁻¹ K⁻¹`. -/
  heatCapacity_oxygen : heatCapacity .oxygen = 29
  /-- Printed table value `C_P(CO₂) = 37 J mol⁻¹ K⁻¹`. -/
  heatCapacity_carbonDioxide : heatCapacity .carbonDioxide = 37
  /-- Printed table value `C_P(H₂O, gas) = 34 J mol⁻¹ K⁻¹`. -/
  heatCapacity_waterVapor : heatCapacity .waterVapor = 34

/-- The reaction heat-capacity change `ΔC_P = Σ_s ν_s · C_P(s)` of the
combustion as written, in J mol⁻¹ K⁻¹ per mole of methane. -/
def deltaHeatCapacity (heatCapacity : Species → ℝ) : ℝ :=
  ∑ s : Species, stoichiometricCoefficient s * heatCapacity s

/-- A Kirchhoff model of the combustion enthalpy: the molar reaction enthalpy
(readout in kJ mol⁻¹ per mole of methane) as a function of the absolute
temperature in kelvin, obeying Kirchhoff's law anchored at 298 K under the
constant-heat-capacity assumption.  The division by 1000 converts the
J mol⁻¹ K⁻¹ of `ΔC_P` into the kJ mol⁻¹ used for the enthalpy. -/
structure KirchhoffModel (data : ThermodynamicData) where
  /-- Molar reaction enthalpy in kJ mol⁻¹ at temperature `T` in K. -/
  reactionEnthalpy : ℝ → ℝ
  /-- Kirchhoff's law with constant heat capacities:
  `ΔH(T) = ΔH(298) + ΔC_P · (T − 298) / 1000`. -/
  kirchhoff :
    ∀ T : ℝ, reactionEnthalpy T =
      reactionEnthalpy 298 + deltaHeatCapacity data.heatCapacity * (T - 298) / 1000

/-- `ΔC_P` in the explicit grouped form used by the marking scheme,
`[C_P(CO₂) + 2 C_P(H₂O)] − [C_P(CH₄) + 2 C_P(O₂)]`. -/
theorem deltaHeatCapacity_eq (heatCapacity : Species → ℝ) :
    deltaHeatCapacity heatCapacity =
      (heatCapacity .carbonDioxide + 2 * heatCapacity .waterVapor) -
        (heatCapacity .methane + 2 * heatCapacity .oxygen) := by
  unfold deltaHeatCapacity
  have huniv : (Finset.univ : Finset Species) =
      {.methane, .oxygen, .carbonDioxide, .waterVapor} := by
    ext s
    cases s <;> simp
  rw [huniv]
  simp [stoichiometricCoefficient]
  ring

/-- Rubric item 1: the heat-capacity change evaluates to
`ΔC_P = [37 + 2·34] − [35 + 2·29] = 12 J mol⁻¹ K⁻¹`. -/
theorem deltaHeatCapacity_value (data : ThermodynamicData) :
    deltaHeatCapacity data.heatCapacity = 12 := by
  rw [deltaHeatCapacity_eq, data.heatCapacity_carbonDioxide,
    data.heatCapacity_waterVapor, data.heatCapacity_methane,
    data.heatCapacity_oxygen]
  norm_num

/-- Kirchhoff's law evaluated at `T = 2000 K`: the enthalpy shift relative to
the 298 K anchor is `12 · (2000 − 298) / 1000 = 20.424 kJ mol⁻¹`.  This form
keeps the anchor symbolic so that both answer branches share one derivation. -/
theorem reactionEnthalpy_2000_eq_anchor_add (data : ThermodynamicData)
    (model : KirchhoffModel data) :
    model.reactionEnthalpy 2000 = model.reactionEnthalpy 298 + 20.424 := by
  rw [model.kirchhoff 2000, deltaHeatCapacity_value data]
  norm_num

/-- Main target of part 4.7: with the part-4.6 anchor
`Δ_r H°_298 = -802.3 kJ mol⁻¹` (restated as an explicit hypothesis under the
`natural_language_prerequisite_only` policy), Kirchhoff's law gives
`Δ_r H°_2000 = -802.3 + 20.424 = -781.876 kJ mol⁻¹`. -/
theorem reactionEnthalpy_2000 (data : ThermodynamicData)
    (model : KirchhoffModel data)
    (anchor : model.reactionEnthalpy 298 = -802.3) :
    model.reactionEnthalpy 2000 = -781.876 := by
  rw [reactionEnthalpy_2000_eq_anchor_add data model, anchor]
  norm_num

/-- The reported value, rounded to one decimal place as in the marking
scheme: `Δ_r H°_2000 = -781.9 kJ mol⁻¹`. -/
theorem reactionEnthalpy_2000_rounded (data : ThermodynamicData)
    (model : KirchhoffModel data)
    (anchor : model.reactionEnthalpy 298 = -802.3) :
    (round (model.reactionEnthalpy 2000 * 10) : ℝ) / 10 = -781.9 := by
  rw [reactionEnthalpy_2000 data model anchor]
  have hround : round (-781.876 * 10 : ℝ) = -7819 := by
    rw [round_eq, Int.floor_eq_iff]
    constructor <;> norm_num
  rw [hround]
  norm_num

/-- Alternative answer branch sanctioned by the marking scheme: a contestant
who used the part-4.6 fallback `ΔH_298 = -750 kJ mol⁻¹` obtains
`Δ_r H_2000 = -750 + 20.424 = -729.576 kJ mol⁻¹`. -/
theorem reactionEnthalpy_2000_fallback (data : ThermodynamicData)
    (model : KirchhoffModel data)
    (anchor : model.reactionEnthalpy 298 = -750) :
    model.reactionEnthalpy 2000 = -729.576 := by
  rw [reactionEnthalpy_2000_eq_anchor_add data model, anchor]
  norm_num

/-- The fallback branch rounded to one decimal place:
`Δ_r H_2000 = -729.6 kJ mol⁻¹`. -/
theorem reactionEnthalpy_2000_fallback_rounded (data : ThermodynamicData)
    (model : KirchhoffModel data)
    (anchor : model.reactionEnthalpy 298 = -750) :
    (round (model.reactionEnthalpy 2000 * 10) : ℝ) / 10 = -729.6 := by
  rw [reactionEnthalpy_2000_fallback data model anchor]
  have hround : round (-729.576 * 10 : ℝ) = -7296 := by
    rw [round_eq, Int.floor_eq_iff]
    constructor <;> norm_num
  rw [hround]
  norm_num

end IChO2026T4A7
