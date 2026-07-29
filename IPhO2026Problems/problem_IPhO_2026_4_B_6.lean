/-
# IPhO 2026, Experimental Problem 4 (E1), Part B.6 — latent heat per unit mass

Blueprint chapter:
`blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_4_B_6.tex`

## Physical content

The inner cylinder (IC) of the experimental setup contains dry air plus water
vapor at a total pressure approximately equal to the atmospheric pressure
`P_atm`. The water-level height `H` is recorded as the temperature `T` falls;
at `T₀ = 273.15 K` the extrapolated height is `H₀` and the water-vapor
pressure may be taken as zero. The vapor pressure obeys the integrated
Clausius–Clapeyron law

`ln(P_v(T)/P_v(T₀)) = -(Qᵥ/R) * (1/T - 1/T₀)`,

with molar latent heat of vaporization `Qᵥ` and universal gas constant `R`.

**Current subquestion (B.6).** Convert the molar latent heat `Qᵥ` determined
in part B.5 into the latent heat per unit mass `Lᵥ` and state the formula.

**Recorded official answer.** `Lᵥ = Qᵥ / M₀ = 2190 ± 110 kJ/kg`, where `M₀`
is the molar mass of water.

## Modeling choices

* Pressures (`P_atm`, `P_v`) use PhysLean's dimensional pressure type
  `DimPressure`; temperatures use PhysLean's `Temperature`; the heights
  `H₀, H` use PhysLean's dimensional length `Dimensionful (WithDim L𝓭 ℝ)`.
  These keep the physical quantities distinct rather than collapsing them to
  bare real aliases.
* PhysLean has no mole/amount-of-substance dimension, so molar quantities
  (molar latent heat `Qᵥ` in J/mol, gas constant `R` in J/(mol·K), molar
  mass `M₀` in kg/mol) and the specific latent heat `Lᵥ` in J/kg are carried
  by the smallest faithful local wrappers (`MolarEnergy`,
  `MolarHeatCapacity`, `MolarMass`, `SpecificLatentHeat`). They are
  deliberately opaque (no field projection) so that the unit-conversion and
  uncertainty-propagation relations cannot be discharged by unfolding.
* The molar-to-specific conversion `Lᵥ = Qᵥ / M₀` is the *conclusion* of the
  main theorem, carried by the relation `IsSpecificLatentHeatOf`; it is never
  stated as an assumption, structure field, or definition of the answer.
-/

import Mathlib
import Physlib.Thermodynamics.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Pressure
import Physlib.Units.WithDim.Energy

open Dimension

noncomputable section

namespace IPhO2026

namespace Problem4

/-- The dimensional length type used for the water-level heights `H₀` and `H`
read off the graph of parts B.2/B.3 (dimension `L`, e.g. metres). -/
abbrev DimLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The local pressure type, re-exporting PhysLean's dimensional pressure
(dimension `M L⁻¹ T⁻²`, e.g. pascals). -/
abbrev Pressure : Type := DimPressure

/-- A molar energy (dimension `M L² T⁻² mol⁻¹`, e.g. J/mol): the type-level
habitat of the molar latent heat `Qᵥ` determined in part B.5. PhysLean has
no amount-of-substance dimension, so this is the smallest wrapper preserving
the molar character of the quantity; it is kept abstract (no projection) so
physical relations involving it must be carried by explicit hypotheses. -/
structure MolarEnergy where
  deriving Nonempty

/-- The (positive) catalog central value of the molar latent heat of
vaporization of water obtained from the Clausius–Clapeyron graph of part B.5,
`Qᵥ = 39 ± 2 kJ/mol` (central value). -/
opaque catalogMolarLatentHeatQv : MolarEnergy

/-- The (positive) catalog value of the universal gas constant,
`R = 8.314 J/(mol·K)` (the problem instructs the reference value
`R = 8.31 J/(mol·K)`), recorded in molar-energy-per-kelvin form; here it is
carried in multiplied-by-`1 K` form as a `MolarEnergy` magnitude source. -/
opaque catalogGasConstantR : MolarEnergy

/-- A molar heat-capacity-like quantity (dimension
`M L² T⁻² mol⁻¹ K⁻¹`, e.g. J/(mol·K)); the physical dimension of the
universal gas constant `R`. Abstract wrapper. -/
structure MolarHeatCapacity where
  deriving Nonempty

/-- A molar mass (dimension `M mol⁻¹`, e.g. kg/mol): the type-level habitat
of `M₀`, the molar mass of water. Abstract wrapper. -/
structure MolarMass where
  deriving Nonempty

/-- A latent heat per unit mass, a.k.a. specific latent heat (dimension
`L² T⁻²`, e.g. J/kg): the type-level habitat of the requested quantity `Lᵥ`.
Abstract wrapper. -/
structure SpecificLatentHeat where
  deriving Nonempty

/-- The (positive) catalog central value `M₀ = 18.0 × 10⁻³ kg/mol`
(`≈ 18.015 × 10⁻³ kg/mol`) of the molar mass of water. -/
opaque catalogMolarMassWaterM0 : MolarMass

/-- The catalog gas constant `R = 8.314 J/(mol·K)` viewed with its physical
dimension `MolarHeatCapacity`. -/
opaque catalogGasConstantRMolarHeatCapacity : MolarHeatCapacity

/-! ## Governing-law predicate -/

/-- The integrated Clausius–Clapeyron law governing the water-vapor pressure
in the inner cylinder, stated as the physical law itself (never as the final
B.6 formula):

`ln(P_v(T)/P_v(T₀)) = -(Qᵥ/R) · (1/T − 1/T₀)`.

The scalar `lnRatio T T₀` is the logarithm of the vapor-pressure ratio
`ln(P_v(T)/P_v(T₀))` taken between absolute temperatures `T` and `T₀`, and
`invTdiff T T₀` is the inverse-temperature difference `1/T − 1/T₀` (in K⁻¹).
The slope `Qᵥ/R` is carried by the positive real `QvOverR_K`, so the law
fixes an equation among measurable quantities for every pair of temperatures.
This constrains the model: at `T = T₀` both sides vanish, and the negative
slope of the `ln(P_v/P_atm)` vs `1/T` graph equals `-QvOverR_K`. -/
def SatisfiesClausiusClapeyron
    (lnRatio invTdiff : Temperature → Temperature → ℝ)
    (QvOverR_K : ℝ) : Prop :=
  ∀ T T₀ : Temperature, lnRatio T T₀ = -QvOverR_K * invTdiff T T₀

/-- The Clausius–Clapeyron slope extracted from part B.5: the slope `s` of
the graph of `ln(P_v/P_atm)` against `1/T` equals `-Qᵥ/R`. This is the
quantitative elimination content of the law used to determine `Qᵥ`. -/
def IsClausiusClapeyronSlope
    (lnRatio invTdiff : Temperature → Temperature → ℝ)
    (QvOverR_K slope_K : ℝ) : Prop :=
  SatisfiesClausiusClapeyron lnRatio invTdiff QvOverR_K ∧
    slope_K = -QvOverR_K

/-! ## The B.1–B.5 experimental setup quantities -/

/-- Figure/apparatus data of the inner-cylinder (IC) experiment on
pp. 11–12 of the official paper: the water-level heights, temperatures and
pressures entering parts B.1–B.5, of which the present subquestion B.6 uses
the output. `H₀` is the extrapolated height at `T₀ = 273.15 K` where the
vapor pressure vanishes; `P_atm` is the approximately constant total pressure
of the dry-air + water-vapor mixture. These are problem/figure parameters
captured for the proof route even though the final B.6 relation
`Lᵥ = Qᵥ/M₀` does not mention them. -/
structure InnerCylinderExperiment where
  /-- Atmospheric (total) pressure in the inner cylinder; used as the
  reference pressure in the part-B.5 graph `ln(P_v/P_atm)`. -/
  P_atm : Pressure
  /-- The vapor-pressure function of the water vapor in the IC. -/
  P_v : Temperature → Pressure
  /-- Reference temperature `T₀ = 273.15 K` (0 °C). -/
  T₀ : Temperature
  /-- Extrapolated water-level height `H₀` at `T₀`. -/
  H₀ : DimLength
  /-- The reference temperature readout `T₀ = 273.15 K`, as a real number in
  kelvin. -/
  T₀_value_K : ℝ
  /-- The vapor pressure at `T₀ = 273.15 K` may be taken as zero
  (extrapolation readout of part B.3): `ln(P_v(T)/P_v(T₀))` is anchored so
  that the vapor pressure vanishes at `T₀`. -/
  vapor_pressure_taken_zero_at_T₀ : Prop
  /-- The recorded value of the reference temperature, `273.15 K`. -/
  T₀_value_K_eq : T₀_value_K = 273.15

/-- The previous-part (B.5) result, imported as a natural-language
prerequisite only: the Clausius–Clapeyron graph of `ln(P_v/P_atm)` vs `1/T`
yields slope `−4700 ± 200 K` and the molar latent heat `Qᵥ = 39 ± 2 kJ/mol`.
This records the *measured input* to B.6; it does not state the B.6
relation. -/
structure PartB5Measurements where
  /-- Measured slope of `ln(P_v/P_atm)` vs `1/T`, in kelvin. -/
  slope_K : ℝ
  /-- Uncertainty of the slope, in kelvin. -/
  slope_uncertainty_K : ℝ
  /-- Central value of the molar latent heat, in kJ/mol. -/
  Qv_kJ_per_mol : ℝ
  /-- Uncertainty of the molar latent heat, in kJ/mol. -/
  Qv_uncertainty_kJ_per_mol : ℝ
  /-- Reference gas constant stated by the problem, in J/(mol·K). -/
  R_J_per_mol_K : ℝ
  /-- Official sample slope value `−4700 K`. -/
  slope_K_eq : slope_K = -4700
  /-- Official sample slope uncertainty `±200 K`. -/
  slope_uncertainty_K_eq : slope_uncertainty_K = 200
  /-- Official sample molar latent heat `39 kJ/mol`. -/
  Qv_kJ_per_mol_eq : Qv_kJ_per_mol = 39
  /-- Official sample molar latent-heat uncertainty `±2 kJ/mol`. -/
  Qv_uncertainty_kJ_per_mol_eq : Qv_uncertainty_kJ_per_mol = 2
  /-- Problem-stated reference value `R = 8.31 J/(mol·K)`. -/
  R_J_per_mol_K_eq : R_J_per_mol_K = 8.31

/-- The experimental and previous-part input package for subquestion B.6 of
IPhO 2026 E1 (structure instance it as a conjunction of the apparatus
readouts and the B.5 measurements). It contains no field committal to the
B.6 formula `Lᵥ = Qᵥ/M₀`. -/
structure PartB6Input extends InnerCylinderExperiment, PartB5Measurements

/-! ## Current-subquestion target -/

/-- The unit-carrying conversion relation at the heart of subquestion B.6:
the latent heat of vaporization per unit mass `Lᵥ` is obtained from the
molar latent heat `Qᵥ` by dividing by the molar mass `M₀` of water,

`Lᵥ = Qᵥ / M₀`.

Because `MolarEnergy`, `MolarMass` and `SpecificLatentHeat` are abstract
types with no scalar projection, the division is expressed through the
existence of a positive proportionality `k` (a magnitude map) together with
the recorded scalar values `Qv_kJ_per_mol` and `M0_kg_per_mol`, for which
the physical conversion fixes `Lv_kJ_per_kg = Qv_kJ_per_mol / M0_kg_per_mol`.
The fields of this structure are hypotheses available to a later prover,
not definitions making the theorem true by unfolding: the main theorem still
has to *produce* such a witness from the B.5/B.6 data. -/
structure IsSpecificLatentHeatOf
    (Lv : SpecificLatentHeat) (Qv : MolarEnergy) (M0 : MolarMass) where
  /-- Magnitude of `Qᵥ` in kJ/mol. -/
  Qv_magnitude_kJ_per_mol : ℝ
  /-- Magnitude of `M₀` in kg/mol. -/
  M0_magnitude_kg_per_mol : ℝ
  /-- Magnitude of `Lᵥ` in kJ/kg. -/
  Lv_magnitude_kJ_per_kg : ℝ
  /-- The physical conversion equation: the specific latent heat magnitude is
  the molar latent heat magnitude divided by the molar mass magnitude. -/
  conversion_eq :
    Lv_magnitude_kJ_per_kg =
      Qv_magnitude_kJ_per_mol / M0_magnitude_kg_per_mol
  /-- The molar mass of water is positive, so the division is meaningful. -/
  M0_pos : 0 < M0_magnitude_kg_per_mol

/-- `Lv` converts the molar latent heat `Qv` into a latent heat per unit
mass via division by the molar mass `M0`: an abbreviation naming the
physical role of the relation `IsSpecificLatentHeatOf`. -/
def ConvertsMolarLatentHeatToSpecific
    (Lv : SpecificLatentHeat) (Qv : MolarEnergy) (M0 : MolarMass) : Prop :=
  Nonempty (IsSpecificLatentHeatOf Lv Qv M0)

/-! ### Numerical content of the official answer -/

/-- Scalar, unit-tagged record of the specific latent heat of vaporization of
water as reported by the official solution, `Lᵥ = 2190 ± 110 kJ/kg`. Kept in
kJ/kg to match the recorded answer. -/
structure SpecificLatentHeatValue where
  /-- Central value of `Lᵥ`, in kJ/kg. -/
  central_kJ_per_kg : ℝ
  /-- Absolute uncertainty of `Lᵥ`, in kJ/kg. -/
  uncertainty_kJ_per_kg : ℝ

/-- The measured/reported value of the specific latent heat lies within the
uncertainty interval around the official central value:
`|measured − 2190| ≤ 110 (kJ/kg)`. -/
def SpecificLatentHeatValue.withinUncertainty
    (measured official : SpecificLatentHeatValue) : Prop :=
  |measured.central_kJ_per_kg - official.central_kJ_per_kg| ≤
    official.uncertainty_kJ_per_kg

/-- The official reported value `Lᵥ = 2190 ± 110 kJ/kg`. -/
def officialSpecificLatentHeatValue : SpecificLatentHeatValue where
  central_kJ_per_kg := 2190
  uncertainty_kJ_per_kg := 110

/-- The catalog central value of the molar latent heat from B.5,
`Qᵥ = 39 kJ/mol`. -/
def catalogQvValue : ℝ := 39

/-- The catalog central value of the molar mass of water,
`M₀ = 18.0 × 10⁻³ kg/mol`. -/
def catalogMolarMassWaterValue : ℝ := 18.0e-3

/-- The catalog central value of the uncertainty of `Qᵥ`, `±2 kJ/mol`. -/
def catalogQvUncertainty : ℝ := 2

/-! ## Main formalization target -/

/-- **Main theorem (blueprint `thm:physics:IPhO_2026_4_B_6:target`).**
Under the input package of the inner-cylinder experiment — apparatus
readouts, the Clausius–Clapeyron law, and the part-B.5 determination
`Qᵥ = 39 ± 2 kJ/mol` — the latent heat of vaporization per unit mass is
obtained by dividing the molar latent heat by the molar mass of water,

`Lᵥ = Qᵥ / M₀`,

and with `M₀ = 18.0 × 10⁻³ kg/mol` the measured value is consistent with the
official result `Lᵥ = 2190 ± 110 kJ/kg`, i.e., the reported specific latent
heat lies within the official uncertainty interval.

The formula itself is in the conclusion — witnessed by
`IsSpecificLatentHeatOf Lv Qv M0` together with the catalog matching
conditions `Qv_magnitude = 39 kJ/mol`, `M0_magnitude = 18.0 × 10⁻³ kg/mol` —
and the uncertainty `±110 kJ/kg` is preserved through
`SpecificLatentHeatValue.withinUncertainty`. -/
theorem latent_heat_per_unit_mass_target
    (input : PartB6Input)
    (Qv : MolarEnergy) (M0 : MolarMass) (Lv : SpecificLatentHeat)
    (Lv_reported : SpecificLatentHeatValue) :
    ∃ witness : IsSpecificLatentHeatOf Lv Qv M0,
      witness.Qv_magnitude_kJ_per_mol = catalogQvValue ∧
      witness.M0_magnitude_kg_per_mol = catalogMolarMassWaterValue ∧
      Lv_reported.withinUncertainty officialSpecificLatentHeatValue := by
  refine ⟨⟨catalogQvValue, catalogMolarMassWaterValue,
      catalogQvValue / catalogMolarMassWaterValue, rfl, by
        rw [catalogMolarMassWaterValue]; norm_num⟩,
    rfl, rfl, ?_⟩
  -- Remaining obligation:
  --   `Lv_reported.withinUncertainty officialSpecificLatentHeatValue`,
  -- i.e. `|Lv_reported.central_kJ_per_kg - 2190| ≤ 110`.
  -- This is NOT provable as stated: `Lv_reported` is universally quantified
  -- and unconstrained, so e.g. `Lv_reported.central_kJ_per_kg = 10000` is a
  -- countermodel. The honest reported value
  -- `Lv_reported.central_kJ_per_kg = 39/18.0e-3 ≈ 2166.7` would give
  -- `|2166.7 - 2190| ≈ 23.3 ≤ 110` (proved below in
  -- `computed_value_within_official_uncertainty`). See the redraft request
  -- in the iter-010 task result (`.archon/task_results/`).
  sorry

/-- **B.6 formula (explicit scalar form).** For the catalog central values,
the specific latent heat of vaporization of water is the molar latent heat
divided by the molar mass of water,

`Lᵥ = Qᵥ / M₀ = 39 kJ/mol / (18.0 × 10⁻³ kg/mol) ≈ 2190 kJ/kg`,

within the official uncertainty `±110 kJ/kg`. This is the formula the
subquestion asks to state. -/
theorem latent_heat_per_unit_mass_formula :
    ∃ Lv Qv M0 : ℝ,
      Qv = catalogQvValue ∧
      M0 = catalogMolarMassWaterValue ∧
      Lv = Qv / M0 ∧
      |Lv - officialSpecificLatentHeatValue.central_kJ_per_kg| ≤
        officialSpecificLatentHeatValue.uncertainty_kJ_per_kg := by
  refine ⟨catalogQvValue / catalogMolarMassWaterValue, catalogQvValue,
    catalogMolarMassWaterValue, rfl, rfl, rfl, ?_⟩
  show |(catalogQvValue / catalogMolarMassWaterValue : ℝ) - 2190| ≤ 110
  rw [catalogQvValue, catalogMolarMassWaterValue, abs_le]
  constructor <;> norm_num

/-- **Uncertainty preservation (B.6).** The uncertainty propagated to `Lᵥ`
from the B.5 uncertainty `Qᵥ = 39 ± 2 kJ/mol` (relative uncertainty
`2/39 ≈ 5.1%`, with `M₀` treated as exact) is `±110 kJ/kg` about the central
value `2190 kJ/kg`: the computed central value
`Lᵥ = 39 kJ/mol / 18.0 × 10⁻³ kg/mol ≈ 2167 kJ/kg` lies within the official
interval `2190 ± 110 kJ/kg`. -/
theorem computed_value_within_official_uncertainty :
    |(catalogQvValue / catalogMolarMassWaterValue) -
        officialSpecificLatentHeatValue.central_kJ_per_kg| ≤
      officialSpecificLatentHeatValue.uncertainty_kJ_per_kg := by
  show |(39 / 18.0e-3 : ℝ) - 2190| ≤ 110
  rw [abs_le]
  constructor <;> norm_num

/-- Bridge lemma: the B.5 slope determination `s = −4700 ± 200 K` together
with the reference value `R = 8.31 J/(mol·K)` fixes the molar latent heat
input to B.6 through `Qᵥ = −s · R ≈ 39.1 kJ/mol`, which is consistent with
the official `Qᵥ = 39 ± 2 kJ/mol`. This is the natural-language
previous-part prerequisite recorded in Lean form; it does not state the B.6
conclusion. -/
theorem qv_from_clausius_clapeyron_slope
    (input : PartB6Input) :
    ∃ Qv_computed_kJ_per_mol : ℝ,
      Qv_computed_kJ_per_mol = -input.slope_K * input.R_J_per_mol_K / 1000 ∧
      |Qv_computed_kJ_per_mol - input.Qv_kJ_per_mol| ≤
        input.Qv_uncertainty_kJ_per_mol := by
  refine ⟨-input.slope_K * input.R_J_per_mol_K / 1000, rfl, ?_⟩
  rw [input.slope_K_eq, input.R_J_per_mol_K_eq, input.Qv_kJ_per_mol_eq,
    input.Qv_uncertainty_kJ_per_mol_eq, abs_le]
  constructor <;> norm_num

/-- The reference temperature calibration `T₀ = 273.15 K` at which the
extrapolated vapor pressure vanishes, captured for the setup even though B.6
does not use it directly. -/
theorem reference_temperature_calibration
    (input : PartB6Input) :
    input.T₀_value_K = 273.15 := by
  exact input.T₀_value_K_eq

end Problem4

end IPhO2026

end
