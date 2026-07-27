import Mathlib
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026, problem 3, part C.3

We model the four labelled states of the paramagnetic-torus Carnot refrigerator and
the fixed-SI readouts supplied in the question.  `WithDim` keeps the ordinary SI
dimensions distinct.  Amount of substance and the two molar material constants are
represented by explicitly unit-named real readouts because the current PhysLean
`Dimension` has no amount-of-substance component.
-/

namespace IPhO2026Problems.IPhO2026_3_C_3

open Dimension

/-- The four vertices of the Carnot cycle `1 → 2 → 3 → 4 → 1`. -/
inductive CarnotState
  | one
  | two
  | three
  | four
  deriving DecidableEq

/-- The oriented cycle order shown in Figure 3b. -/
def CarnotState.next : CarnotState → CarnotState
  | .one => .two
  | .two => .three
  | .three => .four
  | .four => .one

/-- Absolute temperature, recorded in kelvin in the supplied-data hypotheses. -/
abbrev Temperature := WithDim Θ𝓭 ℝ

/-- Volume, recorded in cubic metres in the supplied-data hypotheses. -/
abbrev Volume := WithDim (L𝓭 ^ 3) ℝ

/-- Mass density, recorded in kilograms per cubic metre. -/
abbrev MassDensity := WithDim (M𝓭 * (L𝓭 ^ 3)⁻¹) ℝ

/-- Specific heat capacity, with dimension `L² T⁻² Θ⁻¹`. -/
abbrev SpecificHeatCapacity :=
  WithDim (L𝓭 ^ 2 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) ℝ

/-- Magnetic field strength `H`, with SI unit ampere per metre. -/
abbrev MagneticFieldStrength :=
  WithDim (C𝓭 * T𝓭⁻¹ * L𝓭⁻¹) ℝ

/-- Magnetization `M`, with the same SI dimension as magnetic field strength. -/
abbrev Magnetization :=
  WithDim (C𝓭 * T𝓭⁻¹ * L𝓭⁻¹) ℝ

/-- Energy, recorded in joules. -/
abbrev Energy :=
  WithDim (M𝓭 * L𝓭 ^ 2 * T𝓭⁻¹ * T𝓭⁻¹) ℝ

/-- Magnetic permeability, with SI unit newton per ampere squared. -/
abbrev MagneticPermeability :=
  WithDim (M𝓭 * L𝓭 * (C𝓭 ^ 2)⁻¹) ℝ

/-- All physical quantities needed to describe the torus, cycle, and helium sample. -/
structure Setup where
  /-- Amount of potassium chromate, as a scalar readout in moles. -/
  torusAmountMol : ℝ
  /-- Molar Curie constant `K`, as a readout in `K m³/mol`. -/
  molarCurieConstantK_m3_per_mol : ℝ
  /-- Potassium-chromate density. -/
  torusDensity : MassDensity
  /-- Potassium-chromate molar mass, as a readout in `kg/mol`. -/
  torusMolarMassKgPerMol : ℝ
  /-- Volume of the paramagnetic torus. -/
  torusVolume : Volume
  /-- Hot-reservoir temperature `T_h`. -/
  hotReservoirTemperature : Temperature
  /-- Cold-reservoir temperature `T_c`. -/
  coldReservoirTemperature : Temperature
  /-- Temperature at each labelled vertex of Figure 3b. -/
  cycleTemperature : CarnotState → Temperature
  /-- Magnetic field strength at each labelled vertex of Figure 3b. -/
  magneticFieldStrength : CarnotState → MagneticFieldStrength
  /-- Nonnegative magnetization magnitude at each labelled vertex. -/
  magnetization : CarnotState → Magnetization
  /-- Volume of liquid helium being cooled. -/
  heliumVolume : Volume
  /-- Liquid-helium mass density. -/
  heliumDensity : MassDensity
  /-- Constant liquid-helium specific heat capacity. -/
  heliumSpecificHeatCapacity : SpecificHeatCapacity
  /-- Helium temperature immediately before the cycle. -/
  heliumInitialTemperature : Temperature
  /-- Helium temperature immediately after the cycle. -/
  heliumFinalTemperature : Temperature
  /-- Magnitude `Q_c` of the heat absorbed from the helium during the cold isotherm. -/
  heatAbsorbedFromHelium : Energy
  /-- Magnitude `Q_h` of the heat delivered to the hot reservoir. -/
  heatDeliveredToHotReservoir : Energy
  /-- Vacuum permeability `μ₀`. -/
  vacuumPermeability : MagneticPermeability

/--
The numerical readouts supplied on the official source page, all expressed in the
fixed SI units documented by the corresponding fields.
-/
structure HasSuppliedData (s : Setup) : Prop where
  torusAmountMol : s.torusAmountMol = 2
  molarCurieConstant :
    s.molarCurieConstantK_m3_per_mol = (187 : ℝ) / 100000000
  torusDensity : s.torusDensity.val = 2730
  torusMolarMass : s.torusMolarMassKgPerMol = (19 : ℝ) / 100
  fieldOne : (s.magneticFieldStrength CarnotState.one).val = 411624
  fieldTwo : (s.magneticFieldStrength CarnotState.two).val = 311306
  fieldThree : (s.magneticFieldStrength CarnotState.three).val = 204618
  fieldFour : (s.magneticFieldStrength CarnotState.four).val = 240446
  heliumVolume : s.heliumVolume.val = (1 : ℝ) / 1000
  heliumInitialTemperature : s.heliumInitialTemperature.val = 1
  heliumSpecificHeatCapacity : s.heliumSpecificHeatCapacity.val = 100
  heliumDensity : s.heliumDensity.val = 130
  vacuumPermeability :
    s.vacuumPermeability.val = 4 * Real.pi / 10000000

/--
The governing physical model: Figure 3b's isotherm labels, material geometry, the
paramagnet equation of state, and calorimetric energy conservation for the helium.
None of these laws fixes the requested numerical final temperature.
-/
structure GoverningLaws (s : Setup) : Prop where
  stateOneAtHotReservoir :
    s.cycleTemperature CarnotState.one = s.hotReservoirTemperature
  stateTwoAtColdReservoir :
    s.cycleTemperature CarnotState.two = s.coldReservoirTemperature
  stateThreeAtColdReservoir :
    s.cycleTemperature CarnotState.three = s.coldReservoirTemperature
  stateFourAtHotReservoir :
    s.cycleTemperature CarnotState.four = s.hotReservoirTemperature
  coldReservoirInitiallyIsHelium :
    s.coldReservoirTemperature = s.heliumInitialTemperature
  torusMassDensityRelation :
    s.torusDensity.val * s.torusVolume.val =
      s.torusAmountMol * s.torusMolarMassKgPerMol
  equationOfState :
    ∀ i : CarnotState,
      (s.cycleTemperature i).val * (s.magnetization i).val * s.torusVolume.val =
        s.torusAmountMol * s.molarCurieConstantK_m3_per_mol *
          (s.magneticFieldStrength i).val
  heliumCalorimetry :
    s.heatAbsorbedFromHelium.val =
      s.heliumDensity.val * s.heliumVolume.val *
        s.heliumSpecificHeatCapacity.val *
          (s.heliumInitialTemperature.val - s.heliumFinalTemperature.val)
  hotTemperaturePositive : 0 < s.hotReservoirTemperature.val
  coldTemperaturePositive : 0 < s.coldReservoirTemperature.val
  finalHeliumTemperatureNonnegative : 0 ≤ s.heliumFinalTemperature.val
  magnetizationNonnegative :
    ∀ i : CarnotState, 0 ≤ (s.magnetization i).val
  heatAbsorbedNonnegative : 0 ≤ s.heatAbsorbedFromHelium.val
  heatDeliveredNonnegative : 0 ≤ s.heatDeliveredToHotReservoir.val

/--
The two reusable results explicitly licensed by the blueprint: the part B.1
isothermal-heat relation on the cold leg `2 → 3`, and the nonnegative-magnitude
relation from part C.2.
-/
structure PreviousPartResults (s : Setup) : Prop where
  coldIsothermalHeat :
    s.heatAbsorbedFromHelium.val =
      -(s.vacuumPermeability.val * s.torusAmountMol *
          s.molarCurieConstantK_m3_per_mol /
          (2 * s.coldReservoirTemperature.val)) *
        ((s.magneticFieldStrength CarnotState.three).val ^ 2 -
          (s.magneticFieldStrength CarnotState.two).val ^ 2)
  hotIsothermalHeat :
    s.heatDeliveredToHotReservoir.val =
      s.vacuumPermeability.val * s.torusAmountMol *
          s.molarCurieConstantK_m3_per_mol /
          (2 * s.hotReservoirTemperature.val) *
        ((s.magneticFieldStrength CarnotState.one).val ^ 2 -
          (s.magneticFieldStrength CarnotState.four).val ^ 2)
  magnetizationOne :
    (s.magnetization CarnotState.one).val =
      Real.sqrt
        ((s.magnetization CarnotState.two).val ^ 2 -
          (s.magnetization CarnotState.three).val ^ 2 +
          (s.magnetization CarnotState.four).val ^ 2)

/--
After one cycle, the calculated heat, helium temperature decrease, and final
temperature agree with the reported rounded values `0.129 J`, `0.00992 K`, and
`0.99008 K`, within explicit tolerances appropriate to the rounded input data.
-/
theorem helium_temperature_after_one_cycle
    (s : Setup)
    (hData : HasSuppliedData s)
    (hLaws : GoverningLaws s)
    (hPrevious : PreviousPartResults s) :
    |s.heatAbsorbedFromHelium.val - (129 : ℝ) / 1000| ≤ (1 : ℝ) / 2000 ∧
      |(s.heliumInitialTemperature.val - s.heliumFinalTemperature.val) -
          (992 : ℝ) / 100000| ≤ (1 : ℝ) / 20000 ∧
      |s.heliumFinalTemperature.val - (99008 : ℝ) / 100000| ≤ (1 : ℝ) / 20000 := by
  have hColdTemperature : s.coldReservoirTemperature.val = 1 := by
    rw [hLaws.coldReservoirInitiallyIsHelium]
    exact hData.heliumInitialTemperature
  have hHeat := hPrevious.coldIsothermalHeat
  rw [hData.vacuumPermeability, hData.torusAmountMol,
    hData.molarCurieConstant, hColdTemperature, hData.fieldThree,
    hData.fieldTwo] at hHeat
  norm_num at hHeat
  have hCalorimetry := hLaws.heliumCalorimetry
  rw [hData.heliumDensity, hData.heliumVolume,
    hData.heliumSpecificHeatCapacity, hData.heliumInitialTemperature] at hCalorimetry
  norm_num at hCalorimetry
  have hPiLower := Real.pi_gt_d4
  have hPiUpper := Real.pi_lt_d4
  rw [hData.heliumInitialTemperature]
  refine
    ⟨abs_le.2 ⟨?_, ?_⟩, abs_le.2 ⟨?_, ?_⟩,
      abs_le.2 ⟨?_, ?_⟩⟩ <;>
    nlinarith [hHeat, hCalorimetry, hPiLower, hPiUpper]

end IPhO2026Problems.IPhO2026_3_C_3
