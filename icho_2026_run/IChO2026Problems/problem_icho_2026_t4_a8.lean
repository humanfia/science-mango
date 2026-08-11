import IChO2026Chem
import CRNT.Basic.Reaction

/-!
# IChO 2026 T4-A8: daily energy from methane combustion

This formalization keeps the chemical reaction distinct from the scalar gas
readouts.  Pressures are measured in Pa, volume flow in m³ day⁻¹,
temperatures in K, the gas constant in J mol⁻¹ K⁻¹, reaction enthalpies in
kJ mol⁻¹, and released energy in J day⁻¹.

T4-A7 is a natural-language prerequisite only.  Consequently, its value for
the 2000 K reaction enthalpy is an explicit hypothesis below, rather than an
import from the generated T4-A7 Lean file.
-/

namespace IChO2026Problems.T4A8

/-- The species in the complete, all-gaseous combustion reaction. -/
private inductive GaseousSpecies where
  | methane
  | dioxygen
  | carbonDioxide
  | water
  deriving DecidableEq, Fintype

/-- A pressure represented by its numerical value in Pa. -/
private abbrev Pressure := ℝ

/-- A temperature represented by its numerical value in K. -/
private abbrev Temperature := ℝ

/-- A daily volume flow represented by its numerical value in m³ day⁻¹. -/
private abbrev DailyVolumeFlow := ℝ

/-- An amount of methane represented by its numerical value in mol day⁻¹. -/
private abbrev DailyMolarAmount := ℝ

/-- The molar gas constant represented by its numerical value in J mol⁻¹ K⁻¹. -/
private abbrev MolarGasConstant := ℝ

/-- A molar reaction enthalpy represented by its numerical value in kJ mol⁻¹. -/
private abbrev MolarReactionEnthalpy := ℝ

/-- An energy release represented by its numerical value in J day⁻¹. -/
private abbrev DailyEnergyRelease := ℝ

/-- Fractions of the one-day interval over which the combustion is observed. -/
private abbrev DayFraction := Set.Icc (0 : ℝ) 1

/-- The balanced complete-combustion reaction `CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g)`. -/
private def methaneCombustion : CRNT.Reaction GaseousSpecies where
  source
    | .methane => 1
    | .dioxygen => 2
    | .carbonDioxide => 0
    | .water => 0
  target
    | .methane => 0
    | .dioxygen => 0
    | .carbonDioxide => 1
    | .water => 2

/-- A reaction is complete methane combustion precisely when it has the displayed stoichiometry. -/
private def IsCompleteMethaneCombustion (reaction : CRNT.Reaction GaseousSpecies) : Prop :=
  reaction = methaneCombustion

/--
The source state of the methane stream and its subsequently isothermal
combustion process.  The energy to be calculated is deliberately not a field:
it is defined from the amount and reaction enthalpy below.
-/
private structure DailyMethaneCombustionData where
  reaction : CRNT.Reaction GaseousSpecies
  sourcePressure : Pressure
  sourceTemperature : Temperature
  dailyMethaneVolume : DailyVolumeFlow
  dailyMethaneAmount : DailyMolarAmount
  gasConstant : MolarGasConstant
  temperatureDuringCombustion : DayFraction → Temperature
  reactionEnthalpy : CRNT.Reaction GaseousSpecies → Temperature → MolarReactionEnthalpy

/-- Isothermal combustion means that every time in the one-day process has the same temperature. -/
private def IsIsothermalAt (data : DailyMethaneCombustionData) (temperature : Temperature) : Prop :=
  ∀ elapsed, data.temperatureDuringCombustion elapsed = temperature

/-- The dimensional scalar form of the ideal-gas law, `PV = nRT`. -/
private def ObeysIdealGasLaw (data : DailyMethaneCombustionData) : Prop :=
  data.sourcePressure * data.dailyMethaneVolume =
    data.dailyMethaneAmount * data.gasConstant * data.sourceTemperature

/-- Positivity side conditions required for the ideal-gas calculation. -/
private def HasPhysicalWellConditions (data : DailyMethaneCombustionData) : Prop :=
  0 < data.sourcePressure ∧
    0 < data.sourceTemperature ∧
    0 < data.dailyMethaneVolume ∧
    0 < data.dailyMethaneAmount ∧
    0 < data.gasConstant

/--
The numerical observations printed in T4-A8.  The value `101325` is the given
`101.325 kPa` converted to Pa, and `220000` is `2.2 × 10⁵ m³ day⁻¹`.
-/
private def MatchesT4A8SourceData (data : DailyMethaneCombustionData) : Prop :=
  data.sourcePressure = 101325 ∧
    data.sourceTemperature = 298 ∧
    data.dailyMethaneVolume = 220000 ∧
    data.gasConstant = 8.314

/-- The process temperature used to calculate the energy: the beginning of the one-day interval. -/
private def processTemperature (data : DailyMethaneCombustionData) : Temperature :=
  data.temperatureDuringCombustion ⟨0, by norm_num⟩

/--
The positive energy released by one day's actual combustion process.  Its
enthalpy is indexed by both the reaction which occurs and the temperature at
the beginning of the process.  The minus sign converts the negative enthalpy
of an exothermic reaction into released energy; `1000` converts kJ to J.
-/
private def dailyEnergyReleasedDuringProcess
    (data : DailyMethaneCombustionData) : DailyEnergyRelease :=
  -data.reactionEnthalpy data.reaction (processTemperature data) * 1000 *
    data.dailyMethaneAmount

/-- Reporting `9.00 × 10⁶ mol day⁻¹` keeps three significant figures, so
the half-unit in the last displayed place is `5000 mol day⁻¹`. -/
private def RoundsToNearestTenThousand (value reported : ℝ) : Prop :=
  |value - reported| ≤ 5000

/-- Half-unit criterion for the one-decimal enthalpy report
`781.9 kJ mol⁻¹`. -/
private def RoundsToOneDecimal (value reported : ℝ) : Prop :=
  |value - reported| ≤ (1 : ℝ) / 20

/-- Reporting an energy near `7 × 10¹² J day⁻¹` to three significant
figures has a `10¹⁰ J day⁻¹` last place. -/
private def RoundsToNearestTenBillion (value reported : ℝ) : Prop :=
  |value - reported| ≤ 5000000000

/-- The staged calculation used by the official rubric: multiply a reported
molar flow by a reported positive enthalpy magnitude and convert kJ to J. -/
private def dailyEnergyFromReportedStages
    (reportedMolesPerDay reportedEnthalpyMagnitude : ℝ) : DailyEnergyRelease :=
  reportedMolesPerDay * reportedEnthalpyMagnitude * 1000

/--
T4-A8 using the reusable T4-A7 conclusion
`ΔᵣH°₂₀₀₀ = -781.876 kJ mol⁻¹`.  The theorem makes the official
reporting stages explicit:

* the ideal-gas result reports as `9.00 × 10⁶ mol day⁻¹`;
* the enthalpy magnitude reports as `781.9 kJ mol⁻¹`;
* their staged product is `7.0371 × 10¹² J day⁻¹`, which reports to three
  significant figures as the official `7.04 × 10¹² J day⁻¹`.

The final conjuncts retain the different raw, unrounded calculation for
auditability; that raw value is not labelled as the official report.
-/
theorem daily_energy_released_at_2000K
    (data : DailyMethaneCombustionData)
    (hreaction : IsCompleteMethaneCombustion data.reaction)
    (hphysical : HasPhysicalWellConditions data)
    (hsource : MatchesT4A8SourceData data)
    (hidealGas : ObeysIdealGasLaw data)
    (hisothermal : IsIsothermalAt data 2000)
    (henthalpyAt2000 : data.reactionEnthalpy methaneCombustion 2000 = -781.876) :
    data.dailyMethaneAmount =
        data.sourcePressure * data.dailyMethaneVolume /
          (data.gasConstant * data.sourceTemperature) ∧
      RoundsToNearestTenThousand data.dailyMethaneAmount 9000000 ∧
        RoundsToOneDecimal
            (-data.reactionEnthalpy data.reaction (processTemperature data)) 781.9 ∧
          dailyEnergyFromReportedStages 9000000 781.9 = 7037100000000 ∧
            RoundsToNearestTenBillion
                (dailyEnergyFromReportedStages 9000000 781.9) 7040000000000 ∧
              dailyEnergyReleasedDuringProcess data =
                  781876 * data.dailyMethaneAmount ∧
                7034000000000 < dailyEnergyReleasedDuringProcess data ∧
                  dailyEnergyReleasedDuringProcess data < 7035000000000 := by
  rcases hphysical with ⟨hpressure, htemperature, hvolume, hamount, hgas⟩
  rcases hsource with ⟨hpressureSource, htemperatureSource, hvolumeSource, hgasSource⟩
  have hgasTemperature : data.gasConstant * data.sourceTemperature ≠ 0 :=
    mul_ne_zero (ne_of_gt hgas) (ne_of_gt htemperature)
  have hamountFormula :
      data.dailyMethaneAmount =
        data.sourcePressure * data.dailyMethaneVolume /
          (data.gasConstant * data.sourceTemperature) := by
    apply (eq_div_iff hgasTemperature).2
    calc
      data.dailyMethaneAmount * (data.gasConstant * data.sourceTemperature) =
          data.dailyMethaneAmount * data.gasConstant * data.sourceTemperature := by
            ring
      _ = data.sourcePressure * data.dailyMethaneVolume := hidealGas.symm
  have hprocessTemperature : processTemperature data = 2000 := by
    simpa [processTemperature] using
      hisothermal (⟨0, by norm_num⟩ : DayFraction)
  have henergy : dailyEnergyReleasedDuringProcess data =
      781876 * data.dailyMethaneAmount := by
    rw [dailyEnergyReleasedDuringProcess, hreaction, hprocessTemperature, henthalpyAt2000]
    ring
  have hreportedEnthalpy :
      RoundsToOneDecimal
        (-data.reactionEnthalpy data.reaction (processTemperature data)) 781.9 := by
    rw [hreaction, hprocessTemperature, henthalpyAt2000]
    norm_num [RoundsToOneDecimal]
  refine ⟨hamountFormula, ?_, hreportedEnthalpy, ?_, ?_, henergy, ?_, ?_⟩
  · rw [hamountFormula, hpressureSource, hvolumeSource, hgasSource, htemperatureSource]
    norm_num [RoundsToNearestTenThousand, abs_of_nonneg, abs_of_nonpos]
  · norm_num [dailyEnergyFromReportedStages]
  · norm_num [RoundsToNearestTenBillion, dailyEnergyFromReportedStages]
  · rw [henergy, hamountFormula, hpressureSource, hvolumeSource, hgasSource,
      htemperatureSource]
    norm_num
  · rw [henergy, hamountFormula, hpressureSource, hvolumeSource, hgasSource,
      htemperatureSource]
    norm_num

/--
The conditional branch explicitly supplied in T4-A8 when the preceding part
was unavailable: use `ΔᵣH₂₀₀₀ = -700 kJ mol⁻¹`.  Applying the same
reported `9.00 × 10⁶ mol day⁻¹` stage yields exactly the official fallback
report `6.30 × 10¹² J day⁻¹`.
-/
private theorem daily_energy_released_at_2000K_from_supplied_fallback
    (data : DailyMethaneCombustionData)
    (hreaction : IsCompleteMethaneCombustion data.reaction)
    (hphysical : HasPhysicalWellConditions data)
    (hsource : MatchesT4A8SourceData data)
    (hidealGas : ObeysIdealGasLaw data)
    (hisothermal : IsIsothermalAt data 2000)
    (henthalpyAt2000 : data.reactionEnthalpy methaneCombustion 2000 = -700) :
    data.dailyMethaneAmount =
        data.sourcePressure * data.dailyMethaneVolume /
          (data.gasConstant * data.sourceTemperature) ∧
      RoundsToNearestTenThousand data.dailyMethaneAmount 9000000 ∧
        dailyEnergyFromReportedStages 9000000 700 = 6300000000000 ∧
          RoundsToNearestTenBillion
              (dailyEnergyFromReportedStages 9000000 700) 6300000000000 ∧
            dailyEnergyReleasedDuringProcess data =
                700000 * data.dailyMethaneAmount := by
  rcases hphysical with ⟨hpressure, htemperature, hvolume, hamount, hgas⟩
  rcases hsource with ⟨hpressureSource, htemperatureSource, hvolumeSource, hgasSource⟩
  have hgasTemperature : data.gasConstant * data.sourceTemperature ≠ 0 :=
    mul_ne_zero (ne_of_gt hgas) (ne_of_gt htemperature)
  have hamountFormula :
      data.dailyMethaneAmount =
        data.sourcePressure * data.dailyMethaneVolume /
          (data.gasConstant * data.sourceTemperature) := by
    apply (eq_div_iff hgasTemperature).2
    calc
      data.dailyMethaneAmount * (data.gasConstant * data.sourceTemperature) =
          data.dailyMethaneAmount * data.gasConstant * data.sourceTemperature := by
            ring
      _ = data.sourcePressure * data.dailyMethaneVolume := hidealGas.symm
  have hprocessTemperature : processTemperature data = 2000 := by
    simpa [processTemperature] using
      hisothermal (⟨0, by norm_num⟩ : DayFraction)
  have henergy : dailyEnergyReleasedDuringProcess data =
      700000 * data.dailyMethaneAmount := by
    rw [dailyEnergyReleasedDuringProcess, hreaction, hprocessTemperature, henthalpyAt2000]
    ring
  refine ⟨hamountFormula, ?_, ?_, ?_, henergy⟩
  · rw [hamountFormula, hpressureSource, hvolumeSource, hgasSource,
      htemperatureSource]
    norm_num [RoundsToNearestTenThousand, abs_of_nonneg, abs_of_nonpos]
  · norm_num [dailyEnergyFromReportedStages]
  · norm_num [RoundsToNearestTenBillion, dailyEnergyFromReportedStages]

end IChO2026Problems.T4A8
