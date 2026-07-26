import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0461

open Dimension

/-!
# Isothermal expansion in an air pistol

The bullet is treated as a piston.  Compressed air expands behind it while
the exterior pressure `P₀` resists its motion.  All dimensional quantities
are represented coherently in every choice of units.  Real numbers below are
used only for named-unit readouts, dimensionless ratios, and answer choices.
-/

/-- A nonnegative physical volume, with dimension length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative physical mass, independent of its readout unit. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative absolute temperature, independent of its readout unit. -/
abbrev AbsoluteTemperatureQuantity : Type :=
  Dimensionful (WithDim Θ𝓭 NNReal)

/-- A physical pressure. -/
abbrev PressureQuantity : Type := DimPressure

/-- A nonnegative physical speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A physical work or energy. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a volume in the cube of the selected length unit. -/
def volumeReadout (unit : LengthUnit) (volume : VolumeQuantity) : ℝ :=
  ((volume {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a mass in the selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read an absolute temperature in the selected temperature unit. -/
def absoluteTemperatureReadout
    (unit : TemperatureUnit) (temperature : AbsoluteTemperatureQuantity) : ℝ :=
  ((temperature {UnitChoices.SI with temperature := unit}).val : ℝ)

/-- Pressure readout in pascals. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Pressure readout in megapascals. -/
def pressureInMegapascals (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure / 1000000

/-- Volume readout in cubic meters. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  volumeReadout LengthUnit.meters volume

/-- Volume readout in cubic centimeters. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  volumeReadout LengthUnit.centimeters volume

/-- Mass readout in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Mass readout in grams. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.grams mass

/-- Absolute-temperature readout in kelvin. -/
def temperatureInKelvin (temperature : AbsoluteTemperatureQuantity) : ℝ :=
  absoluteTemperatureReadout TemperatureUnit.kelvin temperature

/-- Celsius readout obtained from the absolute Kelvin readout. -/
def temperatureInDegreesCelsius
    (temperature : AbsoluteTemperatureQuantity) : ℝ :=
  temperatureInKelvin temperature - 27315 / 100

/-- Speed readout in meters per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Energy readout in joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val

/-- Thermodynamic data for the air at one stage of the shot. -/
structure AirState where
  pressure : PressureQuantity
  volume : VolumeQuantity
  absoluteTemperature : AbsoluteTemperatureQuantity

/-- Components distinguishable in the supplied air-pistol figure. -/
inductive FigureComponent where
  | compressedAir
  | bullet
  | triggerPin
  | barrel
  deriving DecidableEq, Repr

/-- Text or mathematical labels printed in the supplied figure. -/
inductive FigureLabel where
  | air
  | exteriorPressureP0
  deriving DecidableEq, Repr

/-- The thermodynamic-process idealization stated in the problem. -/
inductive ThermodynamicProcess where
  | isothermal
  deriving DecidableEq, Repr

/-- Mechanical role played by the bullet in the air chamber. -/
inductive BulletRole where
  | piston
  deriving DecidableEq, Repr

/-- Release mechanism shown at the lower side of the barrel. -/
inductive ReleaseMechanism where
  | triggerPin
  deriving DecidableEq, Repr

/-!
Qualitative evidence transcribed from the primary image.  In particular,
the hatched bullet separates the blue air region from the open bore, the pin
initially retains it, and the exterior pressure is labelled `P₀`.
-/
structure SuppliedAirPistolFigure where
  showsComponent : FigureComponent → Bool
  showsLabel : FigureLabel → Bool
  isLeftOf : FigureComponent → FigureComponent → Bool
  bulletSeparatesAirFromExterior : Bool
  pinInitiallyEngagesBullet : Bool
  exteriorPressureLabel : PressureQuantity

/-!
All physical quantities needed by the model.  The exit speed is an
unconstrained physical speed here; no structure field assigns it an answer
choice or numerical value.
-/
structure AirPistolSetup where
  initialAir : AirState
  exitAir : AirState
  bulletMass : MassQuantity
  bulletInitialSpeed : SpeedQuantity
  bulletExitSpeed : SpeedQuantity
  ambientPressure : PressureQuantity
  gasBoundaryWork : EnergyQuantity
  ambientDisplacementWork : EnergyQuantity
  process : ThermodynamicProcess
  bulletRole : BulletRole
  releaseMechanism : ReleaseMechanism
  figure : SuppliedAirPistolFigure

/-!
Numerical readouts stated in the problem.  The `0.101 MPa` value for `P₀`
is the usual textbook standard-atmosphere approximation implicit in the
figure and is the value used by the recorded answer.  No exit volume, work,
or exit-speed value occurs among these premises.
-/
structure MatchesProblemReadouts (setup : AirPistolSetup) : Prop where
  initialVolumeCubicCentimeters :
    volumeInCubicCentimeters setup.initialAir.volume = 1
  initialPressureMegapascals :
    pressureInMegapascals setup.initialAir.pressure = 1
  initialTemperatureDegreesCelsius :
    temperatureInDegreesCelsius setup.initialAir.absoluteTemperature = 27
  bulletMassGrams : massInGrams setup.bulletMass = 15
  bulletInitiallyAtRest :
    speedInMetersPerSecond setup.bulletInitialSpeed = 0
  exitPressureMegapascals :
    pressureInMegapascals setup.exitAir.pressure = 1 / 10
  ambientPressureMegapascals :
    pressureInMegapascals setup.ambientPressure = 101 / 1000

/-- Qualitative prose assumptions together with the primary-image facts. -/
def MatchesScenarioAndSuppliedFigure (setup : AirPistolSetup) : Prop :=
  setup.process = .isothermal ∧
    setup.bulletRole = .piston ∧
    setup.releaseMechanism = .triggerPin ∧
    setup.figure.exteriorPressureLabel = setup.ambientPressure ∧
    setup.figure.showsComponent .compressedAir = true ∧
    setup.figure.showsComponent .bullet = true ∧
    setup.figure.showsComponent .triggerPin = true ∧
    setup.figure.showsComponent .barrel = true ∧
    setup.figure.showsLabel .air = true ∧
    setup.figure.showsLabel .exteriorPressureP0 = true ∧
    setup.figure.isLeftOf .compressedAir .bullet = true ∧
    setup.figure.isLeftOf .bullet .barrel = true ∧
    setup.figure.bulletSeparatesAirFromExterior = true ∧
    setup.figure.pinInitiallyEngagesBullet = true

/-- Positivity and nondegeneracy conditions for the physical shot. -/
def HasPhysicalAirPistolParameters (setup : AirPistolSetup) : Prop :=
  0 < volumeInCubicMeters setup.initialAir.volume ∧
    volumeInCubicMeters setup.initialAir.volume <
      volumeInCubicMeters setup.exitAir.volume ∧
    0 < pressureInPascals setup.initialAir.pressure ∧
    0 < pressureInPascals setup.exitAir.pressure ∧
    0 < pressureInPascals setup.ambientPressure ∧
    0 < temperatureInKelvin setup.initialAir.absoluteTemperature ∧
    0 < massInKilograms setup.bulletMass ∧
    0 < speedInMetersPerSecond setup.bulletExitSpeed

/-!
The fixed amount of ideal gas obeys `P V = constant` during the expansion,
and its absolute temperature is unchanged.  Both statements are required in
every coherent unit system.  Neither law assigns a value to the bullet speed.
-/
structure SatisfiesIsothermalIdealGasExpansion
    (setup : AirPistolSetup) : Prop where
  temperatureConstant :
    ∀ units,
      setup.exitAir.absoluteTemperature units =
        setup.initialAir.absoluteTemperature units
  pressureVolumeInvariant :
    ∀ units,
      (setup.initialAir.pressure units).val *
          ((setup.initialAir.volume units).val : ℝ) =
        (setup.exitAir.pressure units).val *
          ((setup.exitAir.volume units).val : ℝ)

/-!
For an isothermal ideal-gas expansion, the gas boundary work is
`Pᵢ Vᵢ log (V_f / Vᵢ)`.  Motion against the constant exterior pressure does
work `P₀ (V_f - Vᵢ)`.  The equations are stated in every coherent unit
system, so each side has the readout dimension of energy.
-/
structure SatisfiesPressureWorkRelations (setup : AirPistolSetup) : Prop where
  gasBoundaryWorkLaw :
    ∀ units,
      (setup.gasBoundaryWork units).val =
        (setup.initialAir.pressure units).val *
          ((setup.initialAir.volume units).val : ℝ) *
            Real.log
              (((setup.exitAir.volume units).val : ℝ) /
                ((setup.initialAir.volume units).val : ℝ))
  ambientDisplacementWorkLaw :
    ∀ units,
      (setup.ambientDisplacementWork units).val =
        (setup.ambientPressure units).val *
          (((setup.exitAir.volume units).val : ℝ) -
            ((setup.initialAir.volume units).val : ℝ))

/-!
With friction and other losses neglected, the net pressure work changes the
bullet's translational kinetic energy.  The initial kinetic term is retained
explicitly rather than hidden by the rest readout.
-/
structure SatisfiesBulletWorkEnergyLaw (setup : AirPistolSetup) : Prop where
  workEnergyBalance :
    ∀ units,
      ((setup.bulletMass units).val : ℝ) *
          ((setup.bulletExitSpeed units).val : ℝ) ^ 2 =
        ((setup.bulletMass units).val : ℝ) *
            ((setup.bulletInitialSpeed units).val : ℝ) ^ 2 +
          2 * ((setup.gasBoundaryWork units).val -
            (setup.ambientDisplacementWork units).val)

/-- The ideal-gas invariant determines an exit volume of `10 cm³`. -/
lemma exitVolumeInCubicCentimeters_eq_ten
    (setup : AirPistolSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalAirPistolParameters setup)
    (hGas : SatisfiesIsothermalIdealGasExpansion setup) :
    volumeInCubicCentimeters setup.exitAir.volume = 10 := by
  let ucm : UnitChoices :=
    {UnitChoices.SI with length := LengthUnit.centimeters}
  have hInitialPressure :
      pressureInPascals setup.initialAir.pressure = 1000000 := by
    have h := hReadouts.initialPressureMegapascals
    norm_num [pressureInMegapascals] at h ⊢
    linarith
  have hExitPressure :
      pressureInPascals setup.exitAir.pressure = 100000 := by
    have h := hReadouts.exitPressureMegapascals
    norm_num [pressureInMegapascals] at h ⊢
    linarith
  let pressureScale : NNReal :=
    ucm.dimScale UnitChoices.SI
      (M𝓭 * L𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹)
  have hPressureScalePositive : 0 < (pressureScale : ℝ) := by
    apply NNReal.coe_pos.mpr
    rw [pos_iff_ne_zero]
    exact UnitChoices.dimScale_ne_zero ucm UnitChoices.SI
      (M𝓭 * L𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹)
  have hInitialPressureUnits :=
    congrArg (fun value ↦ value.val)
      (setup.initialAir.pressure.2 ucm UnitChoices.SI)
  have hExitPressureUnits :=
    congrArg (fun value ↦ value.val)
      (setup.exitAir.pressure.2 ucm UnitChoices.SI)
  change
    pressureInPascals setup.initialAir.pressure =
      (pressureScale : ℝ) * (setup.initialAir.pressure ucm).val
      at hInitialPressureUnits
  change
    pressureInPascals setup.exitAir.pressure =
      (pressureScale : ℝ) * (setup.exitAir.pressure ucm).val
      at hExitPressureUnits
  have hPressureRatio :
      (setup.initialAir.pressure ucm).val =
        10 * (setup.exitAir.pressure ucm).val := by
    rw [hInitialPressure] at hInitialPressureUnits
    rw [hExitPressure] at hExitPressureUnits
    nlinarith
  have hExitPressurePositive :
      0 < (setup.exitAir.pressure ucm).val := by
    rw [hExitPressure] at hExitPressureUnits
    nlinarith
  have hInvariant := hGas.pressureVolumeInvariant ucm
  change
    (setup.initialAir.pressure ucm).val *
        volumeInCubicCentimeters setup.initialAir.volume =
      (setup.exitAir.pressure ucm).val *
        volumeInCubicCentimeters setup.exitAir.volume at hInvariant
  rw [hPressureRatio, hReadouts.initialVolumeCubicCentimeters] at hInvariant
  nlinarith

/-- The isothermal gas does `log 10` joules of positive boundary work. -/
lemma gasBoundaryWorkInJoules_eq_log_ten
    (setup : AirPistolSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalAirPistolParameters setup)
    (hGas : SatisfiesIsothermalIdealGasExpansion setup)
    (hWork : SatisfiesPressureWorkRelations setup) :
    energyInJoules setup.gasBoundaryWork = Real.log 10 := by
  let ucm : UnitChoices :=
    {UnitChoices.SI with length := LengthUnit.centimeters}
  have hVolumeScale :
      ucm.dimScale UnitChoices.SI (L𝓭 * L𝓭 * L𝓭) =
        (1 / 1000000 : NNReal) := by
    norm_num [ucm, UnitChoices.dimScale, L𝓭, LengthUnit.centimeters,
      LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val]
    change (1 / 100 : NNReal) ^ (3 : ℕ) = 1 / 1000000
    norm_num
  have hVolumeConversion (volume : VolumeQuantity) :
      volumeInCubicMeters volume =
        volumeInCubicCentimeters volume / 1000000 := by
    have h := congrArg (fun value ↦ ((value.val : NNReal) : ℝ))
      (volume.2 ucm UnitChoices.SI)
    rw [show dim (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal) =
      L𝓭 * L𝓭 * L𝓭 by rfl, hVolumeScale] at h
    change
      volumeInCubicMeters volume =
        ((1 / 1000000 : NNReal) : ℝ) *
          volumeInCubicCentimeters volume at h
    norm_num at h ⊢
    linarith
  have hInitialPressure :
      pressureInPascals setup.initialAir.pressure = 1000000 := by
    have h := hReadouts.initialPressureMegapascals
    norm_num [pressureInMegapascals] at h ⊢
    linarith
  have hInitialVolume :
      volumeInCubicMeters setup.initialAir.volume = 1 / 1000000 := by
    rw [hVolumeConversion, hReadouts.initialVolumeCubicCentimeters]
  have hExitVolumeReadout :=
    exitVolumeInCubicCentimeters_eq_ten setup hReadouts hPhysical hGas
  have hExitVolume :
      volumeInCubicMeters setup.exitAir.volume = 1 / 100000 := by
    rw [hVolumeConversion, hExitVolumeReadout]
    norm_num
  have hWorkLaw := hWork.gasBoundaryWorkLaw UnitChoices.SI
  change
    energyInJoules setup.gasBoundaryWork =
      pressureInPascals setup.initialAir.pressure *
        volumeInCubicMeters setup.initialAir.volume *
          Real.log
            (volumeInCubicMeters setup.exitAir.volume /
              volumeInCubicMeters setup.initialAir.volume) at hWorkLaw
  rw [hInitialPressure, hInitialVolume, hExitVolume] at hWorkLaw
  norm_num at hWorkLaw ⊢
  exact hWorkLaw

/-- At `P₀ = 0.101 MPa`, displacing `9 cm³` costs `0.909 J`. -/
lemma ambientDisplacementWorkInJoules_eq
    (setup : AirPistolSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalAirPistolParameters setup)
    (hGas : SatisfiesIsothermalIdealGasExpansion setup)
    (hWork : SatisfiesPressureWorkRelations setup) :
    energyInJoules setup.ambientDisplacementWork = 909 / 1000 := by
  let ucm : UnitChoices :=
    {UnitChoices.SI with length := LengthUnit.centimeters}
  have hVolumeScale :
      ucm.dimScale UnitChoices.SI (L𝓭 * L𝓭 * L𝓭) =
        (1 / 1000000 : NNReal) := by
    norm_num [ucm, UnitChoices.dimScale, L𝓭, LengthUnit.centimeters,
      LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val]
    change (1 / 100 : NNReal) ^ (3 : ℕ) = 1 / 1000000
    norm_num
  have hVolumeConversion (volume : VolumeQuantity) :
      volumeInCubicMeters volume =
        volumeInCubicCentimeters volume / 1000000 := by
    have h := congrArg (fun value ↦ ((value.val : NNReal) : ℝ))
      (volume.2 ucm UnitChoices.SI)
    rw [show dim (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal) =
      L𝓭 * L𝓭 * L𝓭 by rfl, hVolumeScale] at h
    change
      volumeInCubicMeters volume =
        ((1 / 1000000 : NNReal) : ℝ) *
          volumeInCubicCentimeters volume at h
    norm_num at h ⊢
    linarith
  have hAmbientPressure :
      pressureInPascals setup.ambientPressure = 101000 := by
    have h := hReadouts.ambientPressureMegapascals
    norm_num [pressureInMegapascals] at h ⊢
    linarith
  have hInitialVolume :
      volumeInCubicMeters setup.initialAir.volume = 1 / 1000000 := by
    rw [hVolumeConversion, hReadouts.initialVolumeCubicCentimeters]
  have hExitVolumeReadout :=
    exitVolumeInCubicCentimeters_eq_ten setup hReadouts hPhysical hGas
  have hExitVolume :
      volumeInCubicMeters setup.exitAir.volume = 1 / 100000 := by
    rw [hVolumeConversion, hExitVolumeReadout]
    norm_num
  have hWorkLaw := hWork.ambientDisplacementWorkLaw UnitChoices.SI
  change
    energyInJoules setup.ambientDisplacementWork =
      pressureInPascals setup.ambientPressure *
        (volumeInCubicMeters setup.exitAir.volume -
          volumeInCubicMeters setup.initialAir.volume) at hWorkLaw
  rw [hAmbientPressure, hInitialVolume, hExitVolume] at hWorkLaw
  norm_num at hWorkLaw ⊢
  exact hWorkLaw

/-!
The positive solution of the work-energy equation.  This exact radical is a
derived conclusion; the decimal answer is obtained only by rounding it.
-/
lemma bulletExitSpeed_exact_readout
    (setup : AirPistolSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalAirPistolParameters setup)
    (hGas : SatisfiesIsothermalIdealGasExpansion setup)
    (hWork : SatisfiesPressureWorkRelations setup)
    (hEnergy : SatisfiesBulletWorkEnergyLaw setup) :
    speedInMetersPerSecond setup.bulletExitSpeed =
      Real.sqrt ((400 / 3) * (Real.log 10 - 909 / 1000)) := by
  have hGasWork :=
    gasBoundaryWorkInJoules_eq_log_ten
      setup hReadouts hPhysical hGas hWork
  have hAmbientWork :=
    ambientDisplacementWorkInJoules_eq
      setup hReadouts hPhysical hGas hWork
  have hMassConversion :
      massInGrams setup.bulletMass =
        1000 * massInKilograms setup.bulletMass := by
    have h := congrArg (fun value ↦ ((value.val : NNReal) : ℝ))
      (setup.bulletMass.2 UnitChoices.SI
        {UnitChoices.SI with mass := MassUnit.grams})
    norm_num [massInGrams, massInKilograms, massReadout,
      UnitChoices.dimScale, M𝓭, MassUnit.grams, MassUnit.kilograms,
      MassUnit.scale, MassUnit.div_eq_val, NNReal.smul_def,
      smul_eq_mul] at h ⊢
    exact h
  have hMass :
      massInKilograms setup.bulletMass = 3 / 200 := by
    have hMassGrams := hReadouts.bulletMassGrams
    rw [hMassConversion] at hMassGrams
    norm_num at hMassGrams ⊢
    linarith
  have hExitSpeedPositive :
      0 < speedInMetersPerSecond setup.bulletExitSpeed :=
    hPhysical.2.2.2.2.2.2.2
  have hEnergyBalance := hEnergy.workEnergyBalance UnitChoices.SI
  change
    massInKilograms setup.bulletMass *
        speedInMetersPerSecond setup.bulletExitSpeed ^ 2 =
      massInKilograms setup.bulletMass *
          speedInMetersPerSecond setup.bulletInitialSpeed ^ 2 +
        2 * (energyInJoules setup.gasBoundaryWork -
          energyInJoules setup.ambientDisplacementWork) at hEnergyBalance
  rw [hMass, hReadouts.bulletInitiallyAtRest, hGasWork, hAmbientWork]
    at hEnergyBalance
  have hSpeedSquared :
      speedInMetersPerSecond setup.bulletExitSpeed ^ 2 =
        (400 / 3) * (Real.log 10 - 909 / 1000) := by
    norm_num at hEnergyBalance ⊢
    linarith
  calc
    speedInMetersPerSecond setup.bulletExitSpeed =
        |speedInMetersPerSecond setup.bulletExitSpeed| :=
      (abs_of_pos hExitSpeedPositive).symm
    _ = Real.sqrt (speedInMetersPerSecond setup.bulletExitSpeed ^ 2) :=
      (Real.sqrt_sq_eq_abs _).symm
    _ = Real.sqrt ((400 / 3) * (Real.log 10 - 909 / 1000)) := by
      rw [hSpeedSquared]

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Speed in meters per second printed beside each answer choice. -/
def displayedAnswerSpeedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 27
  | .B => 13 / 2
  | .C => 21 / 10
  | .D => 1363 / 100

/-- The answer label recorded in the supplied dataset; it is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Agreement with a speed printed to the nearest hundredth meter per second. -/
def RoundsToNearestHundredthMeterPerSecond
    (speed : SpeedQuantity) (displayedSpeed : ℝ) : Prop :=
  |speedInMetersPerSecond speed - displayedSpeed| < 1 / 200

/-- The physical exit speed rounds to the number printed beside a choice. -/
def MatchesAnswerChoice (setup : AirPistolSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestHundredthMeterPerSecond setup.bulletExitSpeed
    (displayedAnswerSpeedInMetersPerSecond choice)

/-!
The isothermal pressure work, after subtracting work against `P₀`, predicts
approximately `13.63 m/s`, which is answer choice D.

Blueprint label: `thm:physics:phyx_mini_0461:target`.
-/
theorem problem_phyx_mini_0461
    (setup : AirPistolSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hScenario : MatchesScenarioAndSuppliedFigure setup)
    (hPhysical : HasPhysicalAirPistolParameters setup)
    (hGas : SatisfiesIsothermalIdealGasExpansion setup)
    (hWork : SatisfiesPressureWorkRelations setup)
    (hEnergy : SatisfiesBulletWorkEnergyLaw setup) :
    speedInMetersPerSecond setup.bulletExitSpeed =
        Real.sqrt ((400 / 3) * (Real.log 10 - 909 / 1000)) ∧
      RoundsToNearestHundredthMeterPerSecond
        setup.bulletExitSpeed (1363 / 100) ∧
      MatchesAnswerChoice setup .D := by
  have hExact :=
    bulletExitSpeed_exact_readout
      setup hReadouts hPhysical hGas hWork hEnergy
  have hLogTen :
      Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    calc
      Real.log (10 : ℝ) = Real.log ((2 : ℝ) * 5) := by norm_num
      _ = Real.log 2 + Real.log 5 :=
        Real.log_mul (by norm_num) (by norm_num)
  have hLogTenLower : (1151 / 500 : ℝ) < Real.log 10 := by
    rw [hLogTen]
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hLogTenUpper : Real.log 10 < (2303 / 1000 : ℝ) := by
    rw [hLogTen]
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hRadicandLower :
      (109 / 8 : ℝ) ^ 2 <
        (400 / 3) * (Real.log 10 - 909 / 1000) := by
    nlinarith
  have hRadicandUpper :
      (400 / 3) * (Real.log 10 - 909 / 1000) <
        (2727 / 200 : ℝ) ^ 2 := by
    nlinarith
  have hSqrtLower :
      (109 / 8 : ℝ) <
        Real.sqrt ((400 / 3) * (Real.log 10 - 909 / 1000)) :=
    (Real.lt_sqrt (by norm_num)).2 hRadicandLower
  have hSqrtUpper :
      Real.sqrt ((400 / 3) * (Real.log 10 - 909 / 1000)) <
        (2727 / 200 : ℝ) :=
    (Real.sqrt_lt' (by norm_num)).2 hRadicandUpper
  have hRounds :
      RoundsToNearestHundredthMeterPerSecond
        setup.bulletExitSpeed (1363 / 100) := by
    rw [RoundsToNearestHundredthMeterPerSecond, hExact, abs_lt]
    constructor <;> nlinarith
  refine ⟨hExact, hRounds, ?_⟩
  simpa [MatchesAnswerChoice, displayedAnswerSpeedInMetersPerSecond]
    using hRounds

end PhyXMiniProblems.ProblemPhyXMini0461
