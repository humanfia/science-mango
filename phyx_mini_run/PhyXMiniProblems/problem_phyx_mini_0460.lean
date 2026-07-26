import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0460

open Dimension

/-!
# Heat transfer during polytropic compression of air

A closed piston--cylinder initially contains `0.2 L` of air at `90 kPa` and
`20 °C`.  The piston compresses the air quasi-statically to one sixth of its
initial volume along a polytropic path with exponent `n = 1.25`.

Pressure, volume, absolute temperature, internal energy, work, and heat retain
their physical roles.  Real numbers below are explicitly named SI or displayed
answer readouts, or dimensionless model parameters.  Heat is positive into the
air and work is positive when done by the air, so the closed-system first law
is written `Q = ΔU + W`.
-/

/-! ## Dimensionful quantities and unit-labelled readouts -/

/-- A nonnegative physical gas volume, carrying dimension `L³`. -/
abbrev GasVolume : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Read a physical gas volume in coherent SI cubic metres. -/
def volumeInCubicMeters (volume : GasVolume) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical gas volume in litres. -/
def volumeInLiters (volume : GasVolume) : ℝ :=
  1000 * volumeInCubicMeters volume

/-- Read a physical pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Read a physical pressure in kilopascals. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Read a Physlib absolute temperature in kelvin. -/
def temperatureInKelvins
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- Read the same temperature on the degrees-Celsius scale. -/
def temperatureInDegreesCelsius
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  temperatureInKelvins storageUnit temperature - 5463 / 20

/-- Read signed heat, work, or internal energy in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Read signed heat, work, or internal energy in kilojoules. -/
def energyInKilojoules (energy : DimEnergy) : ℝ :=
  energyInJoules energy / 1000

/-! ## Thermodynamic states, process roles, and figure vocabulary -/

/-- The initial and final equilibrium states of the air. -/
inductive Endpoint where
  | initial
  | final
  deriving DecidableEq, Fintype, Repr

/-- A macroscopic equilibrium state of the fixed air sample. -/
structure AirState where
  pressure : DimPressure
  volume : GasVolume
  absoluteTemperature : Temperature
  internalEnergy : DimEnergy

/-- Working-fluid identity named by the problem statement and figure. -/
inductive WorkingFluid where
  | air
  | other
  deriving DecidableEq, Repr

/-- Equation-of-state model used for the air. -/
inductive GasModel where
  | caloricallyPerfectIdealGas
  | other
  deriving DecidableEq, Repr

/-- Whether mass crosses the piston--cylinder boundary. -/
inductive InventoryRegime where
  | closed
  | open
  deriving DecidableEq, Repr

/-- Mechanical regime of the moving piston. -/
inductive MechanicalRegime where
  | quasiEquilibrium
  | irreversible
  deriving DecidableEq, Repr

/-- Direction of the volume change. -/
inductive ProcessDirection where
  | compression
  | expansion
  deriving DecidableEq, Repr

/-- Regions visually distinguished in the supplied piston--cylinder image. -/
inductive FigureRegion where
  | airChamber
  | pistonSweep
  | cylinderCasing
  deriving DecidableEq, Repr

/-- Line style used to distinguish the two piston positions in the image. -/
inductive PistonOutline where
  | solid
  | dashed
  deriving DecidableEq, Repr

/-- Horizontal ordering of the two depicted piston positions. -/
inductive HorizontalPlacement where
  | left
  | right
  deriving DecidableEq, Repr

/-- Qualitative data carried by the supplied piston--cylinder schematic. -/
structure PistonCylinderFigure where
  regionLabel : FigureRegion → Option String
  pistonOutlineAt : Endpoint → PistonOutline
  pistonPlacementAt : Endpoint → HorizontalPlacement
  outerCasingShown : Bool

/-- The complete physical process, including unknown heat and work. -/
structure AirPolytropicCompression where
  stateAt : Endpoint → AirState
  workingFluid : WorkingFluid
  gasModel : GasModel
  inventoryRegime : InventoryRegime
  mechanicalRegime : MechanicalRegime
  direction : ProcessDirection
  temperatureStorageUnit : TemperatureUnit
  polytropicExponent : ℝ
  ratioOfSpecificHeats : ℝ
  workDoneByAir : DimEnergy
  heatTransferredIntoAir : DimEnergy
  figure : PistonCylinderFigure

/-! ## Scenario, figure, and numerical readouts -/

/-- Qualitative physical information stated in the problem. -/
structure MatchesStatedScenario
    (process : AirPolytropicCompression) : Prop where
  workingFluidIsAir : process.workingFluid = .air
  gasUsesColdAirIdealization :
    process.gasModel = .caloricallyPerfectIdealGas
  airInventoryIsClosed : process.inventoryRegime = .closed
  pistonMotionIsQuasiEquilibrium :
    process.mechanicalRegime = .quasiEquilibrium
  processIsCompression : process.direction = .compression

/-- Exact transcription of the scalar data printed in the question. -/
structure MatchesProblemReadouts
    (process : AirPolytropicCompression) : Prop where
  temperatureStoredInKelvin :
    process.temperatureStorageUnit = TemperatureUnit.kelvin
  initialVolumeIsPointTwoLiters :
    volumeInLiters (process.stateAt .initial).volume = 1 / 5
  initialPressureIsNinetyKilopascals :
    pressureInKilopascals (process.stateAt .initial).pressure = 90
  initialTemperatureIsTwentyDegreesCelsius :
    temperatureInDegreesCelsius process.temperatureStorageUnit
      (process.stateAt .initial).absoluteTemperature = 20
  statedPolytropicExponent : process.polytropicExponent = 5 / 4
  finalVolumeIsOneSixthOfInitial :
    6 * volumeInCubicMeters (process.stateAt .final).volume =
      volumeInCubicMeters (process.stateAt .initial).volume

/-!
The cold-air-standard caloric index is model input, separated from the values
explicitly printed in the question.  It is not a heat-transfer conclusion.
-/
structure UsesColdAirStandardCaloricModel
    (process : AirPolytropicCompression) : Prop where
  ratioOfSpecificHeatsIsSevenFifths :
    process.ratioOfSpecificHeats = 7 / 5

/-- Figure-derived label, casing, and relative piston-position information. -/
structure MatchesSuppliedPistonCylinderFigure
    (process : AirPolytropicCompression) : Prop where
  chamberIsLabelledAir :
    process.figure.regionLabel .airChamber = some "Air"
  pistonSweepIsUnlabelled :
    process.figure.regionLabel .pistonSweep = none
  casingIsShown : process.figure.outerCasingShown = true
  initialPistonIsSolid :
    process.figure.pistonOutlineAt .initial = .solid
  finalPistonIsDashed :
    process.figure.pistonOutlineAt .final = .dashed
  initialPistonIsToTheRight :
    process.figure.pistonPlacementAt .initial = .right
  finalPistonIsToTheLeft :
    process.figure.pistonPlacementAt .final = .left

/-- Positivity and nondegeneracy conditions for the physical process. -/
structure HasPhysicalPolytropicParameters
    (process : AirPolytropicCompression) : Prop where
  pressurePositive : ∀ endpoint,
    0 < pressureInPascals (process.stateAt endpoint).pressure
  volumePositive : ∀ endpoint,
    0 < volumeInCubicMeters (process.stateAt endpoint).volume
  absoluteTemperaturePositive : ∀ endpoint,
    0 < temperatureInKelvins process.temperatureStorageUnit
      (process.stateAt endpoint).absoluteTemperature
  finalVolumeLessThanInitial :
    volumeInCubicMeters (process.stateAt .final).volume <
      volumeInCubicMeters (process.stateAt .initial).volume
  polytropicExponentNotOne : process.polytropicExponent ≠ 1
  caloricIndexGreaterThanOne : 1 < process.ratioOfSpecificHeats

/-! ## Governing thermodynamic laws -/

/-!
These are general endpoint laws for a calorically perfect ideal gas on a
quasi-equilibrium polytropic path.  None contains the requested heat value or
an answer-choice label.
-/
structure SatisfiesPolytropicIdealAirLaws
    (process : AirPolytropicCompression) : Prop where
  polytropicPressureEndpointLaw :
    pressureInPascals (process.stateAt .final).pressure =
      pressureInPascals (process.stateAt .initial).pressure *
        Real.rpow
          (volumeInCubicMeters (process.stateAt .initial).volume /
            volumeInCubicMeters (process.stateAt .final).volume)
          process.polytropicExponent
  idealGasTemperatureEndpointLaw :
    temperatureInKelvins process.temperatureStorageUnit
        (process.stateAt .final).absoluteTemperature =
      temperatureInKelvins process.temperatureStorageUnit
          (process.stateAt .initial).absoluteTemperature *
        Real.rpow
          (volumeInCubicMeters (process.stateAt .initial).volume /
            volumeInCubicMeters (process.stateAt .final).volume)
          (process.polytropicExponent - 1)
  caloricallyPerfectInternalEnergyLaw :
    energyInJoules (process.stateAt .final).internalEnergy -
        energyInJoules (process.stateAt .initial).internalEnergy =
      (pressureInPascals (process.stateAt .final).pressure *
            volumeInCubicMeters (process.stateAt .final).volume -
          pressureInPascals (process.stateAt .initial).pressure *
            volumeInCubicMeters (process.stateAt .initial).volume) /
        (process.ratioOfSpecificHeats - 1)
  quasiEquilibriumPolytropicBoundaryWork :
    process.mechanicalRegime = .quasiEquilibrium →
      process.polytropicExponent ≠ 1 →
        energyInJoules process.workDoneByAir =
          (pressureInPascals (process.stateAt .final).pressure *
                volumeInCubicMeters (process.stateAt .final).volume -
              pressureInPascals (process.stateAt .initial).pressure *
                volumeInCubicMeters (process.stateAt .initial).volume) /
            (1 - process.polytropicExponent)
  closedSystemFirstLaw :
    process.inventoryRegime = .closed →
      energyInJoules process.heatTransferredIntoAir =
        energyInJoules (process.stateAt .final).internalEnergy -
          energyInJoules (process.stateAt .initial).internalEnergy +
            energyInJoules process.workDoneByAir

/-! ## Exact model expression and displayed answer choices -/

/--
The unrounded cold-air-standard result in joules.  It is obtained by adding
`ΔU = Δ(PV)/(γ - 1)` and `W = Δ(PV)/(1 - n)`, with
`Δ(PV) = P₁ V₁ (6^(n-1) - 1)`.
-/
def exactModeledHeatTransferInJoules : ℝ :=
  let initialPressureInPascals : ℝ := 90000
  let initialVolumeInCubicMeters : ℝ := 1 / 5000
  let compressionRatio : ℝ := 6
  let polytropicExponent : ℝ := 5 / 4
  let caloricIndex : ℝ := 7 / 5
  let changeInPressureVolumeProduct : ℝ :=
    initialPressureInPascals * initialVolumeInCubicMeters *
      (Real.rpow compressionRatio (polytropicExponent - 1) - 1)
  changeInPressureVolumeProduct / (caloricIndex - 1) +
    changeInPressureVolumeProduct / (1 - polytropicExponent)

/-- Labels printed beside the four candidate heat-transfer values. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed candidate values, interpreted in kilojoules with heat into air positive. -/
def displayedHeatTransferInKilojoules : AnswerChoice → ℝ
  | .A => -(190 / 1000)
  | .B => 147 / 10000
  | .C => 190 / 1000
  | .D => -(147 / 10000)

/-- The answer label recorded by the source dataset, retained as metadata only. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A displayed option is strictly closer to a modeled heat than every alternative. -/
def IsUniqueClosestDisplayedHeat
    (modeledHeatInKilojoules : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |modeledHeatInKilojoules - displayedHeatTransferInKilojoules choice| <
      |modeledHeatInKilojoules - displayedHeatTransferInKilojoules other|

/-! ## Derived heat and requested answer -/

/--
The physical laws determine the unrounded heat-transfer value.  This is a
derived conclusion, not a premise of the model.
-/
lemma heatTransfer_eq_exactModeledValue
    (process : AirPolytropicCompression)
    (_scenario : MatchesStatedScenario process)
    (_readouts : MatchesProblemReadouts process)
    (_airModel : UsesColdAirStandardCaloricModel process)
    (_physical : HasPhysicalPolytropicParameters process)
    (_laws : SatisfiesPolytropicIdealAirLaws process) :
    energyInJoules process.heatTransferredIntoAir =
      exactModeledHeatTransferInJoules := by
  have hP₁ :
      pressureInPascals (process.stateAt .initial).pressure = 90000 := by
    have h := _readouts.initialPressureIsNinetyKilopascals
    unfold pressureInKilopascals at h
    linarith
  have hV₁ :
      volumeInCubicMeters (process.stateAt .initial).volume = 1 / 5000 := by
    have h := _readouts.initialVolumeIsPointTwoLiters
    unfold volumeInLiters at h
    norm_num at h ⊢
    linarith
  have hV₂ :
      volumeInCubicMeters (process.stateAt .final).volume = 1 / 30000 := by
    have h := _readouts.finalVolumeIsOneSixthOfInitial
    rw [hV₁] at h
    norm_num at h ⊢
    linarith
  have hratio :
      volumeInCubicMeters (process.stateAt .initial).volume /
          volumeInCubicMeters (process.stateAt .final).volume = 6 := by
    rw [hV₁, hV₂]
    norm_num
  have hn : process.polytropicExponent = 5 / 4 :=
    _readouts.statedPolytropicExponent
  have hγ : process.ratioOfSpecificHeats = 7 / 5 :=
    _airModel.ratioOfSpecificHeatsIsSevenFifths
  have hpow :
      Real.rpow 6 (5 / 4 : ℝ) =
        Real.rpow 6 (1 / 4 : ℝ) * 6 := by
    calc
      Real.rpow 6 (5 / 4 : ℝ) =
          Real.rpow 6 ((1 / 4 : ℝ) + 1) := by norm_num
      _ = Real.rpow 6 (1 / 4 : ℝ) * Real.rpow 6 1 := by
        exact Real.rpow_add (by norm_num) (1 / 4) 1
      _ = Real.rpow 6 (1 / 4 : ℝ) * 6 := by norm_num
  have hP₂ :
      pressureInPascals (process.stateAt .final).pressure =
        90000 * Real.rpow 6 (5 / 4 : ℝ) := by
    simpa [hP₁, hratio, hn] using _laws.polytropicPressureEndpointLaw
  have hΔPV :
      pressureInPascals (process.stateAt .final).pressure *
            volumeInCubicMeters (process.stateAt .final).volume -
          pressureInPascals (process.stateAt .initial).pressure *
            volumeInCubicMeters (process.stateAt .initial).volume =
        18 * (Real.rpow 6 (1 / 4 : ℝ) - 1) := by
    rw [hP₂, hV₂, hP₁, hV₁, hpow]
    ring
  have hΔU := _laws.caloricallyPerfectInternalEnergyLaw
  have hW := _laws.quasiEquilibriumPolytropicBoundaryWork
    _scenario.pistonMotionIsQuasiEquilibrium
    _physical.polytropicExponentNotOne
  have hQ := _laws.closedSystemFirstLaw _scenario.airInventoryIsClosed
  rw [hQ, hΔU, hW, hΔPV, hγ, hn]
  simp only [exactModeledHeatTransferInJoules]
  norm_num

/-- The unrounded cold-air model selects the printed value `-0.0147 kJ`. -/
lemma exactModeledHeatTransfer_selects_choice_D :
    IsUniqueClosestDisplayedHeat
      (exactModeledHeatTransferInJoules / 1000) .D := by
  let q : ℝ :=
    -(27 / 1000) * (Real.rpow 6 (1 / 4 : ℝ) - 1)
  have hmodel : exactModeledHeatTransferInJoules / 1000 = q := by
    dsimp [q, exactModeledHeatTransferInJoules]
    norm_num
    ring
  have hroot_lower :
      (3 / 2 : ℝ) < Real.rpow 6 (1 / 4 : ℝ) := by
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num]
    refine
      (Real.lt_rpow_inv_iff_of_pos
        (x := 3 / 2) (y := 6) (z := 4)
        (by norm_num) (by norm_num) (by norm_num)).2 ?_
    norm_num [Real.rpow_natCast]
  have hroot_upper :
      Real.rpow 6 (1 / 4 : ℝ) < (5 / 3 : ℝ) := by
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num]
    refine
      (Real.rpow_inv_lt_iff_of_pos
        (x := 6) (y := 5 / 3) (z := 4)
        (by norm_num) (by norm_num) (by norm_num)).2 ?_
    norm_num [Real.rpow_natCast]
  have hq_lower : (-9 / 500 : ℝ) < q := by
    dsimp [q]
    norm_num at hroot_upper ⊢
    linarith
  have hq_upper : q < (-27 / 2000 : ℝ) := by
    dsimp [q]
    norm_num at hroot_lower ⊢
    linarith
  unfold IsUniqueClosestDisplayedHeat
  intro other hother
  rw [hmodel]
  fin_cases other
  · simp only [displayedHeatTransferInKilojoules, sub_neg_eq_add]
    have hright : 0 < q + 190 / 1000 := by
      norm_num at hq_lower ⊢
      linarith
    rw [abs_of_pos hright, abs_lt]
    constructor
    · norm_num at hq_lower hq_upper ⊢
      linarith
    · norm_num at hq_lower hq_upper ⊢
  · simp only [displayedHeatTransferInKilojoules, sub_neg_eq_add]
    have hright : q - 147 / 10000 < 0 := by
      norm_num at hq_upper ⊢
      linarith
    rw [abs_of_neg hright, abs_lt]
    constructor
    · norm_num at hq_lower hq_upper ⊢
      linarith
    · norm_num at hq_lower hq_upper ⊢
      linarith
  · simp only [displayedHeatTransferInKilojoules, sub_neg_eq_add]
    have hright : q - 190 / 1000 < 0 := by
      norm_num at hq_upper ⊢
      linarith
    rw [abs_of_neg hright, abs_lt]
    constructor
    · norm_num at hq_lower hq_upper ⊢
      linarith
    · norm_num at hq_lower hq_upper ⊢
      linarith
  · exact (hother rfl).elim

/-!
The quasi-equilibrium polytropic compression has the exact modeled heat above,
and among the four printed values its unique closest answer is D,
`-0.0147 kJ`.

This declaration formalizes blueprint label
`thm:physics:phyx_mini_0460:target`.
-/
theorem problem_phyx_mini_0460
    (process : AirPolytropicCompression)
    (_scenario : MatchesStatedScenario process)
    (_readouts : MatchesProblemReadouts process)
    (_figure : MatchesSuppliedPistonCylinderFigure process)
    (_airModel : UsesColdAirStandardCaloricModel process)
    (_physical : HasPhysicalPolytropicParameters process)
    (_laws : SatisfiesPolytropicIdealAirLaws process) :
    energyInJoules process.heatTransferredIntoAir =
        exactModeledHeatTransferInJoules ∧
      IsUniqueClosestDisplayedHeat
        (energyInKilojoules process.heatTransferredIntoAir) .D := by
  have hheat := heatTransfer_eq_exactModeledValue
    process _scenario _readouts _airModel _physical _laws
  constructor
  · exact hheat
  · simpa [energyInKilojoules, hheat] using
      exactModeledHeatTransfer_selects_choice_D

end PhyXMiniProblems.ProblemPhyXMini0460
