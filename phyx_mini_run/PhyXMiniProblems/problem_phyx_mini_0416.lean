import Mathlib.Data.Real.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0416

open Dimension

/-!
# Heat added to a monatomic gas expanding against a spring

The supplied figure shows a gas chamber of cross-sectional area `8.0 cm²` on
the left of a piston. On the right, a spring of constant `2000 N/m` is
compressed into a vacuum. Initially the gas is at `300 K`, its cylinder
length is `10.0 cm`, and the spring compression is `2.0 cm`; the requested
final cylinder length is `16.0 cm`.

Physical lengths, area, volume, spring constant, pressure, temperature, and
energy are represented by dimension-aware or dedicated physical types. Real
numbers occur only as calibrated unit readouts and displayed answer values.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative cylinder length carrying the physical dimension of length. -/
abbrev CylinderLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative gas volume carrying the physical dimension length cubed. -/
abbrev GasVolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-!
A nonnegative spring constant. Its dimension is mass per time squared,
equivalently force per length (`N/m`).
-/
abbrev SpringConstantQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a cylinder length or spring compression in metres. -/
def lengthInMetres (length : CylinderLengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a cylinder length or spring compression in centimetres. -/
def lengthInCentimetres (length : CylinderLengthQuantity) : ℝ :=
  ((length { UnitChoices.SI with
    length := LengthUnit.centimeters }).val : ℝ)

/-- Read an area in square metres. -/
def areaInSquareMetres (area : DimArea) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Read an area in square centimetres, as printed in the figure. -/
def areaInSquareCentimetres (area : DimArea) : ℝ :=
  ((area { UnitChoices.SI with
    length := LengthUnit.centimeters }).val : ℝ)

/-- Read a gas volume in cubic metres. -/
def volumeInCubicMetres (volume : GasVolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a spring constant in newtons per metre. -/
def springConstantInNewtonsPerMetre
    (springConstant : SpringConstantQuantity) : ℝ :=
  ((springConstant UnitChoices.SI).val : ℝ)

/-- Read a physical pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-!
Read an absolute temperature in kelvin, accounting for the zero-preserving
unit in which a Physlib `Temperature` value is stored.
-/
def temperatureInKelvin
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- Read heat, internal energy, or work in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Physical states and figure labels -/

/-- The initial and requested final equilibrium states of the gas. -/
inductive ProcessStage where
  | initial
  | final
  deriving DecidableEq, Fintype, Repr

/-- The left and right regions separated by the piston in the figure. -/
inductive ChamberSide where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- Material shown in each region of the supplied figure. -/
inductive ChamberContents where
  | gas
  | vacuum
  deriving DecidableEq, Repr

/-- The gas model specified in the problem statement. -/
inductive GasKind where
  | monatomicIdeal
  | other
  deriving DecidableEq, Repr

/-- The process idealization needed for equilibrium force balance at each endpoint. -/
inductive ProcessKind where
  | quasistaticSpringExpansion
  | other
  deriving DecidableEq, Repr

/-!
The information represented in the primary image. The area and spring
constant remain physical quantities; the Boolean fields record the labelled
geometry rather than introducing any thermodynamic conclusion.
-/
structure PistonCylinderFigure where
  contents : ChamberSide → ChamberContents
  crossSectionArea : DimArea
  springConstant : SpringConstantQuantity
  pistonShown : Bool
  springShown : Bool
  springTouchesPiston : Bool
  springAnchoredAtRightWall : Bool
  lengthLabelLShown : Bool
  areaLabelShown : Bool
  vacuumLabelShown : Bool
  springConstantLabelShown : Bool

/-!
A gas state stores independent physical observables. In particular, volume,
pressure, temperature, spring compression, and internal energy are not defined
from the answer sought; the governing relations between them are assumptions
below.
-/
structure MonatomicGasState where
  cylinderLength : CylinderLengthQuantity
  springCompression : CylinderLengthQuantity
  volume : GasVolumeQuantity
  pressure : DimPressure
  temperature : Temperature
  internalEnergy : DimEnergy

/-!
The closed gas-piston-spring experiment. `amountTimesGasConstant` is the fixed
`nR` coefficient of this particular gas sample, calibrated in joules per
kelvin. Heat and work are independent energy observables.
-/
structure SpringLoadedGasSetup where
  figure : PistonCylinderFigure
  stateAt : ProcessStage → MonatomicGasState
  gasKind : GasKind
  processKind : ProcessKind
  temperatureStorageUnit : TemperatureUnit
  amountTimesGasConstantJoulesPerKelvin : ℝ
  heatAddedToGas : DimEnergy
  workDoneByGas : DimEnergy
  gasIsSealed : Bool
  pistonIsFrictionless : Bool

/-- The joule readout of the heat added to the gas. -/
def heatAddedInJoules (setup : SpringLoadedGasSetup) : ℝ :=
  energyInJoules setup.heatAddedToGas

/-! ## Assumptions: problem data, image readouts, and governing physics -/

/-!
The qualitative model and the numerical endpoint data stated in the prose.
The final spring compression, final pressure, final temperature, work, and
heat are deliberately absent.
-/
structure MatchesProblemScenario (setup : SpringLoadedGasSetup) : Prop where
  gasIsMonatomicIdeal : setup.gasKind = .monatomicIdeal
  processIsQuasistatic : setup.processKind = .quasistaticSpringExpansion
  gasRemainsSealed : setup.gasIsSealed = true
  pistonIsFrictionless : setup.pistonIsFrictionless = true
  temperatureUnitIsKelvin :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin
  initialTemperatureKelvin :
    temperatureInKelvin setup.temperatureStorageUnit
      (setup.stateAt .initial).temperature = 300
  initialCylinderLengthCentimetres :
    lengthInCentimetres (setup.stateAt .initial).cylinderLength = 10
  initialSpringCompressionCentimetres :
    lengthInCentimetres (setup.stateAt .initial).springCompression = 2
  requestedFinalCylinderLengthCentimetres :
    lengthInCentimetres (setup.stateAt .final).cylinderLength = 16

/-!
Facts read directly from the supplied raster: gas on the left, vacuum and the
spring on the right, the piston and spring geometry, the `L` label, area
`8.0 cm²`, and spring constant `2000 N/m`. No heat value occurs here.
-/
structure MatchesSuppliedFigure (setup : SpringLoadedGasSetup) : Prop where
  leftRegionContainsGas : setup.figure.contents .left = .gas
  rightRegionIsVacuum : setup.figure.contents .right = .vacuum
  pistonIsShown : setup.figure.pistonShown = true
  springIsShown : setup.figure.springShown = true
  springTouchesPiston : setup.figure.springTouchesPiston = true
  springIsAnchoredAtRightWall :
    setup.figure.springAnchoredAtRightWall = true
  lengthLabelLIsShown : setup.figure.lengthLabelLShown = true
  areaLabelIsShown : setup.figure.areaLabelShown = true
  vacuumLabelIsShown : setup.figure.vacuumLabelShown = true
  springConstantLabelIsShown :
    setup.figure.springConstantLabelShown = true
  crossSectionAreaSquareCentimetres :
    areaInSquareCentimetres setup.figure.crossSectionArea = 8
  springConstantNewtonsPerMetre :
    springConstantInNewtonsPerMetre setup.figure.springConstant = 2000

/-- Positivity and nondegeneracy conditions selecting physical states. -/
structure HasPhysicalParameters (setup : SpringLoadedGasSetup) : Prop where
  crossSectionAreaPositive :
    0 < areaInSquareMetres setup.figure.crossSectionArea
  springConstantPositive :
    0 < springConstantInNewtonsPerMetre setup.figure.springConstant
  amountTimesGasConstantPositive :
    0 < setup.amountTimesGasConstantJoulesPerKelvin
  cylinderLengthPositive : ∀ stage,
    0 < lengthInMetres (setup.stateAt stage).cylinderLength
  springCompressionNonnegative : ∀ stage,
    0 ≤ lengthInMetres (setup.stateAt stage).springCompression
  volumePositive : ∀ stage,
    0 < volumeInCubicMetres (setup.stateAt stage).volume
  pressurePositive : ∀ stage,
    0 < pressureInPascals (setup.stateAt stage).pressure
  absoluteTemperaturePositive : ∀ stage,
    0 < temperatureInKelvin setup.temperatureStorageUnit
      (setup.stateAt stage).temperature

/-!
The governing endpoint and energy-balance laws in coherent SI readouts:

* cylinder geometry gives `V = A L`;
* piston displacement changes spring compression by the same amount;
* the sealed ideal gas obeys `PV = nRT`;
* quasistatic force balance against vacuum gives `PA = kx`;
* a monatomic ideal gas has `ΔU = (3/2)nRΔT`;
* work done by the gas is the increase in spring energy; and
* the first law gives `Q = ΔU + W_by`.

These are general physical relations. None states the requested heat or an
answer-choice value.
-/
structure SatisfiesQuasistaticIdealGasSpringPhysics
    (setup : SpringLoadedGasSetup) : Prop where
  volumeFromCylinderGeometry : ∀ stage,
    volumeInCubicMetres (setup.stateAt stage).volume =
      areaInSquareMetres setup.figure.crossSectionArea *
        lengthInMetres (setup.stateAt stage).cylinderLength
  pistonSpringKinematics :
    lengthInMetres (setup.stateAt .final).springCompression -
        lengthInMetres (setup.stateAt .initial).springCompression =
      lengthInMetres (setup.stateAt .final).cylinderLength -
        lengthInMetres (setup.stateAt .initial).cylinderLength
  idealGasLaw : ∀ stage,
    pressureInPascals (setup.stateAt stage).pressure *
        volumeInCubicMetres (setup.stateAt stage).volume =
      setup.amountTimesGasConstantJoulesPerKelvin *
        temperatureInKelvin setup.temperatureStorageUnit
          (setup.stateAt stage).temperature
  springForceBalance : ∀ stage,
    pressureInPascals (setup.stateAt stage).pressure *
        areaInSquareMetres setup.figure.crossSectionArea =
      springConstantInNewtonsPerMetre setup.figure.springConstant *
        lengthInMetres (setup.stateAt stage).springCompression
  monatomicInternalEnergyChange :
    energyInJoules (setup.stateAt .final).internalEnergy -
        energyInJoules (setup.stateAt .initial).internalEnergy =
      (3 / 2 : ℝ) * setup.amountTimesGasConstantJoulesPerKelvin *
        (temperatureInKelvin setup.temperatureStorageUnit
            (setup.stateAt .final).temperature -
          temperatureInKelvin setup.temperatureStorageUnit
            (setup.stateAt .initial).temperature)
  quasistaticSpringWork :
    energyInJoules setup.workDoneByGas =
      (1 / 2 : ℝ) *
        springConstantInNewtonsPerMetre setup.figure.springConstant *
          (lengthInMetres (setup.stateAt .final).springCompression ^ 2 -
            lengthInMetres (setup.stateAt .initial).springCompression ^ 2)
  firstLawEnergyBalance :
    heatAddedInJoules setup =
      (energyInJoules (setup.stateAt .final).internalEnergy -
        energyInJoules (setup.stateAt .initial).internalEnergy) +
      energyInJoules setup.workDoneByGas

/-! ## Displayed answers and current target -/

/-- Labels of the four answer choices supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Heat in joules printed beside each answer label. -/
def displayedHeatInJoules : AnswerChoice → ℝ
  | .A => 0
  | .B => 18
  | .C => 39
  | .D => 78

/-- The source dataset records choice C; this is metadata, not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A choice is at least as close to a heat readout as every displayed choice. -/
def IsClosestDisplayedHeatAnswer
    (heatInJoules : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |heatInJoules - displayedHeatInJoules choice| ≤
      |heatInJoules - displayedHeatInJoules other|

/-!
The endpoint laws determine a final spring compression of `0.08 m`. The
ideal-gas and monatomic-energy laws then give an internal-energy increase of
`32.4 J`, while the spring receives `6 J` of work. Thus the required heat is
`38.4 J = 192/5 J`, whose unique closest displayed value is `39 J`, choice C.

Blueprint: `thm:physics:phyx_mini_0416:target`.
-/
theorem heat_required_for_spring_loaded_monatomic_gas_expansion
    (setup : SpringLoadedGasSetup)
    (hScenario : MatchesProblemScenario setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hPhysical : HasPhysicalParameters setup)
    (hPhysics : SatisfiesQuasistaticIdealGasSpringPhysics setup) :
    heatAddedInJoules setup = (192 / 5 : ℝ) ∧
      ∀ choice : AnswerChoice,
        IsClosestDisplayedHeatAnswer (heatAddedInJoules setup) choice ↔
          choice = .C := by
  have length_centimetres_eq (length : CylinderLengthQuantity) :
      lengthInCentimetres length = 100 * lengthInMetres length := by
    unfold lengthInCentimetres lengthInMetres
    rw [length.2 UnitChoices.SI
      ({ UnitChoices.SI with length := LengthUnit.centimeters } :
        UnitChoices)]
    simp [UnitChoices.dimScale, UnitChoices.SI, LengthUnit.centimeters,
      LengthUnit.scale, LengthUnit.div_eq_val, LengthUnit.meters]
    left
    change ((10 : ℝ) ^ 2 = 100)
    norm_num
  have area_square_centimetres_eq (area : DimArea) :
      areaInSquareCentimetres area = 10000 * areaInSquareMetres area := by
    change
      ((area { UnitChoices.SI with
        length := LengthUnit.centimeters }).val : ℝ) =
        10000 * ((area UnitChoices.SI).val : ℝ)
    rw [area.2 UnitChoices.SI
      { UnitChoices.SI with length := LengthUnit.centimeters }]
    have hscale :
        UnitChoices.dimScale UnitChoices.SI
          { UnitChoices.SI with length := LengthUnit.centimeters }
          (dim (WithDim (L𝓭 * L𝓭) NNReal)) = 10000 := by
      apply NNReal.eq
      norm_num [UnitChoices.dimScale, LengthUnit.centimeters,
        LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val]
      change (((100 : NNReal) : ℝ) ^ 2 = 10000)
      norm_num
    rw [hscale]
    norm_num [WithDim.smul_val, NNReal.smul_def, smul_eq_mul]
  have h_initial_length :
      lengthInMetres (setup.stateAt .initial).cylinderLength =
        (1 / 10 : ℝ) := by
    have h := hScenario.initialCylinderLengthCentimetres
    rw [length_centimetres_eq] at h
    norm_num at h ⊢
    linarith
  have h_final_length :
      lengthInMetres (setup.stateAt .final).cylinderLength =
        (4 / 25 : ℝ) := by
    have h := hScenario.requestedFinalCylinderLengthCentimetres
    rw [length_centimetres_eq] at h
    norm_num at h ⊢
    linarith
  have h_initial_compression :
      lengthInMetres (setup.stateAt .initial).springCompression =
        (1 / 50 : ℝ) := by
    have h := hScenario.initialSpringCompressionCentimetres
    rw [length_centimetres_eq] at h
    norm_num at h ⊢
    linarith
  have h_final_compression :
      lengthInMetres (setup.stateAt .final).springCompression =
        (2 / 25 : ℝ) := by
    have h := hPhysics.pistonSpringKinematics
    rw [h_initial_compression, h_final_length, h_initial_length] at h
    norm_num at h ⊢
    linarith
  have h_area :
      areaInSquareMetres setup.figure.crossSectionArea =
        (1 / 1250 : ℝ) := by
    have h := hFigure.crossSectionAreaSquareCentimetres
    rw [area_square_centimetres_eq] at h
    norm_num at h ⊢
    linarith
  have h_spring_constant :
      springConstantInNewtonsPerMetre setup.figure.springConstant = 2000 :=
    hFigure.springConstantNewtonsPerMetre
  have h_initial_volume :
      volumeInCubicMetres (setup.stateAt .initial).volume =
        (1 / 12500 : ℝ) := by
    rw [hPhysics.volumeFromCylinderGeometry, h_area, h_initial_length]
    norm_num
  have h_final_volume :
      volumeInCubicMetres (setup.stateAt .final).volume =
        (2 / 15625 : ℝ) := by
    rw [hPhysics.volumeFromCylinderGeometry, h_area, h_final_length]
    norm_num
  have h_initial_pressure :
      pressureInPascals (setup.stateAt .initial).pressure = 50000 := by
    have h := hPhysics.springForceBalance .initial
    rw [h_area, h_spring_constant, h_initial_compression] at h
    norm_num at h ⊢
    linarith
  have h_final_pressure :
      pressureInPascals (setup.stateAt .final).pressure = 200000 := by
    have h := hPhysics.springForceBalance .final
    rw [h_area, h_spring_constant, h_final_compression] at h
    norm_num at h ⊢
    linarith
  have h_amount_times_gas_constant :
      setup.amountTimesGasConstantJoulesPerKelvin = (1 / 75 : ℝ) := by
    have h := hPhysics.idealGasLaw .initial
    rw [h_initial_pressure, h_initial_volume,
      hScenario.initialTemperatureKelvin] at h
    norm_num at h ⊢
    linarith
  have h_final_temperature :
      temperatureInKelvin setup.temperatureStorageUnit
          (setup.stateAt .final).temperature = 1920 := by
    have h := hPhysics.idealGasLaw .final
    rw [h_final_pressure, h_final_volume,
      h_amount_times_gas_constant] at h
    norm_num at h ⊢
    linarith
  have h_internal_energy_change :
      energyInJoules (setup.stateAt .final).internalEnergy -
          energyInJoules (setup.stateAt .initial).internalEnergy =
        (162 / 5 : ℝ) := by
    have h := hPhysics.monatomicInternalEnergyChange
    rw [h_amount_times_gas_constant, h_final_temperature,
      hScenario.initialTemperatureKelvin] at h
    norm_num at h ⊢
    linarith
  have h_work : energyInJoules setup.workDoneByGas = 6 := by
    rw [hPhysics.quasistaticSpringWork, h_spring_constant,
      h_final_compression, h_initial_compression]
    norm_num
  have h_heat : heatAddedInJoules setup = (192 / 5 : ℝ) := by
    rw [hPhysics.firstLawEnergyBalance, h_internal_energy_change, h_work]
    norm_num
  refine ⟨h_heat, ?_⟩
  intro choice
  constructor
  · intro h_closest
    rw [h_heat] at h_closest
    cases choice with
    | A =>
        have h := h_closest .C
        norm_num [displayedHeatInJoules] at h
    | B =>
        have h := h_closest .C
        norm_num [displayedHeatInJoules] at h
    | C => rfl
    | D =>
        have h := h_closest .C
        norm_num [displayedHeatInJoules] at h
  · intro h_choice
    subst choice
    rw [h_heat]
    intro other
    cases other <;> norm_num [displayedHeatInJoules]

end PhyXMiniProblems.ProblemPhyXMini0416
