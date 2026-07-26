import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0472

open Dimension

/-!
# Work done by air during diesel-engine compression

Air in a diesel-engine cylinder is compressed from the figure state `V₁` to
the maximum-compression state `V₂ = V₁ / 15`.  The stated initial volume is
`1.00 L = 1.00 * 10⁻³ m³`, the molar heat capacity at constant volume is
`20.8 J/(mol K)`, and the adiabatic index is `1.400`.

The source does not give an initial pressure, an amount of air, endpoint
temperatures, heat transfer, or an adiabatic/reversible process law.  Thus it
does not support a numerical work value.  The theorem below records instead
the symbolic work relation that follows from the caloric equation of state and
the first law, leaving the unreported quantities independent.

Pressure and energy use Physlib's dimensionful quantities.  Volume and molar
energy per temperature are local dimensionful types because Physlib has no
named volume or amount-of-substance dimension.  Real numbers below are
explicit SI readouts, dimensionless ratios, schematic image coordinates, mole
readouts, or displayed-answer metadata.
-/

/-! ## Dimensionful physical quantities and SI readouts -/

/-- A physical gas volume, carrying length-cubed dimension. -/
abbrev GasVolume : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/--
Energy per absolute temperature.  Its inverse-mole role is represented by
explicitly named mole readouts, since Physlib's dimension system has no
amount-of-substance component.
-/
abbrev MolarEnergyPerTemperature : Type :=
  Dimensionful
    (WithDim
      (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) ℝ)

/-- Read a physical gas volume in coherent SI cubic metres. -/
def volumeInCubicMeters (volume : GasVolume) : ℝ :=
  (volume UnitChoices.SI).val

/-- Read a physical gas volume in litres. -/
def volumeInLiters (volume : GasVolume) : ℝ :=
  1000 * volumeInCubicMeters volume

/-- Read a physical pressure in coherent SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a signed physical energy in coherent SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val / (DimEnergy.joule UnitChoices.SI).val

/-- Read an absolute temperature in kelvin. -/
def temperatureInKelvins (temperature : Temperature) : ℝ :=
  temperature.toReal

/-- Read a molar heat capacity in `J/(mol K)`. -/
def molarEnergyPerTemperatureInSI
    (quantity : MolarEnergyPerTemperature) : ℝ :=
  (quantity UnitChoices.SI).val

/-! ## Thermodynamic states and primary-figure labels -/

/-- The two labeled cylinder states in the source figure. -/
inductive CompressionState where
  | initial
  | maximumCompression
  deriving DecidableEq, Repr

/-- The two side-by-side panels in the source figure. -/
inductive FigurePanel where
  | left
  | right
  deriving DecidableEq, Repr

/-- The volume symbols printed in the source figure. -/
inductive FigureVolumeLabel where
  | V1
  | V2
  deriving DecidableEq, Repr

/-- The gas species specified by the problem. -/
inductive CylinderGas where
  | air
  | other
  deriving DecidableEq, Repr

/-- The kind of engine cylinder specified by the problem. -/
inductive EngineKind where
  | diesel
  | other
  deriving DecidableEq, Repr

/-!
Primary-image metadata is kept distinct from the thermodynamic state.  Piston
coordinates and rendered gas heights are schematic image readouts; they are
not physical lengths or volumes.
-/
structure DieselCompressionFigure where
  stateDepicted : FigurePanel → CompressionState
  volumeLabel : FigurePanel → FigureVolumeLabel
  pistonVerticalCoordinate : FigurePanel → ℝ
  renderedGasHeight : FigurePanel → ℝ
  cylinderWallsVisible : FigurePanel → Bool
  pistonVisible : FigurePanel → Bool
  pistonRodVisible : FigurePanel → Bool
  greenGasVisible : FigurePanel → Bool
  compressionEquationVisible : Bool

/-!
The independent physical quantities for the cylinder compression.

The initial pressure is retained as an unconstrained physical quantity because
the source does not supply a pressure calibration.  Likewise, the amount,
endpoint temperatures, heat supplied to the gas, and work done by the gas are
independent fields.  In particular, `workDoneByGas` is not defined using any
displayed answer or process-specific work formula.
-/
structure DieselCylinderCompression where
  engineKind : EngineKind
  gas : CylinderGas
  compressionRatio : ℝ
  amountOfAirMoles : ℝ
  molarHeatCapacityAtConstantVolume : MolarEnergyPerTemperature
  adiabaticIndexGamma : ℝ
  pressure : CompressionState → DimPressure
  volume : CompressionState → GasVolume
  temperature : CompressionState → Temperature
  internalEnergy : CompressionState → DimEnergy
  heatTransferredToGas : DimEnergy
  workDoneByGas : DimEnergy
  figure : DieselCompressionFigure

/-! ## Scenario, figure/data readouts, and physical branch -/

/-- Qualitative problem setup, without any requested work value. -/
structure MatchesDieselCompressionScenario
    (setup : DieselCylinderCompression) : Prop where
  engineIsDiesel : setup.engineKind = .diesel
  workingGasIsAir : setup.gas = .air

/-!
Transcription of the primary raster image.  The left panel is labeled
"Initial volume" with symbol `V₁`; the right panel is labeled "Maximum
compression" with symbol `V₂`.  The right piston is higher and its green gas
region is shorter.  The printed equation is tied to the physical endpoint
volumes using the independently stored compression ratio.
-/
structure MatchesPrimaryCompressionFigure
    (setup : DieselCylinderCompression) : Prop where
  leftDepictsInitial : setup.figure.stateDepicted .left = .initial
  rightDepictsMaximumCompression :
    setup.figure.stateDepicted .right = .maximumCompression
  leftVolumeLabel : setup.figure.volumeLabel .left = .V1
  rightVolumeLabel : setup.figure.volumeLabel .right = .V2
  compressedPistonIsHigher :
    setup.figure.pistonVerticalCoordinate .left <
      setup.figure.pistonVerticalCoordinate .right
  compressedGasRegionIsShorter :
    setup.figure.renderedGasHeight .right <
      setup.figure.renderedGasHeight .left
  cylinderWallsShown :
    ∀ panel, setup.figure.cylinderWallsVisible panel = true
  bothPistonsShown : ∀ panel, setup.figure.pistonVisible panel = true
  bothPistonRodsShown : ∀ panel, setup.figure.pistonRodVisible panel = true
  greenGasShown : ∀ panel, setup.figure.greenGasVisible panel = true
  equationIsPrinted : setup.figure.compressionEquationVisible = true
  printedCompressionEquation :
    volumeInCubicMeters (setup.volume .maximumCompression) =
      (1 / setup.compressionRatio) *
        volumeInCubicMeters (setup.volume .initial)

/-!
Numerical readouts stated in the problem.  Both stated forms of the initial
volume are retained.  The compression ratio and adiabatic index are
dimensionless; the molar heat capacity is an explicitly unit-tagged scalar
readout.  The value of `gamma` is data, but no adiabatic law is asserted.
-/
structure MatchesCompressionProblemReadouts
    (setup : DieselCylinderCompression) : Prop where
  compressionRatioIsFifteen : setup.compressionRatio = 15
  initialVolumeInLiters : volumeInLiters (setup.volume .initial) = 1
  initialVolumeInCubicMeters :
    volumeInCubicMeters (setup.volume .initial) = 1 / 1000
  statedMolarHeatCapacityAtConstantVolume :
    molarEnergyPerTemperatureInSI
        setup.molarHeatCapacityAtConstantVolume = 104 / 5
  statedAdiabaticIndex : setup.adiabaticIndexGamma = 7 / 5

/-- Positivity and nondegeneracy conditions for the physical branch. -/
structure HasPhysicalCompressionParameters
    (setup : DieselCylinderCompression) : Prop where
  compressionRatioGreaterThanOne : 1 < setup.compressionRatio
  amountOfAirPositive : 0 < setup.amountOfAirMoles
  molarHeatCapacityPositive :
    0 < molarEnergyPerTemperatureInSI
      setup.molarHeatCapacityAtConstantVolume
  adiabaticIndexGreaterThanOne : 1 < setup.adiabaticIndexGamma
  pressurePositive :
    ∀ state, 0 < pressureInPascals (setup.pressure state)
  volumePositive :
    ∀ state, 0 < volumeInCubicMeters (setup.volume state)
  temperaturePositive :
    ∀ state, 0 < temperatureInKelvins (setup.temperature state)

/-! ## Governing thermodynamic laws -/

/-!
Endpoint energy laws sufficient for a calorically perfect gas compression:

* `U = n C_V T` at both endpoints;
* `Delta U = Q - W_by_gas`, using the convention that work done by the gas is
  positive.

No pressure calibration, adiabatic temperature-volume relation, or zero-heat
condition is included.  These laws relate independently stored physical
quantities and do not state the requested work formula.
-/
structure SatisfiesCaloricallyPerfectGasCompressionLaws
    (setup : DieselCylinderCompression) : Prop where
  internalEnergyLawSI : ∀ state : CompressionState,
    energyInJoules (setup.internalEnergy state) =
      setup.amountOfAirMoles *
        molarEnergyPerTemperatureInSI
          setup.molarHeatCapacityAtConstantVolume *
            temperatureInKelvins (setup.temperature state)
  firstLawWithWorkByGasPositive :
    energyInJoules (setup.internalEnergy .maximumCompression) -
        energyInJoules (setup.internalEnergy .initial) =
      energyInJoules setup.heatTransferredToGas -
        energyInJoules setup.workDoneByGas

/-! ## Displayed-answer metadata -/

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Work done by the gas printed beside each answer, in joules. -/
def displayedWorkByGasInJoules : AnswerChoice → ℝ
  | .A => -453
  | .B => -494
  | .C => 494
  | .D => 453

/-!
Dataset answer metadata.  It is deliberately absent from every physical
premise and from the theorem conclusion because the stated source data do not
support selecting a numerical answer.
-/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
The source-supported result leaves the unreported heat transfer, amount of
air, and endpoint temperatures symbolic.  Substituting the stated
`C_V = 104/5 J/(mol K)` into the caloric equation of state and combining the
result with the first law gives the signed work done by the gas.

The supplied compression ratio and `gamma` do not determine the temperature
change without an additional process law, and no initial pressure is given.
Consequently this statement does not select any displayed numerical answer.

This formalizes blueprint label `thm:physics:phyx_mini_0472:target` after the
semantic redraft required by the final formalization review gate.
-/
theorem problem_phyx_mini_0472
    (setup : DieselCylinderCompression)
    (_scenario : MatchesDieselCompressionScenario setup)
    (_figure : MatchesPrimaryCompressionFigure setup)
    (_data : MatchesCompressionProblemReadouts setup)
    (_physical : HasPhysicalCompressionParameters setup)
    (_laws : SatisfiesCaloricallyPerfectGasCompressionLaws setup) :
    energyInJoules setup.workDoneByGas =
      energyInJoules setup.heatTransferredToGas -
        setup.amountOfAirMoles * (104 / 5 : ℝ) *
          (temperatureInKelvins
              (setup.temperature .maximumCompression) -
            temperatureInKelvins (setup.temperature .initial)) := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0472
