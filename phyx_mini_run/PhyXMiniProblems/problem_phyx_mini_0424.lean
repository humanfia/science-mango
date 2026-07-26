import Mathlib.Data.Real.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0424

/-!
# Carnot heat engine driving a Carnot refrigerator

The primary raster places a Carnot heat engine between reservoirs at `600 K`
and `300 K`. Heat `Q₁ = 1000 J` enters the engine and heat `Q₂` leaves it.
The engine's work output directly drives a Carnot refrigerator between
reservoirs at `400 K` and `500 K`.

In the raster, `Q₃` is the refrigerator heat rejected to the `500 K` reservoir,
and `Q₄` is the heat absorbed from the `400 K` reservoir. This is the opposite
of the auxiliary prose caption's assignment of those two labels, so the raster
is followed as the primary evidence.

Absolute temperatures use Physlib's dedicated `Temperature` type. Heat and
work use Physlib's unit-independent, dimensionful `DimEnergy`. Real numbers
below are only calibrated readouts in kelvin or joules.
-/

/-! ## Calibrated physical readouts -/

/-- Read a dimensionful energy in coherent SI energy units. -/
def energyReadout (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read heat or work in joules, normalized by the dimensionful one joule. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  energyReadout energy / energyReadout DimEnergy.joule

/--
Read an absolute temperature in kelvin, accounting for the zero-preserving
temperature unit in which the Physlib `Temperature` is stored.
-/
def temperatureInKelvins
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-! ## Devices, reservoirs, and labels in the primary figure -/

/-- The two thermodynamic devices connected by the horizontal work shaft. -/
inductive Device where
  | engine
  | refrigerator
  deriving DecidableEq, Fintype, Repr

/-- The operating role written next to each device in the figure. -/
inductive DeviceMode where
  | heatEngine
  | refrigerator
  deriving DecidableEq, Repr

/-- Whether a device is the reversible Carnot idealization stated in the problem. -/
inductive CycleIdealization where
  | Carnot
  | other
  deriving DecidableEq, Repr

/-- The left and right device positions in the supplied diagram. -/
inductive DevicePosition where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- The four reservoirs attached to the two devices. -/
inductive ThermalReservoir where
  | engineHot
  | engineCold
  | refrigeratorHot
  | refrigeratorCold
  deriving DecidableEq, Fintype, Repr

/-- The four geometric reservoir positions visible in the diagram. -/
inductive ReservoirPosition where
  | upperLeft
  | lowerLeft
  | upperRight
  | lowerRight
  deriving DecidableEq, Fintype, Repr

/-- Heat-transfer symbols printed next to the four vertical arrows. -/
inductive HeatLabel where
  | Q1
  | Q2
  | Q3
  | Q4
  deriving DecidableEq, Fintype, Repr

/-- Work-transfer symbols printed on the horizontal connection. -/
inductive WorkLabel where
  | Wout
  | Win
  deriving DecidableEq, Fintype, Repr

/-- Physical direction and role of each heat arrow in the primary raster. -/
inductive HeatArrowRole where
  | hotReservoirIntoEngine
  | engineIntoColdReservoir
  | refrigeratorIntoHotReservoir
  | coldReservoirIntoRefrigerator
  deriving DecidableEq, Repr

/-- The heat-arrow roles associated with the four printed symbols. -/
def expectedHeatArrowRole : HeatLabel → HeatArrowRole
  | .Q1 => .hotReservoirIntoEngine
  | .Q2 => .engineIntoColdReservoir
  | .Q3 => .refrigeratorIntoHotReservoir
  | .Q4 => .coldReservoirIntoRefrigerator

/-- Physical role of each work label on the shared horizontal shaft. -/
inductive WorkArrowRole where
  | outputFromEngine
  | inputToRefrigerator
  deriving DecidableEq, Repr

/-- The work-arrow roles associated with the two printed symbols. -/
def expectedWorkArrowRole : WorkLabel → WorkArrowRole
  | .Wout => .outputFromEngine
  | .Win => .inputToRefrigerator

/--
Qualitative information displayed by the supplied raster. Numerical
temperatures and energy readouts are related to the setup separately in
`MatchesSuppliedFigure`.
-/
structure CoupledCarnotFigure where
  deviceAt : DevicePosition → Device
  reservoirAt : ReservoirPosition → ThermalReservoir
  shownDeviceMode : Device → DeviceMode
  heatLabelShown : HeatLabel → Bool
  workLabelShown : WorkLabel → Bool
  reservoirTemperatureLabelShown : ThermalReservoir → Bool
  heatArrowRole : HeatLabel → HeatArrowRole
  workArrowRole : WorkLabel → WorkArrowRole
  horizontalWorkConnectionShown : Bool

/-! ## Independent physical quantities in the coupled system -/

/--
The physical observables of the two devices. Heat and work fields are
independent dimensionful magnitudes; none is defined from the requested answer.
-/
structure CoupledCarnotSetup where
  deviceMode : Device → DeviceMode
  cycleIdealization : Device → CycleIdealization
  reservoirTemperature : ThermalReservoir → Temperature
  temperatureStorageUnit : TemperatureUnit
  heatMagnitude : HeatLabel → DimEnergy
  workMagnitude : WorkLabel → DimEnergy
  workShaftDirectlyCoupled : Bool
  figure : CoupledCarnotFigure

/-- Joule readout of one of the four labelled heat-transfer magnitudes. -/
def heatInJoules (setup : CoupledCarnotSetup) (label : HeatLabel) : ℝ :=
  energyInJoules (setup.heatMagnitude label)

/-- Joule readout of one of the two labelled work-transfer magnitudes. -/
def workInJoules (setup : CoupledCarnotSetup) (label : WorkLabel) : ℝ :=
  energyInJoules (setup.workMagnitude label)

/-- Kelvin readout of a labelled reservoir's absolute temperature. -/
def reservoirTemperatureInKelvins
    (setup : CoupledCarnotSetup) (reservoir : ThermalReservoir) : ℝ :=
  temperatureInKelvins setup.temperatureStorageUnit
    (setup.reservoirTemperature reservoir)

/-! ## Assumptions: scenario, figure data, and governing physics -/

/--
The prose-level scenario: a Carnot heat engine directly drives a Carnot
refrigerator. Quantitative energy and reversibility laws are stated separately.
-/
structure MatchesCoupledCarnotScenario (setup : CoupledCarnotSetup) : Prop where
  engineOperatesAsHeatEngine :
    setup.deviceMode .engine = .heatEngine
  refrigeratorOperatesAsRefrigerator :
    setup.deviceMode .refrigerator = .refrigerator
  engineUsesCarnotCycle :
    setup.cycleIdealization .engine = .Carnot
  refrigeratorUsesCarnotCycle :
    setup.cycleIdealization .refrigerator = .Carnot
  directWorkShaftCoupling :
    setup.workShaftDirectlyCoupled = true

/--
Facts read from the primary image. They include positions, arrows, the four
reservoir temperatures, and `Q₁ = 1000 J`, but no numerical value for `Q₃`,
`Q₄`, or either work transfer.
-/
structure MatchesSuppliedFigure (setup : CoupledCarnotSetup) : Prop where
  leftDeviceIsEngine :
    setup.figure.deviceAt .left = .engine
  rightDeviceIsRefrigerator :
    setup.figure.deviceAt .right = .refrigerator
  upperLeftReservoir :
    setup.figure.reservoirAt .upperLeft = .engineHot
  lowerLeftReservoir :
    setup.figure.reservoirAt .lowerLeft = .engineCold
  upperRightReservoir :
    setup.figure.reservoirAt .upperRight = .refrigeratorHot
  lowerRightReservoir :
    setup.figure.reservoirAt .lowerRight = .refrigeratorCold
  displayedModesMatchDevices : ∀ device,
    setup.figure.shownDeviceMode device = setup.deviceMode device
  everyHeatLabelShown : ∀ label,
    setup.figure.heatLabelShown label = true
  everyWorkLabelShown : ∀ label,
    setup.figure.workLabelShown label = true
  everyReservoirTemperatureShown : ∀ reservoir,
    setup.figure.reservoirTemperatureLabelShown reservoir = true
  displayedHeatArrowRoles : ∀ label,
    setup.figure.heatArrowRole label = expectedHeatArrowRole label
  displayedWorkArrowRoles : ∀ label,
    setup.figure.workArrowRole label = expectedWorkArrowRole label
  horizontalWorkConnectionShown :
    setup.figure.horizontalWorkConnectionShown = true
  temperatureUnitIsKelvin :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin
  engineHotTemperature :
    reservoirTemperatureInKelvins setup .engineHot = 600
  engineColdTemperature :
    reservoirTemperatureInKelvins setup .engineCold = 300
  refrigeratorHotTemperature :
    reservoirTemperatureInKelvins setup .refrigeratorHot = 500
  refrigeratorColdTemperature :
    reservoirTemperatureInKelvins setup .refrigeratorCold = 400
  inputHeatQ1 :
    heatInJoules setup .Q1 = 1000

/-- Positivity conditions for the directed heat and work magnitudes. -/
structure HasPhysicalMagnitudes (setup : CoupledCarnotSetup) : Prop where
  reservoirTemperaturePositive : ∀ reservoir,
    0 < reservoirTemperatureInKelvins setup reservoir
  heatMagnitudePositive : ∀ label,
    0 < heatInJoules setup label
  workMagnitudePositive : ∀ label,
    0 < workInJoules setup label

/--
Governing relations for the ideal coupled devices:

* the engine obeys `Q₁ = Q₂ + W_out`;
* reversibility gives `Q₁ / T_engine,hot = Q₂ / T_engine,cold`;
* the refrigerator obeys `Q₃ = Q₄ + W_in`;
* reversibility gives
  `Q₃ / T_refrigerator,hot = Q₄ / T_refrigerator,cold`; and
* the lossless direct shaft gives `W_out = W_in`.

The reversible heat ratios are written without division as cross-products of
kelvin and joule readouts. None of these general laws contains the requested
numerical value of `Q₃`.
-/
structure SatisfiesCoupledCarnotLaws (setup : CoupledCarnotSetup) : Prop where
  engineFirstLaw :
    heatInJoules setup .Q1 =
      heatInJoules setup .Q2 + workInJoules setup .Wout
  engineCarnotHeatRatio :
    reservoirTemperatureInKelvins setup .engineCold *
        heatInJoules setup .Q1 =
      reservoirTemperatureInKelvins setup .engineHot *
        heatInJoules setup .Q2
  refrigeratorFirstLaw :
    heatInJoules setup .Q3 =
      heatInJoules setup .Q4 + workInJoules setup .Win
  refrigeratorCarnotHeatRatio :
    reservoirTemperatureInKelvins setup .refrigeratorCold *
        heatInJoules setup .Q3 =
      reservoirTemperatureInKelvins setup .refrigeratorHot *
        heatInJoules setup .Q4
  losslessWorkTransfer :
    workInJoules setup .Wout = workInJoules setup .Win

/-! ## Displayed answers and target -/

/-- The four answer labels supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The candidate `Q₃` magnitudes printed beside the answer labels, in joules. -/
def displayedQ3InJoules : AnswerChoice → ℝ
  | .A => 1000
  | .B => 1500
  | .C => 2000
  | .D => 2500

/-- The source dataset records answer label D; this metadata is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/--
The heat engine supplies `500 J` of work. A Carnot refrigerator operating
between `400 K` and `500 K` then absorbs `2000 J` as `Q₄` and rejects
`2500 J` as `Q₃`.

Blueprint: `thm:physics:phyx_mini_0424:target`.
-/
theorem q3_for_coupled_carnot_engine_and_refrigerator
    (setup : CoupledCarnotSetup)
    (hScenario : MatchesCoupledCarnotScenario setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hPhysical : HasPhysicalMagnitudes setup)
    (hLaws : SatisfiesCoupledCarnotLaws setup) :
    heatInJoules setup .Q3 = 2500 := by
  have hQ2 : heatInJoules setup .Q2 = 500 := by
    have hEngineRatio := hLaws.engineCarnotHeatRatio
    rw [hFigure.engineColdTemperature, hFigure.inputHeatQ1,
      hFigure.engineHotTemperature] at hEngineRatio
    linarith
  have hWout : workInJoules setup .Wout = 500 := by
    linarith [hLaws.engineFirstLaw, hFigure.inputHeatQ1]
  have hWin : workInJoules setup .Win = 500 := by
    linarith [hLaws.losslessWorkTransfer]
  have hRefrigeratorRatio := hLaws.refrigeratorCarnotHeatRatio
  rw [hFigure.refrigeratorColdTemperature,
    hFigure.refrigeratorHotTemperature] at hRefrigeratorRatio
  linarith [hLaws.refrigeratorFirstLaw]

end PhyXMiniProblems.ProblemPhyXMini0424
