import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0955

open Dimension

/-!
# Muon mass from a Thomson-apparatus `E²`-versus-`V` graph

The experiment accelerates initially stationary negative muons through a
potential difference `V`. Crossed electric and magnetic fields are then
adjusted until the beam has zero deflection. The primary raster `955.png`
plots the measured squared electric-field magnitude against accelerating
potential. Its anchor points include `(100, 200)`, `(200, 400)`,
`(300, 600)`, and `(400, 800)`, where the vertical coordinates are in units
of `10⁸ V²/m²`. Thus the displayed physical slope is
`2 * 10⁸ (V/m)²/V`.

Physical scalar magnitudes use Physlib's unit-independent `Dimensionful`
quantities. Real numbers occur only at explicitly named coherent-SI readout
boundaries or as literal coordinates printed in the graph.

Assumption/target split:

* governing laws: work by the accelerating potential equals the change in
  kinetic energy, zero transverse deflection gives `E = v B`, and the plotted
  `E²` observable is the square of the measured electric-field magnitude;
* previous-part results: none;
* scenario and figure readouts: negative muons have the electron's charge,
  the initial speed is zero, `B = 0.340 T`, the elementary-charge
  calibration, the graph axes/ticks/colors, and the four anchor points;
* current target: the independently stored muon mass agrees, to the displayed
  precision, with choice `B`, `1.85 * 10⁻²⁸ kg`.

No premise states the requested mass or the combined mass formula.
-/

/-! ## Dimensions, physical quantities, and coherent-SI readouts -/

/-- A speed has physical dimension `L T⁻¹`. -/
def speedDimension : Dimension :=
  L𝓭 * T𝓭⁻¹

/-- Electric potential has physical dimension `M L² T⁻² C⁻¹`. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Electric-field magnitude has dimension `M L T⁻² C⁻¹` (volts per metre). -/
def electricFieldDimension : Dimension :=
  electricPotentialDimension * L𝓭⁻¹

/-- Magnetic flux density has dimension `M T⁻¹ C⁻¹` (tesla). -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- The vertical graph variable has the squared electric-field dimension. -/
def electricFieldSquaredDimension : Dimension :=
  electricFieldDimension * electricFieldDimension

/-- A nonnegative, unit-independent particle mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent electric-charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative, unit-independent speed magnitude. -/
abbrev SpeedMagnitudeQuantity : Type :=
  Dimensionful (WithDim speedDimension NNReal)

/-- A nonnegative, unit-independent accelerating-potential magnitude. -/
abbrev ElectricPotentialMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension NNReal)

/-- A nonnegative, unit-independent electric-field magnitude. -/
abbrev ElectricFieldMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricFieldDimension NNReal)

/-- A nonnegative, unit-independent squared electric-field magnitude. -/
abbrev ElectricFieldSquaredMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricFieldSquaredDimension NNReal)

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitudeQuantity : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- Coherent-SI readout of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a mass in coherent-SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Read a charge magnitude in coherent-SI coulombs. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout charge

/-- Read a speed magnitude in coherent-SI metres per second. -/
def speedInMetersPerSecond (speed : SpeedMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout speed

/-- Read an accelerating potential in coherent-SI volts. -/
def electricPotentialInVolts
    (potential : ElectricPotentialMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout potential

/-- Read an electric-field magnitude in coherent-SI volts per metre. -/
def electricFieldInVoltsPerMeter
    (field : ElectricFieldMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout field

/-- Read squared electric field in coherent-SI volts squared per metre squared. -/
def electricFieldSquaredInVoltsSquaredPerMeterSquared
    (fieldSquared : ElectricFieldSquaredMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout fieldSquared

/-- Read magnetic flux density in coherent-SI teslas. -/
def magneticFluxDensityInTeslas
    (field : MagneticFluxDensityMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout field

/-! ## Apparatus roles and literal primary-figure content -/

/-- Particle species distinguished by the scenario. -/
inductive ParticleSpecies where
  | negativeMuon
  | electron
  | other
  deriving DecidableEq, Repr

/-- The sign of a particle's electric charge. -/
inductive ChargeSign where
  | negative
  | positive
  | neutral
  deriving DecidableEq, Repr

/-- The two charged plates of the modern Thomson apparatus. -/
inductive DeflectionPlate where
  | first
  | second
  deriving DecidableEq, Fintype, Repr

/-- Horizontal and vertical axes in the supplied graph. -/
inductive GraphAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical quantities printed as the two graph-axis labels. -/
inductive PlottedQuantity where
  | acceleratingPotentialV
  | electricFieldSquared
  deriving DecidableEq, Repr

/-- Four exact anchor points readable from the straight-line data plot. -/
inductive GraphAnchor where
  | at100Volts
  | at200Volts
  | at300Volts
  | at400Volts
  deriving DecidableEq, Fintype, Repr

/-!
Literal presentation and coordinate information from image `955.png`.
Vertical coordinates are numbers in the printed scale
`10⁸ V²/m²`; they are not bare electric-field quantities.
-/
structure ESquaredVersusVoltageGraph where
  axisQuantity : GraphAxis → PlottedQuantity
  potentialTickShown : ℝ → Bool
  electricFieldSquaredTickShown : ℝ → Bool
  anchorPointShown : GraphAnchor → Bool
  potentialCoordinateVolts : GraphAnchor → ℝ
  electricFieldSquaredCoordinateInHundredMillions : GraphAnchor → ℝ
  dataPointsAreBlack : Bool
  connectingLineIsMagenta : Bool
  displayedTrendIsLinear : Bool
  horizontalAxisUnitIsVolts : Bool
  verticalAxisUnitIsHundredMillionVoltsSquaredPerMeterSquared : Bool

/-!
Independent physical data in the apparatus and at each plotted measurement.
In particular, `muonMass` is not defined in terms of the answer or the graph.
-/
structure MuonThomsonExperiment where
  unitSystem : UnitChoices
  particleSpecies : ParticleSpecies
  muonChargeSign : ChargeSign
  electronChargeSign : ChargeSign
  chargedPlateShown : DeflectionPlate → Bool
  magneticFieldIsBetweenChargedPlates : Bool
  muonMass : MassQuantity
  muonChargeMagnitude : ChargeMagnitudeQuantity
  electronChargeMagnitude : ChargeMagnitudeQuantity
  magneticFluxDensity : MagneticFluxDensityMagnitudeQuantity
  initialSpeed : SpeedMagnitudeQuantity
  acceleratingPotentialAt : GraphAnchor → ElectricPotentialMagnitudeQuantity
  electricFieldMagnitudeAt : GraphAnchor → ElectricFieldMagnitudeQuantity
  electricFieldSquaredAt :
    GraphAnchor → ElectricFieldSquaredMagnitudeQuantity
  selectedSpeedAt : GraphAnchor → SpeedMagnitudeQuantity
  graph : ESquaredVersusVoltageGraph

/-! ## Scenario, graph readouts, calibration data, and governing laws -/

/-!
Problem prose and literal content of the primary graph. The four dimensionful
observables are tied to the scalar graph coordinates at the SI-readout
boundary. This predicate contains no muon-mass value.
-/
structure MatchesScenarioAndGraphReadouts
    (experiment : MuonThomsonExperiment) : Prop where
  usesSIUnits : experiment.unitSystem = UnitChoices.SI
  beamParticlesAreNegativeMuons :
    experiment.particleSpecies = .negativeMuon
  muonChargeIsNegative : experiment.muonChargeSign = .negative
  electronChargeIsNegative : experiment.electronChargeSign = .negative
  muonHasElectronChargeMagnitude :
    chargeMagnitudeInCoulombs experiment.muonChargeMagnitude =
      chargeMagnitudeInCoulombs experiment.electronChargeMagnitude
  bothChargedPlatesShown :
    ∀ plate, experiment.chargedPlateShown plate = true
  magneticFieldBetweenPlates :
    experiment.magneticFieldIsBetweenChargedPlates = true
  magneticFieldReadout :
    magneticFluxDensityInTeslas experiment.magneticFluxDensity = 34 / 100
  initialSpeedIsZero :
    speedInMetersPerSecond experiment.initialSpeed = 0
  horizontalAxisLabel :
    experiment.graph.axisQuantity .horizontal = .acceleratingPotentialV
  verticalAxisLabel :
    experiment.graph.axisQuantity .vertical = .electricFieldSquared
  horizontalAxisUsesVolts :
    experiment.graph.horizontalAxisUnitIsVolts = true
  verticalAxisUsesPrintedScale :
    experiment.graph.verticalAxisUnitIsHundredMillionVoltsSquaredPerMeterSquared =
      true
  horizontalTicks :
    experiment.graph.potentialTickShown 0 = true ∧
      experiment.graph.potentialTickShown 100 = true ∧
      experiment.graph.potentialTickShown 200 = true ∧
      experiment.graph.potentialTickShown 300 = true ∧
      experiment.graph.potentialTickShown 400 = true
  verticalTicks :
    experiment.graph.electricFieldSquaredTickShown 0 = true ∧
      experiment.graph.electricFieldSquaredTickShown 200 = true ∧
      experiment.graph.electricFieldSquaredTickShown 400 = true ∧
      experiment.graph.electricFieldSquaredTickShown 600 = true ∧
      experiment.graph.electricFieldSquaredTickShown 800 = true
  allAnchorPointsShown :
    ∀ point, experiment.graph.anchorPointShown point = true
  anchor100Coordinates :
    experiment.graph.potentialCoordinateVolts .at100Volts = 100 ∧
      experiment.graph.electricFieldSquaredCoordinateInHundredMillions
          .at100Volts = 200
  anchor200Coordinates :
    experiment.graph.potentialCoordinateVolts .at200Volts = 200 ∧
      experiment.graph.electricFieldSquaredCoordinateInHundredMillions
          .at200Volts = 400
  anchor300Coordinates :
    experiment.graph.potentialCoordinateVolts .at300Volts = 300 ∧
      experiment.graph.electricFieldSquaredCoordinateInHundredMillions
          .at300Volts = 600
  anchor400Coordinates :
    experiment.graph.potentialCoordinateVolts .at400Volts = 400 ∧
      experiment.graph.electricFieldSquaredCoordinateInHundredMillions
          .at400Volts = 800
  dimensionfulPotentialMatchesGraph :
    ∀ point,
      electricPotentialInVolts (experiment.acceleratingPotentialAt point) =
        experiment.graph.potentialCoordinateVolts point
  dimensionfulElectricFieldSquaredMatchesGraph :
    ∀ point,
      electricFieldSquaredInVoltsSquaredPerMeterSquared
          (experiment.electricFieldSquaredAt point) =
        experiment.graph.electricFieldSquaredCoordinateInHundredMillions point *
          10 ^ (8 : ℕ)
  blackDataPoints : experiment.graph.dataPointsAreBlack = true
  magentaConnectingLine : experiment.graph.connectingLineIsMagenta = true
  linearTrend : experiment.graph.displayedTrendIsLinear = true

/-!
Exact SI calibration of the elementary charge magnitude. This is independent
external data, not a premise about the muon's requested mass.
-/
structure HasElementaryChargeCalibration
    (experiment : MuonThomsonExperiment) : Prop where
  electronChargeReadout :
    chargeMagnitudeInCoulombs experiment.electronChargeMagnitude =
      1602176634 / 10 ^ (28 : ℕ)

/-!
The three modeling laws used in the calculation. Acceleration from the common
initial speed is stated before substituting the zero-speed readout. The
zero-deflection relation is the magnitude form of electric/magnetic Lorentz
force balance. No field of this structure states the resulting mass formula.
-/
structure SatisfiesMuonThomsonLaws
    (experiment : MuonThomsonExperiment) : Prop where
  acceleratingPotentialEnergy :
    ∀ point,
      chargeMagnitudeInCoulombs experiment.muonChargeMagnitude *
          electricPotentialInVolts
            (experiment.acceleratingPotentialAt point) =
        ((1 : ℝ) / 2) * massInKilograms experiment.muonMass *
          (speedInMetersPerSecond (experiment.selectedSpeedAt point) ^ 2 -
            speedInMetersPerSecond experiment.initialSpeed ^ 2)
  zeroDeflectionForceBalance :
    ∀ point,
      electricFieldInVoltsPerMeter
          (experiment.electricFieldMagnitudeAt point) =
        speedInMetersPerSecond (experiment.selectedSpeedAt point) *
          magneticFluxDensityInTeslas experiment.magneticFluxDensity
  plottedSquareIsMeasuredFieldSquare :
    ∀ point,
      electricFieldSquaredInVoltsSquaredPerMeterSquared
          (experiment.electricFieldSquaredAt point) =
        electricFieldInVoltsPerMeter
            (experiment.electricFieldMagnitudeAt point) ^ 2

/-- Positivity and nondegeneracy conditions for the measured run. -/
structure HasNondegenerateMuonRun
    (experiment : MuonThomsonExperiment) : Prop where
  muonMassPositive : 0 < massInKilograms experiment.muonMass
  chargeMagnitudePositive :
    0 < chargeMagnitudeInCoulombs experiment.muonChargeMagnitude
  magneticFieldPositive :
    0 < magneticFluxDensityInTeslas experiment.magneticFluxDensity
  potentialPositive :
    ∀ point,
      0 < electricPotentialInVolts
        (experiment.acceleratingPotentialAt point)
  selectedSpeedPositive :
    ∀ point,
      0 < speedInMetersPerSecond (experiment.selectedSpeedAt point)
  electricFieldPositive :
    ∀ point,
      0 < electricFieldInVoltsPerMeter
        (experiment.electricFieldMagnitudeAt point)

/-! ## Displayed answer choices and formal target -/

/-- The four mass choices printed in the problem statement. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Numerical value in kilograms printed beside each answer choice. -/
def answerChoiceMassInKilograms : AnswerChoice → ℝ
  | .A => 163 / 10 ^ (30 : ℕ)
  | .B => 185 / 10 ^ (30 : ℕ)
  | .C => 225 / 10 ^ (30 : ℕ)
  | .D => 911 / 10 ^ (33 : ℕ)

/-- Generic agreement with a displayed value within a positive half-unit. -/
def AgreesToDisplayedPrecision
    (actual displayed halfUnit : ℝ) : Prop :=
  |actual - displayed| < halfUnit

/-!
The Thomson laws and graph data determine a mass that rounds to
`1.85 * 10⁻²⁸ kg`, the value printed as choice `B`.
-/
theorem muonMass_agrees_with_choice_B
    (experiment : MuonThomsonExperiment)
    (hReadouts : MatchesScenarioAndGraphReadouts experiment)
    (hCalibration : HasElementaryChargeCalibration experiment)
    (hLaws : SatisfiesMuonThomsonLaws experiment)
    (hPhysical : HasNondegenerateMuonRun experiment) :
    AgreesToDisplayedPrecision
      (massInKilograms experiment.muonMass)
      (answerChoiceMassInKilograms .B)
      (5 / 10 ^ (31 : ℕ)) := by
  have hV :=
    hReadouts.dimensionfulPotentialMatchesGraph .at100Volts
  rw [hReadouts.anchor100Coordinates.1] at hV
  have hE2 :=
    hReadouts.dimensionfulElectricFieldSquaredMatchesGraph .at100Volts
  rw [hReadouts.anchor100Coordinates.2] at hE2
  have henergy :=
    hLaws.acceleratingPotentialEnergy .at100Volts
  have hforce :=
    hLaws.zeroDeflectionForceBalance .at100Volts
  have hsquare :=
    hLaws.plottedSquareIsMeasuredFieldSquare .at100Volts
  norm_num [hReadouts.muonHasElectronChargeMagnitude,
    hCalibration.electronChargeReadout, hV, hReadouts.initialSpeedIsZero,
    hReadouts.magneticFieldReadout, hE2, hforce] at henergy hsquare
  have hv2 :
      speedInMetersPerSecond (experiment.selectedSpeedAt .at100Volts) ^ 2 =
        (50000000000000 : ℝ) / 289 := by
    nlinarith [hsquare]
  rw [hv2] at henergy
  norm_num [AgreesToDisplayedPrecision, answerChoiceMassInKilograms]
  rw [abs_lt]
  constructor <;> linarith [henergy]

end PhyXMiniProblems.ProblemPhyXMini0955
