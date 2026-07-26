import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0464

open Dimension

/-!
# Heating R-410a in a piston-cylinder until the piston reaches stops

A vertical piston-cylinder contains `5 kg` of R-410a at `10 °C`. Heat first
raises the piston against a constant load. The piston then meets upper stops
when the volume is twice its initial value. Further heating occurs at fixed
volume until the refrigerant reaches `50 °C` and `1.4 MPa`.

The physical quantities below carry their dimensions through Physlib. Real
numbers are used only for calibrated readings in named units, qualitative
figure coordinates, and the displayed multiple-choice values. In particular,
the overall heat transfer is an independent observable and is not defined to
be the recorded `725.0 kJ` answer.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- The physical dimension of volume, `L³`. -/
def volumeDimension : Dimension := L𝓭 * L𝓭 * L𝓭

/-- The physical dimension of specific volume, `L³ M⁻¹`. -/
def specificVolumeDimension : Dimension := volumeDimension * M𝓭⁻¹

/-- The physical dimension of specific internal energy, `L² T⁻²`. -/
def specificEnergyDimension : Dimension :=
  L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical volume. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim volumeDimension NNReal)

/-- A nonnegative specific volume. -/
abbrev SpecificVolumeQuantity : Type :=
  Dimensionful (WithDim specificVolumeDimension NNReal)

/-!
Specific internal energy has a conventional reference zero, so its coherent
SI reading is real-valued rather than restricted to a nonnegative scalar.
-/
abbrev SpecificInternalEnergyQuantity : Type :=
  Dimensionful (WithDim specificEnergyDimension ℝ)

/-- Read a physical mass in coherent SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical volume in coherent SI cubic metres. -/
def volumeInCubicMetres (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a specific volume in cubic metres per kilogram. -/
def specificVolumeInCubicMetresPerKilogram
    (specificVolume : SpecificVolumeQuantity) : ℝ :=
  ((specificVolume UnitChoices.SI).val : ℝ)

/-- Read a pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a pressure in kilopascals. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Read a pressure in megapascals. -/
def pressureInMegapascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000000

/-- Read an energy in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read an energy in kilojoules. -/
def energyInKilojoules (energy : DimEnergy) : ℝ :=
  energyInJoules energy / 1000

/-- Read a specific internal energy in joules per kilogram. -/
def specificInternalEnergyInJoulesPerKilogram
    (energy : SpecificInternalEnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read a specific internal energy in kilojoules per kilogram. -/
def specificInternalEnergyInKilojoulesPerKilogram
    (energy : SpecificInternalEnergyQuantity) : ℝ :=
  specificInternalEnergyInJoulesPerKilogram energy / 1000

/-!
Physlib's `Temperature` is an absolute, zero-preserving temperature. The
affine Celsius reading printed in the exercise is retained alongside it with
an explicit kelvin calibration.
-/
structure CelsiusTemperatureReading where
  absoluteKelvinTemperature : Temperature
  degreesCelsius : ℝ
  kelvinCalibration :
    absoluteKelvinTemperature.toReal = degreesCelsius + 27315 / 100

/-! ## Thermodynamic process, apparatus, and figure vocabulary -/

/-- The three states needed to separate the moving- and fixed-piston legs. -/
inductive ProcessState where
  | initial
  | atUpperStops
  | final
  deriving DecidableEq, Fintype, Repr

/-- The two heat-transfer legs of the overall process. -/
inductive ProcessLeg where
  | pistonRise
  | heatingAtStops
  deriving DecidableEq, Fintype, Repr

/-- Initial state of each directed process leg. -/
def ProcessLeg.initialState : ProcessLeg → ProcessState
  | .pistonRise => .initial
  | .heatingAtStops => .atUpperStops

/-- Final state of each directed process leg. -/
def ProcessLeg.finalState : ProcessLeg → ProcessState
  | .pistonRise => .atUpperStops
  | .heatingAtStops => .final

/-- Refrigerant identity, kept distinct from its scalar property readings. -/
inductive RefrigerantKind where
  | r410a
  | other
  deriving DecidableEq, Repr

/-- Qualitative phase region of an equilibrium refrigerant state. -/
inductive PhaseRegion where
  | saturatedLiquidVapor
  | superheatedVapor
  | other
  deriving DecidableEq, Repr

/-- Orientation of the cylinder axis. -/
inductive CylinderOrientation where
  | vertical
  | other
  deriving DecidableEq, Repr

/-- Mechanical constraint acting on the piston at a modeled state. -/
inductive PistonConstraint where
  | freelyRisingUnderConstantLoad
  | touchingUpperStops
  | other
  deriving DecidableEq, Repr

/-- Physical objects visible in the supplied cross-sectional raster. -/
inductive FigureObject where
  | cylinderWalls
  | horizontalPiston
  | upperStopLeft
  | upperStopRight
  | refrigerantRegion
  deriving DecidableEq, Fintype, Repr

/-- Literal text labels visible in the supplied raster. -/
inductive FigureLabel where
  | r410a
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative evidence from the primary image. Coordinates describe only the
vertical ordering in the drawing and carry no thermodynamic measurement.
-/
structure SuppliedPistonCylinderFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  pistonVerticalCoordinate : ℝ
  upperStopsVerticalCoordinate : ℝ
  refrigerantIsBelowPiston : Bool
  pistonIsHorizontal : Bool
  diagramIsVerticalCrossSection : Bool
  hasPrintedNumericalThermodynamicData : Bool

/-- Extensive and specific properties of R-410a at one equilibrium state. -/
structure RefrigerantState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : CelsiusTemperatureReading
  specificVolume : SpecificVolumeQuantity
  specificInternalEnergy : SpecificInternalEnergyQuantity
  phaseRegion : PhaseRegion

/-!
An abstract equilibrium-property table for R-410a. A relation is used rather
than a function because temperature and pressure alone do not select a unique
state on the saturation curve.
-/
structure R410AEquilibriumPropertyTable where
  isAdmissibleState :
    CelsiusTemperatureReading → DimPressure → SpecificVolumeQuantity →
      SpecificInternalEnergyQuantity → PhaseRegion → Prop

/-!
The complete closed-system experiment. Heat and work are signed positive into
the refrigerant and by the refrigerant, respectively. The overall heat is an
independent physical observable; its relation to state changes is imposed only
by the first-law hypotheses below.
-/
structure HeatingPistonCylinderSetup where
  refrigerant : RefrigerantKind
  cylinderOrientation : CylinderOrientation
  pistonConstraintAt : ProcessState → PistonConstraint
  refrigerantMass : MassQuantity
  stateAt : ProcessState → RefrigerantState
  heatTransferredIntoRefrigerant : ProcessLeg → DimEnergy
  boundaryWorkDoneByRefrigerant : ProcessLeg → DimEnergy
  overallHeatTransferIntoRefrigerant : DimEnergy
  propertyTable : R410AEquilibriumPropertyTable
  figure : SuppliedPistonCylinderFigure
  systemIsClosed : Bool
  processIsQuasistatic : Bool
  pistonFrictionIsNegligible : Bool
  kineticEnergyChangeIsNegligible : Bool
  potentialEnergyChangeIsNegligible : Bool

/-! ## Scenario, problem data, figure evidence, and reference properties -/

/-- Qualitative process conditions stated or implied by the piston model. -/
structure MatchesHeatingPistonCylinderScenario
    (setup : HeatingPistonCylinderSetup) : Prop where
  containsR410a : setup.refrigerant = .r410a
  verticalCylinder : setup.cylinderOrientation = .vertical
  initiallyFreeToRise :
    setup.pistonConstraintAt .initial = .freelyRisingUnderConstantLoad
  reachesUpperStops :
    setup.pistonConstraintAt .atUpperStops = .touchingUpperStops
  remainsAtUpperStops :
    setup.pistonConstraintAt .final = .touchingUpperStops
  closedRefrigerantSystem : setup.systemIsClosed = true
  quasistaticPistonMotion : setup.processIsQuasistatic = true
  negligiblePistonFriction : setup.pistonFrictionIsNegligible = true
  negligibleKineticEnergyChange :
    setup.kineticEnergyChangeIsNegligible = true
  negligiblePotentialEnergyChange :
    setup.potentialEnergyChangeIsNegligible = true
  heatAddedOnBothLegs : ∀ leg,
    0 < energyInJoules (setup.heatTransferredIntoRefrigerant leg)

/-!
Numerical readings stated in the prose. No field constrains any heat-transfer
observable or mentions a displayed answer value.
-/
structure MatchesProblemReadouts
    (setup : HeatingPistonCylinderSetup) : Prop where
  refrigerantMassKilograms : massInKilograms setup.refrigerantMass = 5
  initialTemperatureCelsius :
    (setup.stateAt .initial).temperature.degreesCelsius = 10
  volumeDoublesAtStops :
    volumeInCubicMetres (setup.stateAt .atUpperStops).volume =
      2 * volumeInCubicMetres (setup.stateAt .initial).volume
  finalTemperatureCelsius :
    (setup.stateAt .final).temperature.degreesCelsius = 50
  finalPressureMegapascals :
    pressureInMegapascals (setup.stateAt .final).pressure = 14 / 10

/-- Facts transcribed from the primary piston-cylinder image. -/
structure MatchesSuppliedPistonCylinderFigure
    (figure : SuppliedPistonCylinderFigure) : Prop where
  everyNamedObjectIsShown : ∀ object, figure.showsObject object = true
  refrigerantLabelIsShown : figure.showsLabel .r410a = true
  refrigerantBelowPiston : figure.refrigerantIsBelowPiston = true
  horizontalPiston : figure.pistonIsHorizontal = true
  stopsAreAbovePiston :
    figure.pistonVerticalCoordinate < figure.upperStopsVerticalCoordinate
  verticalCrossSection : figure.diagramIsVerticalCrossSection = true
  noPrintedNumericalData :
    figure.hasPrintedNumericalThermodynamicData = false

/-!
Representative equilibrium-property readings needed to make the numerical
question determinate. These are constitutive R-410a data at the initial and
final states, not heat-transfer data. The values are retained at sufficient
precision for identifying the multiple-choice result despite table rounding.
-/
structure MatchesReferenceR410APropertyData
    (setup : HeatingPistonCylinderSetup) : Prop where
  initialStateIsSaturatedMixture :
    (setup.stateAt .initial).phaseRegion = .saturatedLiquidVapor
  initialPressureKilopascals :
    pressureInKilopascals (setup.stateAt .initial).pressure = 54287 / 50
  initialSpecificInternalEnergyKilojoulesPerKilogram :
    specificInternalEnergyInKilojoulesPerKilogram
        (setup.stateAt .initial).specificInternalEnergy = 297531 / 1000
  finalStateIsSuperheatedVapor :
    (setup.stateAt .final).phaseRegion = .superheatedVapor
  finalSpecificVolumeCubicMetresPerKilogram :
    specificVolumeInCubicMetresPerKilogram
        (setup.stateAt .final).specificVolume = 225243 / 10000000
  finalSpecificInternalEnergyKilojoulesPerKilogram :
    specificInternalEnergyInKilojoulesPerKilogram
        (setup.stateAt .final).specificInternalEnergy = 430256 / 1000

/-- Positivity and nondegeneracy conditions selecting physical states. -/
structure HasPhysicalHeatingPistonParameters
    (setup : HeatingPistonCylinderSetup) : Prop where
  refrigerantMassPositive : 0 < massInKilograms setup.refrigerantMass
  pressurePositive : ∀ state,
    0 < pressureInPascals (setup.stateAt state).pressure
  volumePositive : ∀ state,
    0 < volumeInCubicMetres (setup.stateAt state).volume
  specificVolumePositive : ∀ state,
    0 < specificVolumeInCubicMetresPerKilogram
      (setup.stateAt state).specificVolume
  absoluteTemperaturePositive : ∀ state,
    0 < (setup.stateAt state).temperature.absoluteKelvinTemperature.toReal

/-! ## Governing property, boundary-work, and first-law assumptions -/

/-!
Each modeled state is admitted by the R-410a equilibrium table, and total
volume equals mass times specific volume in coherent SI units.
-/
structure SatisfiesR410AEquilibriumPropertyModel
    (setup : HeatingPistonCylinderSetup) : Prop where
  stateIsAdmissible : ∀ state,
    setup.propertyTable.isAdmissibleState
      (setup.stateAt state).temperature
      (setup.stateAt state).pressure
      (setup.stateAt state).specificVolume
      (setup.stateAt state).specificInternalEnergy
      (setup.stateAt state).phaseRegion
  extensiveVolumeLaw : ∀ state,
    volumeInCubicMetres (setup.stateAt state).volume =
      massInKilograms setup.refrigerantMass *
        specificVolumeInCubicMetresPerKilogram
          (setup.stateAt state).specificVolume

/-!
Mechanical process laws. The freely moving piston produces a constant-
pressure first leg; after the piston reaches the stops the volume is fixed.
For the first leg, `kPa * m³ = kJ`, while the fixed-volume leg does no boundary
work.
-/
structure SatisfiesPistonBoundaryWorkLaws
    (setup : HeatingPistonCylinderSetup) : Prop where
  constantPressureDuringRise :
    (setup.stateAt .atUpperStops).pressure =
      (setup.stateAt .initial).pressure
  volumeFixedAfterReachingStops :
    (setup.stateAt .final).volume =
      (setup.stateAt .atUpperStops).volume
  riseBoundaryWork :
    energyInKilojoules (setup.boundaryWorkDoneByRefrigerant .pistonRise) =
      pressureInKilopascals (setup.stateAt .initial).pressure *
        (volumeInCubicMetres (setup.stateAt .atUpperStops).volume -
          volumeInCubicMetres (setup.stateAt .initial).volume)
  stoppedPistonDoesNoBoundaryWork :
    energyInKilojoules
        (setup.boundaryWorkDoneByRefrigerant .heatingAtStops) = 0

/-!
Closed-system first law on each leg,

`Q_in = m (u_final - u_initial) + W_by`,

together with additivity of heat over the two legs. This is a governing law;
it contains no numerical value for the requested overall heat.
-/
structure SatisfiesClosedSystemFirstLaw
    (setup : HeatingPistonCylinderSetup) : Prop where
  firstLawOnEachLeg : ∀ leg,
    energyInKilojoules (setup.heatTransferredIntoRefrigerant leg) =
      massInKilograms setup.refrigerantMass *
          (specificInternalEnergyInKilojoulesPerKilogram
              (setup.stateAt leg.finalState).specificInternalEnergy -
            specificInternalEnergyInKilojoulesPerKilogram
              (setup.stateAt leg.initialState).specificInternalEnergy) +
        energyInKilojoules (setup.boundaryWorkDoneByRefrigerant leg)
  overallHeatIsLegSum :
    energyInKilojoules setup.overallHeatTransferIntoRefrigerant =
      energyInKilojoules
          (setup.heatTransferredIntoRefrigerant .pistonRise) +
        energyInKilojoules
          (setup.heatTransferredIntoRefrigerant .heatingAtStops)

/-! ## Displayed choices and current target -/

/-- Labels of the four heat-transfer answers printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Heat-transfer value in kilojoules printed beside each answer label. -/
def displayedHeatTransferKilojoules : AnswerChoice → ℝ
  | .A => 5183 / 10
  | .B => 4203 / 5
  | .C => 1307 / 2
  | .D => 725

/-- Answer label recorded by the source dataset, retained as metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
Agreement within `1 kJ` accommodates the rounding variation between standard
R-410a property correlations while remaining tiny compared with the gaps
between answer choices.
-/
def AgreesWithDisplayedHeatWithinOneKilojoule
    (setup : HeatingPistonCylinderSetup) (choice : AnswerChoice) : Prop :=
  |energyInKilojoules setup.overallHeatTransferIntoRefrigerant -
      displayedHeatTransferKilojoules choice| < 1

/-- The chosen displayed heat is strictly closer than every alternative. -/
def IsUniqueClosestDisplayedHeat
    (setup : HeatingPistonCylinderSetup) (chosen : AnswerChoice) : Prop :=
  ∀ other, other ≠ chosen →
    |energyInKilojoules setup.overallHeatTransferIntoRefrigerant -
        displayedHeatTransferKilojoules chosen| <
      |energyInKilojoules setup.overallHeatTransferIntoRefrigerant -
        displayedHeatTransferKilojoules other|

/-!
The endpoint property data, volume doubling, constant-pressure boundary work,
fixed-volume second leg, and closed-system first law give an overall heat near
`725.0 kJ`, uniquely selecting answer D.

This formalizes blueprint label `thm:physics:phyx_mini_0464:target`.
-/
theorem problem_phyx_mini_0464
    (setup : HeatingPistonCylinderSetup)
    (_scenario : MatchesHeatingPistonCylinderScenario setup)
    (_readouts : MatchesProblemReadouts setup)
    (_figure : MatchesSuppliedPistonCylinderFigure setup.figure)
    (_referenceData : MatchesReferenceR410APropertyData setup)
    (_physical : HasPhysicalHeatingPistonParameters setup)
    (_propertyModel : SatisfiesR410AEquilibriumPropertyModel setup)
    (_workLaws : SatisfiesPistonBoundaryWorkLaws setup)
    (_firstLaw : SatisfiesClosedSystemFirstLaw setup) :
    AgreesWithDisplayedHeatWithinOneKilojoule setup .D ∧
      IsUniqueClosestDisplayedHeat setup .D := by
  have hFinalVolume :
      volumeInCubicMetres (setup.stateAt .final).volume =
        225243 / 2000000 := by
    rw [_propertyModel.extensiveVolumeLaw .final,
      _readouts.refrigerantMassKilograms,
      _referenceData.finalSpecificVolumeCubicMetresPerKilogram]
    norm_num
  have hStopsVolume :
      volumeInCubicMetres (setup.stateAt .atUpperStops).volume =
        225243 / 2000000 := by
    have hFixedVolume := congrArg volumeInCubicMetres
      _workLaws.volumeFixedAfterReachingStops
    nlinarith
  have hInitialVolume :
      volumeInCubicMetres (setup.stateAt .initial).volume =
        225243 / 4000000 := by
    nlinarith [_readouts.volumeDoublesAtStops]
  have hRiseWork :
      energyInKilojoules
          (setup.boundaryWorkDoneByRefrigerant .pistonRise) =
        12227766741 / 200000000 := by
    rw [_workLaws.riseBoundaryWork,
      _referenceData.initialPressureKilopascals,
      hStopsVolume, hInitialVolume]
    norm_num
  have hRiseHeat := _firstLaw.firstLawOnEachLeg .pistonRise
  have hStopsHeat := _firstLaw.firstLawOnEachLeg .heatingAtStops
  simp only [ProcessLeg.finalState, ProcessLeg.initialState] at hRiseHeat hStopsHeat
  rw [_readouts.refrigerantMassKilograms,
    _referenceData.initialSpecificInternalEnergyKilojoulesPerKilogram,
    hRiseWork] at hRiseHeat
  rw [_readouts.refrigerantMassKilograms,
    _referenceData.finalSpecificInternalEnergyKilojoulesPerKilogram,
    _workLaws.stoppedPistonDoesNoBoundaryWork] at hStopsHeat
  have hOverallHeat :
      energyInKilojoules setup.overallHeatTransferIntoRefrigerant =
        144952766741 / 200000000 := by
    nlinarith [_firstLaw.overallHeatIsLegSum]
  constructor
  · change
      |energyInKilojoules setup.overallHeatTransferIntoRefrigerant - 725| < 1
    rw [hOverallHeat]
    norm_num [abs_of_nonpos]
  · intro other hOther
    cases other with
    | A =>
        norm_num [displayedHeatTransferKilojoules, hOverallHeat,
          abs_of_nonneg, abs_of_nonpos]
    | B =>
        norm_num [displayedHeatTransferKilojoules, hOverallHeat,
          abs_of_nonneg, abs_of_nonpos]
    | C =>
        norm_num [displayedHeatTransferKilojoules, hOverallHeat,
          abs_of_nonneg, abs_of_nonpos]
    | D => exact (hOther rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0464
