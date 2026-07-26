import Mathlib
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0463

open Dimension

/-!
# Heat transfer to water beneath a piston initially held by stops

Ten kilograms of water initially form a saturated liquid--vapor mixture at
`100 kPa` with vapor quality `0.5`.  The primary figure shows the water below
a horizontal piston that is supported by lower stops.  Heating therefore
first occurs at constant volume.  At `200 kPa` the pressure load floats the
piston; subsequent quasistatic expansion is at that constant pressure until
the total water volume is three times its initial value.

Mass, pressure, volume, area, acceleration, force, energy, specific volume,
and specific internal energy are represented by dimension-carrying physical
quantities.  Real numbers occur only as dimensionless quality or as calibrated
readouts in named SI-derived units.
-/

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- The physical dimension of volume, `L³`. -/
def volumeDimension : Dimension := L𝓭 * L𝓭 * L𝓭

/-- The physical dimension of specific volume, `L³ M⁻¹`. -/
def specificVolumeDimension : Dimension := volumeDimension * M𝓭⁻¹

/-- The physical dimension of specific energy, `L² T⁻²`. -/
def specificEnergyDimension : Dimension :=
  L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of force, `M L T⁻²`. -/
def forceDimension : Dimension := M𝓭 * accelerationDimension

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical volume. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim volumeDimension NNReal)

/-- A nonnegative, unit-independent thermodynamic specific volume. -/
abbrev SpecificVolumeQuantity : Type :=
  Dimensionful (WithDim specificVolumeDimension NNReal)

/-- A signed, unit-independent thermodynamic specific internal energy. -/
abbrev SpecificEnergyQuantity : Type :=
  Dimensionful (WithDim specificEnergyDimension ℝ)

/-- A nonnegative acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative force magnitude. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass { UnitChoices.SI with mass := MassUnit.kilograms }).val : ℝ)

/-- Read a physical volume in cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume { UnitChoices.SI with length := LengthUnit.meters }).val : ℝ)

/-- Read a specific volume in cubic metres per kilogram. -/
def specificVolumeInCubicMetersPerKilogram
    (specificVolume : SpecificVolumeQuantity) : ℝ :=
  ((specificVolume UnitChoices.SI).val : ℝ)

/-- Read a piston area in square metres. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Read a pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a pressure in kilopascals. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Read an acceleration magnitude in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read a force magnitude in newtons. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Read heat or work in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read heat or work in kilojoules. -/
def energyInKilojoules (energy : DimEnergy) : ℝ :=
  energyInJoules energy / 1000

/-- Read specific internal energy in kilojoules per kilogram. -/
def specificEnergyInKilojoulesPerKilogram
    (energy : SpecificEnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val / 1000

/-! ## Water states, piston apparatus, and primary-figure vocabulary -/

/-- Distinguished equilibrium states of the two-stage heating process. -/
inductive ProcessState where
  | initialOnStops
  | liftOff
  | finalExpanded
  deriving DecidableEq, Fintype, Repr

/-- Substance confined below the piston. -/
inductive FluidSubstance where
  | water
  | other
  deriving DecidableEq, Repr

/-- Thermodynamic phase region occupied by a water state. -/
inductive WaterPhaseRegion where
  | saturatedLiquidVaporMixture
  | superheatedVapor
  | other
  deriving DecidableEq, Repr

/-- Mechanical support regime of the piston at a distinguished state. -/
inductive PistonSupportRegime where
  | supportedByLowerStops
  | justFloating
  | freelyMovingAtConstantLoad
  | other
  deriving DecidableEq, Repr

/-- Idealized heating path selected by the stops and piston load. -/
inductive HeatingProcessRegime where
  | constantVolumeThenConstantPressure
  | other
  deriving DecidableEq, Repr

/-- Sign convention for the requested heat transfer. -/
inductive HeatTransferSignConvention where
  | positiveIntoWater
  | positiveOutOfWater
  deriving DecidableEq, Repr

/-- Vertical directions visible in the supplied figure. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- One equilibrium state of the closed water sample. -/
structure WaterState where
  pressure : DimPressure
  volume : VolumeQuantity
  specificVolume : SpecificVolumeQuantity
  specificInternalEnergy : SpecificEnergyQuantity
  phaseRegion : WaterPhaseRegion

/-- How an off-grid state is interpolated in the external steam table. -/
inductive WaterTableInterpolationConvention where
  | linearAtFixedPressure
  | other
  deriving DecidableEq, Repr

/-!
An abstract equilibrium water-property table.  Saturated-liquid and
saturated-vapor entries are indexed by pressure; a single-phase state can be
looked up by pressure and specific volume.  These are constitutive properties,
not definitions of the requested heat transfer.

The source does not identify a steam-table edition.  The identifier is
therefore retained as a parameter rather than silently fixed here.
-/
structure WaterPropertyTable where
  editionIdentifier : Option String
  interpolationConvention : WaterTableInterpolationConvention
  saturatedLiquidSpecificVolumeAtPressure :
    DimPressure → SpecificVolumeQuantity
  saturatedVaporSpecificVolumeAtPressure :
    DimPressure → SpecificVolumeQuantity
  saturatedLiquidSpecificInternalEnergyAtPressure :
    DimPressure → SpecificEnergyQuantity
  saturatedVaporSpecificInternalEnergyAtPressure :
    DimPressure → SpecificEnergyQuantity
  specificInternalEnergyAtPressureAndSpecificVolume :
    DimPressure → SpecificVolumeQuantity → SpecificEnergyQuantity

/-- Physical objects visible in the supplied raster image. -/
inductive FigureObject where
  | verticalCylinderWalls
  | horizontalMovablePiston
  | lowerPistonStops
  | blueWaterRegion
  | spaceAbovePiston
  deriving DecidableEq, Fintype, Repr

/-- Literal labels visible in the supplied raster image. -/
inductive FigureLabel where
  | outsidePressureP0
  | gravityG
  | waterH2O
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative evidence transcribed from the primary image.  The image contains
no numerical scale or thermodynamic-state readout.
-/
structure StoppedPistonCylinderFigure where
  objectShown : FigureObject → Bool
  labelShown : FigureLabel → Bool
  pressureDenotedByP0 : DimPressure
  gravityArrowDirection : VerticalDirection
  waterIsBelowPiston : Bool
  outsidePressureIsAbovePiston : Bool
  pistonIsHorizontal : Bool
  stopsAreImmediatelyBelowPiston : Bool
  pistonSpansCylinderBore : Bool
  waterRegionIsBlue : Bool
  containsQuantitativeScaleOrStateReadout : Bool

/-!
The complete physical setup.  Heat and boundary work are independent physical
observables; neither is defined from an answer choice or from the desired
numerical conclusion.
-/
structure StoppedPistonWaterSetup where
  contents : FluidSubstance
  waterMass : MassQuantity
  stateAt : ProcessState → WaterState
  initialVaporQuality : ℝ
  waterTable : WaterPropertyTable
  pistonMass : MassQuantity
  pistonCrossSectionalArea : DimArea
  gravitationalAcceleration : AccelerationQuantity
  pistonWeight : ForceQuantity
  initialLowerStopReaction : ForceQuantity
  outsidePressureP0 : DimPressure
  floatPressure : DimPressure
  supportRegimeAt : ProcessState → PistonSupportRegime
  heatingProcessRegime : HeatingProcessRegime
  heatSignConvention : HeatTransferSignConvention
  heatTransferIntoWater : DimEnergy
  boundaryWorkDoneByWater : DimEnergy
  figure : StoppedPistonCylinderFigure
  systemIsClosedToMassTransfer : Bool
  pistonMovesWithoutFriction : Bool
  heatingIsQuasistatic : Bool
  waterIsHeated : Bool
  kineticAndPotentialEnergyChangesNegligible : Bool

/-! ## Assumptions: scenario, readouts, figure evidence, and laws -/

/-- Qualitative conditions stated or conventionally idealized in the problem. -/
structure MatchesStoppedPistonWaterScenario
    (setup : StoppedPistonWaterSetup) : Prop where
  contentsAreWater : setup.contents = .water
  initialStateIsSaturatedMixture :
    (setup.stateAt .initialOnStops).phaseRegion =
      .saturatedLiquidVaporMixture
  initiallySupportedByStops :
    setup.supportRegimeAt .initialOnStops = .supportedByLowerStops
  pistonJustFloatsAtIntermediateState :
    setup.supportRegimeAt .liftOff = .justFloating
  pistonFreelyMovesAtFinalState :
    setup.supportRegimeAt .finalExpanded = .freelyMovingAtConstantLoad
  closedWaterSystem : setup.systemIsClosedToMassTransfer = true
  frictionlessPiston : setup.pistonMovesWithoutFriction = true
  quasistaticHeating : setup.heatingIsQuasistatic = true
  heatingProcess : setup.waterIsHeated = true
  twoStageRegime :
    setup.heatingProcessRegime = .constantVolumeThenConstantPressure
  positiveHeatIntoWater :
    setup.heatSignConvention = .positiveIntoWater
  negligibleBulkEnergyChanges :
    setup.kineticAndPotentialEnergyChangesNegligible = true

/-!
Numerical information stated in the prose.  The triple-volume condition is an
endpoint datum; neither the requested heat nor an answer label occurs here.
-/
structure MatchesProblemReadouts (setup : StoppedPistonWaterSetup) : Prop where
  waterMassKilograms : massInKilograms setup.waterMass = 10
  initialPressureKilopascals :
    pressureInKilopascals (setup.stateAt .initialOnStops).pressure = 100
  initialVaporQualityOneHalf : setup.initialVaporQuality = 1 / 2
  floatPressureKilopascals :
    pressureInKilopascals setup.floatPressure = 200
  finalVolumeIsTripleInitialVolume :
    volumeInCubicMeters (setup.stateAt .finalExpanded).volume =
      3 * volumeInCubicMeters (setup.stateAt .initialOnStops).volume

/-- Exact objects, labels, and geometric relations visible in the image. -/
structure MatchesSuppliedStoppedPistonFigure
    (setup : StoppedPistonWaterSetup) : Prop where
  everyDepictedObjectIsShown :
    ∀ object, setup.figure.objectShown object = true
  everyPrintedLabelIsShown :
    ∀ label, setup.figure.labelShown label = true
  P0DenotesOutsidePressure :
    setup.figure.pressureDenotedByP0 = setup.outsidePressureP0
  gravityArrowPointsDown :
    setup.figure.gravityArrowDirection = .downward
  waterBelowPiston : setup.figure.waterIsBelowPiston = true
  outsidePressureAbovePiston :
    setup.figure.outsidePressureIsAbovePiston = true
  horizontalPiston : setup.figure.pistonIsHorizontal = true
  lowerStopsSupportPiston :
    setup.figure.stopsAreImmediatelyBelowPiston = true
  pistonCrossesCylinderBore :
    setup.figure.pistonSpansCylinderBore = true
  waterFillIsBlue : setup.figure.waterRegionIsBlue = true
  noQuantitativeScaleOrStateReadout :
    setup.figure.containsQuantitativeScaleOrStateReadout = false

/-!
Positivity and quality bounds selecting the physical branch of the model.
-/
structure HasPhysicalStoppedPistonParameters
    (setup : StoppedPistonWaterSetup) : Prop where
  waterMassPositive : 0 < massInKilograms setup.waterMass
  pistonMassPositive : 0 < massInKilograms setup.pistonMass
  pistonAreaPositive : 0 < areaInSquareMeters setup.pistonCrossSectionalArea
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  pressurePositive :
    ∀ state, 0 < pressureInPascals (setup.stateAt state).pressure
  outsidePressurePositive : 0 < pressureInPascals setup.outsidePressureP0
  floatPressurePositive : 0 < pressureInPascals setup.floatPressure
  volumePositive :
    ∀ state, 0 < volumeInCubicMeters (setup.stateAt state).volume
  specificVolumePositive :
    ∀ state,
      0 < specificVolumeInCubicMetersPerKilogram
        (setup.stateAt state).specificVolume
  qualityNonnegative : 0 ≤ setup.initialVaporQuality
  qualityAtMostOne : setup.initialVaporQuality ≤ 1

/-!
Constitutive state relations: saturated-mixture interpolation at the initial
state and a pressure/specific-volume lookup at the final state.  The equations
contain no heat-transfer value.
-/
structure SatisfiesWaterPropertyRelations
    (setup : StoppedPistonWaterSetup) : Prop where
  initialSpecificVolumeMixtureRule :
    specificVolumeInCubicMetersPerKilogram
        (setup.stateAt .initialOnStops).specificVolume =
      (1 - setup.initialVaporQuality) *
          specificVolumeInCubicMetersPerKilogram
            (setup.waterTable.saturatedLiquidSpecificVolumeAtPressure
              (setup.stateAt .initialOnStops).pressure) +
        setup.initialVaporQuality *
          specificVolumeInCubicMetersPerKilogram
            (setup.waterTable.saturatedVaporSpecificVolumeAtPressure
              (setup.stateAt .initialOnStops).pressure)
  initialSpecificInternalEnergyMixtureRule :
    specificEnergyInKilojoulesPerKilogram
        (setup.stateAt .initialOnStops).specificInternalEnergy =
      (1 - setup.initialVaporQuality) *
          specificEnergyInKilojoulesPerKilogram
            (setup.waterTable.saturatedLiquidSpecificInternalEnergyAtPressure
              (setup.stateAt .initialOnStops).pressure) +
        setup.initialVaporQuality *
          specificEnergyInKilojoulesPerKilogram
            (setup.waterTable.saturatedVaporSpecificInternalEnergyAtPressure
              (setup.stateAt .initialOnStops).pressure)
  finalSpecificInternalEnergyFromTable :
    (setup.stateAt .finalExpanded).specificInternalEnergy =
      setup.waterTable.specificInternalEnergyAtPressureAndSpecificVolume
        (setup.stateAt .finalExpanded).pressure
        (setup.stateAt .finalExpanded).specificVolume

/-!
Conservation of water mass and `V = m v` at each modeled equilibrium state.
-/
structure SatisfiesClosedWaterMassVolumeLaw
    (setup : StoppedPistonWaterSetup) : Prop where
  massVolumeRelation :
    ∀ state,
      volumeInCubicMeters (setup.stateAt state).volume =
        massInKilograms setup.waterMass *
          specificVolumeInCubicMetersPerKilogram
            (setup.stateAt state).specificVolume

/-!
Mechanical equilibrium of the piston.  At lift-off the lower-stop reaction is
zero, so the water-pressure force balances the outside-pressure force and
piston weight.  The initial equation records the nonzero support reaction.
-/
structure SatisfiesPistonLoadBalance
    (setup : StoppedPistonWaterSetup) : Prop where
  pistonWeightLaw :
    forceInNewtons setup.pistonWeight =
      massInKilograms setup.pistonMass *
        accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  initialSupportedBalance :
    pressureInPascals (setup.stateAt .initialOnStops).pressure *
          areaInSquareMeters setup.pistonCrossSectionalArea +
        forceInNewtons setup.initialLowerStopReaction =
      pressureInPascals setup.outsidePressureP0 *
          areaInSquareMeters setup.pistonCrossSectionalArea +
        forceInNewtons setup.pistonWeight
  liftOffBalance :
    pressureInPascals setup.floatPressure *
        areaInSquareMeters setup.pistonCrossSectionalArea =
      pressureInPascals setup.outsidePressureP0 *
          areaInSquareMeters setup.pistonCrossSectionalArea +
        forceInNewtons setup.pistonWeight

/-!
The stops enforce constant volume before lift-off.  Once the piston floats,
the fixed outside pressure and piston weight impose the constant float
pressure through the final equilibrium state.
-/
structure SatisfiesStoppedThenConstantPressurePath
    (setup : StoppedPistonWaterSetup) : Prop where
  noVolumeChangeBeforeLiftOff :
    (setup.stateAt .liftOff).volume =
      (setup.stateAt .initialOnStops).volume
  pressureAtLiftOff :
    (setup.stateAt .liftOff).pressure = setup.floatPressure
  finalPressureRemainsAtFloatPressure :
    (setup.stateAt .finalExpanded).pressure = setup.floatPressure

/-!
Boundary work is zero in the stop-constrained stage and equals `p ΔV` in the
subsequent quasistatic constant-pressure stage.  Since `kPa · m³ = kJ`, the
law is written directly in those calibrated readouts.
-/
structure SatisfiesTwoStageBoundaryWorkLaw
    (setup : StoppedPistonWaterSetup) : Prop where
  constantPressureBoundaryWork :
    energyInKilojoules setup.boundaryWorkDoneByWater =
      pressureInKilopascals setup.floatPressure *
        (volumeInCubicMeters (setup.stateAt .finalExpanded).volume -
          volumeInCubicMeters (setup.stateAt .liftOff).volume)

/-!
The closed-system first law with the sign conventions `Q > 0` into the water
and `W > 0` done by the water.  Changes in kinetic and potential energy are
neglected as stated in the scenario assumptions.
-/
structure SatisfiesClosedSystemFirstLaw
    (setup : StoppedPistonWaterSetup) : Prop where
  heatEqualsInternalEnergyChangePlusWork :
    energyInKilojoules setup.heatTransferIntoWater =
      massInKilograms setup.waterMass *
          (specificEnergyInKilojoulesPerKilogram
              (setup.stateAt .finalExpanded).specificInternalEnergy -
            specificEnergyInKilojoulesPerKilogram
              (setup.stateAt .initialOnStops).specificInternalEnergy) +
        energyInKilojoules setup.boundaryWorkDoneByWater

/-! ## Derived values and answer metadata -/

/-- Labels printed beside the four candidate heat-transfer values. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Heat transfer in kilojoules printed beside each answer label. -/
def displayedHeatTransferInKilojoules : AnswerChoice → ℝ
  | .A => 208827 / 10
  | .B => 371879 / 10
  | .C => 3390
  | .D => 25961

/-- Dataset answer metadata, deliberately not used as a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Absolute reporting error, in kilojoules, for one displayed choice. -/
def heatTransferChoiceError
    (setup : StoppedPistonWaterSetup) (choice : AnswerChoice) : ℝ :=
  |energyInKilojoules setup.heatTransferIntoWater -
    displayedHeatTransferInKilojoules choice|

/-- A displayed choice is at least as close as every other displayed value. -/
def IsClosestReportedHeatTransferChoice
    (setup : StoppedPistonWaterSetup) (choice : AnswerChoice) : Prop :=
  ∀ other,
    heatTransferChoiceError setup choice ≤ heatTransferChoiceError setup other

/-- A choice is the unique closest displayed value to the derived heat. -/
def IsUniqueClosestReportedHeatTransferChoice
    (setup : StoppedPistonWaterSetup) (choice : AnswerChoice) : Prop :=
  IsClosestReportedHeatTransferChoice setup choice ∧
    ∀ other, IsClosestReportedHeatTransferChoice setup other → other = choice

/-!
The source gives no steam-table edition, saturation-property entries, final
specific internal energy, or interpolation convention.  Consequently it does
not ground any of the displayed numerical heat-transfer choices.  The
strongest source-supported conclusion is the symbolic heat balance below.

The first term is the internal-energy change of the `10 kg` water sample.  Its
initial value is the quality-weighted saturated-mixture lookup at `100 kPa`,
and its final value is the table lookup at the `200 kPa` float pressure and the
final specific volume.  For the work term, the stopped stage has zero boundary
work, while the moving stage changes the volume from `V₁` to `3 V₁`;
using `V₁ = 10 v₁` gives `200 * (2 * 10 * v₁)` kilojoules.

This formalizes blueprint label `thm:physics:phyx_mini_0463:target`.  No
premise fixes the requested heat-transfer value, supplies uncited numerical
water properties, or selects an answer choice.
-/
theorem problem_phyx_mini_0463
    (setup : StoppedPistonWaterSetup)
    (hScenario : MatchesStoppedPistonWaterScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFigure : MatchesSuppliedStoppedPistonFigure setup)
    (hPhysical : HasPhysicalStoppedPistonParameters setup)
    (hRelations : SatisfiesWaterPropertyRelations setup)
    (hMassVolume : SatisfiesClosedWaterMassVolumeLaw setup)
    (hLoadBalance : SatisfiesPistonLoadBalance setup)
    (hPath : SatisfiesStoppedThenConstantPressurePath setup)
    (hWorkLaw : SatisfiesTwoStageBoundaryWorkLaw setup)
    (hFirstLaw : SatisfiesClosedSystemFirstLaw setup) :
    energyInKilojoules setup.heatTransferIntoWater =
      10 *
        (specificEnergyInKilojoulesPerKilogram
            (setup.waterTable.specificInternalEnergyAtPressureAndSpecificVolume
              setup.floatPressure
              (setup.stateAt .finalExpanded).specificVolume) -
          ((1 - (1 / 2 : ℝ)) *
              specificEnergyInKilojoulesPerKilogram
                (setup.waterTable.saturatedLiquidSpecificInternalEnergyAtPressure
                  (setup.stateAt .initialOnStops).pressure) +
            (1 / 2 : ℝ) *
              specificEnergyInKilojoulesPerKilogram
                (setup.waterTable.saturatedVaporSpecificInternalEnergyAtPressure
                  (setup.stateAt .initialOnStops).pressure))) +
        200 *
          (2 * 10 *
            ((1 - (1 / 2 : ℝ)) *
                specificVolumeInCubicMetersPerKilogram
                  (setup.waterTable.saturatedLiquidSpecificVolumeAtPressure
                    (setup.stateAt .initialOnStops).pressure) +
              (1 / 2 : ℝ) *
                specificVolumeInCubicMetersPerKilogram
                  (setup.waterTable.saturatedVaporSpecificVolumeAtPressure
                    (setup.stateAt .initialOnStops).pressure))) := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0463
