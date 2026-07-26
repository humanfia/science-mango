import Mathlib
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0451

open Dimension

/-!
# Heat transfer to a rigid vessel containing a saturated water mixture

Two kilograms of water initially at `120 °C` and vapor quality `0.25` are
heated through `20 °C` at constant volume.  The primary bitmap shows an
unlabeled rectangular vessel, a water level, four burner flames, and a top
outlet pipe carrying a crossed circular valve symbol.

The water mass, occupied volume, specific volume, specific internal energy,
heat, work, and absolute temperature retain physical quantity types.  Real
numbers occur only as explicitly named unit readouts, the dimensionless vapor
quality, calibrated saturated-water table entries, and displayed answer
values.
-/

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- The physical dimension of volume, `L³`. -/
def volumeDimension : Dimension := L𝓭 * L𝓭 * L𝓭

/-- The physical dimension of specific volume, `L³ M⁻¹`. -/
def specificVolumeDimension : Dimension := volumeDimension * M𝓭⁻¹

/-- The physical dimension of specific internal energy, `L² T⁻²`. -/
def specificInternalEnergyDimension : Dimension :=
  L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical volume. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim volumeDimension NNReal)

/-- A nonnegative, unit-independent thermodynamic specific volume. -/
abbrev SpecificVolumeQuantity : Type :=
  Dimensionful (WithDim specificVolumeDimension NNReal)

/-!
A signed, unit-independent specific internal energy.  Signed values permit an
arbitrary thermodynamic reference datum; the tabulated states in this problem
have positive readouts.
-/
abbrev SpecificInternalEnergyQuantity : Type :=
  Dimensionful (WithDim specificInternalEnergyDimension ℝ)

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := MassUnit.kilograms}).val : ℝ)

/-- Read a physical volume in cubic metres. -/
def volumeInCubicMetres (volume : VolumeQuantity) : ℝ :=
  ((volume {UnitChoices.SI with length := LengthUnit.meters}).val : ℝ)

/-- Read a specific volume in cubic metres per kilogram. -/
def specificVolumeInCubicMetresPerKilogram
    (specificVolume : SpecificVolumeQuantity) : ℝ :=
  ((specificVolume {UnitChoices.SI with
    length := LengthUnit.meters, mass := MassUnit.kilograms}).val : ℝ)

/-- Read a specific internal energy in joules per kilogram. -/
def specificInternalEnergyInJoulesPerKilogram
    (specificInternalEnergy : SpecificInternalEnergyQuantity) : ℝ :=
  (specificInternalEnergy UnitChoices.SI).val

/-- Read a specific internal energy in kilojoules per kilogram. -/
def specificInternalEnergyInKilojoulesPerKilogram
    (specificInternalEnergy : SpecificInternalEnergyQuantity) : ℝ :=
  specificInternalEnergyInJoulesPerKilogram specificInternalEnergy / 1000

/-- Read heat, work, or total internal energy in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read heat, work, or total internal energy in kilojoules. -/
def energyInKilojoules (energy : DimEnergy) : ℝ :=
  energyInJoules energy / 1000

/-!
An absolute temperature together with the zero-preserving unit in which its
magnitude is stored.  The affine Celsius offset is introduced only in the
scalar readout below.
-/
structure MeasuredTemperature where
  absoluteTemperature : Temperature
  storageUnit : TemperatureUnit

/-- Kelvin readout of an absolute physical temperature. -/
def temperatureInKelvins (temperature : MeasuredTemperature) : ℝ :=
  let unitRatio : NNReal :=
    temperature.storageUnit / TemperatureUnit.kelvin
  temperature.absoluteTemperature.toReal * (unitRatio : ℝ)

/-- Celsius readout, using the exact offset `273.15 K = 5463 / 20 K`. -/
def temperatureInDegreesCelsius (temperature : MeasuredTemperature) : ℝ :=
  temperatureInKelvins temperature - 5463 / 20

/-! ## Water states, apparatus, and primary-figure vocabulary -/

/-- The working substance in the depicted vessel. -/
inductive WorkingFluid where
  | water
  | other
  deriving DecidableEq, Repr

/-- The two endpoint states of the heating process. -/
inductive ProcessStage where
  | initial
  | final
  deriving DecidableEq, Fintype, Repr

/-- Thermodynamic phase region of an equilibrium water state. -/
inductive WaterPhaseRegion where
  | compressedLiquid
  | saturatedLiquidVaporMixture
  | superheatedVapor
  | other
  deriving DecidableEq, Repr

/-- Idealized type of the process specified in the prose. -/
inductive ProcessKind where
  | constantVolumeHeating
  | other
  deriving DecidableEq, Repr

/-- Status of the valve on the top outlet during heating. -/
inductive ValveStatus where
  | closed
  | open
  deriving DecidableEq, Repr

/-- Distinct objects visible in the supplied raster. -/
inductive FigureObject where
  | rectangularVessel
  | blueWaterInventory
  | burnerManifold
  | outletPipe
  | circularValve
  | valveCrossMark
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative geometry transcribed from the primary image.  The record contains
no thermodynamic property value and no heat-transfer answer.
-/
structure RigidVesselFigure where
  objectShown : FigureObject → Bool
  burnerFlameCount : ℕ
  burnersBelowVessel : Bool
  liquidBelowHeadspace : Bool
  outletEmergesFromTop : Bool
  outletBendsRight : Bool
  valveLiesOnOutlet : Bool

/-!
An equilibrium state of the fixed water inventory.  `vaporQuality` is a
dimensionless mass fraction whose thermodynamic meaning is imposed only when
`phaseRegion` is the saturated liquid-vapor mixture.
-/
structure WaterState where
  temperature : MeasuredTemperature
  specificVolume : SpecificVolumeQuantity
  specificInternalEnergy : SpecificInternalEnergyQuantity
  phaseRegion : WaterPhaseRegion
  vaporQuality : ℝ

/-!
External saturated-water property data.  The vaporization internal energy is
`u_fg = u_g - u_f`; all outputs remain dimensionful physical quantities.
-/
structure SaturatedWaterTable where
  saturatedLiquidSpecificVolumeAt :
    MeasuredTemperature → SpecificVolumeQuantity
  saturatedVaporSpecificVolumeAt :
    MeasuredTemperature → SpecificVolumeQuantity
  saturatedLiquidSpecificInternalEnergyAt :
    MeasuredTemperature → SpecificInternalEnergyQuantity
  vaporizationSpecificInternalEnergyAt :
    MeasuredTemperature → SpecificInternalEnergyQuantity

/-!
The closed rigid-vessel experiment.  Heat is positive into the water and
boundary work is positive when done by the water.  Endpoint observables are
independent fields until related by the governing laws below.
-/
structure RigidWaterVesselSetup where
  fluid : WorkingFluid
  figure : RigidVesselFigure
  waterTable : SaturatedWaterTable
  processKind : ProcessKind
  valveStatusDuringHeating : ValveStatus
  containerIsRigid : Bool
  closedToMassTransfer : Bool
  kineticAndPotentialEnergyChangesNegligible : Bool
  stateAt : ProcessStage → WaterState
  massAt : ProcessStage → MassQuantity
  occupiedVolumeAt : ProcessStage → VolumeQuantity
  heatTransferredToWater : DimEnergy
  boundaryWorkDoneByWater : DimEnergy

/-! ## Assumptions: scenario, figure, source readouts, data, and laws -/

/-- Qualitative physical idealizations supplied by the scenario. -/
structure MatchesRigidWaterVesselScenario
    (setup : RigidWaterVesselSetup) : Prop where
  workingFluidIsWater : setup.fluid = .water
  processIsConstantVolume : setup.processKind = .constantVolumeHeating
  vesselIsRigid : setup.containerIsRigid = true
  valveRemainsClosed : setup.valveStatusDuringHeating = .closed
  systemIsClosedToMassTransfer : setup.closedToMassTransfer = true
  negligibleKineticAndPotentialEnergyChanges :
    setup.kineticAndPotentialEnergyChangesNegligible = true
  initialStateIsSaturatedMixture :
    (setup.stateAt .initial).phaseRegion =
      .saturatedLiquidVaporMixture

/-!
Facts visible in image `451.png`: the vessel and inventory, four flames below
it, and the top pipe with a crossed circular valve symbol.  Closed-valve
operation is kept in the scenario predicate rather than inferred solely from
the symbol.
-/
structure MatchesSuppliedFigure (setup : RigidWaterVesselSetup) : Prop where
  everyDepictedObjectIsShown :
    ∀ object : FigureObject, setup.figure.objectShown object = true
  fourBurnerFlames : setup.figure.burnerFlameCount = 4
  burnersAreBelowVessel : setup.figure.burnersBelowVessel = true
  liquidIsBelowHeadspace : setup.figure.liquidBelowHeadspace = true
  outletLeavesVesselTop : setup.figure.outletEmergesFromTop = true
  outletPipeBendsRight : setup.figure.outletBendsRight = true
  valveIsOnOutletPipe : setup.figure.valveLiesOnOutlet = true

/-!
Numerical measurements stated in the problem.  The final temperature is
recorded as a `20 °C` rise rather than inserted directly as a table index.
No heat value or answer label occurs here.
-/
structure MatchesProblemReadouts (setup : RigidWaterVesselSetup) : Prop where
  initialMassKilograms :
    massInKilograms (setup.massAt .initial) = 2
  initialTemperatureCelsius :
    temperatureInDegreesCelsius (setup.stateAt .initial).temperature = 120
  initialVaporQuality :
    (setup.stateAt .initial).vaporQuality = 1 / 4
  temperatureRiseCelsius :
    temperatureInDegreesCelsius (setup.stateAt .final).temperature =
      temperatureInDegreesCelsius (setup.stateAt .initial).temperature + 20

/-!
Saturated-water table entries at the independently specified endpoint
temperatures.  Specific volumes are in `m³/kg`; specific internal energies
are in `kJ/kg`.  These reference data determine the final phase and quality
but do not mention heat transfer or an answer choice.
-/
structure MatchesReferenceSaturatedWaterData
    (setup : RigidWaterVesselSetup) : Prop where
  initialSaturatedLiquidSpecificVolume :
    specificVolumeInCubicMetresPerKilogram
      (setup.waterTable.saturatedLiquidSpecificVolumeAt
        (setup.stateAt .initial).temperature) = 53 / 50000
  initialSaturatedVaporSpecificVolume :
    specificVolumeInCubicMetresPerKilogram
      (setup.waterTable.saturatedVaporSpecificVolumeAt
        (setup.stateAt .initial).temperature) = 89133 / 100000
  initialSaturatedLiquidSpecificInternalEnergy :
    specificInternalEnergyInKilojoulesPerKilogram
      (setup.waterTable.saturatedLiquidSpecificInternalEnergyAt
        (setup.stateAt .initial).temperature) = 12587 / 25
  initialVaporizationSpecificInternalEnergy :
    specificInternalEnergyInKilojoulesPerKilogram
      (setup.waterTable.vaporizationSpecificInternalEnergyAt
        (setup.stateAt .initial).temperature) = 50644 / 25
  finalSaturatedLiquidSpecificVolume :
    specificVolumeInCubicMetresPerKilogram
      (setup.waterTable.saturatedLiquidSpecificVolumeAt
        (setup.stateAt .final).temperature) = 27 / 25000
  finalSaturatedVaporSpecificVolume :
    specificVolumeInCubicMetresPerKilogram
      (setup.waterTable.saturatedVaporSpecificVolumeAt
        (setup.stateAt .final).temperature) = 1017 / 2000
  finalSaturatedLiquidSpecificInternalEnergy :
    specificInternalEnergyInKilojoulesPerKilogram
      (setup.waterTable.saturatedLiquidSpecificInternalEnergyAt
        (setup.stateAt .final).temperature) = 29467 / 50
  finalVaporizationSpecificInternalEnergy :
    specificInternalEnergyInKilojoulesPerKilogram
      (setup.waterTable.vaporizationSpecificInternalEnergyAt
        (setup.stateAt .final).temperature) = 97983 / 50

/-!
Governing laws for the closed rigid water system:

* mass is conserved and the occupied volume is unchanged;
* `V = m v` at each endpoint;
* a state whose specific volume lies between saturated liquid and vapor
  values at its temperature is a saturated mixture;
* mixture specific volume and internal energy interpolate by vapor quality;
* the closed-system first law is `ΔU = Q - W_by`;
* a rigid boundary performs no boundary work.

None of these laws includes the requested numerical heat or selects a
multiple-choice answer.
-/
structure SatisfiesRigidVesselWaterLaws
    (setup : RigidWaterVesselSetup) : Prop where
  massConservation : setup.massAt .final = setup.massAt .initial
  constantOccupiedVolume :
    setup.occupiedVolumeAt .final = setup.occupiedVolumeAt .initial
  massSpecificVolumeLaw : ∀ stage : ProcessStage,
    volumeInCubicMetres (setup.occupiedVolumeAt stage) =
      massInKilograms (setup.massAt stage) *
        specificVolumeInCubicMetresPerKilogram
          (setup.stateAt stage).specificVolume
  saturatedMixtureClassification : ∀ stage : ProcessStage,
    specificVolumeInCubicMetresPerKilogram
        (setup.waterTable.saturatedLiquidSpecificVolumeAt
          (setup.stateAt stage).temperature) ≤
      specificVolumeInCubicMetresPerKilogram
        (setup.stateAt stage).specificVolume →
    specificVolumeInCubicMetresPerKilogram
        (setup.stateAt stage).specificVolume ≤
      specificVolumeInCubicMetresPerKilogram
        (setup.waterTable.saturatedVaporSpecificVolumeAt
          (setup.stateAt stage).temperature) →
    (setup.stateAt stage).phaseRegion =
      .saturatedLiquidVaporMixture
  saturatedMixtureQualityBounds : ∀ stage : ProcessStage,
    (setup.stateAt stage).phaseRegion =
        .saturatedLiquidVaporMixture →
      0 ≤ (setup.stateAt stage).vaporQuality ∧
        (setup.stateAt stage).vaporQuality ≤ 1
  saturatedMixtureSpecificVolumeLaw : ∀ stage : ProcessStage,
    (setup.stateAt stage).phaseRegion =
        .saturatedLiquidVaporMixture →
      specificVolumeInCubicMetresPerKilogram
          (setup.stateAt stage).specificVolume =
        specificVolumeInCubicMetresPerKilogram
            (setup.waterTable.saturatedLiquidSpecificVolumeAt
              (setup.stateAt stage).temperature) +
          (setup.stateAt stage).vaporQuality *
            (specificVolumeInCubicMetresPerKilogram
                (setup.waterTable.saturatedVaporSpecificVolumeAt
                  (setup.stateAt stage).temperature) -
              specificVolumeInCubicMetresPerKilogram
                (setup.waterTable.saturatedLiquidSpecificVolumeAt
                  (setup.stateAt stage).temperature))
  saturatedMixtureSpecificInternalEnergyLaw : ∀ stage : ProcessStage,
    (setup.stateAt stage).phaseRegion =
        .saturatedLiquidVaporMixture →
      specificInternalEnergyInKilojoulesPerKilogram
          (setup.stateAt stage).specificInternalEnergy =
        specificInternalEnergyInKilojoulesPerKilogram
            (setup.waterTable.saturatedLiquidSpecificInternalEnergyAt
              (setup.stateAt stage).temperature) +
          (setup.stateAt stage).vaporQuality *
            specificInternalEnergyInKilojoulesPerKilogram
              (setup.waterTable.vaporizationSpecificInternalEnergyAt
                (setup.stateAt stage).temperature)
  closedSystemFirstLaw :
    massInKilograms (setup.massAt .final) *
          specificInternalEnergyInKilojoulesPerKilogram
            (setup.stateAt .final).specificInternalEnergy -
        massInKilograms (setup.massAt .initial) *
          specificInternalEnergyInKilojoulesPerKilogram
            (setup.stateAt .initial).specificInternalEnergy =
      energyInKilojoules setup.heatTransferredToWater -
        energyInKilojoules setup.boundaryWorkDoneByWater
  rigidBoundaryWorkIsZero :
    energyInKilojoules setup.boundaryWorkDoneByWater = 0

/-! ## Displayed choices and current target -/

/-- Labels printed beside the four candidate heat transfers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Heat-transfer value in kilojoules printed beside each answer label. -/
def displayedHeatInKilojoules : AnswerChoice → ℝ
  | .A => 61219 / 50
  | .B => 25248 / 25
  | .C => 12587 / 25
  | .D => 4389 / 5

/-- Dataset answer metadata, deliberately not used as a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
A choice reports the modeled heat to the one-decimal precision of choice D.
This remains a nontrivial relation between an independently modeled heat and
the displayed table.
-/
def IsReportedHeatChoice
    (setup : RigidWaterVesselSetup) (choice : AnswerChoice) : Prop :=
  round (10 * energyInKilojoules setup.heatTransferredToWater) =
    round (10 * displayedHeatInKilojoules choice)

/-!
Constant volume first gives the final quality

`x₂ = 9891 / 22552 ≈ 0.438586`.

The mixture-energy law and the closed-system first law then give the exact
table-based heat

`Q = 98980769 / 112760 kJ ≈ 877.80036 kJ`,

which reports to one decimal place as `877.8 kJ`, uniquely choice D.

Blueprint label: `thm:physics:phyx_mini_0451:target`.
-/
theorem heat_transfer_to_rigid_water_vessel
    (setup : RigidWaterVesselSetup)
    (hScenario : MatchesRigidWaterVesselScenario setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hReferenceData : MatchesReferenceSaturatedWaterData setup)
    (hLaws : SatisfiesRigidVesselWaterLaws setup) :
    (setup.stateAt .final).phaseRegion =
        .saturatedLiquidVaporMixture ∧
      (setup.stateAt .final).vaporQuality = 9891 / 22552 ∧
      energyInKilojoules setup.heatTransferredToWater =
        98980769 / 112760 ∧
      IsReportedHeatChoice setup .D ∧
      ∀ choice : AnswerChoice,
        IsReportedHeatChoice setup choice → choice = .D := by
  have hInitialPhase :
      (setup.stateAt .initial).phaseRegion =
        .saturatedLiquidVaporMixture :=
    hScenario.initialStateIsSaturatedMixture
  have hInitialSpecificVolume :=
    hLaws.saturatedMixtureSpecificVolumeLaw .initial hInitialPhase
  rw [hReferenceData.initialSaturatedLiquidSpecificVolume,
    hReferenceData.initialSaturatedVaporSpecificVolume,
    hReadouts.initialVaporQuality] at hInitialSpecificVolume

  have hFinalMass :
      massInKilograms (setup.massAt .final) = 2 := by
    rw [hLaws.massConservation]
    exact hReadouts.initialMassKilograms
  have hInitialVolumeLaw := hLaws.massSpecificVolumeLaw .initial
  have hFinalVolumeLaw := hLaws.massSpecificVolumeLaw .final
  rw [hReadouts.initialMassKilograms] at hInitialVolumeLaw
  rw [hFinalMass] at hFinalVolumeLaw
  have hOccupiedVolumesEqual :
      volumeInCubicMetres (setup.occupiedVolumeAt .final) =
        volumeInCubicMetres (setup.occupiedVolumeAt .initial) :=
    congrArg volumeInCubicMetres hLaws.constantOccupiedVolume
  have hSpecificVolumesEqual :
      specificVolumeInCubicMetresPerKilogram
          (setup.stateAt .final).specificVolume =
        specificVolumeInCubicMetresPerKilogram
          (setup.stateAt .initial).specificVolume := by
    linarith

  have hFinalAboveSaturatedLiquid :
      specificVolumeInCubicMetresPerKilogram
          (setup.waterTable.saturatedLiquidSpecificVolumeAt
            (setup.stateAt .final).temperature) ≤
        specificVolumeInCubicMetresPerKilogram
          (setup.stateAt .final).specificVolume := by
    rw [hReferenceData.finalSaturatedLiquidSpecificVolume]
    nlinarith [hInitialSpecificVolume, hSpecificVolumesEqual]
  have hFinalBelowSaturatedVapor :
      specificVolumeInCubicMetresPerKilogram
          (setup.stateAt .final).specificVolume ≤
        specificVolumeInCubicMetresPerKilogram
          (setup.waterTable.saturatedVaporSpecificVolumeAt
            (setup.stateAt .final).temperature) := by
    rw [hReferenceData.finalSaturatedVaporSpecificVolume]
    nlinarith [hInitialSpecificVolume, hSpecificVolumesEqual]
  have hFinalPhase :
      (setup.stateAt .final).phaseRegion =
        .saturatedLiquidVaporMixture :=
    hLaws.saturatedMixtureClassification .final
      hFinalAboveSaturatedLiquid hFinalBelowSaturatedVapor

  have hFinalSpecificVolume :=
    hLaws.saturatedMixtureSpecificVolumeLaw .final hFinalPhase
  rw [hReferenceData.finalSaturatedLiquidSpecificVolume,
    hReferenceData.finalSaturatedVaporSpecificVolume] at hFinalSpecificVolume
  have hFinalQuality :
      (setup.stateAt .final).vaporQuality = 9891 / 22552 := by
    nlinarith [hInitialSpecificVolume, hSpecificVolumesEqual,
      hFinalSpecificVolume]

  have hInitialSpecificInternalEnergy :=
    hLaws.saturatedMixtureSpecificInternalEnergyLaw .initial hInitialPhase
  rw [hReferenceData.initialSaturatedLiquidSpecificInternalEnergy,
    hReferenceData.initialVaporizationSpecificInternalEnergy,
    hReadouts.initialVaporQuality] at hInitialSpecificInternalEnergy
  have hFinalSpecificInternalEnergy :=
    hLaws.saturatedMixtureSpecificInternalEnergyLaw .final hFinalPhase
  rw [hReferenceData.finalSaturatedLiquidSpecificInternalEnergy,
    hReferenceData.finalVaporizationSpecificInternalEnergy,
    hFinalQuality] at hFinalSpecificInternalEnergy
  have hFirstLaw := hLaws.closedSystemFirstLaw
  rw [hFinalMass, hReadouts.initialMassKilograms,
    hLaws.rigidBoundaryWorkIsZero] at hFirstLaw
  have hHeat :
      energyInKilojoules setup.heatTransferredToWater =
        98980769 / 112760 := by
    nlinarith [hInitialSpecificInternalEnergy,
      hFinalSpecificInternalEnergy, hFirstLaw]

  have hRoundedHeat :
      round (10 * energyInKilojoules setup.heatTransferredToWater) =
        8778 := by
    rw [hHeat, round_eq_iff]
    norm_num
  have hDisplayedRounds : ∀ choice : AnswerChoice,
      round (10 * displayedHeatInKilojoules choice) =
        match choice with
        | .A => 12244
        | .B => 10099
        | .C => 5035
        | .D => 8778 := by
    intro choice
    cases choice <;> rw [round_eq_iff] <;>
      norm_num [displayedHeatInKilojoules]
  have hChoiceD : IsReportedHeatChoice setup .D := by
    unfold IsReportedHeatChoice
    rw [hRoundedHeat, hDisplayedRounds .D]
  refine ⟨hFinalPhase, hFinalQuality, hHeat, hChoiceD, ?_⟩
  intro choice hChoice
  unfold IsReportedHeatChoice at hChoice
  rw [hRoundedHeat, hDisplayedRounds choice] at hChoice
  cases choice with
  | A => norm_num at hChoice
  | B => norm_num at hChoice
  | C => norm_num at hChoice
  | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0451
