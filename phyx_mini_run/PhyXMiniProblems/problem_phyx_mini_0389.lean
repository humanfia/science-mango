import Mathlib.Data.Real.Basic
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0389

open Dimension

/-!
# Final valve pressure for two connected open water tanks

Tank `B` is the raised tank on the left of the supplied figure, while tank
`A` is the lower tank on the right.  Their bottom connections communicate
through a pipe whose valve is at the elevation chosen as zero.  Both free
surfaces are exposed to the same atmospheric pressure `P₀`.

The physical magnitudes below use Physlib's unit-independent `Dimensionful`
representation.  Real numbers occur only as explicitly unit-labelled SI
readouts and as the numerical labels printed in the multiple-choice answers.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length or vertical elevation. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical cross-sectional area. -/
abbrev AreaQuantity : Type := DimArea

/-- A nonnegative physical volume. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative mass density, with dimension `M L⁻³`. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹) NNReal)

/-- A nonnegative acceleration magnitude, with dimension `L T⁻²`. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A physical pressure, grounded in Physlib's `DimPressure`. -/
abbrev PressureQuantity : Type := DimPressure

/-- Read a mass in coherent-SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a length or elevation in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read an area in square metres, using Physlib's named square-metre unit. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  ((area UnitChoices.SI).val : ℝ) /
    ((DimArea.squareMeter UnitChoices.SI).val : ℝ)

/-- Read a volume in coherent-SI cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a mass density in kilograms per cubic metre. -/
def massDensityInKilogramsPerCubicMeter
    (density : MassDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Read an acceleration magnitude in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read a pressure in pascals, using Physlib's named pascal. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Read a pressure in kilopascals, the unit used by all answer choices. -/
def pressureInKilopascals (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure / 1000

/-! ## Tank, valve, state, and figure vocabulary -/

/-- The two cylinder labels printed in the primary figure. -/
inductive Tank where
  | A
  | B
  deriving DecidableEq, Repr

/-- Horizontal placement of a tank in the primary figure. -/
inductive FigureSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- The direction of the arrow labelled `g` in the primary figure. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Whether the valve blocks or permits flow through the connecting line. -/
inductive ValveState where
  | closed
  | open
  deriving DecidableEq, Repr

/--
Figure-derived geometry and labels.  All elevations are measured upward from
the valve, so the valve itself and the lower tank bottom have elevation zero.
-/
structure TankConnectionFigure where
  side : Tank → FigureSide
  higherTank : Tank
  lowerTank : Tank
  heightOffset : LengthQuantity
  bottomElevationAboveValve : Tank → LengthQuantity
  exposedSurfacePressureLabel : Tank → PressureQuantity
  gravityDirection : VerticalDirection
  pipeConnectsTankBottom : Tank → Bool
  valveLiesOnConnectingPipe : Bool

/-- Water data at either the initial closed-valve state or final equilibrium. -/
structure WaterState where
  waterDepth : Tank → LengthQuantity
  waterVolume : Tank → VolumeQuantity
  freeSurfaceElevationAboveValve : Tank → LengthQuantity
  pressureAtValveSide : Tank → PressureQuantity

/--
The complete two-reservoir experiment, retaining the closed initial state and
the open, motionless equilibrium state requested by the question.
-/
structure ConnectedWaterTanksSetup where
  waterDensity : MassDensityQuantity
  gravitationalAcceleration : AccelerationQuantity
  atmosphericPressure : PressureQuantity
  initialWaterMass : Tank → MassQuantity
  crossSectionArea : Tank → AreaQuantity
  figure : TankConnectionFigure
  initialWaterState : WaterState
  equilibriumWaterState : WaterState
  initialValveState : ValveState
  equilibriumValveState : ValveState
  equilibriumWaterAtRest : Bool

/-- The final pressure at the valve, read from the tank-`A` side. -/
def finalValvePressure (setup : ConnectedWaterTanksSetup) : PressureQuantity :=
  setup.equilibriumWaterState.pressureAtValveSide .A

/-! ## Problem and primary-figure readouts -/

/--
Numerical data stated in the prose.  No initial or final valve pressure occurs
in this structure.
-/
structure MatchesProblemReadouts
    (setup : ConnectedWaterTanksSetup) : Prop where
  waterDensityReadout :
    massDensityInKilogramsPerCubicMeter setup.waterDensity = 1000
  tankAMassReadout :
    massInKilograms (setup.initialWaterMass .A) = 100
  tankBMassReadout :
    massInKilograms (setup.initialWaterMass .B) = 500
  tankAAreaReadout :
    areaInSquareMeters (setup.crossSectionArea .A) = 0.1
  tankBAreaReadout :
    areaInSquareMeters (setup.crossSectionArea .B) = 0.25
  initialValveIsClosed : setup.initialValveState = .closed
  equilibriumValveIsOpen : setup.equilibriumValveState = .open
  finalWaterIsAtRest : setup.equilibriumWaterAtRest = true

/--
Primary-image evidence: `B` is the raised left tank, `A` is the lower right
tank, their bottoms differ by `h = 1 m`, the line joins both bottoms, the valve
is in that line at the lower datum, and both surfaces carry the label `P₀`.
-/
structure MatchesPrimaryFigure
    (setup : ConnectedWaterTanksSetup) : Prop where
  tankBOnLeft : setup.figure.side .B = .left
  tankAOnRight : setup.figure.side .A = .right
  higherTankIsB : setup.figure.higherTank = .B
  lowerTankIsA : setup.figure.lowerTank = .A
  heightOffsetMeters : lengthInMeters setup.figure.heightOffset = 1
  tankABottomAtValveElevation :
    lengthInMeters (setup.figure.bottomElevationAboveValve .A) = 0
  tankBBottomRaisedByHeightOffset :
    setup.figure.bottomElevationAboveValve .B = setup.figure.heightOffset
  tankASurfaceLabelIsP0 :
    setup.figure.exposedSurfacePressureLabel .A = setup.atmosphericPressure
  tankBSurfaceLabelIsP0 :
    setup.figure.exposedSurfacePressureLabel .B = setup.atmosphericPressure
  gravityPointsDownward : setup.figure.gravityDirection = .downward
  pipeConnectsBottomA : setup.figure.pipeConnectsTankBottom .A = true
  pipeConnectsBottomB : setup.figure.pipeConnectsTankBottom .B = true
  valveIsOnPipe : setup.figure.valveLiesOnConnectingPipe = true

/--
The conventional environmental calibration implicit in the numerical answer:
one standard atmosphere and `g = 9.81 m/s²`.
-/
structure UsesStandardAtmosphereAndGravity
    (setup : ConnectedWaterTanksSetup) : Prop where
  atmosphereIsStandard :
    setup.atmosphericPressure = DimPressure.standardAtmosphere
  gravityReadout :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 9.81

/-! ## Governing physical laws -/

/-- For incompressible water, mass is density times volume. -/
def ObeysMassDensityRelation
    (density : MassDensityQuantity) (volume : VolumeQuantity)
    (mass : MassQuantity) : Prop :=
  massInKilograms mass =
    massDensityInKilogramsPerCubicMeter density *
      volumeInCubicMeters volume

/-- A vertical cylinder of constant cross-section has volume `area × depth`. -/
def ObeysPrismaticCylinderVolumeLaw
    (area : AreaQuantity) (depth : LengthQuantity)
    (volume : VolumeQuantity) : Prop :=
  volumeInCubicMeters volume =
    areaInSquareMeters area * lengthInMeters depth

/-- The free-surface elevation is the tank-bottom elevation plus water depth. -/
def ObeysFreeSurfaceGeometry
    (bottomElevation waterDepth freeSurfaceElevation : LengthQuantity) : Prop :=
  lengthInMeters freeSurfaceElevation =
    lengthInMeters bottomElevation + lengthInMeters waterDepth

/--
Hydrostatic pressure at the valve datum is
`P = P₀ + ρ g z_surface`, since the valve elevation is zero.
-/
def ObeysHydrostaticPressureLawAtValve
    (atmosphericPressure : PressureQuantity)
    (density : MassDensityQuantity)
    (gravity : AccelerationQuantity)
    (freeSurfaceElevationAboveValve : LengthQuantity)
    (pressureAtValve : PressureQuantity) : Prop :=
  pressureInPascals pressureAtValve =
    pressureInPascals atmosphericPressure +
      massDensityInKilogramsPerCubicMeter density *
        accelerationInMetersPerSecondSquared gravity *
          lengthInMeters freeSurfaceElevationAboveValve

/-!
The initial constitutive and hydrostatic laws, conservation of water volume,
and the open-valve equilibrium laws.  The final numerical pressure and all
answer-choice values are absent from these premises.
-/
structure SatisfiesConnectedTankLaws
    (setup : ConnectedWaterTanksSetup) : Prop where
  initialMassDensityRelation : ∀ tank,
    ObeysMassDensityRelation setup.waterDensity
      (setup.initialWaterState.waterVolume tank)
      (setup.initialWaterMass tank)
  initialCylinderVolume : ∀ tank,
    ObeysPrismaticCylinderVolumeLaw (setup.crossSectionArea tank)
      (setup.initialWaterState.waterDepth tank)
      (setup.initialWaterState.waterVolume tank)
  initialSurfaceGeometry : ∀ tank,
    ObeysFreeSurfaceGeometry
      (setup.figure.bottomElevationAboveValve tank)
      (setup.initialWaterState.waterDepth tank)
      (setup.initialWaterState.freeSurfaceElevationAboveValve tank)
  initialHydrostaticPressure : ∀ tank,
    ObeysHydrostaticPressureLawAtValve setup.atmosphericPressure
      setup.waterDensity setup.gravitationalAcceleration
      (setup.initialWaterState.freeSurfaceElevationAboveValve tank)
      (setup.initialWaterState.pressureAtValveSide tank)
  equilibriumCylinderVolume : ∀ tank,
    ObeysPrismaticCylinderVolumeLaw (setup.crossSectionArea tank)
      (setup.equilibriumWaterState.waterDepth tank)
      (setup.equilibriumWaterState.waterVolume tank)
  waterVolumeConservation :
    volumeInCubicMeters (setup.equilibriumWaterState.waterVolume .A) +
        volumeInCubicMeters (setup.equilibriumWaterState.waterVolume .B) =
      volumeInCubicMeters (setup.initialWaterState.waterVolume .A) +
        volumeInCubicMeters (setup.initialWaterState.waterVolume .B)
  equilibriumSurfaceGeometry : ∀ tank,
    ObeysFreeSurfaceGeometry
      (setup.figure.bottomElevationAboveValve tank)
      (setup.equilibriumWaterState.waterDepth tank)
      (setup.equilibriumWaterState.freeSurfaceElevationAboveValve tank)
  connectedFreeSurfacesHaveEqualElevation :
    setup.equilibriumWaterState.freeSurfaceElevationAboveValve .A =
      setup.equilibriumWaterState.freeSurfaceElevationAboveValve .B
  equilibriumHydrostaticPressure : ∀ tank,
    ObeysHydrostaticPressureLawAtValve setup.atmosphericPressure
      setup.waterDensity setup.gravitationalAcceleration
      (setup.equilibriumWaterState.freeSurfaceElevationAboveValve tank)
      (setup.equilibriumWaterState.pressureAtValveSide tank)
  openValvePressureContinuity :
    setup.equilibriumWaterState.pressureAtValveSide .A =
      setup.equilibriumWaterState.pressureAtValveSide .B

/-! ## Derived relations and requested conclusion -/

/--
Volume conservation and the common free-surface condition determine the final
surface elevation from the two masses, density, areas, and bottom elevations.
-/
lemma equilibrium_free_surface_elevation
    (setup : ConnectedWaterTanksSetup)
    (h_data : MatchesProblemReadouts setup)
    (h_laws : SatisfiesConnectedTankLaws setup) :
    lengthInMeters
        (setup.equilibriumWaterState.freeSurfaceElevationAboveValve .A) =
      ((massInKilograms (setup.initialWaterMass .A) +
            massInKilograms (setup.initialWaterMass .B)) /
          massDensityInKilogramsPerCubicMeter setup.waterDensity +
        areaInSquareMeters (setup.crossSectionArea .A) *
          lengthInMeters (setup.figure.bottomElevationAboveValve .A) +
        areaInSquareMeters (setup.crossSectionArea .B) *
          lengthInMeters (setup.figure.bottomElevationAboveValve .B)) /
        (areaInSquareMeters (setup.crossSectionArea .A) +
          areaInSquareMeters (setup.crossSectionArea .B)) := by
  have hMassA := h_laws.initialMassDensityRelation .A
  have hMassB := h_laws.initialMassDensityRelation .B
  have hVolumeA := h_laws.equilibriumCylinderVolume .A
  have hVolumeB := h_laws.equilibriumCylinderVolume .B
  have hSurfaceA := h_laws.equilibriumSurfaceGeometry .A
  have hSurfaceB := h_laws.equilibriumSurfaceGeometry .B
  have hCommonSurface :=
    congrArg lengthInMeters
      h_laws.connectedFreeSurfacesHaveEqualElevation
  unfold ObeysMassDensityRelation at hMassA hMassB
  unfold ObeysPrismaticCylinderVolumeLaw at hVolumeA hVolumeB
  unfold ObeysFreeSurfaceGeometry at hSurfaceA hSurfaceB
  rw [h_data.tankAMassReadout, h_data.waterDensityReadout] at hMassA
  rw [h_data.tankBMassReadout, h_data.waterDensityReadout] at hMassB
  rw [h_data.tankAAreaReadout] at hVolumeA
  rw [h_data.tankBAreaReadout] at hVolumeB
  rw [h_data.tankAMassReadout, h_data.tankBMassReadout,
    h_data.waterDensityReadout, h_data.tankAAreaReadout,
    h_data.tankBAreaReadout]
  norm_num at hMassA hMassB hVolumeA hVolumeB ⊢
  nlinarith [hMassA, hMassB, hVolumeA, hVolumeB,
    h_laws.waterVolumeConservation, hSurfaceA, hSurfaceB, hCommonSurface]

/-- The initial closed-valve pressure on the lower tank-`A` side. -/
lemma initial_tank_A_valve_pressure
    (setup : ConnectedWaterTanksSetup)
    (h_data : MatchesProblemReadouts setup)
    (h_figure : MatchesPrimaryFigure setup)
    (h_environment : UsesStandardAtmosphereAndGravity setup)
    (h_laws : SatisfiesConnectedTankLaws setup) :
    |pressureInKilopascals
        (setup.initialWaterState.pressureAtValveSide .A) - 111.1| ≤ 0.1 := by
  have hStandardAtmosphere :
      pressureInPascals DimPressure.standardAtmosphere = 101325 := by
    norm_num [pressureInPascals, DimPressure.standardAtmosphere,
      DimPressure.pascal,
      CarriesDimension.toDimensionful_apply_apply]
  have hMassA := h_laws.initialMassDensityRelation .A
  have hVolumeA := h_laws.initialCylinderVolume .A
  have hSurfaceA := h_laws.initialSurfaceGeometry .A
  have hPressureA := h_laws.initialHydrostaticPressure .A
  unfold ObeysMassDensityRelation at hMassA
  unfold ObeysPrismaticCylinderVolumeLaw at hVolumeA
  unfold ObeysFreeSurfaceGeometry at hSurfaceA
  unfold ObeysHydrostaticPressureLawAtValve at hPressureA
  rw [h_data.tankAMassReadout, h_data.waterDensityReadout] at hMassA
  rw [h_data.tankAAreaReadout] at hVolumeA
  rw [h_figure.tankABottomAtValveElevation] at hSurfaceA
  rw [h_environment.atmosphereIsStandard, hStandardAtmosphere,
    h_data.waterDensityReadout, h_environment.gravityReadout] at hPressureA
  have hPressureReadout :
      pressureInPascals
        (setup.initialWaterState.pressureAtValveSide .A) = 111135 := by
    nlinarith [hMassA, hVolumeA, hSurfaceA, hPressureA]
  norm_num [pressureInKilopascals, hPressureReadout]

/-- The initial closed-valve pressure on the raised tank-`B` side. -/
lemma initial_tank_B_valve_pressure
    (setup : ConnectedWaterTanksSetup)
    (h_data : MatchesProblemReadouts setup)
    (h_figure : MatchesPrimaryFigure setup)
    (h_environment : UsesStandardAtmosphereAndGravity setup)
    (h_laws : SatisfiesConnectedTankLaws setup) :
    |pressureInKilopascals
        (setup.initialWaterState.pressureAtValveSide .B) - 130.8| ≤ 0.1 := by
  have hStandardAtmosphere :
      pressureInPascals DimPressure.standardAtmosphere = 101325 := by
    norm_num [pressureInPascals, DimPressure.standardAtmosphere,
      DimPressure.pascal,
      CarriesDimension.toDimensionful_apply_apply]
  have hBottomB :
      lengthInMeters (setup.figure.bottomElevationAboveValve .B) = 1 := by
    rw [h_figure.tankBBottomRaisedByHeightOffset]
    exact h_figure.heightOffsetMeters
  have hMassB := h_laws.initialMassDensityRelation .B
  have hVolumeB := h_laws.initialCylinderVolume .B
  have hSurfaceB := h_laws.initialSurfaceGeometry .B
  have hPressureB := h_laws.initialHydrostaticPressure .B
  unfold ObeysMassDensityRelation at hMassB
  unfold ObeysPrismaticCylinderVolumeLaw at hVolumeB
  unfold ObeysFreeSurfaceGeometry at hSurfaceB
  unfold ObeysHydrostaticPressureLawAtValve at hPressureB
  rw [h_data.tankBMassReadout, h_data.waterDensityReadout] at hMassB
  rw [h_data.tankBAreaReadout] at hVolumeB
  rw [hBottomB] at hSurfaceB
  rw [h_environment.atmosphereIsStandard, hStandardAtmosphere,
    h_data.waterDensityReadout, h_environment.gravityReadout] at hPressureB
  have hPressureReadout :
      pressureInPascals
        (setup.initialWaterState.pressureAtValveSide .B) = 130755 := by
    nlinarith [hMassB, hVolumeB, hSurfaceB, hPressureB]
  norm_num [pressureInKilopascals, hPressureReadout]

/-- Labels of the four pressure choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Kilopascal value printed beside each answer-choice label. -/
def AnswerChoice.pressureInKilopascals : AnswerChoice → ℝ
  | .A => 490
  | .B => 125.2
  | .C => 154
  | .D => 10.2

/--
Agreement with a displayed answer to its stated `0.1 kPa` precision.  The
tolerance makes explicit that the source reports a rounded textbook value.
-/
def MatchesDisplayedAnswer
    (setup : ConnectedWaterTanksSetup) (choice : AnswerChoice) : Prop :=
  |pressureInKilopascals (finalValvePressure setup) -
      choice.pressureInKilopascals| ≤ 0.1

/--
After the valve is opened, the final valve pressure agrees with `125.2 kPa`
to the precision displayed by answer choice `B`.

This formalizes `thm:physics:phyx_mini_0389:target`.
-/
theorem problem_phyx_mini_0389
    (setup : ConnectedWaterTanksSetup)
    (h_data : MatchesProblemReadouts setup)
    (h_figure : MatchesPrimaryFigure setup)
    (h_environment : UsesStandardAtmosphereAndGravity setup)
    (h_laws : SatisfiesConnectedTankLaws setup) :
    MatchesDisplayedAnswer setup .B := by
  have hStandardAtmosphere :
      pressureInPascals DimPressure.standardAtmosphere = 101325 := by
    norm_num [pressureInPascals, DimPressure.standardAtmosphere,
      DimPressure.pascal,
      CarriesDimension.toDimensionful_apply_apply]
  have hBottomB :
      lengthInMeters (setup.figure.bottomElevationAboveValve .B) = 1 := by
    rw [h_figure.tankBBottomRaisedByHeightOffset]
    exact h_figure.heightOffsetMeters
  have hSurface :=
    equilibrium_free_surface_elevation setup h_data h_laws
  rw [h_data.tankAMassReadout, h_data.tankBMassReadout,
    h_data.waterDensityReadout, h_data.tankAAreaReadout,
    h_data.tankBAreaReadout, h_figure.tankABottomAtValveElevation,
    hBottomB] at hSurface
  norm_num at hSurface
  have hPressure := h_laws.equilibriumHydrostaticPressure .A
  unfold ObeysHydrostaticPressureLawAtValve at hPressure
  rw [h_environment.atmosphereIsStandard, hStandardAtmosphere,
    h_data.waterDensityReadout, h_environment.gravityReadout,
    hSurface] at hPressure
  have hPressureReadout :
      pressureInPascals (finalValvePressure setup) =
        (876045 / 7 : ℝ) := by
    norm_num at hPressure
    simpa [finalValvePressure] using hPressure
  norm_num [MatchesDisplayedAnswer, AnswerChoice.pressureInKilopascals,
    pressureInKilopascals, hPressureReadout]

end PhyXMiniProblems.ProblemPhyXMini0389
