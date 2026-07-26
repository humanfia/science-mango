import Mathlib.Data.Real.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0393

open Dimension

/-!
# Ground-level pump pressure for a pressurized water tower

The primary figure shows water in an elevated bulb-shaped tank and its narrow
vertical riser.  The water surface is a height `H` above the ground line, and
the arrow labelled `g` points downward.  The prose specifies `H = 25 m`, a
headspace-air pressure of `125 kPa`, water density `1000 kg/m^3`, and standard
textbook gravity.  Hydrostatics therefore determines the water pressure at the
ground-level inlet; the minimum pump outlet pressure is the pressure that
balances this inlet pressure.

All basic physical quantities are unit-independent dimensionful quantities.
Real numbers occur only as explicitly named unit readouts and displayed answer
values.
-/

/-! ## Dimensionful physical quantities and calibrated readouts -/

/-- The physical dimension of mass density, `M L^-3`. -/
def massDensityDimension : Dimension :=
  M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- The physical dimension of acceleration, `L T^-2`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length, independent of the readout unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, spatially uniform mass density. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful (WithDim massDensityDimension NNReal)

/-- A nonnegative acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Physical pressure, represented by Physlib's dimensionful pressure type. -/
abbrev PressureQuantity : Type := DimPressure

/-- Read a physical length in the selected length unit. -/
def lengthReadout (lengthUnit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := lengthUnit}).val : ℝ)

/-- Read mass density in the selected mass unit per selected length unit cubed. -/
def densityReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (density : MassDensityQuantity) : ℝ :=
  ((density {UnitChoices.SI with
    mass := massUnit, length := lengthUnit}).val : ℝ)

/-- Read acceleration in the selected length and time units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read pressure in the coherent unit induced by the selected base units. -/
def pressureReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (pressure : PressureQuantity) : ℝ :=
  (pressure {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Kilogram-per-cubic-metre readout of a uniform mass density. -/
def densityInKilogramsPerCubicMeter (density : MassDensityQuantity) : ℝ :=
  densityReadout MassUnit.kilograms LengthUnit.meters density

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-- Pascal readout of a physical pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  pressureReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds pressure

/-- Kilopascal readout of a physical pressure. -/
def pressureInKilopascals (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure / 1000

/-! ## Primary-figure labels and physical setup -/

/-- Literal labels visible in the primary bitmap. -/
inductive FigureLabel where
  | g
  | H
  deriving DecidableEq, Fintype, Repr

/-- Vertical directions used to interpret arrows in the figure. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Qualitative tower shape visible in the primary bitmap. -/
inductive TowerGeometry where
  | elevatedRoundedTankWithNarrowRiser
  | other
  deriving DecidableEq, Repr

/-- The liquid stored and pumped through the tower. -/
inductive TowerLiquid where
  | water
  | other
  deriving DecidableEq, Repr

/-- The gas occupying the pressurized headspace above the water surface. -/
inductive HeadspaceGas where
  | air
  | other
  deriving DecidableEq, Repr

/-- Typed qualitative and dimensionful information read from the bitmap. -/
structure WaterTowerFigure where
  labelShown : FigureLabel → Bool
  markedHeightH : LengthQuantity
  gravityArrowDirection : VerticalDirection
  geometry : TowerGeometry
  groundLineShown : Bool
  waterSurfaceShown : Bool
  waterFillShown : Bool
  heightArrowStartsAtGround : Bool
  heightArrowEndsAtWaterSurface : Bool

/-!
Independent physical quantities of the tower and pump.  In particular, the
ground water pressure and the minimum required pump pressure are independent
fields; neither is defined from the recorded answer.
-/
structure WaterTowerSetup where
  figure : WaterTowerFigure
  liquid : TowerLiquid
  headspaceGas : HeadspaceGas
  waterSurfaceHeightAboveGround : LengthQuantity
  waterMassDensity : MassDensityQuantity
  gravitationalAcceleration : AccelerationQuantity
  headspaceAirPressureAtSurface : PressureQuantity
  waterPressureAtGroundInlet : PressureQuantity
  minimumPumpOutletPressureAtGround : PressureQuantity
  tankPressurized : Bool
  pumpInletAtGroundLevel : Bool

/-! ## Figure/data readouts and physical assumptions -/

/-!
Evidence read from the primary bitmap.  It records the labels `g` and `H`, the
downward gravity arrow, and the endpoints and physical role of the height
mark.  It gives no numerical pressure answer.
-/
structure MatchesPrimaryFigure (setup : WaterTowerSetup) : Prop where
  everyLabelShown : ∀ label, setup.figure.labelShown label = true
  heightMarkMatchesWaterSurfaceHeight :
    setup.figure.markedHeightH = setup.waterSurfaceHeightAboveGround
  gravityArrowPointsDown :
    setup.figure.gravityArrowDirection = .downward
  picturedGeometry :
    setup.figure.geometry = .elevatedRoundedTankWithNarrowRiser
  groundLineIsShown : setup.figure.groundLineShown = true
  waterSurfaceIsShown : setup.figure.waterSurfaceShown = true
  waterFillIsShown : setup.figure.waterFillShown = true
  heightStartsAtGround : setup.figure.heightArrowStartsAtGround = true
  heightEndsAtSurface : setup.figure.heightArrowEndsAtWaterSurface = true

/-! Qualitative information supplied by the problem prose. -/
structure MatchesWaterTowerScenario (setup : WaterTowerSetup) : Prop where
  liquidIsWater : setup.liquid = .water
  headspaceContainsAir : setup.headspaceGas = .air
  towerIsPressurized : setup.tankPressurized = true
  inletIsAtGroundLevel : setup.pumpInletAtGroundLevel = true

/-!
Numerical problem data.  `49/5 m/s^2` is the `9.8 m/s^2` textbook value of
standard gravity used by the recorded multiple-choice answer.  No field fixes
the ground-level water pressure or the required pump pressure.
-/
structure UsesGivenWaterTowerData (setup : WaterTowerSetup) : Prop where
  waterSurfaceHeightMeters :
    lengthInMeters setup.waterSurfaceHeightAboveGround = 25
  headspaceAirPressureKilopascals :
    pressureInKilopascals setup.headspaceAirPressureAtSurface = 125
  waterDensityKilogramsPerCubicMeter :
    densityInKilogramsPerCubicMeter setup.waterMassDensity = 1000
  standardGravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 49 / 5

/-! Positivity conditions for a physically meaningful tower and pump state. -/
structure HasPhysicalWaterTowerParameters (setup : WaterTowerSetup) : Prop where
  heightPositive : 0 < lengthInMeters setup.waterSurfaceHeightAboveGround
  waterDensityPositive :
    0 < densityInKilogramsPerCubicMeter setup.waterMassDensity
  gravityMagnitudePositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  headspacePressurePositive :
    0 < pressureInPascals setup.headspaceAirPressureAtSurface
  groundWaterPressurePositive :
    0 < pressureInPascals setup.waterPressureAtGroundInlet
  minimumPumpPressurePositive :
    0 < pressureInPascals setup.minimumPumpOutletPressureAtGround

/-!
The governing hydrostatic and pump-threshold laws.  The first relation is
`p_ground = p_surface + rho * g * H`, stated in every coherent choice of mass,
length, and time units.  The second says that the minimum pump outlet pressure
balances the water pressure at the ground inlet.  Neither law mentions
`370 kPa` or an answer label.
-/
structure SatisfiesHydrostaticPumpLaws (setup : WaterTowerSetup) : Prop where
  hydrostaticPressureAtGround :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      pressureReadout massUnit lengthUnit timeUnit
          setup.waterPressureAtGroundInlet =
        pressureReadout massUnit lengthUnit timeUnit
            setup.headspaceAirPressureAtSurface +
          densityReadout massUnit lengthUnit setup.waterMassDensity *
            accelerationReadout lengthUnit timeUnit
              setup.gravitationalAcceleration *
            lengthReadout lengthUnit setup.waterSurfaceHeightAboveGround
  minimumPumpPressureBalancesInlet :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      pressureReadout massUnit lengthUnit timeUnit
          setup.minimumPumpOutletPressureAtGround =
        pressureReadout massUnit lengthUnit timeUnit
          setup.waterPressureAtGroundInlet

/-!
The pressure head contributed by the elevated water column, expressed in
pascals.  This is a derived intermediate expression, not the requested pump
pressure.
-/
def hydrostaticPressureHeadInPascals (setup : WaterTowerSetup) : ℝ :=
  densityInKilogramsPerCubicMeter setup.waterMassDensity *
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
    lengthInMeters setup.waterSurfaceHeightAboveGround

/-!
A pump pressure strictly above the equilibrium threshold drives additional
water into the tower.  The multiple-choice question asks for the threshold,
not for an arbitrary operating pressure satisfying this predicate.
-/
def CanPumpMoreWater
    (setup : WaterTowerSetup) (pumpOutletPressure : PressureQuantity) : Prop :=
  pressureInPascals setup.minimumPumpOutletPressureAtGround <
    pressureInPascals pumpOutletPressure

/-! ## Displayed answer choices and target conclusions -/

/-- Labels of the four pressure choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Pressure in kilopascals printed beside each answer label. -/
def AnswerChoice.displayedPressureKilopascals : AnswerChoice → ℝ
  | .A => 490
  | .B => 370
  | .C => 154
  | .D => 51 / 5

/-- A choice is correct when it displays the physical pump-pressure threshold. -/
def IsCorrectAnswer
    (setup : WaterTowerSetup) (choice : AnswerChoice) : Prop :=
  pressureInKilopascals setup.minimumPumpOutletPressureAtGround =
    choice.displayedPressureKilopascals

/-- The `25 m` water column contributes `245 kPa` of hydrostatic head. -/
lemma hydrostaticPressureHeadInPascals_eq_245000
    (setup : WaterTowerSetup)
    (h_data : UsesGivenWaterTowerData setup) :
    hydrostaticPressureHeadInPascals setup = 245000 := by
  unfold hydrostaticPressureHeadInPascals
  rw [h_data.waterDensityKilogramsPerCubicMeter,
    h_data.standardGravityMetersPerSecondSquared,
    h_data.waterSurfaceHeightMeters]
  norm_num

/-- Hydrostatics makes the ground-inlet water pressure `370 kPa`. -/
lemma waterPressureAtGroundInKilopascals_eq_370
    (setup : WaterTowerSetup)
    (h_data : UsesGivenWaterTowerData setup)
    (h_laws : SatisfiesHydrostaticPumpLaws setup) :
    pressureInKilopascals setup.waterPressureAtGroundInlet = 370 := by
  have h_hydro := h_laws.hydrostaticPressureAtGround
    MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  change pressureInPascals setup.waterPressureAtGroundInlet =
    pressureInPascals setup.headspaceAirPressureAtSurface +
      densityInKilogramsPerCubicMeter setup.waterMassDensity *
        accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
          lengthInMeters setup.waterSurfaceHeightAboveGround at h_hydro
  rw [h_data.waterDensityKilogramsPerCubicMeter,
    h_data.standardGravityMetersPerSecondSquared,
    h_data.waterSurfaceHeightMeters] at h_hydro
  norm_num at h_hydro
  have h_surface := h_data.headspaceAirPressureKilopascals
  unfold pressureInKilopascals at h_surface ⊢
  linarith

/-- The minimum ground-level pump outlet pressure is `370 kPa`. -/
lemma minimumPumpOutletPressureInKilopascals_eq_370
    (setup : WaterTowerSetup)
    (h_data : UsesGivenWaterTowerData setup)
    (h_laws : SatisfiesHydrostaticPumpLaws setup) :
    pressureInKilopascals setup.minimumPumpOutletPressureAtGround = 370 := by
  have h_balance := h_laws.minimumPumpPressureBalancesInlet
    MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  change pressureInPascals setup.minimumPumpOutletPressureAtGround =
    pressureInPascals setup.waterPressureAtGroundInlet at h_balance
  unfold pressureInKilopascals
  rw [h_balance]
  exact waterPressureAtGroundInKilopascals_eq_370 setup h_data h_laws

/-!
The pressurized headspace contributes `125 kPa` and the water column
contributes `245 kPa`, so the minimum pressure needed at the ground-level
inlet is `370 kPa`; this is choice B.

This is the Lean declaration corresponding to
`thm:physics:phyx_mini_0393:target`.  Neither `370 kPa` nor choice B occurs in
the setup, figure/data assumptions, positivity assumptions, or governing-law
interface.
-/
theorem problem_phyx_mini_0393
    (setup : WaterTowerSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_scenario : MatchesWaterTowerScenario setup)
    (h_data : UsesGivenWaterTowerData setup)
    (_physical : HasPhysicalWaterTowerParameters setup)
    (h_laws : SatisfiesHydrostaticPumpLaws setup) :
    pressureInKilopascals setup.minimumPumpOutletPressureAtGround = 370 ∧
      IsCorrectAnswer setup .B := by
  have h_pressure :=
    minimumPumpOutletPressureInKilopascals_eq_370 setup h_data h_laws
  constructor
  · exact h_pressure
  · simpa [IsCorrectAnswer, AnswerChoice.displayedPressureKilopascals] using
      h_pressure

end PhyXMiniProblems.ProblemPhyXMini0393
