import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Isothermal compression by a brick on a frictionless disk

This file models problem `phyx_mini_0333`.  A circular disk seals an ideal gas
inside a vertical cylindrical tank in an evacuated enclosure.  The disk is in
mechanical equilibrium first by itself and then with a lead brick on top.

Physical lengths, masses, areas, volumes, pressures, accelerations,
temperatures, and the gas constant carry Physlib dimensions independently of
the choice of units.  Real numbers are used only for explicitly named SI
readouts, the amount-of-substance readout in moles (a base dimension not
present in Physlib's current `Dimension`), and the displayed answer values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0333

open Dimension

/-! ## Dimensionful quantities and named SI readouts -/

/-- A physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- A nonnegative physical area. -/
abbrev AreaQuantity : Type := DimArea

/-- A physical volume, carrying the length-cubed dimension. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- A physical pressure. -/
abbrev PressureQuantity : Type := DimPressure

/-- A physical acceleration, used for the local gravitational acceleration. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- An absolute-temperature quantity carrying Physlib's temperature dimension. -/
abbrev TemperatureQuantity : Type :=
  Dimensionful (WithDim Θ𝓭 ℝ)

/--
The molar gas constant, with energy-per-temperature dimension.  Its omitted
inverse-mole dimension is paired with the explicitly molar scalar readout in
`amountOfGasMoles` below because Physlib currently has no amount-of-substance
component in `Dimension`.
-/
abbrev MolarGasConstantQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  (mass UnitChoices.SI).val

/-- Square-metre readout of a physical area. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  (volume UnitChoices.SI).val

/-- Pascal readout of a physical pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Metres-per-second-squared readout of a physical acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  (acceleration UnitChoices.SI).val

/-- Kelvin readout of a dimensionful temperature. -/
def temperatureInKelvin (temperature : TemperatureQuantity) : ℝ :=
  (temperature UnitChoices.SI).val

/-- SI readout of the molar gas constant. -/
def molarGasConstantInSI (gasConstant : MolarGasConstantQuantity) : ℝ :=
  (gasConstant UnitChoices.SI).val

/-! ## Physical roles, equilibrium states, and figure labels -/

/-- The two rest states compared in the problem. -/
inductive EquilibriumState where
  /-- The initial equilibrium with only the disk loading the gas. -/
  | diskOnly
  /-- The later equilibrium after the brick has been placed on the disk. -/
  | diskAndBrick
  deriving DecidableEq, Repr

/-- Shape of the tank indicated by the primary figure and prose. -/
inductive TankShape where
  | verticalCircularCylinder
  deriving DecidableEq, Repr

/-- Shape of the movable seal. -/
inductive DiskShape where
  | circular
  deriving DecidableEq, Repr

/-- Constraint on the disk's allowed motion. -/
inductive DiskGuide where
  | verticalAndFrictionless
  deriving DecidableEq, Repr

/-- Material model of the gas under the disk. -/
inductive GasModel where
  | ideal
  deriving DecidableEq, Repr

/-- Medium above the disk inside the outer enclosure. -/
inductive AboveDiskMedium where
  | vacuum
  deriving DecidableEq, Repr

/-- How the additional load is applied. -/
inductive BrickPlacementProtocol where
  | gently
  deriving DecidableEq, Repr

/-- Vertical direction of the disk immediately after the brick is placed. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/--
The tank, disk, brick, gas variables, and labels `D`, `h`, and `T` appearing in
the problem and primary figure.

The two cases of `EquilibriumState` represent the initially resting disk and
the disk when it again comes to rest.  Their heights are independent fields;
in particular, the final height is not assigned its requested value here.
-/
structure IsothermalDiskTank where
  tankShape : TankShape
  diskShape : DiskShape
  diskGuide : DiskGuide
  gasModel : GasModel
  aboveDiskMedium : AboveDiskMedium
  brickPlacement : BrickPlacementProtocol
  motionImmediatelyAfterPlacement : VerticalDirection
  /-- Figure label `D`, the internal diameter of the cylindrical tank. -/
  cylinderDiameterD : LengthQuantity
  /-- Horizontal circular area shared by the disk and gas column. -/
  diskCrossSectionalArea : AreaQuantity
  diskMass : MassQuantity
  brickMass : MassQuantity
  localGravitationalAcceleration : AccelerationQuantity
  /-- Figure label `h`, indexed by the two equilibrium states. -/
  gasColumnHeight : EquilibriumState → LengthQuantity
  gasVolume : EquilibriumState → VolumeQuantity
  gasPressure : EquilibriumState → PressureQuantity
  pressureAboveDisk : EquilibriumState → PressureQuantity
  /-- Figure label `T`, allowed as a state variable before isothermality is imposed. -/
  gasTemperatureT : EquilibriumState → TemperatureQuantity
  /-- Scalar amount-of-substance readout in moles. -/
  amountOfGasMoles : EquilibriumState → ℝ
  molarGasConstant : MolarGasConstantQuantity

/--
The mass supported by the gas in each rest state.  This definition only
unpacks which bodies are present; it does not prescribe either gas height.
-/
def supportedMassInKilograms
    (setup : IsothermalDiskTank) : EquilibriumState → ℝ
  | .diskOnly => massInKilograms setup.diskMass
  | .diskAndBrick =>
      massInKilograms setup.diskMass + massInKilograms setup.brickMass

/-! ## Assumptions supplied by the problem -/

/--
Qualitative model choices, the three numerical readouts, and the primary
figure's circular cross-section relation.  The final height does not occur.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : IsothermalDiskTank) : Prop where
  tankIsVerticalCircularCylinder :
    setup.tankShape = .verticalCircularCylinder
  diskIsCircular : setup.diskShape = .circular
  diskMovesVerticallyWithoutFriction :
    setup.diskGuide = .verticalAndFrictionless
  gasIsIdeal : setup.gasModel = .ideal
  enclosureAboveDiskIsEvacuated : setup.aboveDiskMedium = .vacuum
  brickIsPlacedGently : setup.brickPlacement = .gently
  diskInitiallyMovesDownward :
    setup.motionImmediatelyAfterPlacement = .downward
  diskMassIsThreeKilograms : massInKilograms setup.diskMass = 3
  brickMassIsNineKilograms : massInKilograms setup.brickMass = 9
  initialHeightIsFourMeters :
    lengthInMeters (setup.gasColumnHeight .diskOnly) = 4
  circularCrossSectionFromDiameter :
    areaInSquareMeters setup.diskCrossSectionalArea =
      Real.pi * (lengthInMeters setup.cylinderDiameterD / 2) ^ 2
  vacuumPressureInBothStates :
    ∀ state, pressureInPascals (setup.pressureAboveDisk state) = 0

/-- The stated isothermal and sealed operating conditions. -/
structure IsKeptIsothermalAndSealed
    (setup : IsothermalDiskTank) : Prop where
  temperatureIsConstant :
    temperatureInKelvin (setup.gasTemperatureT .diskOnly) =
      temperatureInKelvin (setup.gasTemperatureT .diskAndBrick)
  noGasEscapes :
    setup.amountOfGasMoles .diskOnly =
      setup.amountOfGasMoles .diskAndBrick

/-- Positivity conditions selecting the physical branch of the model. -/
structure HasPhysicalParameters
    (setup : IsothermalDiskTank) : Prop where
  diameterPositive : 0 < lengthInMeters setup.cylinderDiameterD
  areaPositive : 0 < areaInSquareMeters setup.diskCrossSectionalArea
  diskMassPositive : 0 < massInKilograms setup.diskMass
  brickMassPositive : 0 < massInKilograms setup.brickMass
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.localGravitationalAcceleration
  heightPositive :
    ∀ state, 0 < lengthInMeters (setup.gasColumnHeight state)
  volumePositive :
    ∀ state, 0 < volumeInCubicMeters (setup.gasVolume state)
  gasPressurePositive :
    ∀ state, 0 < pressureInPascals (setup.gasPressure state)
  temperaturePositive :
    ∀ state, 0 < temperatureInKelvin (setup.gasTemperatureT state)
  gasAmountPositive :
    ∀ state, 0 < setup.amountOfGasMoles state
  molarGasConstantPositive :
    0 < molarGasConstantInSI setup.molarGasConstant

/--
The governing cylinder-geometry, ideal-gas, and static force-balance laws.

The ideal-gas equation is written in compatible SI readouts as `P V = n R T`.
The equilibrium equation is `(P_gas - P_above) A = m_supported g`; the vacuum
pressure itself is supplied separately by `MatchesProblemAndPrimaryFigure`.
Neither law fixes the final height.
-/
structure SatisfiesIdealGasAndMechanicalLaws
    (setup : IsothermalDiskTank) : Prop where
  cylindricalGasVolume :
    ∀ state,
      volumeInCubicMeters (setup.gasVolume state) =
        areaInSquareMeters setup.diskCrossSectionalArea *
          lengthInMeters (setup.gasColumnHeight state)
  idealGasLaw :
    ∀ state,
      pressureInPascals (setup.gasPressure state) *
          volumeInCubicMeters (setup.gasVolume state) =
        setup.amountOfGasMoles state *
          molarGasConstantInSI setup.molarGasConstant *
            temperatureInKelvin (setup.gasTemperatureT state)
  mechanicalEquilibrium :
    ∀ state,
      (pressureInPascals (setup.gasPressure state) -
          pressureInPascals (setup.pressureAboveDisk state)) *
          areaInSquareMeters setup.diskCrossSectionalArea =
        supportedMassInKilograms setup state *
          accelerationInMetersPerSecondSquared
            setup.localGravitationalAcceleration

/-! ## Displayed choices and requested conclusion -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Metre value printed beside each answer label. -/
def answerHeightInMeters : AnswerChoice → ℝ
  | .A => 1
  | .B => 3 / 2
  | .C => 8 / 5
  | .D => 19 / 10

/-- The answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .A

/--
At the second equilibrium, the disk is one metre above the tank bottom,
which is displayed answer A.

Blueprint label: `thm:physics:phyx_mini_0333:target`.
-/
theorem finalDiskHeight_eq_one_meter
    (setup : IsothermalDiskTank)
    (_figure : MatchesProblemAndPrimaryFigure setup)
    (_operatingConditions : IsKeptIsothermalAndSealed setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesIdealGasAndMechanicalLaws setup) :
    lengthInMeters (setup.gasColumnHeight .diskAndBrick) = 1 := by
  have h_mechanical_initial :=
    _laws.mechanicalEquilibrium EquilibriumState.diskOnly
  have h_mechanical_final :=
    _laws.mechanicalEquilibrium EquilibriumState.diskAndBrick
  simp only [supportedMassInKilograms] at h_mechanical_initial h_mechanical_final
  rw [_figure.vacuumPressureInBothStates EquilibriumState.diskOnly,
      _figure.diskMassIsThreeKilograms] at h_mechanical_initial
  rw [_figure.vacuumPressureInBothStates EquilibriumState.diskAndBrick,
      _figure.diskMassIsThreeKilograms,
      _figure.brickMassIsNineKilograms] at h_mechanical_final
  norm_num at h_mechanical_initial h_mechanical_final

  have h_area_ne :
      areaInSquareMeters setup.diskCrossSectionalArea ≠ 0 :=
    ne_of_gt _physical.areaPositive
  have h_pressure_ratio :
      pressureInPascals (setup.gasPressure .diskAndBrick) =
        4 * pressureInPascals (setup.gasPressure .diskOnly) := by
    apply mul_left_cancel₀ h_area_ne
    nlinarith [h_mechanical_initial, h_mechanical_final]

  have h_pressure_volume :
      pressureInPascals (setup.gasPressure .diskOnly) *
          volumeInCubicMeters (setup.gasVolume .diskOnly) =
        pressureInPascals (setup.gasPressure .diskAndBrick) *
          volumeInCubicMeters (setup.gasVolume .diskAndBrick) := by
    calc
      pressureInPascals (setup.gasPressure .diskOnly) *
            volumeInCubicMeters (setup.gasVolume .diskOnly) =
          setup.amountOfGasMoles .diskOnly *
            molarGasConstantInSI setup.molarGasConstant *
              temperatureInKelvin (setup.gasTemperatureT .diskOnly) :=
        _laws.idealGasLaw EquilibriumState.diskOnly
      _ = setup.amountOfGasMoles .diskAndBrick *
            molarGasConstantInSI setup.molarGasConstant *
              temperatureInKelvin (setup.gasTemperatureT .diskAndBrick) := by
        rw [_operatingConditions.noGasEscapes,
          _operatingConditions.temperatureIsConstant]
      _ = pressureInPascals (setup.gasPressure .diskAndBrick) *
            volumeInCubicMeters (setup.gasVolume .diskAndBrick) :=
        (_laws.idealGasLaw EquilibriumState.diskAndBrick).symm

  have h_volume_initial :=
    _laws.cylindricalGasVolume EquilibriumState.diskOnly
  have h_volume_final :=
    _laws.cylindricalGasVolume EquilibriumState.diskAndBrick
  rw [_figure.initialHeightIsFourMeters] at h_volume_initial
  rw [h_volume_initial, h_volume_final] at h_pressure_volume
  have h_height_pressure :
      4 * pressureInPascals (setup.gasPressure .diskOnly) =
        pressureInPascals (setup.gasPressure .diskAndBrick) *
          lengthInMeters (setup.gasColumnHeight .diskAndBrick) := by
    apply mul_left_cancel₀ h_area_ne
    nlinarith [h_pressure_volume]
  rw [h_pressure_ratio] at h_height_pressure

  have h_initial_pressure_ne :
      pressureInPascals (setup.gasPressure .diskOnly) ≠ 0 :=
    ne_of_gt (_physical.gasPressurePositive EquilibriumState.diskOnly)
  have h_four :
      (4 : ℝ) =
        4 * lengthInMeters (setup.gasColumnHeight .diskAndBrick) := by
    apply mul_left_cancel₀ h_initial_pressure_ne
    nlinarith [h_height_pressure]
  nlinarith

end PhyXMiniProblems.ProblemPhyXMini0333
