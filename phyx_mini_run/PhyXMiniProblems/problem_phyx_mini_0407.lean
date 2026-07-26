import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Work on nitrogen beneath a rising copper piston

This file models problem `phyx_mini_0407`.  A movable copper piston closes a
vertical circular cylinder of nitrogen, and the region above the piston is a
vacuum.  The primary figure shows a `6.0 cm` internal diameter and a `20 cm`
initial gas-column height; the prose additionally gives a `4.0 cm` piston
thickness and an initial gas temperature of `20 °C`.

The source does not state a final piston height, a rise distance, or a final
temperature.  Consequently the main theorem records the work as a function
of the (positive) rise and proves its sign under the convention that work on
the gas is positive.  It does not manufacture the missing endpoint in order
to select the recorded numerical answer.

Physical lengths, masses, mass densities, areas, volumes, pressures,
accelerations, temperatures, and energies retain their Physlib dimensions.
Real numbers are used only for named SI readouts, the amount in moles, the
molar gas constant's SI readout, and displayed answer values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0407

open Dimension

/-! ## Dimensionful quantities and SI readouts -/

/-- A physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- A physical mass density, with dimension mass per volume. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹) ℝ)

/-- A physical volume, with length-cubed dimension. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- A physical acceleration, used for local gravitational acceleration. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- An absolute thermodynamic temperature. -/
abbrev TemperatureQuantity : Type := Dimensionful (WithDim Θ𝓭 ℝ)

/-- A molar gas constant, omitting only Physlib's unavailable mole dimension. -/
abbrev MolarGasConstantQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  (mass UnitChoices.SI).val

/-- Kilogram-per-cubic-metre readout of a physical mass density. -/
def massDensityInKilogramsPerCubicMeter
    (density : MassDensityQuantity) : ℝ :=
  (density UnitChoices.SI).val

/-- Square-metre readout of a nonnegative physical area. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  (volume UnitChoices.SI).val

/-- Pascal readout of a physical pressure. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Metres-per-second-squared readout of a physical acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  (acceleration UnitChoices.SI).val

/-- Kelvin readout of an absolute thermodynamic temperature. -/
def temperatureInKelvins (temperature : TemperatureQuantity) : ℝ :=
  (temperature UnitChoices.SI).val

/-- Celsius readout obtained from the kelvin readout by the standard offset. -/
def temperatureInDegreesCelsius (temperature : TemperatureQuantity) : ℝ :=
  temperatureInKelvins temperature - 27315 / 100

/-- SI readout of the molar gas constant in joules per mole-kelvin. -/
def molarGasConstantInSI (gasConstant : MolarGasConstantQuantity) : ℝ :=
  (gasConstant UnitChoices.SI).val

/-- Joule readout of a signed physical energy. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Physical roles, process states, and primary-figure labels -/

/-!
The real parameter `τ` used below is normalized process progress: `τ = 0` is
the initial state and `τ = 1` is the final state.  Only the interval
`Set.Icc 0 1` is physically relevant.  Keeping the intermediate states makes
the constant-pressure boundary-work hypothesis a statement about the whole
rise rather than merely about its endpoints.
-/

/-- The gas species stated in the problem and printed in the figure. -/
inductive GasSpecies where
  | nitrogenN2
  deriving DecidableEq, Repr

/-- The material of the movable piston. -/
inductive PistonMaterial where
  | copper
  deriving DecidableEq, Repr

/-- Orientation of the cylindrical apparatus. -/
inductive CylinderOrientation where
  | vertical
  deriving DecidableEq, Repr

/-- Medium occupying the region above the piston. -/
inductive AbovePistonMedium where
  | vacuum
  deriving DecidableEq, Repr

/-- Kinematic role of the piston stated in the prose. -/
inductive PistonMobility where
  | movableVertically
  deriving DecidableEq, Repr

/-- Direction of the process named in the question. -/
inductive VerticalMotion where
  | rises
  deriving DecidableEq, Repr

/-- Text labels visible in the primary raster. -/
inductive FigureRegionLabel where
  | vacuum
  | piston
  | nitrogenN2
  deriving DecidableEq, Repr

/-!
The cylinder, piston, gas states, and signed work quantities.

`workByGas` is positive when the gas transfers mechanical energy to the
piston.  `workOnGas` is positive when the environment transfers mechanical
energy to the gas; the governing laws below relate the two by a minus sign.
-/
structure CopperPistonNitrogenCylinder where
  gasSpecies : GasSpecies
  pistonMaterial : PistonMaterial
  cylinderOrientation : CylinderOrientation
  abovePistonMedium : AbovePistonMedium
  pistonMobility : PistonMobility
  processMotion : VerticalMotion
  cylinderDiameter : LengthQuantity
  pistonThickness : LengthQuantity
  pistonCrossSectionalArea : DimArea
  pistonVolume : VolumeQuantity
  pistonMassDensity : MassDensityQuantity
  pistonMass : MassQuantity
  localGravitationalAcceleration : AccelerationQuantity
  pistonBottomHeight : ℝ → LengthQuantity
  gasVolume : ℝ → VolumeQuantity
  gasPressure : ℝ → DimPressure
  pressureAbovePiston : ℝ → DimPressure
  gasTemperature : ℝ → TemperatureQuantity
  amountOfGasMoles : ℝ
  molarGasConstant : MolarGasConstantQuantity
  workByGas : DimEnergy
  workOnGas : DimEnergy
  upperRegionLabel : FigureRegionLabel
  pistonRegionLabel : FigureRegionLabel
  lowerRegionLabel : FigureRegionLabel

/-! ## Source data, physical branch, and governing laws -/

/-!
The qualitative setup and exact decimal readouts supplied by the prose and
primary image.  The image's `20 cm` arrow runs from the cylinder bottom to the
underside of the piston, so it is recorded as the initial gas-column height.
No field mentions the final height, rise distance, final temperature, piston
density, gravitational acceleration, work, or an answer choice.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : CopperPistonNitrogenCylinder) : Prop where
  gasIsNitrogen : setup.gasSpecies = .nitrogenN2
  pistonIsCopper : setup.pistonMaterial = .copper
  cylinderIsVertical : setup.cylinderOrientation = .vertical
  regionAbovePistonIsVacuum : setup.abovePistonMedium = .vacuum
  pistonIsMovable : setup.pistonMobility = .movableVertically
  processIsARise : setup.processMotion = .rises
  diameterIsSixCentimeters :
    lengthInMeters setup.cylinderDiameter = 6 / 100
  pistonThicknessIsFourCentimeters :
    lengthInMeters setup.pistonThickness = 4 / 100
  initialHeightIsTwentyCentimeters :
    lengthInMeters (setup.pistonBottomHeight 0) = 20 / 100
  initialTemperatureIsTwentyCelsius :
    temperatureInDegreesCelsius (setup.gasTemperature 0) = 20
  upperLabelIsVacuum : setup.upperRegionLabel = .vacuum
  middleLabelIsPiston : setup.pistonRegionLabel = .piston
  lowerLabelIsNitrogen : setup.lowerRegionLabel = .nitrogenN2

/-- Positivity assumptions selecting physically meaningful parameters. -/
structure HasPhysicalParameters
    (setup : CopperPistonNitrogenCylinder) : Prop where
  diameterPositive : 0 < lengthInMeters setup.cylinderDiameter
  thicknessPositive : 0 < lengthInMeters setup.pistonThickness
  areaPositive : 0 < areaInSquareMeters setup.pistonCrossSectionalArea
  pistonVolumePositive : 0 < volumeInCubicMeters setup.pistonVolume
  pistonDensityPositive :
    0 < massDensityInKilogramsPerCubicMeter setup.pistonMassDensity
  pistonMassPositive : 0 < massInKilograms setup.pistonMass
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.localGravitationalAcceleration
  gasHeightPositive :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      0 < lengthInMeters (setup.pistonBottomHeight τ)
  gasVolumePositive :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      0 < volumeInCubicMeters (setup.gasVolume τ)
  gasPressurePositive :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      0 < pressureInPascals (setup.gasPressure τ)
  gasTemperaturePositive :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      0 < temperatureInKelvins (setup.gasTemperature τ)
  amountPositive : 0 < setup.amountOfGasMoles
  gasConstantPositive : 0 < molarGasConstantInSI setup.molarGasConstant

/-!
General geometry, constitutive, equilibrium, ideal-gas, and work laws for the
apparatus.  The boundary-work field is conditional on constant pressure and
therefore states the standard constant-pressure law rather than a numerical
answer to this problem.  In particular, no field fixes the final height or
the requested work.
-/
structure ObeysPistonCylinderLaws
    (setup : CopperPistonNitrogenCylinder) : Prop where
  circularCrossSection :
    areaInSquareMeters setup.pistonCrossSectionalArea =
      Real.pi * (lengthInMeters setup.cylinderDiameter / 2) ^ 2
  pistonVolumeFromAreaAndThickness :
    volumeInCubicMeters setup.pistonVolume =
      areaInSquareMeters setup.pistonCrossSectionalArea *
        lengthInMeters setup.pistonThickness
  pistonMassFromCopperDensity :
    massInKilograms setup.pistonMass =
      massDensityInKilogramsPerCubicMeter setup.pistonMassDensity *
        volumeInCubicMeters setup.pistonVolume
  cylindricalGasVolume :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      volumeInCubicMeters (setup.gasVolume τ) =
        areaInSquareMeters setup.pistonCrossSectionalArea *
          lengthInMeters (setup.pistonBottomHeight τ)
  evacuatedUpperRegion :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      pressureInPascals (setup.pressureAbovePiston τ) = 0
  pistonMechanicalEquilibrium :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      (pressureInPascals (setup.gasPressure τ) -
          pressureInPascals (setup.pressureAbovePiston τ)) *
          areaInSquareMeters setup.pistonCrossSectionalArea =
        massInKilograms setup.pistonMass *
          accelerationInMetersPerSecondSquared
            setup.localGravitationalAcceleration
  idealGasLaw :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      pressureInPascals (setup.gasPressure τ) *
          volumeInCubicMeters (setup.gasVolume τ) =
        setup.amountOfGasMoles *
          molarGasConstantInSI setup.molarGasConstant *
            temperatureInKelvins (setup.gasTemperature τ)
  oppositeWorkSignConventions :
    energyInJoules setup.workOnGas = -energyInJoules setup.workByGas
  constantPressureBoundaryWork :
    (∀ τ ∈ Set.Icc (0 : ℝ) 1,
        pressureInPascals (setup.gasPressure τ) =
          pressureInPascals (setup.gasPressure 0)) →
      energyInJoules setup.workByGas =
        pressureInPascals (setup.gasPressure 0) *
          (volumeInCubicMeters (setup.gasVolume 1) -
            volumeInCubicMeters (setup.gasVolume 0))

/-! ## Displayed choices and formalization target -/

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Signed joule values displayed beside the four answer labels. -/
def answerChoiceInJoules : AnswerChoice → ℝ
  | .A => 11 / 100
  | .B => 6 / 5
  | .C => 57 / 100
  | .D => -(57 / 100)

/-- A displayed choice matches the signed work-on-gas convention. -/
def WorkOnGasMatchesChoice
    (setup : CopperPistonNitrogenCylinder) (choice : AnswerChoice) : Prop :=
  energyInJoules setup.workOnGas = answerChoiceInJoules choice

/-!
For a rising piston, the work done on the gas is the negative of the piston's
gain in gravitational potential energy.  The second equality expands the
piston mass using its density, circular cross-section, and thickness.

The final height remains a genuine variable because the source supplies no
rise distance or final temperature.  Thus this theorem preserves the physical
answer determined by the stated data without falsely selecting a number.
-/
theorem problem_phyx_mini_0407
    (setup : CopperPistonNitrogenCylinder)
    (hData : MatchesProblemAndPrimaryFigure setup)
    (hPhysical : HasPhysicalParameters setup)
    (hLaws : ObeysPistonCylinderLaws setup)
    (hRise :
      lengthInMeters (setup.pistonBottomHeight 0) <
        lengthInMeters (setup.pistonBottomHeight 1)) :
    energyInJoules setup.workOnGas =
        -(massInKilograms setup.pistonMass *
          accelerationInMetersPerSecondSquared
            setup.localGravitationalAcceleration *
          (lengthInMeters (setup.pistonBottomHeight 1) -
            lengthInMeters (setup.pistonBottomHeight 0))) ∧
      energyInJoules setup.workOnGas =
        -(massDensityInKilogramsPerCubicMeter setup.pistonMassDensity *
          Real.pi * (lengthInMeters setup.cylinderDiameter / 2) ^ 2 *
          lengthInMeters setup.pistonThickness *
          accelerationInMetersPerSecondSquared
            setup.localGravitationalAcceleration *
          (lengthInMeters (setup.pistonBottomHeight 1) -
            lengthInMeters (setup.pistonBottomHeight 0))) ∧
      energyInJoules setup.workOnGas < 0 := by
  have hZero : (0 : ℝ) ∈ Set.Icc 0 1 := by
    constructor <;> norm_num
  have hOne : (1 : ℝ) ∈ Set.Icc 0 1 := by
    constructor <;> norm_num
  have hPressureConstant :
      ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        pressureInPascals (setup.gasPressure τ) =
          pressureInPascals (setup.gasPressure 0) := by
    intro τ hτ
    have hEquilibriumτ :=
      hLaws.pistonMechanicalEquilibrium τ hτ
    have hEquilibriumZero :=
      hLaws.pistonMechanicalEquilibrium 0 hZero
    have hVacuumτ := hLaws.evacuatedUpperRegion τ hτ
    have hVacuumZero := hLaws.evacuatedUpperRegion 0 hZero
    rw [hVacuumτ] at hEquilibriumτ
    rw [hVacuumZero] at hEquilibriumZero
    nlinarith [hPhysical.areaPositive]
  have hBoundaryWork :=
    hLaws.constantPressureBoundaryWork hPressureConstant
  have hVolumeZero := hLaws.cylindricalGasVolume 0 hZero
  have hVolumeOne := hLaws.cylindricalGasVolume 1 hOne
  have hEquilibriumZero :=
    hLaws.pistonMechanicalEquilibrium 0 hZero
  have hVacuumZero := hLaws.evacuatedUpperRegion 0 hZero
  rw [hVacuumZero] at hEquilibriumZero
  have hWorkOnGas :
      energyInJoules setup.workOnGas =
        -(massInKilograms setup.pistonMass *
          accelerationInMetersPerSecondSquared
            setup.localGravitationalAcceleration *
          (lengthInMeters (setup.pistonBottomHeight 1) -
            lengthInMeters (setup.pistonBottomHeight 0))) := by
    calc
      energyInJoules setup.workOnGas =
          -energyInJoules setup.workByGas :=
        hLaws.oppositeWorkSignConventions
      _ = -(pressureInPascals (setup.gasPressure 0) *
          (volumeInCubicMeters (setup.gasVolume 1) -
            volumeInCubicMeters (setup.gasVolume 0))) := by
        rw [hBoundaryWork]
      _ = -(pressureInPascals (setup.gasPressure 0) *
          (areaInSquareMeters setup.pistonCrossSectionalArea *
              lengthInMeters (setup.pistonBottomHeight 1) -
            areaInSquareMeters setup.pistonCrossSectionalArea *
              lengthInMeters (setup.pistonBottomHeight 0))) := by
        rw [hVolumeOne, hVolumeZero]
      _ = -((pressureInPascals (setup.gasPressure 0) *
              areaInSquareMeters setup.pistonCrossSectionalArea) *
            (lengthInMeters (setup.pistonBottomHeight 1) -
              lengthInMeters (setup.pistonBottomHeight 0))) := by
        ring
      _ = -(massInKilograms setup.pistonMass *
          accelerationInMetersPerSecondSquared
            setup.localGravitationalAcceleration *
          (lengthInMeters (setup.pistonBottomHeight 1) -
            lengthInMeters (setup.pistonBottomHeight 0))) := by
        simpa using congrArg
          (fun x : ℝ =>
            -(x *
              (lengthInMeters (setup.pistonBottomHeight 1) -
                lengthInMeters (setup.pistonBottomHeight 0))))
          hEquilibriumZero
  have hExpandedWork :
      energyInJoules setup.workOnGas =
        -(massDensityInKilogramsPerCubicMeter setup.pistonMassDensity *
          Real.pi * (lengthInMeters setup.cylinderDiameter / 2) ^ 2 *
          lengthInMeters setup.pistonThickness *
          accelerationInMetersPerSecondSquared
            setup.localGravitationalAcceleration *
          (lengthInMeters (setup.pistonBottomHeight 1) -
            lengthInMeters (setup.pistonBottomHeight 0))) := by
    calc
      energyInJoules setup.workOnGas =
          -(massInKilograms setup.pistonMass *
            accelerationInMetersPerSecondSquared
              setup.localGravitationalAcceleration *
            (lengthInMeters (setup.pistonBottomHeight 1) -
              lengthInMeters (setup.pistonBottomHeight 0))) :=
        hWorkOnGas
      _ = -(massDensityInKilogramsPerCubicMeter setup.pistonMassDensity *
          Real.pi * (lengthInMeters setup.cylinderDiameter / 2) ^ 2 *
          lengthInMeters setup.pistonThickness *
          accelerationInMetersPerSecondSquared
            setup.localGravitationalAcceleration *
          (lengthInMeters (setup.pistonBottomHeight 1) -
            lengthInMeters (setup.pistonBottomHeight 0))) := by
        rw [hLaws.pistonMassFromCopperDensity,
          hLaws.pistonVolumeFromAreaAndThickness,
          hLaws.circularCrossSection]
        ring
  have hHeightGain :
      0 <
        lengthInMeters (setup.pistonBottomHeight 1) -
          lengthInMeters (setup.pistonBottomHeight 0) :=
    sub_pos.mpr hRise
  have hPositiveGain :
      0 <
        massInKilograms setup.pistonMass *
          accelerationInMetersPerSecondSquared
            setup.localGravitationalAcceleration *
          (lengthInMeters (setup.pistonBottomHeight 1) -
            lengthInMeters (setup.pistonBottomHeight 0)) :=
    mul_pos
      (mul_pos hPhysical.pistonMassPositive hPhysical.gravityPositive)
      hHeightGain
  refine ⟨hWorkOnGas, hExpandedWork, ?_⟩
  rw [hWorkOnGas]
  linarith

/-!
With the explicit work-on-gas sign convention, the recorded positive choice
`C = +0.57 J` cannot describe a rising piston.  This sign statement does not
select choice `D`, because the missing endpoint also leaves the magnitude
undetermined.
-/
theorem recorded_positive_choice_C_conflicts_with_rising_work_on_gas
    (setup : CopperPistonNitrogenCylinder)
    (hData : MatchesProblemAndPrimaryFigure setup)
    (hPhysical : HasPhysicalParameters setup)
    (hLaws : ObeysPistonCylinderLaws setup)
    (hRise :
      lengthInMeters (setup.pistonBottomHeight 0) <
        lengthInMeters (setup.pistonBottomHeight 1)) :
    ¬ WorkOnGasMatchesChoice setup .C := by
  intro hChoice
  have hNegative :=
    (problem_phyx_mini_0407 setup hData hPhysical hLaws hRise).2.2
  unfold WorkOnGasMatchesChoice at hChoice
  simp only [answerChoiceInJoules] at hChoice
  rw [hChoice] at hNegative
  norm_num at hNegative

end PhyXMiniProblems.ProblemPhyXMini0407
