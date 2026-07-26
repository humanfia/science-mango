import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Height of an ideal-gas-supported lead piston

This file models problem `phyx_mini_0374`.  A `50 kg` lead piston floats in
mechanical equilibrium above `0.12 mol` of compressed air at `30 °C`.  The
primary figure shows one standard atmosphere above the piston, an internal
cylinder width of `10 cm`, and a double-headed vertical dimension line
labelled `h`.

The width is interpreted as the internal diameter of the vertical circular
cylinder described by the source.  Length, mass, area, volume, pressure,
acceleration, and the molar gas constant retain their physical dimensions.
Real numbers below are only explicitly unit-labelled readouts, the amount of
substance in moles (whose SI base dimension is not represented by Physlib's
current `Dimension`), schematic figure annotations, or displayed choices.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0374

open Dimension

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical cross-sectional area. -/
abbrev AreaQuantity : Type := DimArea

/-- A nonnegative physical volume carrying dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A physical pressure. -/
abbrev PressureQuantity : Type := DimPressure

/-- A nonnegative physical acceleration. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/--
The molar gas constant, with SI dimension energy per absolute temperature.
The inverse-mole role is recorded by the named molar readout because Physlib's
current dimension vector has no amount-of-substance component.
-/
abbrev MolarGasConstantQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) NNReal)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Centimetre readout of a physical length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Square-metre readout of a physical area. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Pascal readout of a physical pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Pressure readout in standard atmospheres. -/
def pressureInAtmospheres (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure /
    pressureInPascals DimPressure.standardAtmosphere

/-- Metres-per-second-squared readout of a physical acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/--
Read an absolute temperature in kelvins.  Physlib's `Temperature` stores a
nonnegative absolute value, while the unit ratio converts its storage unit to
`TemperatureUnit.kelvin`.
-/
def temperatureInKelvins
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- Celsius readout using the exact `273.15` affine offset. -/
def temperatureInDegreesCelsius
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  temperatureInKelvins storageUnit temperature - 27315 / 100

/-- SI readout of the molar gas constant in joules per mole-kelvin. -/
def molarGasConstantInJoulesPerMoleKelvin
    (gasConstant : MolarGasConstantQuantity) : ℝ :=
  ((gasConstant UnitChoices.SI).val : ℝ)

/-! ## Physical roles and primary-figure labels -/

/-- Material identified for the movable piston. -/
inductive PistonMaterial where
  | lead
  deriving DecidableEq, Repr

/-- Equation-of-state model used for the compressed air. -/
inductive GasModel where
  | idealGas
  deriving DecidableEq, Repr

/-- Gas species named by the problem. -/
inductive GasSpecies where
  | air
  deriving DecidableEq, Repr

/-- Orientation of the cylinder in the primary figure. -/
inductive CylinderOrientation where
  | vertical
  deriving DecidableEq, Repr

/-- Cross-sectional geometry inferred from the word “cylinder”. -/
inductive CylinderCrossSection where
  | circular
  deriving DecidableEq, Repr

/-- Interpretation of the horizontal `10 cm` dimension line. -/
inductive WidthInterpretation where
  | internalDiameter
  deriving DecidableEq, Repr

/-- Mechanical state conveyed by the statement that the piston “floats”. -/
inductive PistonMechanicalState where
  | staticEquilibrium
  deriving DecidableEq, Repr

/-- Directions indicated by the two heads of the vertical height marker. -/
inductive VerticalArrowDirection where
  | upwardAndDownward
  deriving DecidableEq, Repr

/-- Symbol printed beside the unknown vertical dimension. -/
inductive HeightFigureLabel where
  | h
  deriving DecidableEq, Repr

/--
Literal annotations and qualitative labels read from the primary raster.
The unknown height has a symbol and double-headed dimension marker but
deliberately no value.
-/
structure PistonCylinderFigure where
  pistonMassTextKilograms : ℝ
  pressureAboveTextAtmospheres : ℝ
  gasTemperatureTextCelsius : ℝ
  cylinderWidthTextCentimeters : ℝ
  widthInterpretation : WidthInterpretation
  heightArrowDirection : VerticalArrowDirection
  heightLabel : HeightFigureLabel

/--
The cylinder, piston, gas state, and figure-derived quantities.  The height
`gasColumnHeightH` is an independent physical field; it is not defined using
any displayed answer.
-/
structure FloatingPistonSetup where
  pistonMaterial : PistonMaterial
  gasSpecies : GasSpecies
  gasModel : GasModel
  cylinderOrientation : CylinderOrientation
  cylinderCrossSection : CylinderCrossSection
  pistonMechanicalState : PistonMechanicalState
  figure : PistonCylinderFigure
  cylinderInternalDiameter : LengthQuantity
  gasColumnHeightH : LengthQuantity
  cylinderCrossSectionalArea : AreaQuantity
  gasVolume : VolumeQuantity
  pistonMass : MassQuantity
  localGravitationalAcceleration : AccelerationQuantity
  pressureAbovePiston : PressureQuantity
  compressedAirPressure : PressureQuantity
  temperatureStorageUnit : TemperatureUnit
  compressedAirTemperature : Temperature
  /-- Explicit amount-of-substance readout in moles. -/
  amountOfAirMoles : ℝ
  molarGasConstant : MolarGasConstantQuantity

/-! ## Problem statement and figure/data readouts -/

/--
Prose data and primary-image evidence.  The source values are linked to the
independent physical quantities, but no numerical value is assigned to `h`.
-/
structure MatchesProblemStatementAndPrimaryFigure
    (setup : FloatingPistonSetup) : Prop where
  pistonIsLead : setup.pistonMaterial = .lead
  gasIsAir : setup.gasSpecies = .air
  gasUsesIdealEquationOfState : setup.gasModel = .idealGas
  cylinderIsVertical : setup.cylinderOrientation = .vertical
  crossSectionIsCircular : setup.cylinderCrossSection = .circular
  pistonFloatsInStaticEquilibrium :
    setup.pistonMechanicalState = .staticEquilibrium
  figurePistonMassText : setup.figure.pistonMassTextKilograms = 50
  figurePressureAboveText : setup.figure.pressureAboveTextAtmospheres = 1
  figureGasTemperatureText : setup.figure.gasTemperatureTextCelsius = 30
  figureCylinderWidthText : setup.figure.cylinderWidthTextCentimeters = 10
  figureWidthIsInternalDiameter :
    setup.figure.widthInterpretation = .internalDiameter
  figureHeightArrowIsDoubleHeaded :
    setup.figure.heightArrowDirection = .upwardAndDownward
  figureHeightIsLabelledH : setup.figure.heightLabel = .h
  pistonMassAgreesWithFigure :
    massInKilograms setup.pistonMass = setup.figure.pistonMassTextKilograms
  pressureAboveAgreesWithFigure :
    pressureInAtmospheres setup.pressureAbovePiston =
      setup.figure.pressureAboveTextAtmospheres
  pressureAboveIsOneStandardAtmosphere :
    setup.pressureAbovePiston = DimPressure.standardAtmosphere
  temperatureIsStoredInKelvins :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin
  temperatureAgreesWithFigure :
    temperatureInDegreesCelsius setup.temperatureStorageUnit
        setup.compressedAirTemperature = setup.figure.gasTemperatureTextCelsius
  diameterAgreesWithFigure :
    lengthInCentimeters setup.cylinderInternalDiameter =
      setup.figure.cylinderWidthTextCentimeters
  gasAmountIsPointTwelveMoles : setup.amountOfAirMoles = 3 / 25

/--
Standard textbook SI readouts for background terrestrial constants omitted
from the problem statement.  They are physical calibration data, not a
relation involving the requested height.
-/
structure UsesStandardTerrestrialConstants
    (setup : FloatingPistonSetup) : Prop where
  gravitationalAccelerationInSI :
    accelerationInMetersPerSecondSquared
      setup.localGravitationalAcceleration = 981 / 100
  molarGasConstantInSI :
    molarGasConstantInJoulesPerMoleKelvin setup.molarGasConstant = 8314 / 1000

/-! ## Physical-domain conditions and governing laws -/

/-- Positivity conditions selecting physically meaningful parameters. -/
structure HasPhysicalFloatingPistonParameters
    (setup : FloatingPistonSetup) : Prop where
  diameterPositive : 0 < lengthInMeters setup.cylinderInternalDiameter
  heightPositive : 0 < lengthInMeters setup.gasColumnHeightH
  areaPositive : 0 < areaInSquareMeters setup.cylinderCrossSectionalArea
  volumePositive : 0 < volumeInCubicMeters setup.gasVolume
  pistonMassPositive : 0 < massInKilograms setup.pistonMass
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.localGravitationalAcceleration
  pressureAbovePositive : 0 < pressureInPascals setup.pressureAbovePiston
  gasPressurePositive : 0 < pressureInPascals setup.compressedAirPressure
  gasPressureExceedsPressureAbove :
    pressureInPascals setup.pressureAbovePiston <
      pressureInPascals setup.compressedAirPressure
  absoluteTemperaturePositive :
    0 < temperatureInKelvins setup.temperatureStorageUnit
      setup.compressedAirTemperature
  gasAmountPositive : 0 < setup.amountOfAirMoles
  molarGasConstantPositive :
    0 < molarGasConstantInJoulesPerMoleKelvin setup.molarGasConstant

/-!
Generic circular-cylinder geometry, the molar ideal-gas equation, and the
vertical force balance for a freely floating piston.  These laws relate
independently stored quantities and contain neither `22.7 cm` nor an answer
label.
-/
structure SatisfiesIdealGasAndFloatingPistonLaws
    (setup : FloatingPistonSetup) : Prop where
  circularCrossSectionFromDiameter :
    areaInSquareMeters setup.cylinderCrossSectionalArea =
      Real.pi * (lengthInMeters setup.cylinderInternalDiameter / 2) ^ 2
  cylindricalGasVolume :
    volumeInCubicMeters setup.gasVolume =
      areaInSquareMeters setup.cylinderCrossSectionalArea *
        lengthInMeters setup.gasColumnHeightH
  molarIdealGasLaw :
    pressureInPascals setup.compressedAirPressure *
        volumeInCubicMeters setup.gasVolume =
      setup.amountOfAirMoles *
        molarGasConstantInJoulesPerMoleKelvin setup.molarGasConstant *
          temperatureInKelvins setup.temperatureStorageUnit
            setup.compressedAirTemperature
  verticalMechanicalEquilibrium :
    (pressureInPascals setup.compressedAirPressure -
        pressureInPascals setup.pressureAbovePiston) *
        areaInSquareMeters setup.cylinderCrossSectionalArea =
      massInKilograms setup.pistonMass *
        accelerationInMetersPerSecondSquared
          setup.localGravitationalAcceleration

/-! ## General consequence, numerical height, and displayed choices -/

/-!
Eliminating gas pressure and volume from the three governing relations gives
the standard piston-height formula.  This lemma is independent of all four
displayed numerical choices.
-/
lemma pistonHeightFromIdealGasAndEquilibrium
    (setup : FloatingPistonSetup)
    (_physical : HasPhysicalFloatingPistonParameters setup)
    (_laws : SatisfiesIdealGasAndFloatingPistonLaws setup) :
    lengthInMeters setup.gasColumnHeightH =
      (setup.amountOfAirMoles *
          molarGasConstantInJoulesPerMoleKelvin setup.molarGasConstant *
            temperatureInKelvins setup.temperatureStorageUnit
              setup.compressedAirTemperature) /
        (pressureInPascals setup.pressureAbovePiston *
            areaInSquareMeters setup.cylinderCrossSectionalArea +
          massInKilograms setup.pistonMass *
            accelerationInMetersPerSecondSquared
              setup.localGravitationalAcceleration) := by
  have hden :
      0 <
        pressureInPascals setup.pressureAbovePiston *
            areaInSquareMeters setup.cylinderCrossSectionalArea +
          massInKilograms setup.pistonMass *
            accelerationInMetersPerSecondSquared
              setup.localGravitationalAcceleration := by
    exact
      add_pos
        (mul_pos _physical.pressureAbovePositive _physical.areaPositive)
        (mul_pos _physical.pistonMassPositive _physical.gravityPositive)
  rw [eq_div_iff hden.ne']
  have hideal := _laws.molarIdealGasLaw
  rw [_laws.cylindricalGasVolume] at hideal
  have hpressureArea :
      pressureInPascals setup.compressedAirPressure *
          areaInSquareMeters setup.cylinderCrossSectionalArea =
        pressureInPascals setup.pressureAbovePiston *
            areaInSquareMeters setup.cylinderCrossSectionalArea +
          massInKilograms setup.pistonMass *
            accelerationInMetersPerSecondSquared
              setup.localGravitationalAcceleration := by
    nlinarith [_laws.verticalMechanicalEquilibrium]
  rw [← hpressureArea]
  nlinarith [hideal]

/-- Labels printed beside the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Height in centimetres printed beside an answer label. -/
def AnswerChoice.heightInCentimeters : AnswerChoice → ℝ
  | .A => 227 / 10
  | .B => 239 / 10
  | .C => 335 / 10
  | .D => 12

/--
Answer label recorded in the supplied dataset metadata.  This is retained as
metadata only: the governing laws and exact figure readouts below do not imply
the height printed beside this label.
-/
def recordedAnswerChoice : AnswerChoice := .A

/-!
For the exact conventions stated above, the governing laws give

`h = (0.12 * 8.314 * 303.15) /
  (101325 * π * (0.10 / 2)^2 + 50 * 9.81)` metres.

Thus the height is between `23.512 cm` and `23.513 cm`.  None of the displayed
decimal heights is exactly this value; choice B (`23.9 cm`) is the uniquely
closest displayed choice.  The recorded metadata label A is deliberately not
used in the conclusion.

Blueprint label: `thm:physics:phyx_mini_0374:target`.
-/
theorem pistonHeight_supportedByFigureAndGoverningLaws
    (setup : FloatingPistonSetup)
    (_problemAndFigure : MatchesProblemStatementAndPrimaryFigure setup)
    (_constants : UsesStandardTerrestrialConstants setup)
    (_physical : HasPhysicalFloatingPistonParameters setup)
    (_laws : SatisfiesIdealGasAndFloatingPistonLaws setup) :
    lengthInCentimeters setup.gasColumnHeightH =
        (75611673 / 2500) /
          (101325 * Real.pi / 400 + 981 / 2) ∧
      23512 / 1000 < lengthInCentimeters setup.gasColumnHeightH ∧
      lengthInCentimeters setup.gasColumnHeightH < 23513 / 1000 ∧
      ∀ choice : AnswerChoice, choice ≠ .B →
        |lengthInCentimeters setup.gasColumnHeightH -
            AnswerChoice.heightInCentimeters .B| <
          |lengthInCentimeters setup.gasColumnHeightH -
            AnswerChoice.heightInCentimeters choice| := by
  have hmass : massInKilograms setup.pistonMass = 50 := by
    calc
      _ = setup.figure.pistonMassTextKilograms :=
        _problemAndFigure.pistonMassAgreesWithFigure
      _ = 50 := _problemAndFigure.figurePistonMassText
  have htemperatureK :
      temperatureInKelvins setup.temperatureStorageUnit
          setup.compressedAirTemperature =
        30315 / 100 := by
    have htemperatureC := _problemAndFigure.temperatureAgreesWithFigure
    rw [_problemAndFigure.figureGasTemperatureText] at htemperatureC
    unfold temperatureInDegreesCelsius at htemperatureC
    linarith
  have hdiameterM :
      lengthInMeters setup.cylinderInternalDiameter = 1 / 10 := by
    have hdiameterCm := _problemAndFigure.diameterAgreesWithFigure
    rw [_problemAndFigure.figureCylinderWidthText] at hdiameterCm
    unfold lengthInCentimeters at hdiameterCm
    linarith
  have harea :
      areaInSquareMeters setup.cylinderCrossSectionalArea = Real.pi / 400 := by
    rw [_laws.circularCrossSectionFromDiameter, hdiameterM]
    ring
  have hpressure :
      pressureInPascals setup.pressureAbovePiston = 101325 := by
    rw [_problemAndFigure.pressureAboveIsOneStandardAtmosphere]
    norm_num [pressureInPascals, DimPressure.standardAtmosphere,
      CarriesDimension.toDimensionful]
  have hheightMeters :=
    pistonHeightFromIdealGasAndEquilibrium setup _physical _laws
  have hheightExact :
      lengthInCentimeters setup.gasColumnHeightH =
        (75611673 / 2500) /
          (101325 * Real.pi / 400 + 981 / 2) := by
    unfold lengthInCentimeters
    rw [hheightMeters, _problemAndFigure.gasAmountIsPointTwelveMoles,
      _constants.molarGasConstantInSI, htemperatureK, hpressure, harea,
      hmass, _constants.gravitationalAccelerationInSI]
    norm_num
    ring
  have cos_taylor_bound (x : ℝ) (hx : |x| ≤ 1) :
      |Real.cos x -
          (∑ m ∈ Finset.range 12,
            (((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ))).re| ≤
        |x| ^ 12 * ((13 : ℝ) / ((12 : ℕ).factorial * 12)) := by
    have h := Complex.exp_bound
      (x := (x : ℂ) * Complex.I) (n := 12)
      (by simpa using hx) (by norm_num)
    have hre := Complex.abs_re_le_norm
      (Complex.exp ((x : ℂ) * Complex.I) -
        ∑ m ∈ Finset.range 12,
          ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ))
    calc
      _ = |(Complex.exp ((x : ℂ) * Complex.I) -
          ∑ m ∈ Finset.range 12,
            ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)).re| := by
        rw [Complex.exp_mul_I]
        simp [← Complex.ofReal_cos]
      _ ≤ ‖Complex.exp ((x : ℂ) * Complex.I) -
          ∑ m ∈ Finset.range 12,
            ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)‖ := hre
      _ ≤ _ := by
        convert h using 1
        norm_num [div_eq_mul_inv]
  have hcosLower : 0 < Real.cos ((78539 / 25000 : ℝ) / 2) := by
    rw [show (78539 / 25000 : ℝ) / 2 = 2 * (78539 / 100000) by ring,
      Real.cos_two_mul]
    have happrox := cos_taylor_bound (78539 / 100000) (by norm_num)
    have hcos : 0 < Real.cos (78539 / 100000) :=
      Real.cos_pos_of_le_one (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg, pow_succ]
      at happrox
    rcases abs_le.mp happrox with ⟨hlower, hupper⟩
    nlinarith
  have hpiLower : (78539 / 25000 : ℝ) < Real.pi := by
    by_contra h
    have hpiLe : Real.pi ≤ (78539 / 25000 : ℝ) := le_of_not_gt h
    have hcosNonpos :
        Real.cos ((78539 / 25000 : ℝ) / 2) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le
        (by linarith)
        (by nlinarith [Real.two_le_pi])
    linarith
  have hcosUpper : Real.cos ((31417 / 10000 : ℝ) / 2) < 0 := by
    rw [show (31417 / 10000 : ℝ) / 2 = 2 * (31417 / 40000) by ring,
      Real.cos_two_mul]
    have happrox := cos_taylor_bound (31417 / 40000) (by norm_num)
    have hcos : 0 < Real.cos (31417 / 40000) :=
      Real.cos_pos_of_le_one (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg, pow_succ]
      at happrox
    rcases abs_le.mp happrox with ⟨hlower, hupper⟩
    nlinarith
  have hpiUpper : Real.pi < (31417 / 10000 : ℝ) := by
    by_contra h
    have hqLe : (31417 / 10000 : ℝ) ≤ Real.pi := le_of_not_gt h
    have hcosNonneg :
        0 ≤ Real.cos ((31417 / 10000 : ℝ) / 2) :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by nlinarith [Real.pi_pos])
        (by linarith)
    linarith
  have hdenom : 0 < 101325 * Real.pi / 400 + 981 / 2 := by
    positivity
  have hheightLower :
      23512 / 1000 < lengthInCentimeters setup.gasColumnHeightH := by
    rw [hheightExact, lt_div_iff₀ hdenom]
    nlinarith [hpiUpper]
  have hheightUpper :
      lengthInCentimeters setup.gasColumnHeightH < 23513 / 1000 := by
    rw [hheightExact, div_lt_iff₀ hdenom]
    nlinarith [hpiLower]
  refine ⟨hheightExact, hheightLower, hheightUpper, ?_⟩
  intro choice hchoice
  cases choice with
  | A =>
      simp only [AnswerChoice.heightInCentimeters]
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
      linarith
  | B =>
      exact (hchoice rfl).elim
  | C =>
      simp only [AnswerChoice.heightInCentimeters]
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
  | D =>
      simp only [AnswerChoice.heightInCentimeters]
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
      linarith

end PhyXMiniProblems.ProblemPhyXMini0374
