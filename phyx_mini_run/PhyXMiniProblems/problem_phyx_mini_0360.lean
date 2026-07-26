import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Isothermal compression of air under a loaded piston

This file models problem `phyx_mini_0360`.  A vertical circular metal cylinder
contains sealed air below a frictionless piston.  The initial equilibrium has
only the piston as a load; in the final equilibrium an 80 kg student stands on
the piston and the gas has had several minutes to return to ambient temperature.

Lengths, masses, areas, volumes, pressures, accelerations, and the molar gas
constant are represented by Physlib dimensionful quantities.  Physlib's
absolute `Temperature` represents the gas and ambient temperatures.  Real
numbers occur only as named SI or centimetre readouts, dimensionless figure
coordinates, molar readouts (Physlib has no amount-of-substance dimension),
and displayed answer values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0360

open Dimension

/-! ## Dimensionful physical quantities and named readouts -/

/-- A physical length, independent of the chosen unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical mass, independent of the chosen unit. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- A nonnegative physical cross-sectional area. -/
abbrev AreaQuantity : Type := DimArea

/-- A physical volume, with dimension length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- A physical pressure. -/
abbrev PressureQuantity : Type := DimPressure

/-- A physical acceleration, used for local gravitational acceleration. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-!
The molar gas constant has energy-per-temperature dimension here.  Its inverse
amount-of-substance dimension is paired with the explicitly molar readout
below because amount of substance is not a base dimension in Physlib.
-/
abbrev MolarGasConstantQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) ℝ)

/-!
An abstract amount-of-substance carrier together with its calibrated mole
readout.  This keeps the physical amount distinct from a bare real number.
-/
structure AmountOfSubstanceScale where
  Quantity : Type
  inMoles : Quantity → ℝ

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

/-!
The scenario fixes Physlib's arbitrary absolute-temperature scale to kelvin,
so `Temperature.toReal` is the kelvin readout in this setup.
-/
def temperatureInKelvin (temperature : Temperature) : ℝ :=
  Temperature.toReal temperature

/-- Celsius readout derived from an absolute kelvin readout. -/
def temperatureInCelsius (temperature : Temperature) : ℝ :=
  temperatureInKelvin temperature - (27315 / 100 : ℝ)

/-- SI readout of the molar gas constant. -/
def molarGasConstantInSI (gasConstant : MolarGasConstantQuantity) : ℝ :=
  (gasConstant UnitChoices.SI).val

/-! ## Equilibrium states, physical roles, and primary-figure labels -/

/-- The two mechanical-equilibrium states shown side by side in the figure. -/
inductive EquilibriumState where
  /-- Left panel: pressure `P₁`, height `h₁`, piston alone. -/
  | pistonOnly
  /-- Right panel: pressure `P₂`, height `h₂`, student on the piston. -/
  | pistonAndStudent
  deriving DecidableEq, Repr

/-- Pressure symbols printed in the primary figure. -/
inductive FigurePressureLabel where
  | P1
  | P2
  | Patmos
  deriving DecidableEq, Repr

/-- Height symbols printed in the primary figure. -/
inductive FigureHeightLabel where
  | h1
  | h2
  deriving DecidableEq, Repr

/-- Cross-sectional-area symbol printed in both figure panels. -/
inductive FigureAreaLabel where
  | A
  deriving DecidableEq, Repr

/-- Shape and orientation of the container. -/
inductive CylinderShape where
  | verticalCircularCylinder
  deriving DecidableEq, Repr

/-- Material named for the cylinder. -/
inductive CylinderMaterial where
  | metal
  deriving DecidableEq, Repr

/-- Gas species named in the problem. -/
inductive GasSpecies where
  | air
  deriving DecidableEq, Repr

/-- Equation-of-state model used for the trapped air. -/
inductive GasModel where
  | ideal
  deriving DecidableEq, Repr

/-- Constraint on the piston's allowed motion. -/
inductive PistonMotion where
  | verticalAndFrictionless
  deriving DecidableEq, Repr

/-- Medium exerting pressure on the top face of the piston. -/
inductive AbovePistonMedium where
  | atmosphere
  deriving DecidableEq, Repr

/-- How the second load is applied. -/
inductive AdditionalLoad where
  | studentStandsOnPiston
  deriving DecidableEq, Repr

/-- Waiting condition described before the requested final readout. -/
inductive WaitingProtocol where
  | severalMinutesToThermalEquilibrium
  deriving DecidableEq, Repr

/-!
The physical apparatus and its two independent equilibrium states.  The
pressure and height functions are the figure's `P₁`, `P₂`, `h₁`, and `h₂`.
In particular, the final height is an unconstrained field and is not defined
from the displayed 3.8 cm answer.
-/
structure AirPistonSetup (amountScale : AmountOfSubstanceScale) where
  cylinderShape : CylinderShape
  cylinderMaterial : CylinderMaterial
  gasSpecies : GasSpecies
  gasModel : GasModel
  pistonMotion : PistonMotion
  abovePistonMedium : AbovePistonMedium
  additionalLoad : AdditionalLoad
  waitingProtocol : WaitingProtocol
  temperatureUnit : TemperatureUnit
  /-- Cylinder diameter, stated as 50.0 cm. -/
  cylinderDiameter : LengthQuantity
  /-- Figure label `A`, common to both panels. -/
  crossSectionalAreaA : AreaQuantity
  pistonMass : MassQuantity
  studentMass : MassQuantity
  localGravitationalAcceleration : AccelerationQuantity
  /-- Figure labels `P₁` and `P₂`, indexed by equilibrium state. -/
  gasPressureP : EquilibriumState → PressureQuantity
  /-- Figure labels `h₁` and `h₂`, indexed by equilibrium state. -/
  gasColumnHeightH : EquilibriumState → LengthQuantity
  gasVolume : EquilibriumState → VolumeQuantity
  /-- Figure label `P_atmos`. -/
  atmosphericPressurePatmos : PressureQuantity
  gasTemperature : EquilibriumState → Temperature
  ambientTemperature : Temperature
  gasAmount : EquilibriumState → amountScale.Quantity
  molarGasConstant : MolarGasConstantQuantity
  figurePressureLabel : EquilibriumState → FigurePressureLabel
  figureHeightLabel : EquilibriumState → FigureHeightLabel
  figureAtmosphericPressureLabel : FigurePressureLabel
  figureAreaLabel : FigureAreaLabel

/-!
Total load mass supported by the pressure difference in each state.  This
only records which bodies stand on the piston; it does not constrain a height.
-/
def supportedMassInKilograms
    {amountScale : AmountOfSubstanceScale}
    (setup : AirPistonSetup amountScale) : EquilibriumState → ℝ
  | .pistonOnly => massInKilograms setup.pistonMass
  | .pistonAndStudent =>
      massInKilograms setup.pistonMass + massInKilograms setup.studentMass

/-! ## Assumptions supplied by the scenario and figure -/

/-!
Qualitative setup, primary-figure label assignments, and numerical readouts
given in the source.  No final height or depression value occurs here.
-/
structure MatchesProblemStatementAndFigure
    {amountScale : AmountOfSubstanceScale}
    (setup : AirPistonSetup amountScale) : Prop where
  cylinderIsVerticalAndCircular :
    setup.cylinderShape = .verticalCircularCylinder
  cylinderIsMetal : setup.cylinderMaterial = .metal
  trappedGasIsAir : setup.gasSpecies = .air
  airUsesIdealGasModel : setup.gasModel = .ideal
  pistonMovesVerticallyWithoutFriction :
    setup.pistonMotion = .verticalAndFrictionless
  atmosphereIsAbovePiston : setup.abovePistonMedium = .atmosphere
  studentStandsOnPiston : setup.additionalLoad = .studentStandsOnPiston
  finalStateIsReadAfterSeveralMinutes :
    setup.waitingProtocol = .severalMinutesToThermalEquilibrium
  temperatureScaleIsKelvin : setup.temperatureUnit = TemperatureUnit.kelvin
  initialPressureLabelIsP1 :
    setup.figurePressureLabel .pistonOnly = .P1
  finalPressureLabelIsP2 :
    setup.figurePressureLabel .pistonAndStudent = .P2
  initialHeightLabelIsH1 : setup.figureHeightLabel .pistonOnly = .h1
  finalHeightLabelIsH2 : setup.figureHeightLabel .pistonAndStudent = .h2
  atmosphereLabelIsPatmos :
    setup.figureAtmosphericPressureLabel = .Patmos
  commonAreaLabelIsA : setup.figureAreaLabel = .A
  cylinderDiameterIsFiftyCentimeters :
    lengthInMeters setup.cylinderDiameter = 1 / 2
  pistonMassIsTwentyKilograms : massInKilograms setup.pistonMass = 20
  studentMassIsEightyKilograms : massInKilograms setup.studentMass = 80
  initialHeightIsOneHundredCentimeters :
    lengthInMeters (setup.gasColumnHeightH .pistonOnly) = 1
  ambientTemperatureIsTwentyCelsius :
    temperatureInCelsius setup.ambientTemperature = 20
  initialGasIsAtAmbientTemperature :
    setup.gasTemperature .pistonOnly = setup.ambientTemperature
  atmosphericPressureIsOneAtmosphere :
    setup.atmosphericPressurePatmos = DimPressure.standardAtmosphere

/-!
The piston is observed after the sealed gas has thermally re-equilibrated with
the unchanged ambient.  These are operating conditions, not a final-height
readout.
-/
structure IsSealedAndThermallyReequilibrated
    {amountScale : AmountOfSubstanceScale}
    (setup : AirPistonSetup amountScale) : Prop where
  noAirEscapes :
    setup.gasAmount .pistonOnly = setup.gasAmount .pistonAndStudent
  finalGasReturnsToAmbientTemperature :
    setup.gasTemperature .pistonAndStudent = setup.ambientTemperature

/-!
The standard near-surface Earth acceleration used for the numerical answer.
This environmental calibration is independent of the unknown displacement.
-/
structure UsesStandardEarthGravity
    {amountScale : AmountOfSubstanceScale}
    (setup : AirPistonSetup amountScale) : Prop where
  gravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
      setup.localGravitationalAcceleration = 49 / 5

/-- Positivity and nondegeneracy conditions selecting the physical branch. -/
structure HasPhysicalParameters
    {amountScale : AmountOfSubstanceScale}
    (setup : AirPistonSetup amountScale) : Prop where
  diameterPositive : 0 < lengthInMeters setup.cylinderDiameter
  areaPositive : 0 < areaInSquareMeters setup.crossSectionalAreaA
  pistonMassPositive : 0 < massInKilograms setup.pistonMass
  studentMassPositive : 0 < massInKilograms setup.studentMass
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.localGravitationalAcceleration
  heightPositive :
    ∀ state, 0 < lengthInMeters (setup.gasColumnHeightH state)
  volumePositive : ∀ state, 0 < volumeInCubicMeters (setup.gasVolume state)
  gasPressurePositive :
    ∀ state, 0 < pressureInPascals (setup.gasPressureP state)
  atmosphericPressurePositive :
    0 < pressureInPascals setup.atmosphericPressurePatmos
  gasTemperaturePositive :
    ∀ state, 0 < temperatureInKelvin (setup.gasTemperature state)
  gasAmountPositive :
    ∀ state, 0 < amountScale.inMoles (setup.gasAmount state)
  molarGasConstantPositive :
    0 < molarGasConstantInSI setup.molarGasConstant

/-!
The governing circular-cylinder geometry, ideal-gas equation, and static
vertical force balance.  The force law is

`(P_gas - P_atmos) A = m_supported g`.

These relations apply uniformly to the two independent states and contain no
numerical value for `h₂` or for the requested depression.
-/
structure SatisfiesCylinderIdealGasAndEquilibriumLaws
    {amountScale : AmountOfSubstanceScale}
    (setup : AirPistonSetup amountScale) : Prop where
  circularCrossSectionFromDiameter :
    areaInSquareMeters setup.crossSectionalAreaA =
      Real.pi * (lengthInMeters setup.cylinderDiameter / 2) ^ 2
  cylindricalGasVolume :
    ∀ state,
      volumeInCubicMeters (setup.gasVolume state) =
        areaInSquareMeters setup.crossSectionalAreaA *
          lengthInMeters (setup.gasColumnHeightH state)
  idealGasEquationOfState :
    ∀ state,
      pressureInPascals (setup.gasPressureP state) *
          volumeInCubicMeters (setup.gasVolume state) =
        amountScale.inMoles (setup.gasAmount state) *
          molarGasConstantInSI setup.molarGasConstant *
            temperatureInKelvin (setup.gasTemperature state)
  staticMechanicalEquilibrium :
    ∀ state,
      (pressureInPascals (setup.gasPressureP state) -
          pressureInPascals setup.atmosphericPressurePatmos) *
          areaInSquareMeters setup.crossSectionalAreaA =
        supportedMassInKilograms setup state *
          accelerationInMetersPerSecondSquared
            setup.localGravitationalAcceleration

/-! ## Derived readout, displayed choices, and requested conclusion -/

/-!
The signed downward displacement in centimetres.  This definition is only the
geometric difference `100 (h₁ - h₂)` and contains no answer-choice value.
-/
def pistonDepressionInCentimeters
    {amountScale : AmountOfSubstanceScale}
    (setup : AirPistonSetup amountScale) : ℝ :=
  100 *
    (lengthInMeters (setup.gasColumnHeightH .pistonOnly) -
      lengthInMeters (setup.gasColumnHeightH .pistonAndStudent))

/-- Labels of the four answers printed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Centimetre value printed beside each answer label. -/
def answerDepressionInCentimeters : AnswerChoice → ℝ
  | .A => 19 / 5
  | .B => 3
  | .C => 5
  | .D => 4

/-- The answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .A

/-!
The computed depression rounds to `3.8 cm` at the precision displayed in
answer A.  The bound `0.05 cm` is the half-unit interval for rounding to the
nearest tenth of a centimetre; it avoids asserting that rounded input data and
the irrational circular area produce exactly `3.8 cm`.

Blueprint label: `thm:physics:phyx_mini_0360:target`.
-/
theorem pistonDepression_rounds_to_three_point_eight_centimeters
    {amountScale : AmountOfSubstanceScale}
    (setup : AirPistonSetup amountScale)
    (_scenario : MatchesProblemStatementAndFigure setup)
    (_thermal : IsSealedAndThermallyReequilibrated setup)
    (_gravity : UsesStandardEarthGravity setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesCylinderIdealGasAndEquilibriumLaws setup) :
    |pistonDepressionInCentimeters setup -
        answerDepressionInCentimeters .A| ≤ 1 / 20 := by
  have hpa :
      pressureInPascals setup.atmosphericPressurePatmos = 101325 := by
    rw [_scenario.atmosphericPressureIsOneAtmosphere]
    simp [pressureInPascals, DimPressure.standardAtmosphere,
      CarriesDimension.toDimensionful_apply_apply]
  have harea :
      areaInSquareMeters setup.crossSectionalAreaA = Real.pi / 16 := by
    rw [_laws.circularCrossSectionFromDiameter,
      _scenario.cylinderDiameterIsFiftyCentimeters]
    ring

  have hmechanical1 := _laws.staticMechanicalEquilibrium .pistonOnly
  have hmechanical2 := _laws.staticMechanicalEquilibrium .pistonAndStudent
  rw [hpa, harea, _gravity.gravityMetersPerSecondSquared] at hmechanical1 hmechanical2
  norm_num [supportedMassInKilograms,
    _scenario.pistonMassIsTwentyKilograms,
    _scenario.studentMassIsEightyKilograms] at hmechanical1 hmechanical2
  have hp1pi :
      pressureInPascals (setup.gasPressureP .pistonOnly) * Real.pi =
        101325 * Real.pi + 3136 := by
    nlinarith only [hmechanical1]
  have hp2pi :
      pressureInPascals (setup.gasPressureP .pistonAndStudent) * Real.pi =
        101325 * Real.pi + 15680 := by
    nlinarith only [hmechanical2]

  have hamount :
      amountScale.inMoles (setup.gasAmount .pistonOnly) =
        amountScale.inMoles (setup.gasAmount .pistonAndStudent) :=
    congrArg amountScale.inMoles _thermal.noAirEscapes
  have htemperature :
      temperatureInKelvin (setup.gasTemperature .pistonOnly) =
        temperatureInKelvin (setup.gasTemperature .pistonAndStudent) := by
    rw [_scenario.initialGasIsAtAmbientTemperature,
      _thermal.finalGasReturnsToAmbientTemperature]
  have hisothermal :
      pressureInPascals (setup.gasPressureP .pistonOnly) *
          volumeInCubicMeters (setup.gasVolume .pistonOnly) =
        pressureInPascals (setup.gasPressureP .pistonAndStudent) *
          volumeInCubicMeters (setup.gasVolume .pistonAndStudent) := by
    calc
      _ = amountScale.inMoles (setup.gasAmount .pistonOnly) *
            molarGasConstantInSI setup.molarGasConstant *
              temperatureInKelvin (setup.gasTemperature .pistonOnly) :=
        _laws.idealGasEquationOfState .pistonOnly
      _ = amountScale.inMoles (setup.gasAmount .pistonAndStudent) *
            molarGasConstantInSI setup.molarGasConstant *
              temperatureInKelvin
                (setup.gasTemperature .pistonAndStudent) := by
        rw [hamount, htemperature]
      _ = _ := (_laws.idealGasEquationOfState .pistonAndStudent).symm
  rw [_laws.cylindricalGasVolume .pistonOnly,
    _laws.cylindricalGasVolume .pistonAndStudent,
    _scenario.initialHeightIsOneHundredCentimeters, harea] at hisothermal
  have hisothermalPi :
      pressureInPascals (setup.gasPressureP .pistonOnly) * Real.pi =
        (pressureInPascals (setup.gasPressureP .pistonAndStudent) *
          Real.pi) *
            lengthInMeters
              (setup.gasColumnHeightH .pistonAndStudent) := by
    nlinarith only [hisothermal]
  have hheightEquation :
      101325 * Real.pi + 3136 =
        (101325 * Real.pi + 15680) *
          lengthInMeters
            (setup.gasColumnHeightH .pistonAndStudent) := by
    calc
      _ = pressureInPascals (setup.gasPressureP .pistonOnly) *
            Real.pi := hp1pi.symm
      _ = _ := hisothermalPi
      _ = _ := by rw [hp2pi]

  have sin_lt_local :
      ∀ {x : ℝ}, 0 < x → Real.sin x < x := by
    intro x hx
    rcases lt_or_ge 1 x with hlarge | hsmall
    · exact (Real.sin_le_one x).trans_lt hlarge
    · have hxabs : |x| = x := abs_of_nonneg hx.le
      have hbound :=
        le_of_abs_le
          (Real.sin_bound (show |x| ≤ 1 by rwa [hxabs]))
      rw [sub_le_iff_le_add', hxabs] at hbound
      apply hbound.trans_lt
      rw [sub_add, sub_lt_self_iff, sub_pos,
        div_eq_mul_inv (x ^ 3)]
      refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos hx 3)
      apply pow_le_pow_of_le_one hx.le hsmall
      simp
  have sin_gt_sub_cube_local :
      ∀ {x : ℝ}, 0 < x → x ≤ 1 →
        x - x ^ 3 / 4 < Real.sin x := by
    intro x hx hxone
    have hxabs : |x| = x := abs_of_nonneg hx.le
    have hbound :=
      neg_le_of_abs_le
        (Real.sin_bound (show |x| ≤ 1 by rwa [hxabs]))
    rw [le_sub_iff_add_le, hxabs] at hbound
    refine lt_of_lt_of_le ?_ hbound
    have hdiff :
        x ^ 3 / (4 : ℝ) - x ^ 3 / 6 = x ^ 3 * 12⁻¹ := by
      norm_num [div_eq_mul_inv, ← mul_sub]
    rw [add_comm, sub_add, sub_neg_eq_add, sub_lt_sub_iff_left,
      ← lt_sub_iff_add_lt', hdiff]
    refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos hx 3)
    apply pow_le_pow_of_le_one hx.le hxone
    simp
  have hpi_lower_series (n : ℕ) :
      (2 : ℝ) ^ (n + 1) *
          Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) < Real.pi := by
    have hmain :
        Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) / 2 *
            (2 : ℝ) ^ (n + 2) < Real.pi := by
      rw [← lt_div_iff₀, ← Real.sin_pi_over_two_pow_succ]
      focus
        apply sin_lt_local
        apply div_pos Real.pi_pos
      all_goals
        apply pow_pos
        norm_num
    refine lt_of_le_of_lt (le_of_eq ?_) hmain
    rw [pow_succ' _ (n + 1), ← mul_assoc, div_mul_cancel₀, mul_comm]
    simp
  have hpi_upper_series (n : ℕ) :
      Real.pi <
        (2 : ℝ) ^ (n + 1) *
            Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) +
          1 / (4 : ℝ) ^ n := by
    have hmain :
        Real.pi <
          (Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) / 2 +
            1 / ((2 : ℝ) ^ n) ^ 3 / 4) *
              (2 : ℝ) ^ (n + 2) := by
      rw [← div_lt_iff₀ (by positivity),
        ← Real.sin_pi_over_two_pow_succ, ← sub_lt_iff_lt_add']
      calc
        Real.pi / (2 : ℝ) ^ (n + 2) -
              Real.sin (Real.pi / (2 : ℝ) ^ (n + 2)) <
            (Real.pi / (2 : ℝ) ^ (n + 2)) ^ 3 / 4 :=
          sub_lt_comm.1 <|
            sin_gt_sub_cube_local (by positivity) <|
              div_le_one_of_le₀ (by
                calc
                  Real.pi ≤ 4 := Real.pi_le_four
                  _ = (2 : ℝ) ^ (0 + 2) := by norm_num
                  _ ≤ (2 : ℝ) ^ (n + 2) := by
                    gcongr <;> norm_num) (by positivity)
        _ ≤ (4 / (2 : ℝ) ^ (n + 2)) ^ 3 / 4 := by
          gcongr
          exact Real.pi_le_four
        _ = 1 / ((2 : ℝ) ^ n) ^ 3 / 4 := by
          simp [add_comm n, pow_add, div_mul_eq_div_div]
          norm_num
    refine lt_of_lt_of_le hmain (le_of_eq ?_)
    rw [add_mul]
    congr 1
    · ring
    simp only [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
      div_div, ← pow_add]
    rw [one_div, one_div, inv_mul_eq_iff_eq_mul₀, eq_comm,
      mul_inv_eq_iff_eq_mul₀, ← pow_add]
    · rw [add_assoc, Nat.mul_succ, add_comm, add_comm n,
        add_assoc, mul_comm n]
    all_goals norm_num

  have hsqrt2_sq :
      Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2_nonneg : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have hsqrt2_upper : Real.sqrt (2 : ℝ) ≤ 283 / 200 := by
    nlinarith only [hsqrt2_sq, hsqrt2_nonneg]
  let x2 : ℝ := Real.sqrt (2 + Real.sqrt 2)
  have hx2_sq : x2 ^ 2 = 2 + Real.sqrt 2 := by
    dsimp [x2]
    rw [Real.sq_sqrt]
    positivity
  have hx2_nonneg : 0 ≤ x2 := by
    dsimp [x2]
    positivity
  have hx2_upper : x2 ≤ 231 / 125 := by
    nlinarith only [hx2_sq, hx2_nonneg, hsqrt2_upper]
  have hseries2_upper :
      Real.sqrtTwoAddSeries 0 2 ≤ (231 / 125 : ℝ) := by
    simpa [Real.sqrtTwoAddSeries, x2] using hx2_upper
  have hroot2_sq :
      Real.sqrt (2 - Real.sqrtTwoAddSeries 0 2) ^ 2 =
        2 - Real.sqrtTwoAddSeries 0 2 := by
    rw [Real.sq_sqrt]
    exact sub_nonneg.mpr (Real.sqrtTwoAddSeries_lt_two 2).le
  have hroot2_nonneg :
      0 ≤ Real.sqrt (2 - Real.sqrtTwoAddSeries 0 2) :=
    Real.sqrt_nonneg _
  have hroot2_lower :
      (31 / 80 : ℝ) <
        Real.sqrt (2 - Real.sqrtTwoAddSeries 0 2) := by
    nlinarith only [hseries2_upper, hroot2_sq, hroot2_nonneg]
  have hpiLowerRaw :
      8 * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 2) < Real.pi := by
    convert hpi_lower_series 2 using 1
    all_goals norm_num
  have hpiLower : (31 / 10 : ℝ) < Real.pi := by
    nlinarith only [hroot2_lower, hpiLowerRaw]

  have hsqrt2_lower :
      (141421 / 100000 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith only [hsqrt2_sq, hsqrt2_nonneg]
  have hx2_lower : (184775 / 100000 : ℝ) ≤ x2 := by
    nlinarith only [hx2_sq, hx2_nonneg, hsqrt2_lower]
  let x3 : ℝ := Real.sqrt (2 + x2)
  have hx3_sq : x3 ^ 2 = 2 + x2 := by
    dsimp [x3]
    rw [Real.sq_sqrt]
    positivity
  have hx3_nonneg : 0 ≤ x3 := by
    dsimp [x3]
    positivity
  have hx3_lower : (196156 / 100000 : ℝ) ≤ x3 := by
    nlinarith only [hx3_sq, hx3_nonneg, hx2_lower]
  let x4 : ℝ := Real.sqrt (2 + x3)
  have hx4_sq : x4 ^ 2 = 2 + x3 := by
    dsimp [x4]
    rw [Real.sq_sqrt]
    positivity
  have hx4_nonneg : 0 ≤ x4 := by
    dsimp [x4]
    positivity
  have hx4_lower : (199036 / 100000 : ℝ) ≤ x4 := by
    nlinarith only [hx4_sq, hx4_nonneg, hx3_lower]
  have hsameRational :
      (49759 / 25000 : ℝ) = 199036 / 100000 := by
    norm_num
  have hseries4_lower :
      (49759 / 25000 : ℝ) ≤ Real.sqrtTwoAddSeries 0 4 := by
    rw [hsameRational]
    simpa [Real.sqrtTwoAddSeries, x2, x3, x4] using hx4_lower
  have hroot4_sq :
      Real.sqrt (2 - Real.sqrtTwoAddSeries 0 4) ^ 2 =
        2 - Real.sqrtTwoAddSeries 0 4 := by
    rw [Real.sq_sqrt]
    exact sub_nonneg.mpr (Real.sqrtTwoAddSeries_lt_two 4).le
  have hroot4_nonneg :
      0 ≤ Real.sqrt (2 - Real.sqrtTwoAddSeries 0 4) :=
    Real.sqrt_nonneg _
  have hroot4_upper :
      Real.sqrt (2 - Real.sqrtTwoAddSeries 0 4) <
        (100547 / 1024000 : ℝ) := by
    nlinarith only [hseries4_lower, hroot4_sq, hroot4_nonneg]
  have hpiUpperRaw :
      Real.pi <
        32 * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 4) + 1 / 256 := by
    convert hpi_upper_series 4 using 1
    all_goals norm_num
  have hpiUpper : Real.pi < (1573 / 500 : ℝ) := by
    nlinarith only [hroot4_upper, hpiUpperRaw]

  let numerator : ℝ := 101325 * Real.pi + 3136
  let denominator : ℝ := 101325 * Real.pi + 15680
  have hdenominatorPositive : 0 < denominator := by
    dsimp [denominator]
    positivity
  have hheightAsRatio :
      lengthInMeters
          (setup.gasColumnHeightH .pistonAndStudent) =
        numerator / denominator := by
    apply (eq_div_iff hdenominatorPositive.ne').2
    dsimp [numerator, denominator]
    nlinarith only [hheightEquation]
  have hheightUpper :
      lengthInMeters
          (setup.gasColumnHeightH .pistonAndStudent) ≤
        (77 / 80 : ℝ) := by
    rw [hheightAsRatio]
    apply (div_le_iff₀ hdenominatorPositive).2
    dsimp [numerator, denominator]
    nlinarith only [hpiUpper]
  have hheightLower :
      (1923 / 2000 : ℝ) ≤
        lengthInMeters
          (setup.gasColumnHeightH .pistonAndStudent) := by
    rw [hheightAsRatio]
    apply (le_div_iff₀ hdenominatorPositive).2
    dsimp [numerator, denominator]
    nlinarith only [hpiLower]

  change
    |100 *
          (lengthInMeters (setup.gasColumnHeightH .pistonOnly) -
            lengthInMeters
              (setup.gasColumnHeightH .pistonAndStudent)) -
        19 / 5| ≤ 1 / 20
  rw [_scenario.initialHeightIsOneHundredCentimeters, abs_le]
  constructor
  · nlinarith only [hheightUpper]
  · nlinarith only [hheightLower]

end PhyXMiniProblems.ProblemPhyXMini0360
