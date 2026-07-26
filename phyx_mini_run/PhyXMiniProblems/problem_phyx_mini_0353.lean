import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0353

open Dimension

/-!
# Coefficient of performance of a hydrogen-gas refrigerator

The primary figure is a pressure--volume diagram for the directed cycle
`a → b → c → a`.  The gas expands isothermally from `a` to `b`, is heated at
constant volume from `b` to `c`, and is compressed at constant pressure from
`c` to `a`.  The refrigerator contains `0.850 mol` of ideal diatomic hydrogen.

Pressure, volume, heat, work, and internal-energy change are represented by
dimensionful Physlib quantities.  Real numbers occur only as readouts in
named units, for the mole count, and for the dimensionless coefficient of
performance.  In particular, the coefficient of performance is an independent
setup field and is not defined to be the displayed answer.
-/

/-! ## Dimensionful quantities and unit readouts -/

/-- A signed physical volume, with dimension `length³`. -/
abbrev GasVolume : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/--
Energy per mole per kelvin.  The amount of substance is recorded numerically
in moles, so only the energy and temperature dimensions occur in this type.
-/
abbrev MolarEnergyPerKelvin : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) ℝ)

/-- Read a physical pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a physical pressure in standard atmospheres. -/
def pressureInAtmospheres (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure /
    pressureInPascals DimPressure.standardAtmosphere

/-- Read a physical volume in cubic metres. -/
def volumeInCubicMeters (volume : GasVolume) : ℝ :=
  (volume UnitChoices.SI).val

/-- Read a physical energy in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read a molar energy-per-kelvin quantity in joules per mole-kelvin. -/
def molarEnergyPerKelvinInSI (quantity : MolarEnergyPerKelvin) : ℝ :=
  (quantity UnitChoices.SI).val

/-! ## Cycle, gas, and primary-figure vocabulary -/

/-- The three labeled thermodynamic states in the supplied diagram. -/
inductive CyclePoint where
  | a
  | b
  | c
  deriving DecidableEq, Repr

/-- The three directed legs, named in their arrow direction. -/
inductive CycleLeg where
  | ab
  | bc
  | ca
  deriving DecidableEq, Repr

/-- Initial state of each directed process. -/
def startPoint : CycleLeg → CyclePoint
  | .ab => .a
  | .bc => .b
  | .ca => .c

/-- Final state of each directed process. -/
def endPoint : CycleLeg → CyclePoint
  | .ab => .b
  | .bc => .c
  | .ca => .a

/-- Process classifications used by the problem and inferred from the axes. -/
inductive ProcessKind where
  | isothermal
  | isochoric
  | isobaric
  deriving DecidableEq, Repr

/-- The working substance specified by the problem. -/
inductive GasSpecies where
  | diatomicHydrogen
  deriving DecidableEq, Repr

/-- Whether the working substance is modeled as an ideal gas. -/
inductive GasModel where
  | ideal
  deriving DecidableEq, Repr

/-- A thermodynamic state with dimensionful pressure and volume. -/
structure GasState where
  pressure : DimPressure
  volume : GasVolume
  temperature : Temperature

/-- Unit printed on the vertical axis of the primary diagram. -/
inductive PressureAxisUnit where
  | atmosphere
  deriving DecidableEq, Repr

/-- Unit printed on the horizontal axis of the primary diagram. -/
inductive VolumeAxisUnit where
  | cubicMeter
  deriving DecidableEq, Repr

/-- Label printed where the two diagram axes meet. -/
inductive OriginLabel where
  | O
  deriving DecidableEq, Repr

/--
Qualitative evidence transcribed from the actual raster image.  A shown
directed leg uses the direction encoded in `CycleLeg`.
-/
structure PVDiagramFigure where
  showsPoint : CyclePoint → Bool
  showsDirectedLeg : CycleLeg → Bool
  pressureAxisUnit : PressureAxisUnit
  volumeAxisUnit : VolumeAxisUnit
  originLabel : OriginLabel
  abDrawnCurved : Bool
  bcDrawnVertical : Bool
  caDrawnHorizontal : Bool
  bAndCVerticallyAligned : Bool
  cAndAHorizontallyAligned : Bool

/-! ## Independent setup and assumption interfaces -/

/--
Independent physical quantities for the refrigerator cycle.  Heat is positive
when transferred into the gas, and work is positive when done by the gas.
`coldSpaceHeatAbsorbed` and `cycleWorkInput` are positive energy magnitudes.
-/
structure HydrogenRefrigeratorSetup where
  figure : PVDiagramFigure
  species : GasSpecies
  gasModel : GasModel
  amountOfGasMoles : ℝ
  state : CyclePoint → GasState
  processKind : CycleLeg → ProcessKind
  molarGasConstant : MolarEnergyPerKelvin
  molarHeatCapacityAtConstantVolume : MolarEnergyPerKelvin
  heatIntoGas : CycleLeg → DimEnergy
  workDoneByGas : CycleLeg → DimEnergy
  internalEnergyChange : CycleLeg → DimEnergy
  coldSpaceHeatAbsorbed : DimEnergy
  cycleWorkInput : DimEnergy
  coefficientOfPerformance : ℝ

/-- Scenario facts stated in the prose, excluding the requested coefficient. -/
structure MatchesProblemScenario (setup : HydrogenRefrigeratorSetup) : Prop where
  hydrogenWorkingSubstance : setup.species = .diatomicHydrogen
  idealGasApproximation : setup.gasModel = .ideal
  amountOfGas : setup.amountOfGasMoles = 17 / 20
  processAB : setup.processKind .ab = .isothermal
  processBC : setup.processKind .bc = .isochoric
  processCA : setup.processKind .ca = .isobaric

/-!
Numerical and qualitative information read from the primary image.  The
pressure at `b` is deliberately only constrained to lie below the `0.700 atm`
line: its numerical value follows from the isothermal law rather than being a
figure datum.
-/
structure MatchesPrimaryFigure (setup : HydrogenRefrigeratorSetup) : Prop where
  everyPointShown : ∀ point, setup.figure.showsPoint point = true
  everyDirectedLegShown : ∀ leg, setup.figure.showsDirectedLeg leg = true
  pressureAxisInAtmospheres :
    setup.figure.pressureAxisUnit = .atmosphere
  volumeAxisInCubicMeters :
    setup.figure.volumeAxisUnit = .cubicMeter
  originMarkedO : setup.figure.originLabel = .O
  abCurveShown : setup.figure.abDrawnCurved = true
  bcVerticalShown : setup.figure.bcDrawnVertical = true
  caHorizontalShown : setup.figure.caDrawnHorizontal = true
  bAndCAligned : setup.figure.bAndCVerticallyAligned = true
  cAndAAligned : setup.figure.cAndAHorizontallyAligned = true
  volumeAtA : volumeInCubicMeters (setup.state .a).volume = 3 / 100
  volumeAtB : volumeInCubicMeters (setup.state .b).volume = 1 / 10
  volumeAtC : volumeInCubicMeters (setup.state .c).volume = 1 / 10
  pressureAtA :
    pressureInAtmospheres (setup.state .a).pressure = 7 / 10
  pressureAtC :
    pressureInAtmospheres (setup.state .c).pressure = 7 / 10
  pressureAtBBelowTopLine :
    pressureInAtmospheres (setup.state .b).pressure < 7 / 10

/-- Positivity assumptions selecting the physical refrigerator branch. -/
structure HasPhysicalCycleParameters (setup : HydrogenRefrigeratorSetup) : Prop where
  gasAmountPositive : 0 < setup.amountOfGasMoles
  pressurePositive :
    ∀ point, 0 < pressureInPascals (setup.state point).pressure
  volumePositive :
    ∀ point, 0 < volumeInCubicMeters (setup.state point).volume
  temperaturePositive :
    ∀ point, 0 < (setup.state point).temperature.toReal
  gasConstantPositive :
    0 < molarEnergyPerKelvinInSI setup.molarGasConstant
  heatCapacityPositive :
    0 < molarEnergyPerKelvinInSI
      setup.molarHeatCapacityAtConstantVolume
  coldHeatPositive : 0 < energyInJoules setup.coldSpaceHeatAbsorbed
  workInputPositive : 0 < energyInJoules setup.cycleWorkInput
  coefficientOfPerformanceNonnegative :
    0 ≤ setup.coefficientOfPerformance

/-!
Governing thermodynamic laws for this cycle, expressed in coherent SI
readouts:

* `pV = nRT` at each state;
* `C_V = (5/2)R` for ideal diatomic hydrogen;
* `ΔU = Q - W` and `ΔU = n C_V ΔT` on each leg;
* the standard isothermal, isochoric, and isobaric work relations;
* cold-side heat and work-input balances for the complete refrigerator cycle;
* the defining relation `COP · W_in = Q_cold`.

None of these fields gives a numerical value for the coefficient of
performance.
-/
structure SatisfiesIdealDiatomicRefrigeratorLaws
    (setup : HydrogenRefrigeratorSetup) : Prop where
  idealGasLaw : ∀ point,
    pressureInPascals (setup.state point).pressure *
        volumeInCubicMeters (setup.state point).volume =
      setup.amountOfGasMoles *
        molarEnergyPerKelvinInSI setup.molarGasConstant *
          (setup.state point).temperature.toReal
  diatomicHydrogenHeatCapacity :
    molarEnergyPerKelvinInSI
        setup.molarHeatCapacityAtConstantVolume =
      (5 / 2) * molarEnergyPerKelvinInSI setup.molarGasConstant
  isothermalAB :
    (setup.state .a).temperature = (setup.state .b).temperature
  isochoricBC : (setup.state .b).volume = (setup.state .c).volume
  isobaricCA : (setup.state .c).pressure = (setup.state .a).pressure
  firstLaw : ∀ leg,
    energyInJoules (setup.internalEnergyChange leg) =
      energyInJoules (setup.heatIntoGas leg) -
        energyInJoules (setup.workDoneByGas leg)
  idealGasInternalEnergyChange : ∀ leg,
    energyInJoules (setup.internalEnergyChange leg) =
      setup.amountOfGasMoles *
        molarEnergyPerKelvinInSI
          setup.molarHeatCapacityAtConstantVolume *
        ((setup.state (endPoint leg)).temperature.toReal -
          (setup.state (startPoint leg)).temperature.toReal)
  isothermalExpansionWork :
    energyInJoules (setup.workDoneByGas .ab) =
      setup.amountOfGasMoles *
        molarEnergyPerKelvinInSI setup.molarGasConstant *
        (setup.state .a).temperature.toReal *
        Real.log
          (volumeInCubicMeters (setup.state .b).volume /
            volumeInCubicMeters (setup.state .a).volume)
  isochoricWork : energyInJoules (setup.workDoneByGas .bc) = 0
  isobaricCompressionWork :
    energyInJoules (setup.workDoneByGas .ca) =
      pressureInPascals (setup.state .c).pressure *
        (volumeInCubicMeters (setup.state .a).volume -
          volumeInCubicMeters (setup.state .c).volume)
  coldSpaceHeatBalance :
    energyInJoules setup.coldSpaceHeatAbsorbed =
      energyInJoules (setup.heatIntoGas .ab) +
        energyInJoules (setup.heatIntoGas .bc)
  workInputBalance :
    energyInJoules setup.cycleWorkInput =
      -(energyInJoules (setup.workDoneByGas .ab) +
        energyInJoules (setup.workDoneByGas .bc) +
        energyInJoules (setup.workDoneByGas .ca))
  coefficientOfPerformanceDefinition :
    setup.coefficientOfPerformance *
        energyInJoules setup.cycleWorkInput =
      energyInJoules setup.coldSpaceHeatAbsorbed

/-! ## Closed form and multiple-choice target -/

/--
The exact dimensionless COP obtained after the common pressure scale and the
gas amount cancel.  The first numerator term is the isothermal heat on `ab`;
the second is the constant-volume heat on `bc`; the denominator is the work
input over the cycle.
-/
def exactCoefficientOfPerformance : ℝ :=
  ((3 / 100 : ℝ) * Real.log (10 / 3) +
      (5 / 2) * (7 / 100)) /
    ((7 / 100) - (3 / 100) * Real.log (10 / 3))

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Dimensionless coefficient printed by each answer choice. -/
def answerCoefficientOfPerformance : AnswerChoice → ℝ
  | .A => 512 / 100
  | .B => 623 / 100
  | .C => 221 / 100
  | .D => 505 / 100

/-- Dataset metadata records answer B; this definition is not a theorem premise. -/
def recordedAnswerChoice : AnswerChoice := .B

/-- A real value rounds to the displayed coefficient at two decimal places. -/
def RoundsToDisplayedHundredth (value displayed : ℝ) : Prop :=
  |value - displayed| < 1 / 200

/-- The selected answer is strictly closer than every other displayed choice. -/
def IsUniqueClosestDisplayedAnswer
    (setup : HydrogenRefrigeratorSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |setup.coefficientOfPerformance -
        answerCoefficientOfPerformance choice| <
      |setup.coefficientOfPerformance -
        answerCoefficientOfPerformance other|

/-!
The cycle laws give the exact logarithmic coefficient above.  Numerically it
rounds to `6.23`, which is uniquely answer B.

This formalizes blueprint label `thm:physics:phyx_mini_0353:target`.
-/
theorem refrigerator_coefficient_of_performance
    (setup : HydrogenRefrigeratorSetup)
    (_scenario : MatchesProblemScenario setup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasPhysicalCycleParameters setup)
    (_laws : SatisfiesIdealDiatomicRefrigeratorLaws setup) :
    setup.coefficientOfPerformance = exactCoefficientOfPerformance ∧
      RoundsToDisplayedHundredth setup.coefficientOfPerformance
        (answerCoefficientOfPerformance .B) ∧
      IsUniqueClosestDisplayedAnswer setup .B := by
  have htemperatureAB :
      (setup.state .a).temperature.toReal =
        (setup.state .b).temperature.toReal :=
    congrArg Temperature.toReal _laws.isothermalAB
  have hpressureCA :
      pressureInPascals (setup.state .c).pressure =
        pressureInPascals (setup.state .a).pressure :=
    congrArg pressureInPascals _laws.isobaricCA
  have hinternalEnergyAB :
      energyInJoules (setup.internalEnergyChange .ab) = 0 := by
    rw [_laws.idealGasInternalEnergyChange]
    simp [startPoint, endPoint, htemperatureAB]
  have hheatAB :
      energyInJoules (setup.heatIntoGas .ab) =
        energyInJoules (setup.workDoneByGas .ab) := by
    linarith [_laws.firstLaw .ab]
  have hworkAB :
      energyInJoules (setup.workDoneByGas .ab) =
        pressureInPascals (setup.state .a).pressure * (3 / 100) *
          Real.log (10 / 3) := by
    rw [_laws.isothermalExpansionWork, ← _laws.idealGasLaw .a,
      _figure.volumeAtA, _figure.volumeAtB]
    norm_num
  have hidealGasAtB :
      setup.amountOfGasMoles *
          molarEnergyPerKelvinInSI setup.molarGasConstant *
            (setup.state .b).temperature.toReal =
        pressureInPascals (setup.state .a).pressure *
          volumeInCubicMeters (setup.state .a).volume := by
    rw [← htemperatureAB]
    exact (_laws.idealGasLaw .a).symm
  have hidealGasAtC :
      setup.amountOfGasMoles *
          molarEnergyPerKelvinInSI setup.molarGasConstant *
            (setup.state .c).temperature.toReal =
        pressureInPascals (setup.state .c).pressure *
          volumeInCubicMeters (setup.state .c).volume :=
    (_laws.idealGasLaw .c).symm
  have hinternalEnergyBC :
      energyInJoules (setup.internalEnergyChange .bc) =
        (5 / 2) *
          (pressureInPascals (setup.state .c).pressure *
              volumeInCubicMeters (setup.state .c).volume -
            pressureInPascals (setup.state .a).pressure *
              volumeInCubicMeters (setup.state .a).volume) := by
    rw [_laws.idealGasInternalEnergyChange]
    simp only [startPoint, endPoint]
    rw [_laws.diatomicHydrogenHeatCapacity]
    calc
      setup.amountOfGasMoles *
            ((5 / 2) *
              molarEnergyPerKelvinInSI setup.molarGasConstant) *
          ((setup.state .c).temperature.toReal -
            (setup.state .b).temperature.toReal) =
          (5 / 2) *
            (setup.amountOfGasMoles *
                  molarEnergyPerKelvinInSI setup.molarGasConstant *
                    (setup.state .c).temperature.toReal -
              setup.amountOfGasMoles *
                  molarEnergyPerKelvinInSI setup.molarGasConstant *
                    (setup.state .b).temperature.toReal) := by ring
      _ = (5 / 2) *
          (pressureInPascals (setup.state .c).pressure *
                volumeInCubicMeters (setup.state .c).volume -
            pressureInPascals (setup.state .a).pressure *
                volumeInCubicMeters (setup.state .a).volume) := by
          rw [hidealGasAtB, hidealGasAtC]
  have hheatBC :
      energyInJoules (setup.heatIntoGas .bc) =
        pressureInPascals (setup.state .a).pressure *
          ((5 / 2) * (7 / 100)) := by
    have hfirstLawBC := _laws.firstLaw .bc
    rw [hinternalEnergyBC, _laws.isochoricWork, hpressureCA,
      _figure.volumeAtA, _figure.volumeAtC] at hfirstLawBC
    norm_num at hfirstLawBC ⊢
    linarith
  have hcoldHeat :
      energyInJoules setup.coldSpaceHeatAbsorbed =
        pressureInPascals (setup.state .a).pressure *
          ((3 / 100) * Real.log (10 / 3) +
            (5 / 2) * (7 / 100)) := by
    rw [_laws.coldSpaceHeatBalance, hheatAB, hworkAB, hheatBC]
    ring
  have hworkCA :
      energyInJoules (setup.workDoneByGas .ca) =
        -(pressureInPascals (setup.state .a).pressure * (7 / 100)) := by
    rw [_laws.isobaricCompressionWork, hpressureCA,
      _figure.volumeAtA, _figure.volumeAtC]
    ring
  have hworkInput :
      energyInJoules setup.cycleWorkInput =
        pressureInPascals (setup.state .a).pressure *
          ((7 / 100) - (3 / 100) * Real.log (10 / 3)) := by
    rw [_laws.workInputBalance, hworkAB, _laws.isochoricWork, hworkCA]
    ring
  have hpressurePositive :
      0 < pressureInPascals (setup.state .a).pressure :=
    _physical.pressurePositive .a
  have hdenominatorPositive :
      0 < (7 / 100 : ℝ) - (3 / 100) * Real.log (10 / 3) := by
    have hproductPositive :
        0 < pressureInPascals (setup.state .a).pressure *
          ((7 / 100) - (3 / 100) * Real.log (10 / 3)) := by
      rw [← hworkInput]
      exact _physical.workInputPositive
    rcases mul_pos_iff.mp hproductPositive with hpositive | hnegative
    · exact hpositive.2
    · exact (not_lt_of_ge hpressurePositive.le hnegative.1).elim
  have hcoefficientTimesDenominator :
      setup.coefficientOfPerformance *
          ((7 / 100) - (3 / 100) * Real.log (10 / 3)) =
        (3 / 100) * Real.log (10 / 3) +
          (5 / 2) * (7 / 100) := by
    have hcoefficientLaw := _laws.coefficientOfPerformanceDefinition
    rw [hworkInput, hcoldHeat] at hcoefficientLaw
    apply (mul_left_cancel₀ hpressurePositive.ne')
    calc
      pressureInPascals (setup.state .a).pressure *
          (setup.coefficientOfPerformance *
            ((7 / 100) - (3 / 100) * Real.log (10 / 3))) =
        setup.coefficientOfPerformance *
          (pressureInPascals (setup.state .a).pressure *
            ((7 / 100) - (3 / 100) * Real.log (10 / 3))) := by ring
      _ = pressureInPascals (setup.state .a).pressure *
          ((3 / 100) * Real.log (10 / 3) +
            (5 / 2) * (7 / 100)) := hcoefficientLaw
  have hcoefficient :
      setup.coefficientOfPerformance = exactCoefficientOfPerformance := by
    unfold exactCoefficientOfPerformance
    exact (eq_div_iff hdenominatorPositive.ne').2
      hcoefficientTimesDenominator
  have hlogLower :
      (1043 / 867 : ℝ) < Real.log (10 / 3) := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 10 / 3)]
    calc
      Real.exp (1043 / 867 : ℝ) =
          Real.exp ((1043 / 867 : ℝ) / 16) ^ 16 := by
            rw [← Real.exp_nat_mul]
            congr 1
            norm_num
      _ < ((2 + (1043 / 867 : ℝ) / 16) /
            (2 - (1043 / 867 : ℝ) / 16)) ^ 16 := by
          gcongr
          exact Real.exp_lt_two_add_div_two_sub (by norm_num) (by norm_num)
      _ < (10 / 3 : ℝ) := by norm_num
  have hlogUpper :
      Real.log (10 / 3) < (1743 / 1447 : ℝ) := by
    rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 10 / 3)]
    calc
      (10 / 3 : ℝ) <
          ∑ i ∈ Finset.range 7,
            (1743 / 1447 : ℝ) ^ i / Nat.factorial i := by
              norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp (1743 / 1447 : ℝ) :=
        Real.sum_le_exp_of_nonneg (by norm_num) 7
  have hexactLower :
      (249 / 40 : ℝ) < exactCoefficientOfPerformance := by
    unfold exactCoefficientOfPerformance
    rw [lt_div_iff₀ hdenominatorPositive]
    nlinarith [hlogLower]
  have hexactUpper :
      exactCoefficientOfPerformance < (1247 / 200 : ℝ) := by
    unfold exactCoefficientOfPerformance
    rw [div_lt_iff₀ hdenominatorPositive]
    nlinarith [hlogUpper]
  have hrounding :
      RoundsToDisplayedHundredth setup.coefficientOfPerformance
        (answerCoefficientOfPerformance .B) := by
    rw [RoundsToDisplayedHundredth, hcoefficient, abs_lt]
    norm_num [answerCoefficientOfPerformance] at hexactLower hexactUpper ⊢
    constructor <;> linarith
  refine ⟨hcoefficient, hrounding, ?_⟩
  have hcoefficientLower :
      (249 / 40 : ℝ) < setup.coefficientOfPerformance := by
    rw [hcoefficient]
    exact hexactLower
  have hdistanceB :
      |setup.coefficientOfPerformance - (623 / 100 : ℝ)| <
        (1 / 200 : ℝ) := by
    simpa [RoundsToDisplayedHundredth, answerCoefficientOfPerformance]
      using hrounding
  intro other hother
  cases other with
  | A =>
      change
        |setup.coefficientOfPerformance - (623 / 100 : ℝ)| <
          |setup.coefficientOfPerformance - (512 / 100 : ℝ)|
      have hdistanceA :
          |setup.coefficientOfPerformance - (512 / 100 : ℝ)| =
            setup.coefficientOfPerformance - (512 / 100 : ℝ) :=
        abs_of_pos (by nlinarith [hcoefficientLower])
      rw [hdistanceA]
      nlinarith
  | B =>
      exact (hother rfl).elim
  | C =>
      change
        |setup.coefficientOfPerformance - (623 / 100 : ℝ)| <
          |setup.coefficientOfPerformance - (221 / 100 : ℝ)|
      have hdistanceC :
          |setup.coefficientOfPerformance - (221 / 100 : ℝ)| =
            setup.coefficientOfPerformance - (221 / 100 : ℝ) :=
        abs_of_pos (by nlinarith [hcoefficientLower])
      rw [hdistanceC]
      nlinarith
  | D =>
      change
        |setup.coefficientOfPerformance - (623 / 100 : ℝ)| <
          |setup.coefficientOfPerformance - (505 / 100 : ℝ)|
      have hdistanceD :
          |setup.coefficientOfPerformance - (505 / 100 : ℝ)| =
            setup.coefficientOfPerformance - (505 / 100 : ℝ) :=
        abs_of_pos (by nlinarith [hcoefficientLower])
      rw [hdistanceD]
      nlinarith

end PhyXMiniProblems.ProblemPhyXMini0353
