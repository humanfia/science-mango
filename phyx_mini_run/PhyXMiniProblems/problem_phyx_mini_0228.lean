import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0228

open Dimension

/-!
# Torsion constant of a watch balance-wheel spring

The source gives a balance-wheel period of `0.250 s`, a wheel mass of
`20.0 g`, and a rim radius of `0.500 cm`.  The primary image identifies the
balance wheel inside the watch mechanism by a printed label and pointer.

Mass, length, time, moment of inertia, and torsion constant are represented by
unit-independent Physlib quantities.  Real numbers below occur only as scalar
readouts in named units and as the numerical values printed in the answer list.
-/

/-! ## Dimensionful physical quantities and unit readouts -/

/-- A nonnegative physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length, used for the balance-wheel rim radius. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration, used for the oscillation period. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- Moment of inertia, carrying the physical dimension mass times length squared. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/--
Torsion constant of a rotational spring.  Radians are dimensionless, so
`N m / rad` has dimension `mass * length^2 / time^2`, the same dimension as
energy but a distinct physical role in this model.
-/
abbrev TorsionConstantQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical duration in a selected time unit. -/
def timeReadout (unit : TimeUnit) (duration : TimeQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read moment of inertia in the selected mass unit times length unit squared. -/
def momentOfInertiaReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia {UnitChoices.SI with
    mass := massUnit, length := lengthUnit}).val : ℝ)

/--
Read a torsion constant in the coherent unit
`massUnit * lengthUnit^2 / timeUnit^2` per dimensionless radian.
-/
def torsionConstantReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (torsionConstant : TorsionConstantQuantity) : ℝ :=
  ((torsionConstant {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val : ℝ)

/-- The period readout in seconds. -/
def periodInSeconds (period : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.seconds period

/-- The wheel-mass readout in grams. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.grams mass

/-- The rim-radius readout in centimeters. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- The wheel-mass readout in SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- The rim-radius readout in SI meters. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Moment of inertia in SI `kg m^2`. -/
def momentOfInertiaInSI (inertia : MomentOfInertiaQuantity) : ℝ :=
  momentOfInertiaReadout MassUnit.kilograms LengthUnit.meters inertia

/-- Torsion constant in SI `N m / rad`, equivalently `kg m^2 s^-2`. -/
def torsionConstantInSI (torsionConstant : TorsionConstantQuantity) : ℝ :=
  torsionConstantReadout MassUnit.kilograms LengthUnit.meters
    TimeUnit.seconds torsionConstant

/-! ## Physical roles and figure-derived labels -/

/-- Watch components distinguished by the source and the primary image. -/
inductive WatchComponent where
  | balanceWheel
  | otherMechanism
  deriving DecidableEq, Repr

/-- Text labels visible in the supplied image. -/
inductive FigureLabel where
  | balanceWheel
  deriving DecidableEq, Repr

/-- The radial mass-distribution idealization used for the wheel. -/
inductive WheelMassDistribution where
  | concentratedAroundRim
  | unspecified
  deriving DecidableEq, Repr

/-- The mechanical type of the spring attached to the balance wheel. -/
inductive AttachedSpringKind where
  | torsionSpring
  | unspecified
  deriving DecidableEq, Repr

/-- The ideal oscillation regime in which the standard torsional period law applies. -/
inductive OscillationRegime where
  | smallUndampedTorsional
  | unspecified
  deriving DecidableEq, Repr

/-- Qualitative evidence read from the supplied watch image. -/
structure BalanceWheelFigure where
  showsWatchMechanism : Bool
  showsBalanceWheel : Bool
  printedLabel : FigureLabel
  labelPointerTarget : WatchComponent
  showsInterconnectedGearsWheelsAndLevers : Bool

/-!
The physical quantities are independent fields.  In particular,
`springTorsionConstant` is not defined from the answer value or from the other
measurements; it is constrained only by the governing torsional-oscillator law.
-/
structure WatchBalanceWheelSetup where
  wheelMass : MassQuantity
  rimRadius : LengthQuantity
  momentOfInertia : MomentOfInertiaQuantity
  oscillationPeriod : TimeQuantity
  springTorsionConstant : TorsionConstantQuantity
  massDistribution : WheelMassDistribution
  attachedSpringKind : AttachedSpringKind
  oscillationRegime : OscillationRegime
  figure : BalanceWheelFigure

/-! ## Assumptions: source data, physical regime, and governing laws -/

/--
Numerical data stated in the problem and qualitative evidence visible in the
primary image.  This predicate contains no torsion-constant value and names no
answer choice.
-/
structure MatchesProblemAndFigureReadouts
    (setup : WatchBalanceWheelSetup) : Prop where
  periodSeconds : periodInSeconds setup.oscillationPeriod = 1 / 4
  wheelMassGrams : massInGrams setup.wheelMass = 20
  rimRadiusCentimeters : lengthInCentimeters setup.rimRadius = 1 / 2
  massIsConcentratedAroundRim :
    setup.massDistribution = .concentratedAroundRim
  attachedSpringIsTorsional : setup.attachedSpringKind = .torsionSpring
  figureShowsWatchMechanism : setup.figure.showsWatchMechanism = true
  figureShowsBalanceWheel : setup.figure.showsBalanceWheel = true
  figurePrintedLabel : setup.figure.printedLabel = .balanceWheel
  figurePointerTargetsBalanceWheel :
    setup.figure.labelPointerTarget = .balanceWheel
  figureShowsInterconnectedMechanism :
    setup.figure.showsInterconnectedGearsWheelsAndLevers = true

/-- The idealized small, undamped torsional-oscillation regime. -/
structure UsesIdealTorsionalOscillatorModel
    (setup : WatchBalanceWheelSetup) : Prop where
  smallUndampedTorsionalMotion :
    setup.oscillationRegime = .smallUndampedTorsional

/-- Positivity and nondegeneracy conditions for the mechanical parameters. -/
structure HasPhysicalBalanceWheelParameters
    (setup : WatchBalanceWheelSetup) : Prop where
  massPositive : ∀ unit, 0 < massReadout unit setup.wheelMass
  radiusPositive : ∀ unit, 0 < lengthReadout unit setup.rimRadius
  momentOfInertiaPositive :
    ∀ massUnit lengthUnit,
      0 < momentOfInertiaReadout massUnit lengthUnit setup.momentOfInertia
  periodPositive : ∀ unit, 0 < timeReadout unit setup.oscillationPeriod
  torsionConstantPositive :
    ∀ massUnit lengthUnit timeUnit,
      0 < torsionConstantReadout massUnit lengthUnit timeUnit
        setup.springTorsionConstant

/--
Thin-ring moment-of-inertia law for a mass concentrated around a rim:
`I = m r^2`, stated in every coherent pair of mass and length units.
-/
structure SatisfiesRimMomentOfInertiaLaw
    (setup : WatchBalanceWheelSetup) : Prop where
  rimMomentOfInertia :
    ∀ massUnit lengthUnit,
      momentOfInertiaReadout massUnit lengthUnit setup.momentOfInertia =
        massReadout massUnit setup.wheelMass *
          lengthReadout lengthUnit setup.rimRadius ^ 2

/--
Governing period law for an ideal torsional oscillator:
`T = 2 pi sqrt (I / kappa)`.  The law relates the unknown torsion constant to
the independently stored period and inertia, but assigns it no answer value.
-/
structure SatisfiesTorsionalOscillatorPeriodLaw
    (setup : WatchBalanceWheelSetup) : Prop where
  periodLaw :
    ∀ massUnit lengthUnit timeUnit,
      timeReadout timeUnit setup.oscillationPeriod =
        2 * Real.pi *
          Real.sqrt
            (momentOfInertiaReadout massUnit lengthUnit
                setup.momentOfInertia /
              torsionConstantReadout massUnit lengthUnit timeUnit
                setup.springTorsionConstant)

/-! ## Derived quantities, displayed answers, and current target -/

/-- Labels of the four numerical choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Torsion-constant readout printed beside each choice, interpreted in `N m / rad`. -/
def displayedAnswerTorsionConstantSI : AnswerChoice → ℝ
  | .A => 361 / 1000000
  | .B => 316 / 100000
  | .C => 216 / 1000000
  | .D => 316 / 1000000

/-- Half a unit in the final displayed significant digit of each choice. -/
def displayedAnswerToleranceSI : AnswerChoice → ℝ
  | .A => 1 / 2000000
  | .B => 1 / 200000
  | .C => 1 / 2000000
  | .D => 1 / 2000000

/-- The answer label recorded by the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Agreement of a physical torsion constant with a displayed rounded choice. -/
def MatchesAnswerChoice
    (torsionConstant : TorsionConstantQuantity) (choice : AnswerChoice) : Prop :=
  |torsionConstantInSI torsionConstant -
      displayedAnswerTorsionConstantSI choice| ≤
    displayedAnswerToleranceSI choice

/--
The source mass and radius, together with the rim-concentrated model, imply
the intermediate moment of inertia `I = 1 / 2,000,000 kg m^2`.
-/
lemma momentOfInertiaInSI_eq_one_div_twoMillion
    (setup : WatchBalanceWheelSetup)
    (hData : MatchesProblemAndFigureReadouts setup)
    (hRim : SatisfiesRimMomentOfInertiaLaw setup) :
    momentOfInertiaInSI setup.momentOfInertia = 1 / 2000000 := by
  have hMassConversion :
      massInGrams setup.wheelMass =
        1000 * massInKilograms setup.wheelMass := by
    have h := congrArg (fun value ↦ ((value.val : NNReal) : ℝ))
      (setup.wheelMass.2 UnitChoices.SI
        {UnitChoices.SI with mass := MassUnit.grams})
    norm_num [massInGrams, massInKilograms, massReadout,
      UnitChoices.dimScale, M𝓭, MassUnit.grams, MassUnit.kilograms,
      MassUnit.scale, MassUnit.div_eq_val, NNReal.smul_def,
      smul_eq_mul] at h ⊢
    exact h
  have hMassKilograms :
      massInKilograms setup.wheelMass = (1 : ℝ) / 50 := by
    rw [hData.wheelMassGrams] at hMassConversion
    linarith
  have hLengthConversion :
      lengthInCentimeters setup.rimRadius =
        100 * lengthInMeters setup.rimRadius := by
    have h := congrArg (fun value ↦ ((value.val : NNReal) : ℝ))
      (setup.rimRadius.2 UnitChoices.SI
        {UnitChoices.SI with length := LengthUnit.centimeters})
    norm_num [lengthInCentimeters, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.centimeters, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.smul_def,
      smul_eq_mul] at h ⊢
    exact h
  have hRadiusMeters :
      lengthInMeters setup.rimRadius = (1 : ℝ) / 200 := by
    rw [hData.rimRadiusCentimeters] at hLengthConversion
    linarith
  have hInertia := hRim.rimMomentOfInertia
    MassUnit.kilograms LengthUnit.meters
  change
    momentOfInertiaInSI setup.momentOfInertia =
      massInKilograms setup.wheelMass *
        lengthInMeters setup.rimRadius ^ 2 at hInertia
  rw [hMassKilograms, hRadiusMeters] at hInertia
  norm_num at hInertia ⊢
  exact hInertia

/--
For the stated balance wheel, the ideal model gives
`kappa = pi^2 / 31250 N m / rad`.  This is approximately
`3.16 * 10^-4 N m / rad`, hence it matches recorded answer choice D.

This theorem formalizes `thm:physics:phyx_mini_0228:target`.
-/
theorem problem_phyx_mini_0228
    (setup : WatchBalanceWheelSetup)
    (hData : MatchesProblemAndFigureReadouts setup)
    (hModel : UsesIdealTorsionalOscillatorModel setup)
    (hPhysical : HasPhysicalBalanceWheelParameters setup)
    (hRim : SatisfiesRimMomentOfInertiaLaw setup)
    (hPeriod : SatisfiesTorsionalOscillatorPeriodLaw setup) :
    torsionConstantInSI setup.springTorsionConstant =
        Real.pi ^ 2 / 31250 ∧
      MatchesAnswerChoice setup.springTorsionConstant recordedDatasetAnswer := by
  have hInertia :=
    momentOfInertiaInSI_eq_one_div_twoMillion setup hData hRim
  have hTorsionPositive :
      0 < torsionConstantInSI setup.springTorsionConstant := by
    exact hPhysical.torsionConstantPositive
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  have hPeriodSI := hPeriod.periodLaw
    MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  change
    periodInSeconds setup.oscillationPeriod =
      2 * Real.pi *
        Real.sqrt
          (momentOfInertiaInSI setup.momentOfInertia /
            torsionConstantInSI setup.springTorsionConstant) at hPeriodSI
  rw [hData.periodSeconds, hInertia] at hPeriodSI
  have hRatioNonnegative :
      0 ≤ (1 / 2000000 : ℝ) /
        torsionConstantInSI setup.springTorsionConstant :=
    div_nonneg (by norm_num) hTorsionPositive.le
  have hSquared := congrArg (fun value : ℝ ↦ value ^ 2) hPeriodSI
  rw [mul_pow, Real.sq_sqrt hRatioNonnegative] at hSquared
  have hTorsionExact :
      torsionConstantInSI setup.springTorsionConstant =
        Real.pi ^ 2 / 31250 := by
    field_simp [ne_of_gt hTorsionPositive] at hSquared ⊢
    nlinarith
  constructor
  · exact hTorsionExact
  · rw [MatchesAnswerChoice, recordedDatasetAnswer,
      displayedAnswerTorsionConstantSI, displayedAnswerToleranceSI,
      hTorsionExact]
    have hSinPiDivThirtyTwoBounds :
        (0.09801 : ℝ) < Real.sin (Real.pi / 32) ∧
          Real.sin (Real.pi / 32) < (0.09802 : ℝ) := by
      have hSqrtTwoLower : (1.41421 : ℝ) < Real.sqrt 2 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      have hSqrtTwoUpper : Real.sqrt 2 < (1.41422 : ℝ) := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num
      have hNestedSqrtThreeLower :
          (1.847757 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num at ⊢
        linarith
      have hNestedSqrtThreeUpper :
          Real.sqrt (2 + Real.sqrt 2) < (1.847762 : ℝ) := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num at ⊢
        linarith
      have hNestedSqrtFourLower :
          (1.961570 : ℝ) <
            Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num at ⊢
        linarith
      have hNestedSqrtFourUpper :
          Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) <
            (1.961572 : ℝ) := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num at ⊢
        linarith
      have hFinalRadicalLower :
          (0.19603 : ℝ) <
            Real.sqrt
              (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num at ⊢
        linarith
      have hFinalRadicalUpper :
          Real.sqrt
              (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) <
            (0.19604 : ℝ) := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num at ⊢
        linarith
      rw [Real.sin_pi_div_thirty_two]
      constructor <;> linarith
    have hPiBounds :
        (3.141 : ℝ) < Real.pi ∧ Real.pi < (3.142 : ℝ) := by
      let x : ℝ := Real.pi / 32
      have hxNonnegative : 0 ≤ x := by
        dsimp [x]
        positivity
      have hxCubeNonnegative : 0 ≤ x ^ 3 := pow_nonneg hxNonnegative _
      have hxLeOneEighth : x ≤ (1 / 8 : ℝ) := by
        dsimp [x]
        linarith [Real.pi_le_four]
      have hxAbsLeOne : |x| ≤ 1 := by
        rw [abs_of_nonneg hxNonnegative]
        linarith
      have hSinApproximation := Real.sin_bound hxAbsLeOne
      rw [abs_of_nonneg hxNonnegative] at hSinApproximation
      have hApproximationLower := (abs_le.mp hSinApproximation).1
      have hApproximationUpper := (abs_le.mp hSinApproximation).2
      constructor
      · by_contra h
        have hxUpper : x ≤ (3.141 / 32 : ℝ) := by
          dsimp [x]
          linarith
        have hxUpper' : x ≤ (1 / 10 : ℝ) := by
          linarith
        have hxFourthUpper : x ^ 4 ≤ (1 / 10 : ℝ) ^ 4 :=
          pow_le_pow_left₀ hxNonnegative hxUpper' 4
        have hxLower : (0.097 : ℝ) ≤ x := by
          by_contra hx
          have hx' : x < (0.097 : ℝ) := lt_of_not_ge hx
          have hSinLower := hSinPiDivThirtyTwoBounds.1
          change Real.sin x > (0.09801 : ℝ) at hSinLower
          norm_num at hxFourthUpper
          linarith
        have hxCubeLower : (0.097 : ℝ) ^ 3 ≤ x ^ 3 :=
          pow_le_pow_left₀ (by norm_num) hxLower 3
        have hSinLower := hSinPiDivThirtyTwoBounds.1
        change Real.sin x > (0.09801 : ℝ) at hSinLower
        norm_num at hxCubeLower hxFourthUpper
        linarith
      · by_contra h
        have hxLower : (3.142 / 32 : ℝ) ≤ x := by
          dsimp [x]
          linarith
        have hxUpper : x ≤ (0.099 : ℝ) := by
          by_contra hx
          have hx' : (0.099 : ℝ) < x := lt_of_not_ge hx
          have hxCubeUpper : x ^ 3 ≤ (1 / 8 : ℝ) ^ 3 :=
            pow_le_pow_left₀ hxNonnegative hxLeOneEighth 3
          have hxFourthUpper : x ^ 4 ≤ (1 / 8 : ℝ) ^ 4 :=
            pow_le_pow_left₀ hxNonnegative hxLeOneEighth 4
          have hSinUpper := hSinPiDivThirtyTwoBounds.2
          change Real.sin x < (0.09802 : ℝ) at hSinUpper
          norm_num at hxCubeUpper hxFourthUpper
          linarith
        have hxCubeUpper : x ^ 3 ≤ (0.099 : ℝ) ^ 3 :=
          pow_le_pow_left₀ hxNonnegative hxUpper 3
        have hxFourthUpper : x ^ 4 ≤ (0.099 : ℝ) ^ 4 :=
          pow_le_pow_left₀ hxNonnegative hxUpper 4
        have hSinUpper := hSinPiDivThirtyTwoBounds.2
        change Real.sin x < (0.09802 : ℝ) at hSinUpper
        norm_num at hxCubeUpper hxFourthUpper
        linarith
    have hPiLower : (3.14 : ℝ) < Real.pi := by
      linarith [hPiBounds.1]
    have hPiUpper : Real.pi < (3.142 : ℝ) := hPiBounds.2
    have hPiSquaredLower : (3.14 : ℝ) ^ 2 < Real.pi ^ 2 := by
      simpa [pow_two] using
        (mul_self_lt_mul_self (by norm_num : (0 : ℝ) ≤ 3.14) hPiLower)
    have hPiSquaredUpper : Real.pi ^ 2 < (3.142 : ℝ) ^ 2 := by
      simpa [pow_two] using
        (mul_self_lt_mul_self Real.pi_nonneg hPiUpper)
    have hDifferenceNegative :
        Real.pi ^ 2 / 31250 - 316 / 1000000 < 0 := by
      nlinarith
    rw [abs_of_neg hDifferenceNegative]
    nlinarith

end PhyXMiniProblems.ProblemPhyXMini0228
