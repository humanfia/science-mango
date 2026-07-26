import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0154

open Dimension

/-!
# Thermal buckling of a centrally cracked bar

A straight bar spans a fixed distance `L₀` between two supports.  A crack at
the midpoint acts as a hinge.  After a temperature increase, the two expanded
half-bars form the equal sloping sides of an inverted V, whose center rises by
the length `x`.

The supplied primary raster `154.png` does not depict this bar: it is an
unrelated bulb-and-plane-mirror ray diagram.  Consequently, the bar geometry
below is grounded in the unambiguous problem text and its intended-diagram
caption.  No numerical or geometric datum from the mismatched optics raster is
used as a premise of the bar theorem.

Lengths, temperature intervals, and coefficients of linear expansion are
unit-independent Physlib quantities.  Real numbers occur only as readouts in
named units and as dimensionless expressions built from compatible readouts.
-/

/-! ## Physical quantities and their unit readouts -/

/-- A nonnegative physical magnitude carrying the dimension of length. -/
abbrev LengthMagnitude : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical temperature interval, rather than an absolute temperature. -/
abbrev TemperatureIntervalMagnitude : Type :=
  Dimensionful (WithDim Θ𝓭 NNReal)

/-- A coefficient of linear expansion, carrying inverse-temperature dimension. -/
abbrev LinearExpansionCoefficientMagnitude : Type :=
  Dimensionful (WithDim (Θ𝓭⁻¹) NNReal)

/-!
For temperature *differences*, one degree Celsius has the same scale as one
kelvin.  Physlib currently exposes kelvin but no separately named Celsius
interval unit, so this name records the intended interpretation of the source
readouts without introducing an offset appropriate only to absolute
temperatures.
-/
def celsiusDegreeUnit : TemperatureUnit := TemperatureUnit.kelvin

/-- Read a physical length as a real scalar in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (quantity : LengthMagnitude) : ℝ :=
  ((quantity ({ UnitChoices.SI with length := unit } : UnitChoices)).val : ℝ)

/-- The metre readout used for `L₀`, `x`, and the displayed answers. -/
def lengthInMeters (quantity : LengthMagnitude) : ℝ :=
  lengthReadout LengthUnit.meters quantity

/-- Read a physical temperature interval in the selected temperature unit. -/
def temperatureIntervalReadout
    (unit : TemperatureUnit) (quantity : TemperatureIntervalMagnitude) : ℝ :=
  ((quantity ({ UnitChoices.SI with temperature := unit } : UnitChoices)).val : ℝ)

/-- The source's Celsius-degree readout of the temperature rise. -/
def temperatureRiseInCelsiusDegrees
    (quantity : TemperatureIntervalMagnitude) : ℝ :=
  temperatureIntervalReadout celsiusDegreeUnit quantity

/-- Read an inverse-temperature expansion coefficient per selected unit. -/
def expansionCoefficientReadout
    (temperatureUnit : TemperatureUnit)
    (quantity : LinearExpansionCoefficientMagnitude) : ℝ :=
  ((quantity
    ({ UnitChoices.SI with temperature := temperatureUnit } : UnitChoices)).val : ℝ)

/-- The source's readout of the expansion coefficient per Celsius degree. -/
def expansionCoefficientPerCelsiusDegree
    (quantity : LinearExpansionCoefficientMagnitude) : ℝ :=
  expansionCoefficientReadout celsiusDegreeUnit quantity

/-! ## Physical setup and intended figure labels -/

/-- The two configurations shown by the intended before/after diagram. -/
inductive ThermalState where
  | beforeHeating
  | afterHeating
  deriving DecidableEq, Repr

/-- The two pieces of the bar meeting at the central crack. -/
inductive BarHalf where
  | left
  | right
  deriving DecidableEq, Repr

/-- Qualitative beam profiles described by the intended diagram. -/
inductive BeamProfile where
  | straight
  | invertedV
  deriving DecidableEq, Repr

/-- The length labels printed in the intended diagram. -/
inductive FigureLengthLabel where
  | L0
  | x
  deriving DecidableEq, Repr

/-!
The physical bar data.  `supportSeparation` is indexed by state so that the
fixed-support condition is an explicit assumption rather than hidden in a
definition.  Similarly, the unknown `centerRise` is a physical length and is
not defined to be the requested numerical answer.
-/
structure CenterCrackedBarSetup where
  supportSeparation : ThermalState → LengthMagnitude
  halfLength : ThermalState → BarHalf → LengthMagnitude
  horizontalRun : BarHalf → LengthMagnitude
  centerRise : LengthMagnitude
  temperatureRise : TemperatureIntervalMagnitude
  linearExpansionCoefficient : LinearExpansionCoefficientMagnitude
  depictedProfile : ThermalState → BeamProfile

/-- Interpret the intended figure labels `L₀` and `x` as physical quantities. -/
def figureLengthQuantity
    (setup : CenterCrackedBarSetup) : FigureLengthLabel → LengthMagnitude
  | .L0 => setup.supportSeparation .beforeHeating
  | .x => setup.centerRise

/-!
The three numerical measurements stated in the problem.  They contain no
numerical value for the unknown rise `x` and no displayed answer choice.
-/
structure MatchesStatedMeasurements (setup : CenterCrackedBarSetup) : Prop where
  initialSpanMeters :
    lengthInMeters (setup.supportSeparation .beforeHeating) = 377 / 100
  temperatureRiseCelsiusDegrees :
    temperatureRiseInCelsiusDegrees setup.temperatureRise = 32
  expansionCoefficientPerCelsiusDegree :
    expansionCoefficientPerCelsiusDegree setup.linearExpansionCoefficient =
      25 / 1000000

/-!
The geometry described by the intended before/after diagram.  The midpoint
relations encode the central crack and the equal horizontal projections, while
the support relation records that the endpoints remain fixed.  These are
figure/setup facts, not the derived Pythagorean rise or its numerical value.
-/
structure MatchesIntendedBarDiagram (setup : CenterCrackedBarSetup) : Prop where
  supportsRemainFixed : ∀ units : UnitChoices,
    (setup.supportSeparation .afterHeating units).val =
      (setup.supportSeparation .beforeHeating units).val
  crackBisectsOriginalBar : ∀ half units,
    (setup.halfLength .beforeHeating half units).val =
      (setup.supportSeparation .beforeHeating units).val / 2
  centerHorizontalProjection : ∀ half units,
    (setup.horizontalRun half units).val =
      (setup.supportSeparation .afterHeating units).val / 2
  beforeProfileStraight :
    setup.depictedProfile .beforeHeating = .straight
  afterProfileInvertedV :
    setup.depictedProfile .afterHeating = .invertedV

/-!
The governing linear thermal-expansion law on each half-bar,

`heated length = original length * (1 + α * ΔT)`.

It is stated in every coherent unit system.  Since `α` has inverse-temperature
dimension and `ΔT` has temperature dimension, their readout product is
dimensionless.
-/
structure ObeysLinearThermalExpansion (setup : CenterCrackedBarSetup) : Prop where
  halfLengthExpansion : ∀ half units,
    (setup.halfLength .afterHeating half units).val =
      (setup.halfLength .beforeHeating half units).val *
        (1 +
          (setup.linearExpansionCoefficient units).val *
            (setup.temperatureRise units).val)

/-!
Each heated half-bar is the hypotenuse of a right triangle whose legs are its
horizontal run and the common center rise.  This is the governing geometric
law, not the numerical conclusion sought by the problem.
-/
structure SatisfiesSymmetricBucklingGeometry
    (setup : CenterCrackedBarSetup) : Prop where
  pythagoreanHalfBar : ∀ half units,
    (setup.halfLength .afterHeating half units).val ^ 2 =
      (setup.horizontalRun half units).val ^ 2 +
        (setup.centerRise units).val ^ 2

/-!
Combining fixed support separation, linear expansion, and the right-triangle
geometry determines the square of the rise.  This is a derived intermediate
result and not a premise of the main theorem.
-/
lemma centerRiseMeters_sq
    (setup : CenterCrackedBarSetup)
    (_measurements : MatchesStatedMeasurements setup)
    (_figure : MatchesIntendedBarDiagram setup)
    (_thermal : ObeysLinearThermalExpansion setup)
    (_geometry : SatisfiesSymmetricBucklingGeometry setup) :
    lengthInMeters setup.centerRise ^ 2 =
      (377 / 200 : ℝ) ^ 2 * ((1251 / 1250 : ℝ) ^ 2 - 1) := by
  have hspan := _measurements.initialSpanMeters
  have htemp := _measurements.temperatureRiseCelsiusDegrees
  have hcoeff := _measurements.expansionCoefficientPerCelsiusDegree
  change
    (↑(setup.supportSeparation .beforeHeating UnitChoices.SI).val : ℝ) =
      377 / 100 at hspan
  change (↑(setup.temperatureRise UnitChoices.SI).val : ℝ) = 32 at htemp
  change
    (↑(setup.linearExpansionCoefficient UnitChoices.SI).val : ℝ) =
      25 / 1000000 at hcoeff
  have hfixedR := congrArg (fun z : NNReal => (z : ℝ))
    (_figure.supportsRemainFixed UnitChoices.SI)
  have hhalfR := congrArg (fun z : NNReal => (z : ℝ))
    (_figure.crackBisectsOriginalBar BarHalf.left UnitChoices.SI)
  have hrunR := congrArg (fun z : NNReal => (z : ℝ))
    (_figure.centerHorizontalProjection BarHalf.left UnitChoices.SI)
  have hexpandR := congrArg (fun z : NNReal => (z : ℝ))
    (_thermal.halfLengthExpansion BarHalf.left UnitChoices.SI)
  have hpythR := congrArg (fun z : NNReal => (z : ℝ))
    (_geometry.pythagoreanHalfBar BarHalf.left UnitChoices.SI)
  norm_num at hhalfR hrunR hexpandR hpythR
  rw [hspan] at hfixedR hhalfR
  rw [hfixedR] at hrunR
  rw [hhalfR, hcoeff, htemp] at hexpandR
  rw [hexpandR, hrunR] at hpythR
  change (↑(setup.centerRise UnitChoices.SI).val : ℝ) ^ 2 = _
  norm_num at hpythR ⊢
  nlinarith

/-! ## Displayed answers -/

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Metre readout printed beside each answer label. -/
def answerRiseMeters : AnswerChoice → ℝ
  | .A => 27 / 400
  | .B => 7 / 100
  | .C => 29 / 400
  | .D => 3 / 40

/-- Dataset metadata records answer D; this declaration is not a theorem premise. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- A choice is selected when its displayed rise is uniquely closest to the exact rise. -/
def IsUniqueClosestDisplayedAnswer
    (setup : CenterCrackedBarSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |lengthInMeters setup.centerRise - answerRiseMeters choice| <
      |lengthInMeters setup.centerRise - answerRiseMeters other|

/-!
The expanded half-length is

`(3.77 m / 2) * (1 + 25 * 10⁻⁶ * 32)`.

The Pythagorean relation therefore gives the exact rise displayed below,
approximately `0.075415 m`.  The uniquely closest listed value is `0.075 m`,
answer D.

This formalizes blueprint label `thm:physics:phyx_mini_0154:target`.
-/
theorem problem_phyx_mini_0154
    (setup : CenterCrackedBarSetup)
    (_measurements : MatchesStatedMeasurements setup)
    (_figure : MatchesIntendedBarDiagram setup)
    (_thermal : ObeysLinearThermalExpansion setup)
    (_geometry : SatisfiesSymmetricBucklingGeometry setup) :
    lengthInMeters setup.centerRise =
        (377 / 200 : ℝ) *
          Real.sqrt ((1251 / 1250 : ℝ) ^ 2 - 1) ∧
      IsUniqueClosestDisplayedAnswer setup .D := by
  have hq : 0 ≤ ((1251 / 1250 : ℝ) ^ 2 - 1) := by
    norm_num
  have hsqrt_sq := Real.sq_sqrt hq
  have hsqrt_nonneg :=
    Real.sqrt_nonneg ((1251 / 1250 : ℝ) ^ 2 - 1)
  have hy_nonneg : 0 ≤ lengthInMeters setup.centerRise := by
    unfold lengthInMeters lengthReadout
    positivity
  have hsq :=
    centerRiseMeters_sq setup _measurements _figure _thermal _geometry
  refine ⟨by nlinarith, ?_⟩
  unfold IsUniqueClosestDisplayedAnswer
  intro other hother
  have hygt : (3 / 40 : ℝ) < lengthInMeters setup.centerRise := by
    norm_num at hsq
    nlinarith [sq_nonneg (lengthInMeters setup.centerRise - 3 / 40)]
  cases other with
  | A =>
      dsimp [answerRiseMeters]
      rw [abs_of_pos (by nlinarith), abs_of_pos (by nlinarith)]
      norm_num
  | B =>
      dsimp [answerRiseMeters]
      rw [abs_of_pos (by nlinarith), abs_of_pos (by nlinarith)]
      norm_num
  | C =>
      dsimp [answerRiseMeters]
      rw [abs_of_pos (by nlinarith), abs_of_pos (by nlinarith)]
      norm_num
  | D => exact (hother rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0154
