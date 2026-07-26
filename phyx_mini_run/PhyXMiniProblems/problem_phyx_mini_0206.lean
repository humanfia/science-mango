import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0206

open Dimension

/-!
# Wave-speed estimate from resonant coffee sloshing

A cup with a circular rim has diameter `8 cm`.  At a walking cadence of about
one step per second, the coffee sloshing grows resonantly until it spills.  We
therefore identify the sloshing frequency with the resonant driving frequency
and use the general propagation law `v = f * lambda`.

Neither the source nor the bitmap supplies a wavelength or a specific
free-surface mode.  In particular, the cup diameter does not by itself justify
identifying the wavelength with the rim circumference.  The strongest
source-supported estimate is consequently symbolic: at the nominal `1 Hz`
cadence, the speed in `cm/s` equals the wavelength in `cm`.  The recorded
multiple-choice answer is retained below only as dataset metadata.

Lengths, frequencies, and speeds are represented by unit-independent Physlib
quantities.  Real numbers occur only as readouts in explicitly selected units
or as the displayed numerical answer choices.
-/

/-! ## Dimensionful quantities and scalar readouts -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical frequency with inverse-time dimension. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative physical propagation speed with length-per-time dimension. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length ({ UnitChoices.SI with length := unit } : UnitChoices)).val : ℝ)

/-- Read a physical frequency in inverse units of a selected time unit. -/
def frequencyReadout
    (unit : TimeUnit) (frequency : FrequencyQuantity) : ℝ :=
  ((frequency ({ UnitChoices.SI with time := unit } : UnitChoices)).val : ℝ)

/-- Read a physical speed in a selected length unit per selected time unit. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed ({ UnitChoices.SI with
    length := lengthUnit, time := timeUnit } : UnitChoices)).val : ℝ)

/-- Centimetre readout used for the cup diameter and surface wavelength. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Hertz readout used for walking cadence and the resonant sloshing mode. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Centimetres-per-second readout used for the requested wave-speed estimate. -/
def speedInCentimetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.centimeters TimeUnit.seconds speed

/-! ## Physical setup and figure labels -/

/-- The liquid whose free-surface wave is being estimated. -/
inductive LiquidMedium where
  | coffee
  deriving DecidableEq, Repr

/-- Rim geometry relevant to the wavelength estimate. -/
inductive CupRimGeometry where
  | circular
  deriving DecidableEq, Repr

/-- Qualitative response of the coffee to periodic walking. -/
inductive SloshingResponse where
  | amplitudeGrowsUntilOverflow
  deriving DecidableEq, Repr

/-- Features visible in the supplied bitmap. -/
inductive FigureFeature where
  | handHoldingCup
  | whiteCeramicCup
  | darkCoffee
  | tippedCup
  | tiltedLiquidSurface
  | coffeeSpillingOverRim
  | fallingDroplets
  | blueBackground
  deriving DecidableEq, Repr

/-!
The physical quantities are independent fields.  In particular, neither the
wavelength nor the requested wave speed is defined from the diameter, cadence,
or a displayed answer.
-/
structure CoffeeSloshingSetup where
  liquid : LiquidMedium
  rimGeometry : CupRimGeometry
  response : SloshingResponse
  figureShows : FigureFeature → Prop
  /-- Diameter of the coffee cup. -/
  cupDiameter : LengthQuantity
  /-- Wavelength of the resonant free-surface wave; not measured by the source. -/
  surfaceWavelength : LengthQuantity
  /-- Periodic drive frequency supplied by the walker. -/
  walkingStepFrequency : FrequencyQuantity
  /-- Natural frequency of the resonantly excited sloshing mode. -/
  sloshingFrequency : FrequencyQuantity
  /-- Phase speed of the surface wave in the coffee. -/
  surfaceWaveSpeed : SpeedQuantity

/-!
Problem-statement and figure readouts.  The phrase “about one step per second”
is idealized by its nominal `1 Hz` value for this order-of-magnitude estimate.
No wavelength or wave-speed value occurs in this predicate.
-/
structure MatchesCoffeeSloshingProblemAndFigure
    (setup : CoffeeSloshingSetup) : Prop where
  liquidIsCoffee : setup.liquid = .coffee
  rimIsCircular : setup.rimGeometry = .circular
  responseGrowsToOverflow :
    setup.response = .amplitudeGrowsUntilOverflow
  cupDiameterCentimeters : lengthInCentimeters setup.cupDiameter = 8
  nominalWalkingCadenceHertz :
    frequencyInHertz setup.walkingStepFrequency = 1
  figureHasHandHoldingCup : setup.figureShows .handHoldingCup
  figureHasWhiteCeramicCup : setup.figureShows .whiteCeramicCup
  figureHasDarkCoffee : setup.figureShows .darkCoffee
  figureHasTippedCup : setup.figureShows .tippedCup
  figureHasTiltedLiquidSurface : setup.figureShows .tiltedLiquidSurface
  figureHasCoffeeSpilling : setup.figureShows .coffeeSpillingOverRim
  figureHasFallingDroplets : setup.figureShows .fallingDroplets
  figureHasBlueBackground : setup.figureShows .blueBackground

/-!
Governing model for the estimate:

* resonant growth locks the natural sloshing frequency to the walking drive;
* the surface wave obeys `v = f * lambda` in compatible units.

These laws relate independent physical quantities.  They contain no relation
between cup diameter and wavelength, no numerical speed estimate, and no
preferred displayed answer.
-/
structure SatisfiesResonantWaveKinematics
    (setup : CoffeeSloshingSetup) : Prop where
  resonantFrequencyMatch :
    ∀ unit : TimeUnit,
      frequencyReadout unit setup.sloshingFrequency =
        frequencyReadout unit setup.walkingStepFrequency
  speedEqualsFrequencyTimesWavelength :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit setup.surfaceWaveSpeed =
        frequencyReadout timeUnit setup.sloshingFrequency *
          lengthReadout lengthUnit setup.surfaceWavelength

/-! ## Displayed-answer metadata and source-supported target -/

/-- Labels of the four wave-speed choices supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed wave speed beside each answer label, in centimetres per second. -/
def displayedSpeedCentimetersPerSecond : AnswerChoice → ℝ
  | .A => 8
  | .B => 12
  | .C => 16
  | .D => 20

/-- The answer label recorded by the source dataset, retained as metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/--
At the nominal resonant cadence of `1 Hz`, the general wave relation
`v = f * lambda` implies that the speed readout in centimetres per second is
the same number as the wavelength readout in centimetres.  Since the source
does not determine that wavelength, no numerical answer choice follows.

This formalizes `thm:physics:phyx_mini_0206:target`.
-/
theorem problem_phyx_mini_0206
    (setup : CoffeeSloshingSetup)
    (h_readouts : MatchesCoffeeSloshingProblemAndFigure setup)
    (h_laws : SatisfiesResonantWaveKinematics setup) :
    speedInCentimetersPerSecond setup.surfaceWaveSpeed =
      lengthInCentimeters setup.surfaceWavelength := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0206
