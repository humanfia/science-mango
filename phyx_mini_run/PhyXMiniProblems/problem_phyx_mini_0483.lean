import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0483

open Dimension

/-!
# Seasonal thermal expansion of the Eiffel Tower

The Eiffel Tower is idealized as a vertical wrought-iron beam.  Its January
height is described only as approximately `300 m`, while its average
temperature rises from `2 °C` in January to `25 °C` in July.  The model asks
for the corresponding increase in height.

Lengths, absolute temperatures, and the coefficient of linear expansion are
represented as unit-independent Physlib quantities.  Real numbers occur only
as readouts in explicitly named units and as differences of compatible
readouts.  Because the source supplies neither a numerical uncertainty for the
height nor a wrought-iron expansion coefficient, both remain symbolic.
-/

/-! ## Physical quantities and named-unit readouts -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative absolute temperature with physical dimension `Θ`. -/
abbrev AbsoluteTemperatureQuantity : Type :=
  Dimensionful (WithDim Θ𝓭 NNReal)

/-- A nonnegative coefficient of linear expansion with dimension `Θ⁻¹`. -/
abbrev LinearExpansionCoefficientQuantity : Type :=
  Dimensionful (WithDim Θ𝓭⁻¹ NNReal)

/-- Read a physical length in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length ({ UnitChoices.SI with length := unit } : UnitChoices)).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read an absolute temperature in kelvin. -/
def temperatureInKelvins (temperature : AbsoluteTemperatureQuantity) : ℝ :=
  ((temperature UnitChoices.SI).val : ℝ)

/--
Read an absolute temperature in degrees Celsius.  The affine offset
`273.15 K` is represented exactly as `5463 / 20`.
-/
def temperatureInDegreesCelsius
    (temperature : AbsoluteTemperatureQuantity) : ℝ :=
  temperatureInKelvins temperature - 5463 / 20

/-- Read a linear expansion coefficient in inverse kelvin. -/
def expansionCoefficientPerKelvin
    (coefficient : LinearExpansionCoefficientQuantity) : ℝ :=
  ((coefficient UnitChoices.SI).val : ℝ)

/-! ## Tower, seasonal, and figure vocabulary -/

/-- The two seasons whose average temperatures are compared. -/
inductive Season where
  | january
  | july
  deriving DecidableEq, Fintype, Repr

/-- Structural materials relevant to the vertical-beam idealization. -/
inductive StructuralMaterial where
  | wroughtIron
  | other
  deriving DecidableEq, Repr

/-- The structural idealization explicitly requested by the problem. -/
inductive StructuralIdealization where
  | verticalBeam
  | spatialLattice
  deriving DecidableEq, Repr

/-!
Qualitative evidence visible in the primary bitmap `483.png`.  The photograph
contains no quantitative dimension or temperature labels.
-/
structure EiffelTowerFigure where
  towerIsShown : Bool
  towerIsCentered : Bool
  gardensAreShown : Bool
  quantitativeLabels : List String

/-!
Independent physical data for the seasonal-expansion model.  In particular,
neither July's height nor the requested height change is defined using a
displayed answer value.
-/
structure EiffelTowerSetup where
  material : StructuralMaterial
  idealization : StructuralIdealization
  heightAt : Season → LengthQuantity
  averageTemperature : Season → AbsoluteTemperatureQuantity
  linearExpansionCoefficient : LinearExpansionCoefficientQuantity
  januaryHeightToleranceMeters : ℝ
  figure : EiffelTowerFigure

/-! ## Scenario, figure/data readouts, and governing law -/

/-- The material and one-dimensional structural assumptions stated in prose. -/
structure MatchesEiffelTowerScenario (setup : EiffelTowerSetup) : Prop where
  towerIsWroughtIron : setup.material = .wroughtIron
  towerTreatedAsVerticalBeam : setup.idealization = .verticalBeam

/-- Exact transcription of the qualitative primary image evidence. -/
structure MatchesPrimaryTowerFigure (setup : EiffelTowerSetup) : Prop where
  towerShown : setup.figure.towerIsShown = true
  towerCentered : setup.figure.towerIsCentered = true
  gardensShown : setup.figure.gardensAreShown = true
  noQuantitativeLabels : setup.figure.quantitativeLabels = []

/-!
The nominal height and seasonal average temperatures supplied by the text.
The phrase "approximately `300 m`" is represented by an explicit nonnegative
tolerance rather than by replacing the physical January height with the exact
number `300`.  The source does not specify the value of this tolerance.
-/
structure MatchesTowerReadouts (setup : EiffelTowerSetup) : Prop where
  januaryHeightToleranceNonnegative :
    0 ≤ setup.januaryHeightToleranceMeters
  januaryHeightWithinTolerance :
    |lengthInMeters (setup.heightAt .january) - 300| ≤
      setup.januaryHeightToleranceMeters
  januaryAverageTemperatureCelsius :
    temperatureInDegreesCelsius (setup.averageTemperature .january) = 2
  julyAverageTemperatureCelsius :
    temperatureInDegreesCelsius (setup.averageTemperature .july) = 25

/-- Positivity assumptions selecting the physical branch of the model. -/
structure HasPhysicalTowerParameters (setup : EiffelTowerSetup) : Prop where
  januaryHeightPositive :
    0 < lengthInMeters (setup.heightAt .january)
  coefficientPositive :
    0 < expansionCoefficientPerKelvin setup.linearExpansionCoefficient
  julyWarmerThanJanuary :
    temperatureInKelvins (setup.averageTemperature .january) <
      temperatureInKelvins (setup.averageTemperature .july)

/-!
The governing one-dimensional linear thermal-expansion law

`L(T) = L(T_january) * (1 + α * (T - T_january))`.

It is stated for every season and every coherent choice of units.  The law
does not assign a numerical July height, height change, or answer label.
-/
structure ObeysLinearThermalExpansion (setup : EiffelTowerSetup) : Prop where
  seasonalHeightLaw : ∀ (season : Season) (units : UnitChoices),
    (setup.heightAt season units).val =
      (setup.heightAt .january units).val *
        (1 +
          (setup.linearExpansionCoefficient units).val *
            ((setup.averageTemperature season units).val -
              (setup.averageTemperature .january units).val))

/-! ## Displayed-answer metadata and current target -/

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metre readouts printed beside the four answer labels. -/
def displayedHeightChangeMeters : AnswerChoice → ℝ
  | .A => 12 / 100
  | .B => 6 / 100
  | .C => 10 / 100
  | .D => 8 / 100

/-- Answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- The July-minus-January height change, read in metres. -/
def seasonalHeightChangeMeters (setup : EiffelTowerSetup) : ℝ :=
  lengthInMeters (setup.heightAt .july) -
    lengthInMeters (setup.heightAt .january)

/-!
The source-supported conclusion is the symbolic linear-expansion relation

`ΔL = L_january α (25 - 2)`.

The second conjunct propagates the unspecified error in the nominal `300 m`
height to the corresponding nominal expansion estimate.  No numerical value
of `α` is supplied by the source, so the recorded answer D is retained only as
metadata and is deliberately not concluded.  This formalizes blueprint label
`thm:physics:phyx_mini_0483:target`, subject to the redraft noted above.
-/
theorem problem_phyx_mini_0483
    (setup : EiffelTowerSetup)
    (_scenario : MatchesEiffelTowerScenario setup)
    (_figure : MatchesPrimaryTowerFigure setup)
    (_readouts : MatchesTowerReadouts setup)
    (_physical : HasPhysicalTowerParameters setup)
    (_thermalExpansion : ObeysLinearThermalExpansion setup) :
    seasonalHeightChangeMeters setup =
        lengthInMeters (setup.heightAt .january) *
          expansionCoefficientPerKelvin setup.linearExpansionCoefficient *
            ((25 : ℝ) - 2) ∧
      |seasonalHeightChangeMeters setup -
          300 *
            expansionCoefficientPerKelvin setup.linearExpansionCoefficient *
              ((25 : ℝ) - 2)| ≤
        setup.januaryHeightToleranceMeters *
          expansionCoefficientPerKelvin setup.linearExpansionCoefficient *
            ((25 : ℝ) - 2) := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0483
