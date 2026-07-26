import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0387

open Dimension

/-!
# Inclined water U-tube manometer

The primary figure compares an upright water U-tube, whose vertical level
difference is labelled `h`, with the same manometer after its right branch is
inclined at `30°` above the horizontal.  In the inclined panel the liquid
column length is labelled `L`.  Hydrostatic pressure depends on vertical head,
whereas the labelled inclined length has vertical projection `L sin θ`.

Lengths, mass density, acceleration, and pressure are represented by
unit-independent Physlib quantities.  Real numbers occur only as coherent
unit readouts, dimensionless trigonometric values, and answer-choice values.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- The physical dimension of mass density, `M L⁻³`. -/
def massDensityDimension : Dimension :=
  M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length, independent of the selected readout unit. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical mass density. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful (WithDim massDensityDimension NNReal)

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Gauge or absolute pressure, using Physlib's pressure dimension. -/
abbrev PressureQuantity : Type := DimPressure

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimetre readout of a physical length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Kilogram-per-cubic-metre readout of a physical mass density. -/
def densityInKilogramsPerCubicMeter (density : MassDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Pascal readout of a pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Convert a numerical degree readout to Mathlib's physical angle type. -/
def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-! ## Apparatus roles and primary-figure labels -/

/-- The liquid filling the connected lower part of the manometer. -/
inductive ManometerLiquid where
  | water
  | other
  deriving DecidableEq, Repr

/-- The two arms, with the right arm being the one tilted in the figure. -/
inductive ManometerArm where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- The two side-by-side configurations drawn in the primary image. -/
inductive FigurePanel where
  | upright
  | rightBranchTilted
  deriving DecidableEq, Fintype, Repr

/-- The two physical length labels printed in the primary image. -/
inductive FigureLengthLabel where
  | h
  | L
  deriving DecidableEq, Fintype, Repr

/-- The baseline from which the displayed `30°` inclination is measured. -/
inductive AngleReference where
  | horizontal
  deriving DecidableEq, Repr

/-!
A structured transcription of image `387.png`.

The labelled lengths are independent physical quantities.  In particular,
`L` is not defined to be `50 cm`; its relation to `h` is supplied only by the
geometric governing law below.
-/
structure SuppliedManometerFigure where
  liquid : ManometerLiquid
  tiltedBranch : ManometerArm
  lengthForLabel : FigureLengthLabel → LengthQuantity
  panelForLabel : FigureLengthLabel → FigurePanel
  branchAngleFromHorizontal : Real.Angle
  angleReference : AngleReference
  lowerSurfaceArm : FigurePanel → ManometerArm
  higherSurfaceArm : FigurePanel → ManometerArm
  showsConnectedUShapedTube : Bool
  showsHorizontalDashedReference : FigurePanel → Bool
  showsVerticalArrowForH : Bool
  showsInclinedArrowForL : Bool
  showsThirtyDegreeArc : Bool

/-- The physical manometer, its boundary pressures, and the quantities in the figure. -/
structure WaterUTubeManometerSetup where
  figure : SuppliedManometerFigure
  liquidDensity : MassDensityQuantity
  gravitationalAcceleration : AccelerationQuantity
  pressureAtArmOpening : ManometerArm → PressureQuantity
  atmosphericPressure : PressureQuantity
  gaugePressure : PressureQuantity

/-- The physical height difference denoted by `h` in the upright panel. -/
def heightDifferenceH (setup : WaterUTubeManometerSetup) : LengthQuantity :=
  setup.figure.lengthForLabel .h

/-- The physical inclined liquid-column length denoted by `L`. -/
def tiltedColumnLengthL (setup : WaterUTubeManometerSetup) : LengthQuantity :=
  setup.figure.lengthForLabel .L

/-!
Qualitative information read directly from the supplied bitmap.  The lower
left surface and higher right surface fix the pressure-sign convention, but no
numerical value for `L` occurs here.
-/
def MatchesSuppliedManometerFigure
    (setup : WaterUTubeManometerSetup) : Prop :=
  setup.figure.liquid = .water ∧
    setup.figure.tiltedBranch = .right ∧
    setup.figure.panelForLabel .h = .upright ∧
    setup.figure.panelForLabel .L = .rightBranchTilted ∧
    setup.figure.angleReference = .horizontal ∧
    setup.figure.lowerSurfaceArm .upright = .left ∧
    setup.figure.higherSurfaceArm .upright = .right ∧
    setup.figure.lowerSurfaceArm .rightBranchTilted = .left ∧
    setup.figure.higherSurfaceArm .rightBranchTilted = .right ∧
    setup.figure.showsConnectedUShapedTube = true ∧
    setup.figure.showsHorizontalDashedReference .upright = true ∧
    setup.figure.showsHorizontalDashedReference .rightBranchTilted = true ∧
    setup.figure.showsVerticalArrowForH = true ∧
    setup.figure.showsInclinedArrowForL = true ∧
    setup.figure.showsThirtyDegreeArc = true

/-!
Numerical data stated in the problem and printed in the figure: water has the
given density, the upright head is `25 cm`, and the right branch is inclined
at `30°`.  The requested length `L` is deliberately absent.
-/
def MatchesProblemReadouts (setup : WaterUTubeManometerSetup) : Prop :=
  densityInKilogramsPerCubicMeter setup.liquidDensity = 1000 ∧
    lengthInCentimeters (heightDifferenceH setup) = 25 ∧
    setup.figure.branchAngleFromHorizontal = degrees 30

/-- Positivity and nondegeneracy conditions for the physical apparatus. -/
structure HasPhysicalManometerParameters
    (setup : WaterUTubeManometerSetup) : Prop where
  densityPositive :
    0 < densityInKilogramsPerCubicMeter setup.liquidDensity
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  heightDifferencePositive :
    0 < lengthInMeters (heightDifferenceH setup)
  inclinedColumnLengthPositive :
    0 < lengthInMeters (tiltedColumnLengthL setup)
  atmosphericPressurePositive :
    0 < pressureInPascals setup.atmosphericPressure
  appliedPressurePositive :
    0 < pressureInPascals (setup.pressureAtArmOpening .left)
  gaugePressureNonnegative :
    0 ≤ pressureInPascals setup.gaugePressure

/-!
Governing pressure and geometry relations.

* The right opening is the atmospheric reference.
* Gauge pressure is applied pressure minus atmospheric pressure.
* Hydrostatic balance gives `Δp = ρ g h` in coherent SI readouts.
* The vertical projection of the tilted length is `L sin θ = h`.

These are physical laws, not solved numerical values for `L`.
-/
structure SatisfiesWaterManometerAndTiltLaws
    (setup : WaterUTubeManometerSetup) : Prop where
  rightArmOpenToAtmosphere :
    setup.pressureAtArmOpening .right = setup.atmosphericPressure
  gaugePressureDefinition :
    pressureInPascals setup.gaugePressure =
      pressureInPascals (setup.pressureAtArmOpening .left) -
        pressureInPascals setup.atmosphericPressure
  hydrostaticPressureBalance :
    pressureInPascals setup.gaugePressure =
      densityInKilogramsPerCubicMeter setup.liquidDensity *
        accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
          lengthInMeters (heightDifferenceH setup)
  tiltedLengthVerticalProjection :
    lengthInMeters (heightDifferenceH setup) =
      lengthInMeters (tiltedColumnLengthL setup) *
        Real.Angle.sin setup.figure.branchAngleFromHorizontal

/-! ## Gauge-pressure consequence and requested inclined length -/

/-- The hydrostatic gauge-pressure relation for the stated water head. -/
theorem gauge_pressure_eq_density_times_gravity_times_height
    (setup : WaterUTubeManometerSetup)
    (hLaws : SatisfiesWaterManometerAndTiltLaws setup) :
    pressureInPascals setup.gaugePressure =
      densityInKilogramsPerCubicMeter setup.liquidDensity *
        accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
          lengthInMeters (heightDifferenceH setup) := by
  exact hLaws.hydrostaticPressureBalance

/-- At `30°`, the inclined column is twice the original vertical head. -/
theorem tilted_column_length_is_twice_height
    (setup : WaterUTubeManometerSetup)
    (hFigure : MatchesSuppliedManometerFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalManometerParameters setup)
    (hLaws : SatisfiesWaterManometerAndTiltLaws setup) :
    lengthInCentimeters (tiltedColumnLengthL setup) =
      2 * lengthInCentimeters (heightDifferenceH setup) := by
  rcases hReadouts with ⟨_, _, hAngle⟩
  have hsinThirty :
      Real.Angle.sin (degrees 30) = (1 : ℝ) / 2 := by
    simp only [degrees, Real.Angle.sin_coe]
    rw [show (30 : ℝ) * Real.pi / 180 = Real.pi / 6 by ring,
      Real.sin_pi_div_six]
  have hmeters :
      lengthInMeters (tiltedColumnLengthL setup) =
        2 * lengthInMeters (heightDifferenceH setup) := by
    have hprojection := hLaws.tiltedLengthVerticalProjection
    rw [hAngle, hsinThirty] at hprojection
    linarith
  have centimeters_eq_hundred_meters (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have hunit := length.2
      ({UnitChoices.SI with length := LengthUnit.meters} : UnitChoices)
      ({UnitChoices.SI with length := LengthUnit.centimeters} : UnitChoices)
    have hval := congrArg WithDim.val hunit
    have hvalReal := congrArg (fun value : NNReal => (value : ℝ)) hval
    norm_num [lengthInCentimeters, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.meters, LengthUnit.centimeters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.smul_def] at hvalReal ⊢
    exact hvalReal
  calc
    lengthInCentimeters (tiltedColumnLengthL setup) =
        100 * lengthInMeters (tiltedColumnLengthL setup) :=
      centimeters_eq_hundred_meters _
    _ = 2 * (100 * lengthInMeters (heightDifferenceH setup)) := by
      rw [hmeters]
      ring
    _ = 2 * lengthInCentimeters (heightDifferenceH setup) := by
      rw [centimeters_eq_hundred_meters]

/-- The four length choices printed in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Centimetre value displayed beside an answer-choice label. -/
def AnswerChoice.lengthInCentimeters : AnswerChoice → ℝ
  | .A => 490
  | .B => 50
  | .C => 154
  | .D => 51 / 5

/-- A choice matches the independently modeled inclined physical length. -/
def AnswersInclinedColumnQuestion
    (setup : WaterUTubeManometerSetup) (choice : AnswerChoice) : Prop :=
  lengthInCentimeters (tiltedColumnLengthL setup) =
    choice.lengthInCentimeters

/--
The requested relation in blueprint label
`thm:physics:phyx_mini_0387:target`: the column marked `L` is `50 cm`.
-/
theorem tilted_column_length_is_fifty_centimeters
    (setup : WaterUTubeManometerSetup)
    (hFigure : MatchesSuppliedManometerFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalManometerParameters setup)
    (hLaws : SatisfiesWaterManometerAndTiltLaws setup) :
    lengthInCentimeters (tiltedColumnLengthL setup) = 50 := by
  calc
    lengthInCentimeters (tiltedColumnLengthL setup) =
        2 * lengthInCentimeters (heightDifferenceH setup) :=
      tilted_column_length_is_twice_height
        setup hFigure hReadouts hPhysical hLaws
    _ = 50 := by
      rw [hReadouts.2.1]
      norm_num

/-- Choice B is the unique displayed choice matching the physical length `L`. -/
theorem problem_phyx_mini_0387
    (setup : WaterUTubeManometerSetup)
    (hFigure : MatchesSuppliedManometerFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalManometerParameters setup)
    (hLaws : SatisfiesWaterManometerAndTiltLaws setup) :
    AnswersInclinedColumnQuestion setup .B ∧
      ∀ choice, AnswersInclinedColumnQuestion setup choice → choice = .B := by
  have hLength :=
    tilted_column_length_is_fifty_centimeters
      setup hFigure hReadouts hPhysical hLaws
  constructor
  · simpa [AnswersInclinedColumnQuestion,
      AnswerChoice.lengthInCentimeters] using hLength
  · intro choice hChoice
    unfold AnswersInclinedColumnQuestion at hChoice
    rw [hLength] at hChoice
    cases choice with
    | A => norm_num [AnswerChoice.lengthInCentimeters] at hChoice
    | B => rfl
    | C => norm_num [AnswerChoice.lengthInCentimeters] at hChoice
    | D => norm_num [AnswerChoice.lengthInCentimeters] at hChoice

end PhyXMiniProblems.ProblemPhyXMini0387
