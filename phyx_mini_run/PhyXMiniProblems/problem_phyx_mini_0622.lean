import Mathlib
import Physlib.Relativity.LorentzGroup.Boosts.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0622

open Dimension

/-!
# Relativistic dimensions of a painting on a spaceship

A rectangular painting has rest-frame height `1.00 m` and width `1.50 m`.
It is mounted on the side wall of a spaceship moving past Earth at `0.90 c`.
The width is parallel to the motion, whereas the height is transverse.  Thus
an Earth-frame simultaneous endpoint measurement contracts only the width.

Physical lengths and the relative speed are represented by unit-independent
Physlib quantities.  Real numbers occur only as named-unit readouts,
dimensionless speed ratios, and displayed multiple-choice values.

Assumption/target split:

* the primary-figure predicate records the vertical `1.00 m` label and the
  horizontal question mark;
* the problem-data predicate records the `1.50 m` proper width and `0.90 c`;
* the geometry predicate identifies width as parallel and height as transverse;
* the governing law gives the generic axis-sensitive Lorentz transformation;
* the Earth-frame dimensions and agreement with answer C occur only in lemma
  or theorem conclusions.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Meter readout used by the problem, figure, and answer choices. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical speed in metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Physlib's vacuum speed of light, read in metres per second. -/
def vacuumSpeedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-! ## Frames, painting geometry, and primary-image vocabulary -/

/-- The two inertial frames relevant to the dimension measurements. -/
inductive InertialFrameLabel where
  | spaceshipRest
  | earth
  deriving DecidableEq, Repr

/-- The two physical dimensions of the rectangular painting. -/
inductive PaintingDimension where
  | height
  | width
  deriving DecidableEq, Fintype, Repr

/-- Whether a painting dimension is parallel or transverse to the motion. -/
inductive MotionAxisRole where
  | parallelToMotion
  | transverseToMotion
  deriving DecidableEq, Repr

/-- The two kinds of dimension annotation appearing in the supplied image. -/
inductive FigureDimensionAnnotation where
  | knownMeters (value : ℝ)
  | questionMark

/-!
Literal evidence carried by `phyx_data/test_image/622.png`.  The image labels
the vertical arrow as `1.00 m` and places a question mark under the horizontal
arrow.  The landscape content is retained as a qualitative check that the
outlined rectangle is the painting referred to in the prose.
-/
structure PaintingFigure where
  verticalArrowDimension : PaintingDimension
  horizontalArrowDimension : PaintingDimension
  dimensionAnnotation : PaintingDimension → FigureDimensionAnnotation
  rectangularOutlineShown : Bool
  landscapeSceneShown : Bool

/-!
Independent physical quantities in the problem.  In particular,
`earthMeasuredDimension` is an observable field rather than a definition made
from an answer choice or from the contraction formula.
-/
structure RelativisticPaintingSetup where
  figure : PaintingFigure
  paintingRestFrame : InertialFrameLabel
  earthMeasurementFrame : InertialFrameLabel
  restDimension : PaintingDimension → LengthQuantity
  earthMeasuredDimension : PaintingDimension → LengthQuantity
  relativeSpeed : DimSpeed
  dimensionAxisRole : PaintingDimension → MotionAxisRole
  paintingIsRectangular : Bool
  paintingMountedOnSpaceshipSideWall : Bool
  earthEndpointMeasurementIsSimultaneous : PaintingDimension → Bool

/-- The dimensionless speed parameter `β = v/c` in coherent SI readouts. -/
def speedFractionOfLight (setup : RelativisticPaintingSetup) : ℝ :=
  speedInMetersPerSecond setup.relativeSpeed /
    vacuumSpeedOfLightInMetersPerSecond

/-- The Lorentz factor supplied by Physlib for the setup's relative speed. -/
def lorentzFactor (setup : RelativisticPaintingSetup) : ℝ :=
  LorentzGroup.γ (speedFractionOfLight setup)

/-! ## Scenario, figure/data readouts, and governing physics -/

/-- The prose scenario and the operational meaning of an Earth-frame length. -/
structure MatchesPaintingOnSpaceshipScenario
    (setup : RelativisticPaintingSetup) : Prop where
  restDimensionsUseSpaceshipFrame :
    setup.paintingRestFrame = .spaceshipRest
  observedDimensionsUseEarthFrame :
    setup.earthMeasurementFrame = .earth
  paintingIsRectangular : setup.paintingIsRectangular = true
  paintingIsOnSideWall : setup.paintingMountedOnSpaceshipSideWall = true
  earthUsesSimultaneousEndpointMeasurements :
    ∀ dimension, setup.earthEndpointMeasurementIsSimultaneous dimension = true

/-- Quantitative and qualitative evidence read directly from the bitmap. -/
structure MatchesSuppliedPaintingFigure
    (figure : PaintingFigure) : Prop where
  verticalArrowMarksHeight :
    figure.verticalArrowDimension = .height
  horizontalArrowMarksWidth :
    figure.horizontalArrowDimension = .width
  printedHeightIsOneMeter :
    figure.dimensionAnnotation .height = .knownMeters 1
  widthIsMarkedByQuestion :
    figure.dimensionAnnotation .width = .questionMark
  rectangularPaintingOutlineShown : figure.rectangularOutlineShown = true
  landscapeInsidePaintingShown : figure.landscapeSceneShown = true

/-!
Numerical data stated in the problem.  The height is linked to the primary
figure's printed rest-frame value; the width and speed come from the prose.
No Earth-frame dimension or answer-choice value occurs here.
-/
structure MatchesProblemReadouts
    (setup : RelativisticPaintingSetup) : Prop where
  figureHeightLabelsRestHeight :
    setup.figure.dimensionAnnotation .height =
      .knownMeters (lengthInMeters (setup.restDimension .height))
  restWidthIsOnePointFiveMeters :
    lengthInMeters (setup.restDimension .width) = (3 / 2 : ℝ)
  relativeSpeedIsPointNineC :
    speedFractionOfLight setup = (9 / 10 : ℝ)

/-- The side-wall orientation relevant to Lorentz length contraction. -/
structure MatchesSideWallMotionGeometry
    (setup : RelativisticPaintingSetup) : Prop where
  widthIsParallelToMotion :
    setup.dimensionAxisRole .width = .parallelToMotion
  heightIsTransverseToMotion :
    setup.dimensionAxisRole .height = .transverseToMotion

/-- Positivity and the nonnegative subluminal regime of the physical model. -/
structure HasPhysicalRelativisticParameters
    (setup : RelativisticPaintingSetup) : Prop where
  positiveVacuumSpeed : 0 < vacuumSpeedOfLightInMetersPerSecond
  positiveRestDimensions :
    ∀ dimension, 0 < lengthInMeters (setup.restDimension dimension)
  positiveEarthDimensions :
    ∀ dimension, 0 < lengthInMeters (setup.earthMeasuredDimension dimension)
  relativeSpeedNonnegative : 0 ≤ speedFractionOfLight setup
  relativeSpeedSubluminal : speedFractionOfLight setup < 1

/-!
The governing special-relativistic length law.  For every painting dimension
and every common length unit, a component parallel to the relative motion is
divided by `γ(β)`, while a transverse component is unchanged.  This generic
law contains neither the numerical Earth-frame dimensions nor an answer label.
-/
structure SatisfiesAxisSensitiveLorentzLengthLaw
    (setup : RelativisticPaintingSetup) : Prop where
  dimensionTransformation : ∀ (unit : LengthUnit) (dimension : PaintingDimension),
    lengthReadout unit (setup.earthMeasuredDimension dimension) =
      match setup.dimensionAxisRole dimension with
      | .parallelToMotion =>
          lengthReadout unit (setup.restDimension dimension) /
            lorentzFactor setup
      | .transverseToMotion =>
          lengthReadout unit (setup.restDimension dimension)

/-! ## Derived dimensions and multiple-choice target -/

/-- Labels of the four width choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Width in metres printed beside each answer label. -/
def displayedWidthInMeters : AnswerChoice → ℝ
  | .A => 69 / 100
  | .B => 67 / 100
  | .C => 65 / 100
  | .D => 62 / 100

/-- The answer label recorded by the source dataset; this is metadata only. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
Agreement with a width displayed to two decimal places.  The strict tolerance
`0.005 m` excludes a rounding tie at a hundredth-place boundary.
-/
def MatchesDisplayedWidthChoice
    (setup : RelativisticPaintingSetup) (choice : AnswerChoice) : Prop :=
  |lengthInMeters (setup.earthMeasuredDimension .width) -
      displayedWidthInMeters choice| < (1 / 200 : ℝ)

/-- The transverse `1.00 m` height is unchanged for the Earth observer. -/
lemma earthMeasuredHeightInMeters_eq_one
    (setup : RelativisticPaintingSetup)
    (_figure : MatchesSuppliedPaintingFigure setup.figure)
    (_data : MatchesProblemReadouts setup)
    (_geometry : MatchesSideWallMotionGeometry setup)
    (_relativity : SatisfiesAxisSensitiveLorentzLengthLaw setup) :
    lengthInMeters (setup.earthMeasuredDimension .height) = 1 := by
  have hrest : lengthInMeters (setup.restDimension .height) = 1 := by
    exact FigureDimensionAnnotation.knownMeters.inj
      (_data.figureHeightLabelsRestHeight.symm.trans _figure.printedHeightIsOneMeter)
  calc
    lengthInMeters (setup.earthMeasuredDimension .height) =
        lengthInMeters (setup.restDimension .height) := by
      simpa [lengthInMeters, _geometry.heightIsTransverseToMotion] using
        _relativity.dimensionTransformation LengthUnit.meters .height
    _ = 1 := hrest

/-!
The longitudinal Earth-frame width is the `1.50 m` proper width divided by
the Lorentz factor at `β = 0.90`.
-/
lemma earthMeasuredWidthInMeters_exact
    (setup : RelativisticPaintingSetup)
    (_data : MatchesProblemReadouts setup)
    (_geometry : MatchesSideWallMotionGeometry setup)
    (_relativity : SatisfiesAxisSensitiveLorentzLengthLaw setup) :
    lengthInMeters (setup.earthMeasuredDimension .width) =
      (3 / 2 : ℝ) / LorentzGroup.γ (9 / 10 : ℝ) := by
  calc
    lengthInMeters (setup.earthMeasuredDimension .width) =
        lengthInMeters (setup.restDimension .width) / lorentzFactor setup := by
      simpa [lengthInMeters, _geometry.widthIsParallelToMotion] using
        _relativity.dimensionTransformation LengthUnit.meters .width
    _ = (3 / 2 : ℝ) / LorentzGroup.γ (9 / 10 : ℝ) := by
      rw [_data.restWidthIsOnePointFiveMeters]
      simp only [lorentzFactor, _data.relativeSpeedIsPointNineC]

/-!
Earth therefore measures the painting as `1.00 m` tall and
`(1.50 / γ(0.90)) m` wide.  The latter is approximately `0.6538 m`, so it
rounds to the displayed `0.65 m`, answer C.

This formalizes blueprint label `thm:physics:phyx_mini_0622:target`.
-/
theorem problem_phyx_mini_0622
    (setup : RelativisticPaintingSetup)
    (_scenario : MatchesPaintingOnSpaceshipScenario setup)
    (_figure : MatchesSuppliedPaintingFigure setup.figure)
    (_data : MatchesProblemReadouts setup)
    (_geometry : MatchesSideWallMotionGeometry setup)
    (_physical : HasPhysicalRelativisticParameters setup)
    (_relativity : SatisfiesAxisSensitiveLorentzLengthLaw setup) :
    lengthInMeters (setup.earthMeasuredDimension .height) = 1 ∧
      lengthInMeters (setup.earthMeasuredDimension .width) =
        (3 / 2 : ℝ) / LorentzGroup.γ (9 / 10 : ℝ) ∧
      MatchesDisplayedWidthChoice setup .C := by
  refine ⟨earthMeasuredHeightInMeters_eq_one setup _figure _data _geometry _relativity,
    earthMeasuredWidthInMeters_exact setup _data _geometry _relativity, ?_⟩
  have hwidth :
      (3 / 2 : ℝ) / LorentzGroup.γ (9 / 10 : ℝ) =
        3 * Real.sqrt 19 / 20 := by
    rw [LorentzGroup.γ]
    norm_num [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 19)]
    have hsqrt_pos : 0 < Real.sqrt 19 := Real.sqrt_pos.2 (by norm_num)
    field_simp
    norm_num
  have hsqrt_nonneg : 0 ≤ Real.sqrt 19 := Real.sqrt_nonneg 19
  have hsqrt_sq : (Real.sqrt 19) ^ 2 = (19 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_lower : (43 / 10 : ℝ) < Real.sqrt 19 := by
    nlinarith
  have hsqrt_upper : Real.sqrt 19 < (131 / 30 : ℝ) := by
    nlinarith
  have hrounding :
      |(3 * Real.sqrt 19 / 20 : ℝ) - 65 / 100| < 1 / 200 := by
    rw [abs_lt]
    constructor <;> norm_num <;> nlinarith
  unfold MatchesDisplayedWidthChoice
  rw [earthMeasuredWidthInMeters_exact setup _data _geometry _relativity]
  simpa [displayedWidthInMeters, hwidth] using hrounding

end PhyXMiniProblems.ProblemPhyXMini0622
