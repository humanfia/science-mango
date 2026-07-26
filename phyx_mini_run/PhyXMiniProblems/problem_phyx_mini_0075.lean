import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0075

open Dimension

/-!
# Diffraction-limited resolution of an eye-chart circle

All wavelengths and distances below are genuine dimensionful lengths.  The
angle `alpha` is a dimensionless real readout in radians.  In the supplied
figure, `d` is the edge-on diameter of the chart circle, `s` is the axial
distance from the circle to the eye, and `alpha` is the angle between the two
limiting rays at the eye lens.

The source gives no illumination wavelength.  Accordingly the wavelength is
an unspecified positive physical parameter, and the recorded multiple-choice
answer is retained only as dataset metadata.  The exact symmetric geometry is
`d / s = 2 * tan (alpha / 2)`.  Its paraxial replacement by `alpha` is controlled
locally by an explicit cubic remainder contract rather than asserted as a
global equality.
-/

/-- A physical length represented independently of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Scalar readout of a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length { UnitChoices.SI with length := unit }).val

/-- Scalar readout of a physical length in millimeters. -/
def lengthInMillimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.millimeters length

/-- Scalar readout of a physical length in feet. -/
def lengthInFeet (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.feet length

/-- Length labels printed in the supplied eye-chart figure. -/
inductive FigureLengthLabel where
  /-- `d`: the edge-on diameter of the circle on the chart. -/
  | d
  /-- `s`: the axial chart-circle-to-eye distance. -/
  | s
  deriving DecidableEq, Repr

/-- The angular label printed between the two limiting rays. -/
inductive FigureAngleLabel where
  /-- `alpha`: angular separation of the two visible circle edges. -/
  | alpha
  deriving DecidableEq, Repr

/-- Illumination condition relevant to the pupil diameter. -/
inductive LightingCondition where
  | bright
  | ordinary
  | dim
  deriving DecidableEq, Repr

/-- Optical effect that limits visual acuity in a pupil-size regime. -/
inductive AcuityLimitation where
  | diffraction
  | aberration
  deriving DecidableEq, Repr

/-- Optical/geometric regime used to interpret a resolution calculation. -/
inductive ResolutionRegime where
  /-- Circular-aperture Rayleigh optics with locally controlled geometry. -/
  | rayleighCircularApertureControlledParaxial
  | aberrationLimited
  deriving DecidableEq, Repr

/-- Provenance of the wavelength used in the diffraction model. -/
inductive WavelengthProvenance where
  /-- The source concerns visible light but supplies no numerical wavelength. -/
  | sourceUnspecifiedVisible
  /-- A wavelength measured for the illumination used during an eye test. -/
  | measuredIllumination
  /-- A wavelength stated for a monochromatic source. -/
  | specifiedMonochromaticSource
  deriving DecidableEq, Repr

/--
Physical quantities for the pupil and eye-chart resolution model.

`minimumResolvedCircleDiameter` is an unknown physical length.  The two
paraxial-control fields are dimensionless: a radian-valued local validity
radius and a coefficient bounding the cubic angular remainder.  No field fixes
the unknown diameter or chooses an answer option.
-/
structure EyeChartResolutionSetup where
  illuminationWavelength : LengthQuantity
  wavelengthProvenance : WavelengthProvenance
  pupilDiameter : LengthQuantity
  normalOptimalPupilDiameter : LengthQuantity
  chartDistance : LengthQuantity
  minimumResolvedCircleDiameter : LengthQuantity
  angularSeparationRad : ℝ
  paraxialValidityRadiusRad : ℝ
  paraxialCubicErrorCoefficient : ℝ
  lighting : LightingCondition
  dominantLimitation : AcuityLimitation
  regime : ResolutionRegime

/-- Interpret each length label in the figure as its setup quantity. -/
def figureLength
    (setup : EyeChartResolutionSetup) : FigureLengthLabel → LengthQuantity
  | .d => setup.minimumResolvedCircleDiameter
  | .s => setup.chartDistance

/-- Interpret the figure's `alpha` label as a radian-valued separation. -/
def figureAngleRad
    (setup : EyeChartResolutionSetup) : FigureAngleLabel → ℝ
  | .alpha => setup.angularSeparationRad

/--
The exact diameter-to-distance ratio for a centered planar circle subtending a
full angle `theta` at the eye.
-/
def centralAngleDiameterRatio (theta : ℝ) : ℝ :=
  2 * Real.tan (theta / 2)

/-- Difference between the exact angular diameter ratio and its paraxial term. -/
def paraxialAngularRemainder (theta : ℝ) : ℝ :=
  centralAngleDiameterRatio theta - theta

/-- Positivity and local angular-range conditions for the physical setup. -/
def HasPhysicalParameters (setup : EyeChartResolutionSetup) : Prop :=
  (∀ unit : LengthUnit,
      0 < lengthReadout unit setup.illuminationWavelength ∧
      0 < lengthReadout unit setup.pupilDiameter ∧
      0 < lengthReadout unit setup.normalOptimalPupilDiameter ∧
      0 < lengthReadout unit setup.chartDistance ∧
      0 < lengthReadout unit setup.minimumResolvedCircleDiameter) ∧
    0 < setup.angularSeparationRad ∧
    0 < setup.paraxialValidityRadiusRad ∧
    |setup.angularSeparationRad| ≤ setup.paraxialValidityRadiusRad ∧
    setup.paraxialValidityRadiusRad < Real.pi ∧
    0 ≤ setup.paraxialCubicErrorCoefficient

/-
Numerical readouts stated in the problem: a `2.0 mm` pupil in bright light,
the normal `3 mm` optimum, and a chart distance of `20 ft`.
-/
def MatchesProblemReadouts (setup : EyeChartResolutionSetup) : Prop :=
  lengthInMillimeters setup.pupilDiameter = 2 ∧
    lengthInMillimeters setup.normalOptimalPupilDiameter = 3 ∧
    lengthInFeet setup.chartDistance = 20 ∧
    setup.lighting = .bright

/-- The source supplies no numerical illumination wavelength. -/
def SourceLeavesWavelengthUnspecified (setup : EyeChartResolutionSetup) : Prop :=
  setup.wavelengthProvenance = .sourceUnspecifiedVisible

/-- The calculation uses Rayleigh optics and a locally controlled paraxial law. -/
def UsesControlledRayleighRegime (setup : EyeChartResolutionSetup) : Prop :=
  setup.regime = .rayleighCircularApertureControlledParaxial

/-
Qualitative pupil-size law stated in the scenario: below the normal optimum,
diffraction dominates; above it, aberration dominates.
-/
def SatisfiesPupilAcuityTrend (setup : EyeChartResolutionSetup) : Prop :=
  (lengthInMillimeters setup.pupilDiameter <
      lengthInMillimeters setup.normalOptimalPupilDiameter →
    setup.dominantLimitation = .diffraction) ∧
  (lengthInMillimeters setup.normalOptimalPupilDiameter <
      lengthInMillimeters setup.pupilDiameter →
    setup.dominantLimitation = .aberration)

/-
Rayleigh's diffraction criterion for a circular pupil,
`alpha = 1.22 * wavelength / pupilDiameter`.  The statement is made in every
length unit so the dimensionless ratio is explicitly unit-independent.
-/
def SatisfiesRayleighCriterion (setup : EyeChartResolutionSetup) : Prop :=
  ∀ unit : LengthUnit,
    setup.angularSeparationRad =
      (61 / 50 : ℝ) *
        lengthReadout unit setup.illuminationWavelength /
          lengthReadout unit setup.pupilDiameter

/-
Exact figure geometry together with a genuinely local paraxial remainder
contract.  For the actual figure angle, `d / s = 2 tan (alpha/2)`.  Uniformly
for angles in the declared neighborhood of zero, replacing that exact ratio
by `theta` incurs at most a cubic error.
-/
def SatisfiesControlledFigureGeometry (setup : EyeChartResolutionSetup) : Prop :=
  (∀ unit : LengthUnit,
      lengthReadout unit (figureLength setup .d) =
        lengthReadout unit (figureLength setup .s) *
          centralAngleDiameterRatio (figureAngleRad setup .alpha)) ∧
    ∀ theta : ℝ,
      |theta| ≤ setup.paraxialValidityRadiusRad →
        |paraxialAngularRemainder theta| ≤
          setup.paraxialCubicErrorCoefficient * |theta| ^ 3

/-- Labels of the four diameter choices printed by the dataset item. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Diameter in millimeters displayed beside each answer label. -/
def displayedDiameterInMillimeters : AnswerChoice → ℝ
  | .A => 1.47
  | .B => 2.26
  | .C => 2.0
  | .D => 1.95

/-
Answer label recorded in the source dataset.  It is metadata only: the source
does not specify the wavelength needed to derive a unique numerical choice.
-/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A `2 mm` pupil is below the `3 mm` optimum, so diffraction is active. -/
lemma dominantLimitation_eq_diffraction
    (setup : EyeChartResolutionSetup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_trend : SatisfiesPupilAcuityTrend setup) :
    setup.dominantLimitation = .diffraction := by
  apply h_trend.1
  rw [h_readouts.1, h_readouts.2.1]
  norm_num

/-
For the source-specified pupil and chart distance, but an arbitrary positive
illumination wavelength, Rayleigh's criterion and the exact centered geometry
give a symbolic minimum visible diameter.  The final conjunct controls the
error made by the usual paraxial replacement `2 tan (theta/2) ≈ theta`.

No numerical diameter or answer choice follows until a wavelength is supplied.
This formalizes `thm:physics:phyx_mini_0075:target`.
-/
theorem problem_phyx_mini_0075
    (setup : EyeChartResolutionSetup)
    (h_physical : HasPhysicalParameters setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_wavelengthSource : SourceLeavesWavelengthUnspecified setup)
    (h_regime : UsesControlledRayleighRegime setup)
    (h_trend : SatisfiesPupilAcuityTrend setup)
    (h_rayleigh : SatisfiesRayleighCriterion setup)
    (h_geometry : SatisfiesControlledFigureGeometry setup) :
    let theta :=
      (61 / 50 : ℝ) *
        lengthInMillimeters setup.illuminationWavelength /
          lengthInMillimeters setup.pupilDiameter
    setup.dominantLimitation = .diffraction ∧
      lengthInMillimeters setup.minimumResolvedCircleDiameter =
        lengthInMillimeters setup.chartDistance *
          centralAngleDiameterRatio theta ∧
      |lengthInMillimeters setup.minimumResolvedCircleDiameter -
          lengthInMillimeters setup.chartDistance * theta| ≤
        lengthInMillimeters setup.chartDistance *
          setup.paraxialCubicErrorCoefficient * |theta| ^ 3 := by
  let theta : ℝ :=
    (61 / 50 : ℝ) *
      lengthInMillimeters setup.illuminationWavelength /
        lengthInMillimeters setup.pupilDiameter
  change
    setup.dominantLimitation = .diffraction ∧
      lengthInMillimeters setup.minimumResolvedCircleDiameter =
        lengthInMillimeters setup.chartDistance *
          centralAngleDiameterRatio theta ∧
      |lengthInMillimeters setup.minimumResolvedCircleDiameter -
          lengthInMillimeters setup.chartDistance * theta| ≤
        lengthInMillimeters setup.chartDistance *
          setup.paraxialCubicErrorCoefficient * |theta| ^ 3
  have h_limitation :=
    dominantLimitation_eq_diffraction setup h_readouts h_trend
  rcases h_physical with
    ⟨h_lengths, _, _, h_angle_bound, _, _⟩
  rcases h_lengths LengthUnit.millimeters with
    ⟨_, _, _, h_distance_pos, _⟩
  have h_chart_pos :
      0 < lengthInMillimeters setup.chartDistance := by
    simpa only [lengthInMillimeters] using h_distance_pos
  have h_theta : setup.angularSeparationRad = theta := by
    simpa only [theta, lengthInMillimeters] using
      h_rayleigh LengthUnit.millimeters
  rcases h_geometry with ⟨h_exact_all, h_error_all⟩
  have h_exact :
      lengthInMillimeters setup.minimumResolvedCircleDiameter =
        lengthInMillimeters setup.chartDistance *
          centralAngleDiameterRatio theta := by
    simpa only [figureLength, figureAngleRad, lengthInMillimeters, h_theta] using
      h_exact_all LengthUnit.millimeters
  have h_theta_bound :
      |theta| ≤ setup.paraxialValidityRadiusRad := by
    simpa only [h_theta] using h_angle_bound
  have h_error :
      |centralAngleDiameterRatio theta - theta| ≤
        setup.paraxialCubicErrorCoefficient * |theta| ^ 3 := by
    simpa only [paraxialAngularRemainder] using
      h_error_all theta h_theta_bound
  refine ⟨h_limitation, h_exact, ?_⟩
  rw [h_exact]
  calc
    |lengthInMillimeters setup.chartDistance *
          centralAngleDiameterRatio theta -
        lengthInMillimeters setup.chartDistance * theta| =
        |lengthInMillimeters setup.chartDistance *
          (centralAngleDiameterRatio theta - theta)| := by
            congr 1
            ring
    _ = |lengthInMillimeters setup.chartDistance| *
          |centralAngleDiameterRatio theta - theta| := by
            rw [abs_mul]
    _ = lengthInMillimeters setup.chartDistance *
          |centralAngleDiameterRatio theta - theta| := by
            rw [abs_of_pos h_chart_pos]
    _ ≤ lengthInMillimeters setup.chartDistance *
          (setup.paraxialCubicErrorCoefficient * |theta| ^ 3) :=
            mul_le_mul_of_nonneg_left h_error (le_of_lt h_chart_pos)
    _ = lengthInMillimeters setup.chartDistance *
          setup.paraxialCubicErrorCoefficient * |theta| ^ 3 := by
            ring

end PhyXMiniProblems.ProblemPhyXMini0075
