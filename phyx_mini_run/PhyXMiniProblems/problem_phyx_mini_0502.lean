import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Order.Interval.Set.Defs
import Physlib.QuantumMechanics.HilbertSpaces.OneDimension.Basic
import Physlib.SpaceAndTime.Space.LengthUnit

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0502

/-!
# Probability for an electron to land in a narrow central strip

The supplied graph shows the position probability density of an electron after
it has passed through an experimental apparatus.  Its horizontal coordinate is
read in millimetres and its density is read in inverse millimetres.  These real
numbers are explicitly calibrated readouts: the physical probability is kept
as a normalized `MeasureTheory.ProbabilityMeasure` on the position readout.

The graph label `P(x) = |ψ(x)|²` is represented by a Born-rule premise.  The
multiple-choice calculation uses the usual narrow-strip model
`Pr(strip) = density(center) * width`.  This approximation is stated as a
governing relation and does not contain the requested numerical answer.
-/

/-! ## Experiment and figure vocabulary -/

/-- The particle species named in the scenario. -/
inductive QuantumParticleKind where
  | electron
  deriving DecidableEq, Repr

/-- Labels for the three triangular peaks visible in the graph. -/
inductive DensityPeakLabel where
  | left
  | central
  | right
  deriving DecidableEq, Fintype, Repr

/-- The qualitative curve shape read from the supplied graph. -/
inductive ProbabilityDensityCurveShape where
  | threeTriangularPeaks
  deriving DecidableEq, Repr

/-!
The numerical and qualitative data printed in the probability-density graph.
All positions, widths, and density values are named readouts in the units shown
on the axes, rather than transparent aliases for physical quantities.
-/
structure ProbabilityDensityFigure where
  xAxisMinimumMillimeters : ℝ
  xAxisMaximumMillimeters : ℝ
  peakCenterMillimeters : DensityPeakLabel → ℝ
  peakDensityPerMillimeter : DensityPeakLabel → ℝ
  peakBaseWidthMillimeters : DensityPeakLabel → ℝ
  curveShape : ProbabilityDensityCurveShape
  symmetricAboutYAxis : Bool

/-!
Physical state of the one-dimensional electron-position experiment.

`waveAmplitudePerSqrtMillimeter` and `densityPerMillimeter` are calibrated
coordinate representations of the wave amplitude and density.  Physlib's
`QuantumMechanics.OneDimension.HilbertSpace.MemHS` ensures that the amplitude
is a square-integrable representative of a one-dimensional quantum state.
The actual dimensionless position probability is the normalized measure
`positionProbability`; it is not defined from an answer choice.
-/
structure ElectronPositionExperiment where
  particleKind : QuantumParticleKind
  hasPassedThroughExperimentalApparatus : Bool
  coordinateLengthUnit : LengthUnit
  waveAmplitudePerSqrtMillimeter : ℝ → ℂ
  waveAmplitudeMemHilbertSpace :
    QuantumMechanics.OneDimension.HilbertSpace.MemHS
      waveAmplitudePerSqrtMillimeter
  densityPerMillimeter : ℝ → ℝ
  positionProbability : MeasureTheory.ProbabilityMeasure ℝ
  figure : ProbabilityDensityFigure

/-! ## Physical laws and figure/data readouts -/

/-!
The Born position-density law and its measure-theoretic interpretation.

Lebesgue volume is taken on the numerical millimetre coordinate, so a density
readout has the displayed reciprocal-millimetre role.  `ENNReal.ofReal` embeds
the nonnegative real density supplied by the squared complex amplitude.
-/
structure SatisfiesBornPositionDensityLaw
    (experiment : ElectronPositionExperiment) : Prop where
  bornRule : ∀ x : ℝ,
    experiment.densityPerMillimeter x =
      Complex.normSq (experiment.waveAmplitudePerSqrtMillimeter x)
  probabilityMeasureHasDensity :
    experiment.positionProbability.toMeasure =
      (MeasureTheory.volume : MeasureTheory.Measure ℝ).withDensity
        (fun x => ENNReal.ofReal (experiment.densityPerMillimeter x))

/-!
Scenario facts and primary-image readouts from `502.png`.

The three peak centers are `-2`, `0`, and `2` mm; the corresponding peak
densities are `0.25`, `0.50`, and `0.25` mm⁻¹; every triangular base is `2` mm
wide; and the plotted axis spans `-3` to `3` mm.  These data contain no strip
probability and no answer-choice value.
-/
structure MatchesProblemStatementAndFigure
    (experiment : ElectronPositionExperiment) : Prop where
  particleIsElectron : experiment.particleKind = .electron
  electronPassedThroughApparatus :
    experiment.hasPassedThroughExperimentalApparatus = true
  positionCoordinateIsInMillimeters :
    experiment.coordinateLengthUnit = LengthUnit.millimeters
  xAxisMinimum : experiment.figure.xAxisMinimumMillimeters = -3
  xAxisMaximum : experiment.figure.xAxisMaximumMillimeters = 3
  curveHasThreeTriangularPeaks :
    experiment.figure.curveShape = .threeTriangularPeaks
  figureIsSymmetric : experiment.figure.symmetricAboutYAxis = true
  leftPeakCenter : experiment.figure.peakCenterMillimeters .left = -2
  centralPeakCenter : experiment.figure.peakCenterMillimeters .central = 0
  rightPeakCenter : experiment.figure.peakCenterMillimeters .right = 2
  leftPeakDensity :
    experiment.figure.peakDensityPerMillimeter .left = (1 : ℝ) / 4
  centralPeakDensity :
    experiment.figure.peakDensityPerMillimeter .central = (1 : ℝ) / 2
  rightPeakDensity :
    experiment.figure.peakDensityPerMillimeter .right = (1 : ℝ) / 4
  eachPeakBaseWidth : ∀ peak : DensityPeakLabel,
    experiment.figure.peakBaseWidthMillimeters peak = 2
  modelDensityAtPeak : ∀ peak : DensityPeakLabel,
    experiment.densityPerMillimeter
        (experiment.figure.peakCenterMillimeters peak) =
      experiment.figure.peakDensityPerMillimeter peak
  modeledDensityIsSymmetric : ∀ x : ℝ,
    experiment.densityPerMillimeter (-x) =
      experiment.densityPerMillimeter x

/-! ## Requested strip and narrow-strip approximation -/

/-- A detector strip specified by its center and full width, both in mm. -/
structure DetectionStripReadout where
  centerMillimeters : ℝ
  widthMillimeters : ℝ

/-- The closed interval of millimetre-coordinate readings covered by a strip. -/
def DetectionStripReadout.region
    (strip : DetectionStripReadout) : Set ℝ :=
  Set.Icc
    (strip.centerMillimeters - strip.widthMillimeters / 2)
    (strip.centerMillimeters + strip.widthMillimeters / 2)

/-- The dimensionless probability assigned by the model to a detector strip. -/
def stripProbability
    (experiment : ElectronPositionExperiment)
    (strip : DetectionStripReadout) : ℝ :=
  (experiment.positionProbability.toMeasure strip.region).toReal

/-- The `0.010`-mm-wide strip centered at `x = 0.000 mm`. -/
def requestedCentralStrip : DetectionStripReadout where
  centerMillimeters := 0
  widthMillimeters := (1 : ℝ) / 100

/-!
The textbook narrow-strip approximation used by the multiple-choice problem.
The premise also records that the strip width is positive and smaller than the
base width of the central peak.  Its probability equation is a general local
density-times-width relation and does not state the requested numeric value.
-/
structure UsesNarrowStripProbabilityApproximation
    (experiment : ElectronPositionExperiment)
    (strip : DetectionStripReadout) : Prop where
  widthIsPositive : 0 < strip.widthMillimeters
  widthIsNarrowRelativeToCentralPeak :
    strip.widthMillimeters <
      experiment.figure.peakBaseWidthMillimeters .central
  probabilityIsCenterDensityTimesWidth :
    stripProbability experiment strip =
      experiment.densityPerMillimeter strip.centerMillimeters *
        strip.widthMillimeters

/-! ## Answer choices and target -/

/-- The four answer-choice labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Dimensionless probability value displayed beside an answer choice. -/
def AnswerChoice.probabilityValue : AnswerChoice → ℝ
  | .A => 3 / 10000
  | .B => 3 / 1000
  | .C => 5 / 1000
  | .D => 5 / 10000

/-- Dataset metadata records choice C; this constant is never a premise. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- A choice matches when its displayed value equals the modeled strip probability. -/
def MatchesAnswerChoice
    (experiment : ElectronPositionExperiment)
    (strip : DetectionStripReadout)
    (choice : AnswerChoice) : Prop :=
  stripProbability experiment strip = choice.probabilityValue

/-!
For the requested central strip, the figure's `0.50 mm⁻¹` density and the
`0.010 mm` width give the dimensionless probability `5.0 × 10⁻³` under the
narrow-strip approximation.
-/
private lemma centralStripProbability_eq_five_thousandths
    (experiment : ElectronPositionExperiment)
    (hBorn : SatisfiesBornPositionDensityLaw experiment)
    (hFigure : MatchesProblemStatementAndFigure experiment)
    (hNarrow : UsesNarrowStripProbabilityApproximation
      experiment requestedCentralStrip) :
    stripProbability experiment requestedCentralStrip = (5 : ℝ) / 1000 := by
  rw [hNarrow.probabilityIsCenterDensityTimesWidth]
  have hDensity := hFigure.modelDensityAtPeak .central
  rw [hFigure.centralPeakCenter, hFigure.centralPeakDensity] at hDensity
  change
    experiment.densityPerMillimeter 0 * ((1 : ℝ) / 100) =
      (5 : ℝ) / 1000
  rw [hDensity]
  norm_num

/-!
The recorded answer is choice C.

This is the declaration corresponding to blueprint label
`thm:physics:phyx_mini_0502:target`.
-/
theorem problem_phyx_mini_0502
    (experiment : ElectronPositionExperiment)
    (hBorn : SatisfiesBornPositionDensityLaw experiment)
    (hFigure : MatchesProblemStatementAndFigure experiment)
    (hNarrow : UsesNarrowStripProbabilityApproximation
      experiment requestedCentralStrip) :
    MatchesAnswerChoice experiment requestedCentralStrip .C := by
  unfold MatchesAnswerChoice AnswerChoice.probabilityValue
  exact
    centralStripProbability_eq_five_thousandths experiment hBorn hFigure hNarrow

end PhyXMiniProblems.ProblemPhyXMini0502
