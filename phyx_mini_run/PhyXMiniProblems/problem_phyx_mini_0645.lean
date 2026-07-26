import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Expected electron count from a triangular position-probability density

The supplied graph is a symmetric triangular position density. Its horizontal
axis is a signed position in millimetres, while its vertical axis has units of
inverse millimetres and is labelled `P(x) = |ψ(x)|²`. One million electrons
pass through the apparatus, and the question asks for the expected count in a
`0.010 mm` strip centred at `x = 2.000 mm`.

Signed positions, nonnegative strip widths, and probability densities retain
their physical dimensions through Physlib. Real numbers occur only as named
unit readouts, wave-amplitude components in a named unit convention, and
dimensionless counts.

Assumption/target split:

* `MatchesElectronExperimentScenario` records the particle and apparatus;
* `MatchesSuppliedPositionDensityFigure` and `MatchesProblemReadouts` record
  the primary-image and question data;
* `FigurePlotsTriangularPositionDensity`, `SatisfiesPositionProbabilityLaws`,
  and `SatisfiesExpectedStripCountLaw` state the graph geometry, Born
  normalization, and the general expectation law; and
* the exact expected count and uniquely closest displayed answer occur only in
  `problem_phyx_mini_0645`.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0645

open CarriesDimension Dimension

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A signed, unit-independent position along the graph's horizontal axis. -/
abbrev PositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative, unit-independent physical length used for the strip width. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative probability density, carrying inverse-length dimension. -/
abbrev ProbabilityDensityQuantity : Type :=
  Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-- Read a signed physical position in a selected length unit. -/
def positionReadout (unit : LengthUnit) (position : PositionQuantity) : ℝ :=
  (position ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- Read a nonnegative physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length ({ UnitChoices.SI with length := unit } : UnitChoices)).val : ℝ)

/-- Read an inverse-length probability density in the reciprocal selected unit. -/
def densityReadout
    (unit : LengthUnit) (density : ProbabilityDensityQuantity) : ℝ :=
  ((density ({ UnitChoices.SI with length := unit } : UnitChoices)).val : ℝ)

/-- Construct a signed position from its millimetre readout. -/
def positionFromMillimeters (value : ℝ) : PositionQuantity :=
  toDimensionful
    ({ UnitChoices.SI with length := LengthUnit.millimeters } : UnitChoices)
    (show WithDim L𝓭 ℝ from ⟨value⟩)

/-! ## Quantum state, experiment, and primary-figure vocabulary -/

/--
An electron's one-dimensional position state after the apparatus.

The complex amplitude is a scalar readout in inverse square-root length units;
the associated probability density is stored as an inverse-length physical
quantity. Their physical relation is imposed separately by Born's rule.
-/
structure ElectronPositionState where
  waveAmplitudeReadout : LengthUnit → PositionQuantity → ℂ
  probabilityDensityAt : PositionQuantity → ProbabilityDensityQuantity

/-- Probability density at a coordinate whose numerical value is in millimetres. -/
def densityAtMillimeterCoordinate
    (state : ElectronPositionState) (xInMillimeters : ℝ) : ℝ :=
  densityReadout LengthUnit.millimeters
    (state.probabilityDensityAt (positionFromMillimeters xInMillimeters))

/-- The particle species sent through the experimental apparatus. -/
inductive ParticleSpecies where
  | electron
  | other
  deriving DecidableEq, Repr

/-- The qualitative shape of the curve shown in the supplied graph. -/
inductive DensityCurveShape where
  | symmetricTriangle
  | other
  deriving DecidableEq, Repr

/--
Axis labels, units, and landmarks read from the primary probability-density
graph. `displayedPeakDensity` is the printed scalar label `0.333`; it is not
asserted to be the exact normalized peak height.
-/
structure PositionDensityFigure where
  horizontalAxisLabel : String
  verticalAxisLabel : String
  horizontalAxisUnit : LengthUnit
  densityReciprocalLengthUnit : LengthUnit
  leftIntercept : PositionQuantity
  peakPosition : PositionQuantity
  rightIntercept : PositionQuantity
  displayedPeakDensity : ℝ
  curveShape : DensityCurveShape

/--
The repeated-electron experiment and the strip whose count is requested.
`expectedElectronCount` is an independent dimensionless observable; it is not
defined from an answer choice or from the requested numerical result.
-/
structure ElectronStripExperiment where
  species : ParticleSpecies
  hasPassedThroughApparatus : Bool
  allElectronsSharePositionState : Bool
  positionState : ElectronPositionState
  figure : PositionDensityFigure
  electronsUsed : ℕ
  stripCenter : PositionQuantity
  stripWidth : LengthQuantity
  expectedElectronCount : ℝ

/-! ## Scenario and figure/data readouts -/

/-- Qualitative physical assumptions in the problem statement. -/
structure MatchesElectronExperimentScenario
    (experiment : ElectronStripExperiment) : Prop where
  particleIsElectron : experiment.species = .electron
  passedThroughApparatus : experiment.hasPassedThroughApparatus = true
  commonPostApparatusState :
    experiment.allElectronsSharePositionState = true
  stripHasPositiveWidth :
    0 < lengthReadout LengthUnit.millimeters experiment.stripWidth
  expectedCountIsNonnegative : 0 ≤ experiment.expectedElectronCount

/--
Text, units, and plotted landmark readouts from the supplied image. The peak
label is recorded to the three decimals actually printed in the raster.
-/
structure MatchesSuppliedPositionDensityFigure
    (figure : PositionDensityFigure) : Prop where
  horizontalLabel : figure.horizontalAxisLabel = "x"
  verticalLabel : figure.verticalAxisLabel = "P(x) = |ψ(x)|²"
  horizontalUnitIsMillimeters :
    figure.horizontalAxisUnit = LengthUnit.millimeters
  densityUnitIsInverseMillimeters :
    figure.densityReciprocalLengthUnit = LengthUnit.millimeters
  leftInterceptInMillimeters :
    positionReadout LengthUnit.millimeters figure.leftIntercept = -3
  peakPositionInMillimeters :
    positionReadout LengthUnit.millimeters figure.peakPosition = 0
  rightInterceptInMillimeters :
    positionReadout LengthUnit.millimeters figure.rightIntercept = 3
  displayedPeakInInverseMillimeters :
    figure.displayedPeakDensity = 333 / 1000
  plottedShape : figure.curveShape = .symmetricTriangle

/-- Numerical data stated in the prose question; no expected count occurs here. -/
structure MatchesProblemReadouts
    (experiment : ElectronStripExperiment) : Prop where
  electronCount : experiment.electronsUsed = 1_000_000
  stripCenterInMillimeters :
    positionReadout LengthUnit.millimeters experiment.stripCenter = 2
  stripWidthInMillimeters :
    lengthReadout LengthUnit.millimeters experiment.stripWidth = 1 / 100

/-! ## Figure geometry and governing physical laws -/

/--
The graph is the linear triangular interpolation through its left intercept,
peak, and right intercept, with zero density outside its base. The exact peak
height is obtained from the physical density itself; the printed `0.333` label
is required only to agree with it to the displayed precision.

This predicate is figure evidence and contains neither an electron-count
expectation nor an answer-choice value.
-/
structure FigurePlotsTriangularPositionDensity
    (experiment : ElectronStripExperiment) : Prop where
  displayedPeakAccuracy :
    let peakX :=
      positionReadout LengthUnit.millimeters experiment.figure.peakPosition
    |densityAtMillimeterCoordinate experiment.positionState peakX -
        experiment.figure.displayedPeakDensity| ≤ 1 / 2000
  triangularInterpolation :
    let leftX :=
      positionReadout LengthUnit.millimeters experiment.figure.leftIntercept
    let peakX :=
      positionReadout LengthUnit.millimeters experiment.figure.peakPosition
    let rightX :=
      positionReadout LengthUnit.millimeters experiment.figure.rightIntercept
    let peakDensity :=
      densityAtMillimeterCoordinate experiment.positionState peakX
    ∀ xInMillimeters : ℝ,
      densityAtMillimeterCoordinate experiment.positionState xInMillimeters =
        if xInMillimeters < leftX ∨ rightX < xInMillimeters then
          0
        else if xInMillimeters ≤ peakX then
          peakDensity * (xInMillimeters - leftX) / (peakX - leftX)
        else
          peakDensity * (rightX - xInMillimeters) / (rightX - peakX)

/--
Born's rule and normalization for the post-apparatus position state. The
wave-amplitude and density readouts use compatible choices of length unit.
-/
structure SatisfiesPositionProbabilityLaws
    (experiment : ElectronStripExperiment) : Prop where
  bornRule :
    ∀ (unit : LengthUnit) (position : PositionQuantity),
      densityReadout unit
          (experiment.positionState.probabilityDensityAt position) =
        Complex.normSq
          (experiment.positionState.waveAmplitudeReadout unit position)
  densityIntervalIntegrable :
    IntervalIntegrable
      (densityAtMillimeterCoordinate experiment.positionState)
      MeasureTheory.volume
      (positionReadout LengthUnit.millimeters experiment.figure.leftIntercept)
      (positionReadout LengthUnit.millimeters experiment.figure.rightIntercept)
  normalizedPositionDensity :
    (∫ xInMillimeters in
        positionReadout LengthUnit.millimeters experiment.figure.leftIntercept..
          positionReadout LengthUnit.millimeters experiment.figure.rightIntercept,
        densityAtMillimeterCoordinate experiment.positionState xInMillimeters) = 1

/-- Left endpoint of the strip, as a scalar millimetre coordinate. -/
def stripLeftEndpointInMillimeters
    (experiment : ElectronStripExperiment) : ℝ :=
  positionReadout LengthUnit.millimeters experiment.stripCenter -
    lengthReadout LengthUnit.millimeters experiment.stripWidth / 2

/-- Right endpoint of the strip, as a scalar millimetre coordinate. -/
def stripRightEndpointInMillimeters
    (experiment : ElectronStripExperiment) : ℝ :=
  positionReadout LengthUnit.millimeters experiment.stripCenter +
    lengthReadout LengthUnit.millimeters experiment.stripWidth / 2

/--
The probability of landing in the centred strip is the density integral over
that strip, and linearity of expectation multiplies this probability by the
number of identically prepared electrons. No numerical answer is assumed.
-/
structure SatisfiesExpectedStripCountLaw
    (experiment : ElectronStripExperiment) : Prop where
  stripDensityIntervalIntegrable :
    IntervalIntegrable
      (densityAtMillimeterCoordinate experiment.positionState)
      MeasureTheory.volume
      (stripLeftEndpointInMillimeters experiment)
      (stripRightEndpointInMillimeters experiment)
  expectedCountLaw :
    experiment.expectedElectronCount =
      (experiment.electronsUsed : ℝ) *
        ∫ xInMillimeters in
            stripLeftEndpointInMillimeters experiment..
              stripRightEndpointInMillimeters experiment,
          densityAtMillimeterCoordinate experiment.positionState xInMillimeters

/-! ## Displayed choices and current target -/

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Expected electron count printed beside each answer label. -/
def displayedExpectedElectronCount : AnswerChoice → ℝ
  | .A => 800
  | .B => 1100
  | .C => 1400
  | .D => 1700

/-- A displayed count is strictly closer to the modeled expectation than every alternative. -/
def IsUniqueClosestDisplayedCount
    (experiment : ElectronStripExperiment) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice : AnswerChoice,
    otherChoice ≠ choice →
      |experiment.expectedElectronCount -
          displayedExpectedElectronCount choice| <
        |experiment.expectedElectronCount -
          displayedExpectedElectronCount otherChoice|

/-!
Normalization fixes the triangular peak at `1/3 mm⁻¹`. Integrating its
linear right branch over the `0.010 mm` strip centred at `2.000 mm` gives a
single-electron probability of `1/900`; among one million electrons the exact
expectation is therefore `10000/9`, whose uniquely closest displayed value is
`1100`, answer B.

This formalizes `thm:physics:phyx_mini_0645:target`.
-/
theorem problem_phyx_mini_0645
    (experiment : ElectronStripExperiment)
    (h_scenario : MatchesElectronExperimentScenario experiment)
    (h_problem : MatchesProblemReadouts experiment)
    (h_figure : MatchesSuppliedPositionDensityFigure experiment.figure)
    (h_triangle : FigurePlotsTriangularPositionDensity experiment)
    (h_probability : SatisfiesPositionProbabilityLaws experiment)
    (h_expectation : SatisfiesExpectedStripCountLaw experiment) :
    experiment.expectedElectronCount = (10000 : ℝ) / 9 ∧
      IsUniqueClosestDisplayedCount experiment .B := by
  let density : ℝ → ℝ :=
    densityAtMillimeterCoordinate experiment.positionState
  let peakDensity : ℝ := density 0

  have h_density_shape : ∀ x : ℝ,
      density x =
        if x < -3 ∨ 3 < x then
          0
        else if x ≤ 0 then
          peakDensity * (x - (-3)) / (0 - (-3))
        else
          peakDensity * (3 - x) / (3 - 0) := by
    intro x
    simpa [density, peakDensity, h_figure.leftInterceptInMillimeters,
      h_figure.peakPositionInMillimeters,
      h_figure.rightInterceptInMillimeters] using
        h_triangle.triangularInterpolation x

  have h_density_integrable :
      IntervalIntegrable density MeasureTheory.volume (-3) 3 := by
    simpa [density, h_figure.leftInterceptInMillimeters,
      h_figure.rightInterceptInMillimeters] using
        h_probability.densityIntervalIntegrable
  have h_density_integrable_left :
      IntervalIntegrable density MeasureTheory.volume (-3) 0 := by
    apply h_density_integrable.mono_set
    intro x hx
    have hx' : (-3 : ℝ) ≤ x ∧ x ≤ 0 := by
      simpa only [Set.uIcc_of_le (show (-3 : ℝ) ≤ 0 by norm_num),
        Set.mem_Icc] using hx
    have : (-3 : ℝ) ≤ x ∧ x ≤ 3 := by
      constructor <;> linarith [hx'.1, hx'.2]
    simpa only [Set.uIcc_of_le (show (-3 : ℝ) ≤ 3 by norm_num),
      Set.mem_Icc] using this
  have h_density_integrable_right :
      IntervalIntegrable density MeasureTheory.volume 0 3 := by
    apply h_density_integrable.mono_set
    intro x hx
    have hx' : (0 : ℝ) ≤ x ∧ x ≤ 3 := by
      simpa only [Set.uIcc_of_le (show (0 : ℝ) ≤ 3 by norm_num),
        Set.mem_Icc] using hx
    have : (-3 : ℝ) ≤ x ∧ x ≤ 3 := by
      constructor <;> linarith [hx'.1, hx'.2]
    simpa only [Set.uIcc_of_le (show (-3 : ℝ) ≤ 3 by norm_num),
      Set.mem_Icc] using this

  have h_left_branch :
      (∫ x in (-3 : ℝ)..0, density x) =
        ∫ x in (-3 : ℝ)..0, peakDensity * (x - (-3)) / (0 - (-3)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : (-3 : ℝ) ≤ x ∧ x ≤ 0 := by
      simpa only [Set.uIcc_of_le (show (-3 : ℝ) ≤ 0 by norm_num),
        Set.mem_Icc] using hx
    have h_inside : ¬ (x < (-3 : ℝ) ∨ 3 < x) := by
      intro h
      rcases h with h | h
      · linarith [hx'.1]
      · linarith [hx'.2]
    rw [h_density_shape x]
    rw [if_neg h_inside, if_pos hx'.2]
  have h_right_branch :
      (∫ x in (0 : ℝ)..3, density x) =
        ∫ x in (0 : ℝ)..3, peakDensity * (3 - x) / (3 - 0) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : (0 : ℝ) ≤ x ∧ x ≤ 3 := by
      simpa only [Set.uIcc_of_le (show (0 : ℝ) ≤ 3 by norm_num),
        Set.mem_Icc] using hx
    have h_inside : ¬ (x < (-3 : ℝ) ∨ 3 < x) := by
      intro h
      rcases h with h | h
      · linarith [hx'.1]
      · linarith [hx'.2]
    rw [h_density_shape x]
    rw [if_neg h_inside]
    by_cases hx0 : x = 0
    · subst x
      norm_num
    · rw [if_neg (not_le.mpr (lt_of_le_of_ne hx'.1 (Ne.symm hx0)))]

  have h_left_affine_integral :
      (∫ x in (-3 : ℝ)..0,
          peakDensity * (x - (-3)) / (0 - (-3))) =
        3 * peakDensity / 2 := by
    let f : ℝ → ℝ :=
      fun x => peakDensity * (x - (-3)) / (0 - (-3))
    have hf : IntervalIntegrable f MeasureTheory.volume (-3) 0 := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hreflected :
        IntervalIntegrable (fun x => f (-3 - x))
          MeasureTheory.volume (-3) 0 := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hreflection :
        (∫ x in (-3 : ℝ)..0, f (-3 - x)) =
          ∫ x in (-3 : ℝ)..0, f x := by
      rw [intervalIntegral.integral_comp_sub_left]
      norm_num
    change (∫ x in (-3 : ℝ)..0, f x) = 3 * peakDensity / 2
    calc
      (∫ x in (-3 : ℝ)..0, f x) =
          (1 / 2 : ℝ) * ((∫ x in (-3 : ℝ)..0, f x) +
            ∫ x in (-3 : ℝ)..0, f (-3 - x)) := by
              rw [hreflection]
              ring
      _ = (1 / 2 : ℝ) *
          (∫ x in (-3 : ℝ)..0, (f x + f (-3 - x))) := by
            rw [intervalIntegral.integral_add hf hreflected]
      _ = (1 / 2 : ℝ) * (∫ _x in (-3 : ℝ)..0, peakDensity) := by
            congr 1
            apply intervalIntegral.integral_congr
            intro x hx
            dsimp [f]
            ring
      _ = 3 * peakDensity / 2 := by
            rw [intervalIntegral.integral_const]
            norm_num
            ring

  have h_right_affine_integral :
      (∫ x in (0 : ℝ)..3,
          peakDensity * (3 - x) / (3 - 0)) =
        3 * peakDensity / 2 := by
    let f : ℝ → ℝ := fun x => peakDensity * (3 - x) / (3 - 0)
    have hf : IntervalIntegrable f MeasureTheory.volume 0 3 := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hreflected :
        IntervalIntegrable (fun x => f (3 - x))
          MeasureTheory.volume 0 3 := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hreflection :
        (∫ x in (0 : ℝ)..3, f (3 - x)) =
          ∫ x in (0 : ℝ)..3, f x := by
      rw [intervalIntegral.integral_comp_sub_left]
      norm_num
    change (∫ x in (0 : ℝ)..3, f x) = 3 * peakDensity / 2
    calc
      (∫ x in (0 : ℝ)..3, f x) =
          (1 / 2 : ℝ) * ((∫ x in (0 : ℝ)..3, f x) +
            ∫ x in (0 : ℝ)..3, f (3 - x)) := by
              rw [hreflection]
              ring
      _ = (1 / 2 : ℝ) *
          (∫ x in (0 : ℝ)..3, (f x + f (3 - x))) := by
            rw [intervalIntegral.integral_add hf hreflected]
      _ = (1 / 2 : ℝ) * (∫ _x in (0 : ℝ)..3, peakDensity) := by
            congr 1
            apply intervalIntegral.integral_congr
            intro x hx
            dsimp [f]
            ring
      _ = 3 * peakDensity / 2 := by
            rw [intervalIntegral.integral_const]
            norm_num
            ring

  have h_normalized :
      (∫ x in (-3 : ℝ)..3, density x) = 1 := by
    simpa [density, h_figure.leftInterceptInMillimeters,
      h_figure.rightInterceptInMillimeters] using
        h_probability.normalizedPositionDensity
  have h_peak_density : peakDensity = (1 : ℝ) / 3 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      h_density_integrable_left h_density_integrable_right,
      h_left_branch, h_right_branch, h_left_affine_integral,
      h_right_affine_integral] at h_normalized
    linarith

  have h_strip_left :
      stripLeftEndpointInMillimeters experiment = (399 : ℝ) / 200 := by
    rw [stripLeftEndpointInMillimeters,
      h_problem.stripCenterInMillimeters,
      h_problem.stripWidthInMillimeters]
    norm_num
  have h_strip_right :
      stripRightEndpointInMillimeters experiment = (401 : ℝ) / 200 := by
    rw [stripRightEndpointInMillimeters,
      h_problem.stripCenterInMillimeters,
      h_problem.stripWidthInMillimeters]
    norm_num

  have h_strip_branch :
      (∫ x in (399 : ℝ) / 200..(401 : ℝ) / 200, density x) =
        ∫ x in (399 : ℝ) / 200..(401 : ℝ) / 200,
          peakDensity * (3 - x) / (3 - 0) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : (399 : ℝ) / 200 ≤ x ∧ x ≤ (401 : ℝ) / 200 := by
      simpa only [Set.uIcc_of_le
        (show (399 : ℝ) / 200 ≤ (401 : ℝ) / 200 by norm_num),
        Set.mem_Icc] using hx
    have h_inside : ¬ (x < (-3 : ℝ) ∨ 3 < x) := by
      intro h
      rcases h with h | h
      · linarith [hx'.1]
      · linarith [hx'.2]
    rw [h_density_shape x]
    rw [if_neg h_inside]
    rw [if_neg (not_le.mpr (by linarith [hx'.1]))]

  have h_strip_affine_integral :
      (∫ x in (399 : ℝ) / 200..(401 : ℝ) / 200,
          peakDensity * (3 - x) / (3 - 0)) =
        peakDensity / 300 := by
    let f : ℝ → ℝ := fun x => peakDensity * (3 - x) / (3 - 0)
    have hf :
        IntervalIntegrable f MeasureTheory.volume
          ((399 : ℝ) / 200) ((401 : ℝ) / 200) := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hreflected :
        IntervalIntegrable (fun x => f (4 - x)) MeasureTheory.volume
          ((399 : ℝ) / 200) ((401 : ℝ) / 200) := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hreflection :
        (∫ x in (399 : ℝ) / 200..(401 : ℝ) / 200, f (4 - x)) =
          ∫ x in (399 : ℝ) / 200..(401 : ℝ) / 200, f x := by
      rw [intervalIntegral.integral_comp_sub_left]
      norm_num
    change
      (∫ x in (399 : ℝ) / 200..(401 : ℝ) / 200, f x) =
        peakDensity / 300
    calc
      (∫ x in (399 : ℝ) / 200..(401 : ℝ) / 200, f x) =
          (1 / 2 : ℝ) *
            ((∫ x in (399 : ℝ) / 200..(401 : ℝ) / 200, f x) +
              ∫ x in (399 : ℝ) / 200..(401 : ℝ) / 200, f (4 - x)) := by
                rw [hreflection]
                ring
      _ = (1 / 2 : ℝ) *
          (∫ x in (399 : ℝ) / 200..(401 : ℝ) / 200,
            (f x + f (4 - x))) := by
              rw [intervalIntegral.integral_add hf hreflected]
      _ = (1 / 2 : ℝ) *
          (∫ _x in (399 : ℝ) / 200..(401 : ℝ) / 200,
            2 * peakDensity / 3) := by
              congr 1
              apply intervalIntegral.integral_congr
              intro x hx
              dsimp [f]
              ring
      _ = peakDensity / 300 := by
            rw [intervalIntegral.integral_const]
            norm_num
            ring

  have h_expected_count :
      experiment.expectedElectronCount = (10000 : ℝ) / 9 := by
    rw [h_expectation.expectedCountLaw, h_problem.electronCount,
      h_strip_left, h_strip_right, h_strip_branch,
      h_strip_affine_integral, h_peak_density]
    norm_num

  constructor
  · exact h_expected_count
  · intro otherChoice h_other
    rw [h_expected_count]
    cases otherChoice with
    | A => norm_num [displayedExpectedElectronCount]
    | B => exact (h_other rfl).elim
    | C => norm_num [displayedExpectedElectronCount]
    | D => norm_num [displayedExpectedElectronCount]

end PhyXMiniProblems.ProblemPhyXMini0645
