import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Expected electron count from a position-probability-density graph

The supplied graph is a symmetric triangular position density. Its horizontal
axis is a signed position in millimetres, while its vertical axis has units of
inverse millimetres and is labelled `P(x) = |ψ(x)|²`. One million electrons
pass through the apparatus, and the question asks for the expected count in a
`0.010 mm` strip centred at `x = 2.000 mm`.

Signed positions, nonnegative strip widths, and probability densities retain
their physical dimensions through Physlib. Real numbers occur only as named
unit readouts, wave-amplitude components in a named unit convention, and
dimensionless expected counts.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0501

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
  | .A => 2200
  | .B => 1000
  | .C => 1100
  | .D => 3500

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
`1100`, answer C.

This formalizes `thm:physics:phyx_mini_0501:target`.
-/
theorem expected_electron_count_and_recorded_answer_C
    (experiment : ElectronStripExperiment)
    (h_scenario : MatchesElectronExperimentScenario experiment)
    (h_problem : MatchesProblemReadouts experiment)
    (h_figure : MatchesSuppliedPositionDensityFigure experiment.figure)
    (h_triangle : FigurePlotsTriangularPositionDensity experiment)
    (h_probability : SatisfiesPositionProbabilityLaws experiment)
    (h_expectation : SatisfiesExpectedStripCountLaw experiment) :
    experiment.expectedElectronCount = (10000 : ℝ) / 9 ∧
      IsUniqueClosestDisplayedCount experiment .C := by
  let density : ℝ → ℝ :=
    densityAtMillimeterCoordinate experiment.positionState
  let peakDensity : ℝ := density 0
  have h_density (x : ℝ) :
      density x =
        if x < -3 ∨ 3 < x then
          0
        else if x ≤ 0 then
          peakDensity * (x - (-3)) / (0 - (-3))
        else
          peakDensity * (3 - x) / (3 - 0) := by
    dsimp [density, peakDensity]
    simpa [h_figure.leftInterceptInMillimeters,
      h_figure.peakPositionInMillimeters,
      h_figure.rightInterceptInMillimeters] using
      h_triangle.triangularInterpolation x
  have h_integral_id (a b : ℝ) :
      (∫ x : ℝ in a..b, x) = (b ^ 2 - a ^ 2) / 2 := by
    have h_reflection := intervalIntegral.integral_comp_sub_left
      (a := a) (b := b) (fun x : ℝ => x) (a + b)
    have h_const :
        (∫ _x : ℝ in a..b, a + b) = (b - a) * (a + b) := by
      rw [intervalIntegral.integral_const]
      simp
    have h_linear :
        (∫ x : ℝ in a..b, (a + b) - x) =
          (b - a) * (a + b) - ∫ x : ℝ in a..b, x := by
      calc
        (∫ x : ℝ in a..b, (a + b) - x) =
            (∫ _x : ℝ in a..b, a + b) -
              ∫ x : ℝ in a..b, x := by
                exact intervalIntegral.integral_sub
                  (continuous_const.intervalIntegrable _ _)
                  (continuous_id.intervalIntegrable _ _)
        _ = _ := by rw [h_const]
    rw [h_linear] at h_reflection
    norm_num at h_reflection ⊢
    nlinarith
  have h_density_integrable :
      IntervalIntegrable density MeasureTheory.volume (-3) 3 := by
    simpa [density, h_figure.leftInterceptInMillimeters,
      h_figure.rightInterceptInMillimeters] using
      h_probability.densityIntervalIntegrable
  have h_density_integrable_left :
      IntervalIntegrable density MeasureTheory.volume (-3) 0 :=
    h_density_integrable.mono_set
      (Set.uIcc_subset_uIcc (by norm_num) (by norm_num))
  have h_density_integrable_right :
      IntervalIntegrable density MeasureTheory.volume 0 3 :=
    h_density_integrable.mono_set
      (Set.uIcc_subset_uIcc (by norm_num) (by norm_num))
  have h_left_integral :
      (∫ x : ℝ in (-3)..0, density x) = 3 * peakDensity / 2 := by
    calc
      (∫ x : ℝ in (-3)..0, density x) =
          ∫ x : ℝ in (-3)..0, peakDensity * (x - (-3)) / (0 - (-3)) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [h_density]
            have hx' : x ∈ Set.Icc (-3 : ℝ) 0 := by
              simpa [Set.uIcc_of_le (by norm_num : (-3 : ℝ) ≤ 0)] using hx
            rcases hx' with ⟨hx_lower, hx_upper⟩
            have h_not_left : ¬x < -3 := not_lt.mpr hx_lower
            have h_not_right : ¬3 < x := by linarith
            simp [h_not_left, h_not_right, hx_upper]
      _ = 3 * peakDensity / 2 := by
        have h_function :
            (fun x : ℝ => peakDensity * (x - (-3)) / (0 - (-3))) =
              fun x : ℝ => (peakDensity / 3) * x + peakDensity := by
          funext x
          ring
        rw [h_function]
        calc
          (∫ x : ℝ in (-3)..0, (peakDensity / 3) * x + peakDensity) =
              (∫ x : ℝ in (-3)..0, (peakDensity / 3) * x) +
                ∫ _x : ℝ in (-3)..0, peakDensity := by
                  exact intervalIntegral.integral_add
                    (f := fun x : ℝ => (peakDensity / 3) * x)
                    (g := fun _x : ℝ => peakDensity)
                    ((continuous_const.mul continuous_id).intervalIntegrable _ _)
                    (continuous_const.intervalIntegrable _ _)
          _ = 3 * peakDensity / 2 := by
            rw [intervalIntegral.integral_const_mul,
              intervalIntegral.integral_const, h_integral_id]
            ring
  have h_right_integral :
      (∫ x : ℝ in 0..3, density x) = 3 * peakDensity / 2 := by
    calc
      (∫ x : ℝ in 0..3, density x) =
          ∫ x : ℝ in 0..3, peakDensity * (3 - x) / (3 - 0) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [h_density]
            have hx' : x ∈ Set.Icc (0 : ℝ) 3 := by
              simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3)] using hx
            rcases hx' with ⟨hx_lower, hx_upper⟩
            have h_not_left : ¬x < -3 := by linarith
            have h_not_right : ¬3 < x := not_lt.mpr hx_upper
            by_cases hx_zero : x ≤ 0
            · have hx_eq : x = 0 := by linarith
              subst x
              norm_num
            · simp [h_not_left, h_not_right, hx_zero]
      _ = 3 * peakDensity / 2 := by
        have h_function :
            (fun x : ℝ => peakDensity * (3 - x) / (3 - 0)) =
              fun x : ℝ => peakDensity - (peakDensity / 3) * x := by
          funext x
          ring
        rw [h_function]
        calc
          (∫ x : ℝ in 0..3, peakDensity - (peakDensity / 3) * x) =
              (∫ _x : ℝ in 0..3, peakDensity) -
                ∫ x : ℝ in 0..3, (peakDensity / 3) * x := by
                  exact intervalIntegral.integral_sub
                    (f := fun _x : ℝ => peakDensity)
                    (g := fun x : ℝ => (peakDensity / 3) * x)
                    (continuous_const.intervalIntegrable _ _)
                    ((continuous_const.mul continuous_id).intervalIntegrable _ _)
          _ = 3 * peakDensity / 2 := by
            rw [intervalIntegral.integral_const,
              intervalIntegral.integral_const_mul, h_integral_id]
            ring
  have h_normalized :
      (∫ x : ℝ in (-3)..3, density x) = 1 := by
    simpa [density, h_figure.leftInterceptInMillimeters,
      h_figure.rightInterceptInMillimeters] using
      h_probability.normalizedPositionDensity
  have h_peak_density : peakDensity = (1 : ℝ) / 3 := by
    have h_split := intervalIntegral.integral_add_adjacent_intervals
      h_density_integrable_left h_density_integrable_right
    rw [h_left_integral, h_right_integral, h_normalized] at h_split
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
  have h_strip_integral :
      (∫ x : ℝ in
          stripLeftEndpointInMillimeters experiment..
            stripRightEndpointInMillimeters experiment,
          density x) = (1 : ℝ) / 900 := by
    rw [h_strip_left, h_strip_right]
    calc
      (∫ x : ℝ in (399 : ℝ) / 200..(401 : ℝ) / 200, density x) =
          ∫ x : ℝ in (399 : ℝ) / 200..(401 : ℝ) / 200,
            peakDensity * (3 - x) / (3 - 0) := by
              apply intervalIntegral.integral_congr
              intro x hx
              rw [h_density]
              have hx' : x ∈ Set.Icc ((399 : ℝ) / 200) (401 / 200) := by
                simpa [Set.uIcc_of_le
                  (by norm_num : (399 : ℝ) / 200 ≤ 401 / 200)] using hx
              rcases hx' with ⟨hx_lower, hx_upper⟩
              have h_not_left : ¬x < -3 := by linarith
              have h_not_right : ¬3 < x := by linarith
              have h_not_zero : ¬x ≤ 0 := by linarith
              simp [h_not_left, h_not_right, h_not_zero]
      _ = (1 : ℝ) / 900 := by
        have h_function :
            (fun x : ℝ => peakDensity * (3 - x) / (3 - 0)) =
              fun x : ℝ => peakDensity - (peakDensity / 3) * x := by
          funext x
          ring
        rw [h_function]
        calc
          (∫ x : ℝ in (399 : ℝ) / 200..(401 : ℝ) / 200,
              peakDensity - (peakDensity / 3) * x) =
              (∫ _x : ℝ in (399 : ℝ) / 200..(401 : ℝ) / 200,
                peakDensity) -
                ∫ x : ℝ in (399 : ℝ) / 200..(401 : ℝ) / 200,
                  (peakDensity / 3) * x := by
                    exact intervalIntegral.integral_sub
                      (f := fun _x : ℝ => peakDensity)
                      (g := fun x : ℝ => (peakDensity / 3) * x)
                      (continuous_const.intervalIntegrable _ _)
                      ((continuous_const.mul continuous_id).intervalIntegrable _ _)
          _ = (1 : ℝ) / 900 := by
            rw [intervalIntegral.integral_const,
              intervalIntegral.integral_const_mul, h_integral_id,
              h_peak_density]
            norm_num
  have h_expected_count :
      experiment.expectedElectronCount = (10000 : ℝ) / 9 := by
    calc
      experiment.expectedElectronCount =
          (experiment.electronsUsed : ℝ) *
            ∫ x : ℝ in
                stripLeftEndpointInMillimeters experiment..
                  stripRightEndpointInMillimeters experiment,
              density x := by
                simpa [density] using h_expectation.expectedCountLaw
      _ = (10000 : ℝ) / 9 := by
        rw [h_problem.electronCount, h_strip_integral]
        norm_num
  refine ⟨h_expected_count, ?_⟩
  intro otherChoice h_other
  rw [h_expected_count]
  fin_cases otherChoice
  all_goals simp_all [displayedExpectedElectronCount] <;> norm_num

end PhyXMiniProblems.ProblemPhyXMini0501
