import Mathlib
import Physlib.Units.WithDim.Speed

/-!
# RMS molecular speed from a histogram

This file models problem `phyx_mini_0378`.  The primary figure is a histogram
of the speeds of the molecules in a very small gas.  Its horizontal axis is
`v (m/s)`, its vertical axis is the molecule count `N`, and its four bars have
speed/count pairs `(2, 2)`, `(4, 4)`, `(6, 3)`, and `(8, 1)`.

Speeds are represented by Physlib's unit-independent `DimSpeed`.  Real numbers
are used only for coherent named-unit readouts and the displayed numerical
answer values; bar heights are natural-number molecule counts.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0378

/-! ## Dimensionful speeds and named-unit readouts -/

/-- A nonnegative physical molecular speed, independent of unit choice. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical speed in the selected length unit per selected time unit. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- The metres-per-second readout used on the histogram's horizontal axis. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-! ## Primary-figure labels and bars -/

/-- The two coordinate axes drawn in the supplied histogram. -/
inductive HistogramAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical/statistical quantity denoted by each printed axis label. -/
inductive HistogramAxisQuantity where
  | molecularSpeedV
  | moleculeCountN
  deriving DecidableEq, Repr

/-- The four speed locations at which the supplied figure displays bars. -/
inductive SpeedBin where
  | atTwo
  | atFour
  | atSix
  | atEight
  deriving DecidableEq, Fintype, Repr

/-- The visible fill shade of each bar in the primary bitmap. -/
inductive BarShade where
  | gray
  deriving DecidableEq, Repr

/-!
The independently represented labels, unit choices, and bar data of the
histogram.  The fields do not build in any RMS calculation or answer choice.
-/
structure MolecularSpeedHistogram where
  axisQuantity : HistogramAxis → HistogramAxisQuantity
  speedLengthUnit : LengthUnit
  speedTimeUnit : TimeUnit
  verticalTickMinimum : ℕ
  verticalTickMaximum : ℕ
  numberOfBars : ℕ
  speedAtBin : SpeedBin → SpeedQuantity
  moleculeCountAtBin : SpeedBin → ℕ
  barShown : SpeedBin → Bool
  barShade : SpeedBin → BarShade
  barsEvenlySpaced : Bool

/-- The qualitative size description used in the problem statement. -/
inductive GasSampleSize where
  | verySmall
  deriving DecidableEq, Repr

/-!
The physical gas sample and the RMS-speed observable to be calculated.
`totalMoleculeCount` and `rmsSpeed` are independent fields; the governing laws
below, rather than these field declarations, relate them to the histogram.
-/
structure MolecularGasSample where
  sampleSize : GasSampleSize
  histogram : MolecularSpeedHistogram
  totalMoleculeCount : ℕ
  rmsSpeed : SpeedQuantity

/-!
Qualitative scenario information and calibrated numerical evidence read from
the primary bitmap.  In particular, the bar heights are molecule counts, not
probability weights or continuous density values.
-/
structure MatchesPrimaryMolecularSpeedHistogram
    (sample : MolecularGasSample) : Prop where
  sampleIsVerySmall : sample.sampleSize = .verySmall
  horizontalAxisLabel :
    sample.histogram.axisQuantity .horizontal = .molecularSpeedV
  verticalAxisLabel :
    sample.histogram.axisQuantity .vertical = .moleculeCountN
  speedAxisLengthUnit :
    sample.histogram.speedLengthUnit = LengthUnit.meters
  speedAxisTimeUnit :
    sample.histogram.speedTimeUnit = TimeUnit.seconds
  verticalAxisStartsAtZero : sample.histogram.verticalTickMinimum = 0
  verticalAxisEndsAtFour : sample.histogram.verticalTickMaximum = 4
  fourBars : sample.histogram.numberOfBars = 4
  allBarsShown : ∀ bin, sample.histogram.barShown bin = true
  allBarsGray : ∀ bin, sample.histogram.barShade bin = .gray
  barsAreEvenlySpaced : sample.histogram.barsEvenlySpaced = true
  speedAtTwoMetersPerSecond :
    speedInMetersPerSecond (sample.histogram.speedAtBin .atTwo) = 2
  speedAtFourMetersPerSecond :
    speedInMetersPerSecond (sample.histogram.speedAtBin .atFour) = 4
  speedAtSixMetersPerSecond :
    speedInMetersPerSecond (sample.histogram.speedAtBin .atSix) = 6
  speedAtEightMetersPerSecond :
    speedInMetersPerSecond (sample.histogram.speedAtBin .atEight) = 8
  countAtTwoMetersPerSecond :
    sample.histogram.moleculeCountAtBin .atTwo = 2
  countAtFourMetersPerSecond :
    sample.histogram.moleculeCountAtBin .atFour = 4
  countAtSixMetersPerSecond :
    sample.histogram.moleculeCountAtBin .atSix = 3
  countAtEightMetersPerSecond :
    sample.histogram.moleculeCountAtBin .atEight = 1

/-! ## Governing finite-sample RMS law -/

/-!
For a finite molecular sample, the total count is the sum of the histogram
bar heights and the RMS speed is the square root of the count-weighted mean of
the squared speeds.  The law is stated in every coherent choice of length and
time units and contains no numerical result or displayed answer choice.
-/
structure SatisfiesDiscreteMolecularRmsLaw
    (sample : MolecularGasSample) : Prop where
  totalCountFromHistogram :
    sample.totalMoleculeCount =
      ∑ bin : SpeedBin, sample.histogram.moleculeCountAtBin bin
  rmsSpeedLaw :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit sample.rmsSpeed =
        Real.sqrt
          ((∑ bin : SpeedBin,
              (sample.histogram.moleculeCountAtBin bin : ℝ) *
                (speedReadout lengthUnit timeUnit
                  (sample.histogram.speedAtBin bin)) ^ 2) /
            (sample.totalMoleculeCount : ℝ))

/-!
The histogram must contain at least one molecule so that the mean-square
denominator has its intended physical meaning.
-/
structure HasNonemptyMolecularSample
    (sample : MolecularGasSample) : Prop where
  positiveTotalMoleculeCount : 0 < sample.totalMoleculeCount

/-! ## Displayed choices and target -/

/-- Labels of the four alternatives printed with the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Metres-per-second value printed beside each answer label. -/
def AnswerChoice.metersPerSecond : AnswerChoice → ℝ
  | .A => 49 / 10
  | .B => 25 / 2
  | .C => 91 / 5
  | .D => 51 / 5

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-!
A computed speed matches a one-decimal-place displayed choice when its SI
readout is within half of `0.1 m/s` of the printed value.
-/
def MatchesDisplayedChoice
    (speed : SpeedQuantity) (choice : AnswerChoice) : Prop :=
  |speedInMetersPerSecond speed - choice.metersPerSecond| < (1 : ℝ) / 20

/-!
The four histogram bars contain ten molecules and give mean square speed
`244 / 10 = 122 / 5 (m/s)^2`.  Thus the RMS speed is exactly
`sqrt (122 / 5) m/s`, approximately `4.9 m/s`, and matches recorded choice A.

This formalizes `thm:physics:phyx_mini_0378:target`.
-/
theorem rmsSpeed_matches_recordedAnswerA
    (sample : MolecularGasSample)
    (hFigure : MatchesPrimaryMolecularSpeedHistogram sample)
    (hNonempty : HasNonemptyMolecularSample sample)
    (hRms : SatisfiesDiscreteMolecularRmsLaw sample) :
    speedInMetersPerSecond sample.rmsSpeed = Real.sqrt (122 / 5) ∧
      MatchesDisplayedChoice sample.rmsSpeed recordedDatasetAnswer := by
  classical
  have hBins : (Finset.univ : Finset SpeedBin) =
      {.atTwo, .atFour, .atSix, .atEight} := by decide
  have hTotal : sample.totalMoleculeCount = 10 := by
    rw [hRms.totalCountFromHistogram, hBins]
    simp [hFigure.countAtTwoMetersPerSecond,
      hFigure.countAtFourMetersPerSecond,
      hFigure.countAtSixMetersPerSecond,
      hFigure.countAtEightMetersPerSecond]
  have hWeighted :
      (∑ bin : SpeedBin,
          (sample.histogram.moleculeCountAtBin bin : ℝ) *
            (speedInMetersPerSecond (sample.histogram.speedAtBin bin)) ^ 2) = 244 := by
    rw [hBins]
    simp [hFigure.countAtTwoMetersPerSecond,
      hFigure.countAtFourMetersPerSecond,
      hFigure.countAtSixMetersPerSecond,
      hFigure.countAtEightMetersPerSecond,
      hFigure.speedAtTwoMetersPerSecond,
      hFigure.speedAtFourMetersPerSecond,
      hFigure.speedAtSixMetersPerSecond,
      hFigure.speedAtEightMetersPerSecond]
    norm_num
  have hTotalPositive : (0 : ℝ) < sample.totalMoleculeCount := by
    exact_mod_cast hNonempty.positiveTotalMoleculeCount
  have hRadicand :
      (∑ bin : SpeedBin,
          (sample.histogram.moleculeCountAtBin bin : ℝ) *
            (speedInMetersPerSecond (sample.histogram.speedAtBin bin)) ^ 2) /
          (sample.totalMoleculeCount : ℝ) = 122 / 5 := by
    rw [hWeighted]
    apply (div_eq_iff (ne_of_gt hTotalPositive)).2
    rw [hTotal]
    norm_num
  have hSpeed := hRms.rmsSpeedLaw LengthUnit.meters TimeUnit.seconds
  change speedInMetersPerSecond sample.rmsSpeed =
    Real.sqrt
      ((∑ bin : SpeedBin,
          (sample.histogram.moleculeCountAtBin bin : ℝ) *
            (speedInMetersPerSecond (sample.histogram.speedAtBin bin)) ^ 2) /
        (sample.totalMoleculeCount : ℝ)) at hSpeed
  rw [hRadicand] at hSpeed
  refine ⟨hSpeed, ?_⟩
  unfold MatchesDisplayedChoice recordedDatasetAnswer AnswerChoice.metersPerSecond
  rw [hSpeed, abs_lt]
  constructor <;>
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 122 / 5 by norm_num),
      Real.sqrt_nonneg (122 / 5)]

end PhyXMiniProblems.ProblemPhyXMini0378
