import Mathlib
import Physlib.QuantumMechanics.HilbertSpaces.OneDimension.Basic
import Physlib.SpaceAndTime.Space.LengthUnit

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

open MeasureTheory

namespace PhyXMiniProblems.ProblemPhyXMini0652

/-!
# Position probability for a linearly varying confined wavefunction

The supplied figure plots a real representative of a particle's complex
one-dimensional wavefunction.  The horizontal coordinate is the numerical
position readout in millimetres.  Accordingly,
`waveAmplitudePerSqrtMillimeter x` is the complex amplitude readout in inverse
square-root millimetres, and its squared norm is a density readout in inverse
millimetres.

The actual position probability is retained as a normalized Mathlib
`ProbabilityMeasure`.  The Born rule below relates this physical probability
to the plotted wavefunction; it is not defined from the recorded answer.
-/

/-! ## Primary-figure vocabulary -/

/-- Labels printed on the axes and vertical scale of the supplied figure. -/
inductive WaveFunctionFigureLabel where
  | psiOfX
  | positionX
  | positiveC
  | negativeC
  deriving DecidableEq, Fintype, Repr

/-- The five labelled horizontal-axis ticks visible in the figure. -/
inductive HorizontalTick where
  | negativeFour
  | negativeTwo
  | zero
  | positiveTwo
  | positiveFour
  deriving DecidableEq, Fintype, Repr

/-!
Raw quantitative and qualitative evidence transcribed from `652.png`.

The plotted amplitude is a real readout of the complex wavefunction.  This
structure stores no interval probability and no answer-choice value.
-/
structure SuppliedWaveFunctionFigure where
  horizontalAxisUnit : LengthUnit
  showsLabel : WaveFunctionFigureLabel → Bool
  coordinateAtTickMillimeters : HorizontalTick → ℝ
  plottedRealAmplitudePerSqrtMillimeter : ℝ → ℝ
  curveIsSingleStraightSegmentInside : Bool
  curvePassesThroughOrigin : Bool
  curveHasEndpointJumpsToZero : Bool
  curveIsRed : Bool

/-! ## Physical setup and observables -/

/-!
A particle confined to a one-dimensional interval, together with the
representative shown in the figure and its position probability observable.

All fields ending in `Millimeters` or `PerSqrtMillimeter` are calibrated
scalar readouts in the units printed or implied by the graph.  In particular,
the wavefunction itself is not replaced by a scalar physical quantity: it is
a complex function with the appropriate amplitude role.
-/
structure ConfinedParticlePositionSetup where
  waveAmplitudePerSqrtMillimeter : ℝ → ℂ
  positionProbability : ProbabilityMeasure ℝ
  leftConfinementMillimeters : ℝ
  rightConfinementMillimeters : ℝ
  queryLowerMillimeters : ℝ
  queryUpperMillimeters : ℝ
  amplitudeScaleCPerSqrtMillimeter : ℝ
  figure : SuppliedWaveFunctionFigure

/-- The Born position-density readout in inverse millimetres. -/
def positionDensityPerMillimeter
    (setup : ConfinedParticlePositionSetup) (xMillimeters : ℝ) : ℝ :=
  Complex.normSq (setup.waveAmplitudePerSqrtMillimeter xMillimeters)

/-- The closed position interval whose probability is requested. -/
def requestedPositionRegion
    (setup : ConfinedParticlePositionSetup) : Set ℝ :=
  Set.Icc setup.queryLowerMillimeters setup.queryUpperMillimeters

/-- The dimensionless probability of the requested position event. -/
def requestedPositionProbability
    (setup : ConfinedParticlePositionSetup) : ℝ :=
  (((setup.positionProbability : Measure ℝ)
      (requestedPositionRegion setup)).toReal)

/-! ## Scenario facts, figure readouts, and governing laws -/

/-!
Numerical data stated in the problem text, including confinement to
`[-4 mm, 4 mm]`, the query interval `[-2 mm, 2 mm]`, and vanishing amplitude
outside the confinement region.  No probability value occurs here.
-/
structure MatchesConfinedParticleScenario
    (setup : ConfinedParticlePositionSetup) : Prop where
  leftConfinementIsNegativeFour :
    setup.leftConfinementMillimeters = -4
  rightConfinementIsPositiveFour :
    setup.rightConfinementMillimeters = 4
  queryLowerIsNegativeTwo :
    setup.queryLowerMillimeters = -2
  queryUpperIsPositiveTwo :
    setup.queryUpperMillimeters = 2
  waveFunctionVanishesOutside : ∀ xMillimeters : ℝ,
    xMillimeters < setup.leftConfinementMillimeters ∨
        setup.rightConfinementMillimeters < xMillimeters →
      setup.waveAmplitudePerSqrtMillimeter xMillimeters = 0

/-!
Exact labels, tick locations, and line profile read from the supplied raster.
The interior profile is the straight line

`ψ(x) = c x / (4 mm)`

in millimetre-coordinate readouts.  It is a figure/model premise and contains
neither the integral over the queried interval nor its numerical value.
-/
structure MatchesSuppliedWaveFunctionFigure
    (setup : ConfinedParticlePositionSetup) : Prop where
  horizontalAxisUsesMillimeters :
    setup.figure.horizontalAxisUnit = LengthUnit.millimeters
  everyPrintedLabelIsShown : ∀ label,
    setup.figure.showsLabel label = true
  tickNegativeFour :
    setup.figure.coordinateAtTickMillimeters .negativeFour = -4
  tickNegativeTwo :
    setup.figure.coordinateAtTickMillimeters .negativeTwo = -2
  tickZero :
    setup.figure.coordinateAtTickMillimeters .zero = 0
  tickPositiveTwo :
    setup.figure.coordinateAtTickMillimeters .positiveTwo = 2
  tickPositiveFour :
    setup.figure.coordinateAtTickMillimeters .positiveFour = 4
  graphRepresentsWaveFunction : ∀ xMillimeters : ℝ,
    setup.waveAmplitudePerSqrtMillimeter xMillimeters =
      ((setup.figure.plottedRealAmplitudePerSqrtMillimeter xMillimeters : ℝ) : ℂ)
  straightLineInsideConfinement : ∀ xMillimeters : ℝ,
    setup.leftConfinementMillimeters ≤ xMillimeters →
    xMillimeters ≤ setup.rightConfinementMillimeters →
      setup.figure.plottedRealAmplitudePerSqrtMillimeter xMillimeters =
        setup.amplitudeScaleCPerSqrtMillimeter * xMillimeters /
          setup.rightConfinementMillimeters
  rightEndpointHasHeightC :
    setup.figure.plottedRealAmplitudePerSqrtMillimeter
        setup.rightConfinementMillimeters =
      setup.amplitudeScaleCPerSqrtMillimeter
  leftEndpointHasHeightNegativeC :
    setup.figure.plottedRealAmplitudePerSqrtMillimeter
        setup.leftConfinementMillimeters =
      -setup.amplitudeScaleCPerSqrtMillimeter
  singleStraightInteriorSegment :
    setup.figure.curveIsSingleStraightSegmentInside = true
  passesThroughOrigin : setup.figure.curvePassesThroughOrigin = true
  endpointJumpsToZero : setup.figure.curveHasEndpointJumpsToZero = true
  redCurve : setup.figure.curveIsRed = true

/-- Positivity and ordering conditions implicit in the physical setup. -/
structure HasPhysicalWaveFunctionParameters
    (setup : ConfinedParticlePositionSetup) : Prop where
  positiveAmplitudeScale :
    0 < setup.amplitudeScaleCPerSqrtMillimeter
  orderedConfinement :
    setup.leftConfinementMillimeters < setup.rightConfinementMillimeters
  orderedQuery :
    setup.queryLowerMillimeters ≤ setup.queryUpperMillimeters
  queryLiesInsideConfinement :
    setup.leftConfinementMillimeters ≤ setup.queryLowerMillimeters ∧
      setup.queryUpperMillimeters ≤ setup.rightConfinementMillimeters

/-!
The normalized one-dimensional Born rule.

`MemHS` is Physlib's membership predicate for the one-dimensional `L²`
Hilbert space.  The probability equation is stated for every measurable event,
so it is a governing law rather than the numerical result for the particular
interval in this problem.
-/
structure SatisfiesNormalizedBornPositionLaw
    (setup : ConfinedParticlePositionSetup) : Prop where
  representativeIsSquareIntegrable :
    QuantumMechanics.OneDimension.HilbertSpace.MemHS
      setup.waveAmplitudePerSqrtMillimeter
  densityIsIntegrable : Integrable (positionDensityPerMillimeter setup)
  waveFunctionIsNormalized :
    (∫ xMillimeters : ℝ, positionDensityPerMillimeter setup xMillimeters) = 1
  probabilityOfMeasurableEvent : ∀ event : Set ℝ, MeasurableSet event →
    (((setup.positionProbability : Measure ℝ) event).toReal) =
      ∫ xMillimeters in event,
        positionDensityPerMillimeter setup xMillimeters

/-! ## Displayed choices and formal target -/

/-- Labels of the four probability choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The dimensionless probability displayed beside each answer label. -/
def displayedProbability : AnswerChoice → ℝ
  | .A => 2 / 25
  | .B => 1 / 10
  | .C => 1 / 8
  | .D => 1 / 4

/-- The answer label recorded by the supplied dataset; it is never a premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A choice matches when its displayed value is the modeled event probability. -/
def MatchesDisplayedProbability
    (setup : ConfinedParticlePositionSetup)
    (choice : AnswerChoice) : Prop :=
  requestedPositionProbability setup = displayedProbability choice

/-- A choice is the unique displayed value matching the modeled probability. -/
def IsUniqueMatchingDisplayedProbability
    (setup : ConfinedParticlePositionSetup)
    (choice : AnswerChoice) : Prop :=
  MatchesDisplayedProbability setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedProbability setup other → other = choice

/-!
Integrating the squared linear wavefunction over `[-2 mm, 2 mm]` and using
normalization over `[-4 mm, 4 mm]` gives the exact probability `1/8`.
This is a derived result, not a premise.
-/
lemma centralIntervalProbability_eq_oneEighth
    (setup : ConfinedParticlePositionSetup)
    (hScenario : MatchesConfinedParticleScenario setup)
    (hFigure : MatchesSuppliedWaveFunctionFigure setup)
    (hPhysical : HasPhysicalWaveFunctionParameters setup)
    (hBorn : SatisfiesNormalizedBornPositionLaw setup) :
    requestedPositionProbability setup = (1 : ℝ) / 8 := by
  have hDensityInside (xMillimeters : ℝ)
      (hLeft : setup.leftConfinementMillimeters ≤ xMillimeters)
      (hRight : xMillimeters ≤ setup.rightConfinementMillimeters) :
      positionDensityPerMillimeter setup xMillimeters =
        setup.amplitudeScaleCPerSqrtMillimeter ^ 2 *
          xMillimeters ^ 2 / 16 := by
    rw [positionDensityPerMillimeter,
      hFigure.graphRepresentsWaveFunction xMillimeters,
      hFigure.straightLineInsideConfinement xMillimeters hLeft hRight,
      Complex.normSq_ofReal, hScenario.rightConfinementIsPositiveFour]
    ring
  have hDensityOutside (xMillimeters : ℝ)
      (hOutside :
        xMillimeters < setup.leftConfinementMillimeters ∨
          setup.rightConfinementMillimeters < xMillimeters) :
      positionDensityPerMillimeter setup xMillimeters = 0 := by
    rw [positionDensityPerMillimeter,
      hScenario.waveFunctionVanishesOutside xMillimeters hOutside]
    exact Complex.normSq_zero
  have hDensity (xMillimeters : ℝ) :
      positionDensityPerMillimeter setup xMillimeters =
        (Set.Icc setup.leftConfinementMillimeters
          setup.rightConfinementMillimeters).indicator
          (fun x : ℝ =>
            setup.amplitudeScaleCPerSqrtMillimeter ^ 2 * x ^ 2 / 16)
          xMillimeters := by
    by_cases hx : xMillimeters ∈
        Set.Icc setup.leftConfinementMillimeters
          setup.rightConfinementMillimeters
    · rw [Set.indicator_of_mem hx]
      exact hDensityInside xMillimeters hx.1 hx.2
    · rw [Set.indicator_of_notMem hx]
      apply hDensityOutside xMillimeters
      rw [Set.mem_Icc] at hx
      by_cases hLeftOutside :
          xMillimeters < setup.leftConfinementMillimeters
      · exact Or.inl hLeftOutside
      · right
        have hLeft :
            setup.leftConfinementMillimeters ≤ xMillimeters :=
          le_of_not_gt hLeftOutside
        exact lt_of_not_ge fun hRight => hx ⟨hLeft, hRight⟩
  have hRampNormalization :
      intervalIntegral
        (fun x : ℝ =>
          setup.amplitudeScaleCPerSqrtMillimeter ^ 2 * x ^ 2 / 16)
        setup.leftConfinementMillimeters
        setup.rightConfinementMillimeters volume = 1 := by
    calc
      intervalIntegral
          (fun x : ℝ =>
            setup.amplitudeScaleCPerSqrtMillimeter ^ 2 * x ^ 2 / 16)
          setup.leftConfinementMillimeters
          setup.rightConfinementMillimeters volume =
          ∫ x : ℝ in
              Set.Icc setup.leftConfinementMillimeters
                setup.rightConfinementMillimeters,
            setup.amplitudeScaleCPerSqrtMillimeter ^ 2 * x ^ 2 / 16 := by
              rw [intervalIntegral.integral_of_le
                (le_of_lt hPhysical.orderedConfinement),
                ← MeasureTheory.integral_Icc_eq_integral_Ioc]
      _ = ∫ x : ℝ,
          (Set.Icc setup.leftConfinementMillimeters
            setup.rightConfinementMillimeters).indicator
            (fun y : ℝ =>
              setup.amplitudeScaleCPerSqrtMillimeter ^ 2 *
                y ^ 2 / 16) x :=
        (MeasureTheory.integral_indicator measurableSet_Icc).symm
      _ = ∫ x : ℝ, positionDensityPerMillimeter setup x := by
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall fun x => (hDensity x).symm
      _ = 1 := hBorn.waveFunctionIsNormalized
  have hRampIntegral :
      intervalIntegral
        (fun x : ℝ =>
          setup.amplitudeScaleCPerSqrtMillimeter ^ 2 * x ^ 2 / 16)
        setup.leftConfinementMillimeters
        setup.rightConfinementMillimeters volume =
          (8 / 3 : ℝ) *
            setup.amplitudeScaleCPerSqrtMillimeter ^ 2 := by
    calc
      intervalIntegral
          (fun x : ℝ =>
            setup.amplitudeScaleCPerSqrtMillimeter ^ 2 * x ^ 2 / 16)
          setup.leftConfinementMillimeters
          setup.rightConfinementMillimeters volume =
          intervalIntegral
            (fun x : ℝ =>
              (setup.amplitudeScaleCPerSqrtMillimeter ^ 2 / 16) *
                x ^ 2)
            setup.leftConfinementMillimeters
            setup.rightConfinementMillimeters volume := by
              apply intervalIntegral.integral_congr
              intro x _
              ring
      _ = (setup.amplitudeScaleCPerSqrtMillimeter ^ 2 / 16) *
          intervalIntegral (fun x : ℝ => x ^ 2)
            setup.leftConfinementMillimeters
            setup.rightConfinementMillimeters volume :=
        intervalIntegral.integral_const_mul _ _
      _ = (8 / 3 : ℝ) *
          setup.amplitudeScaleCPerSqrtMillimeter ^ 2 := by
        rw [integral_pow, hScenario.leftConfinementIsNegativeFour,
          hScenario.rightConfinementIsPositiveFour]
        norm_num
        ring
  have hcSq :
      setup.amplitudeScaleCPerSqrtMillimeter ^ 2 = (3 / 8 : ℝ) := by
    rw [hRampIntegral] at hRampNormalization
    linarith
  have hEventIntegral :
      requestedPositionProbability setup =
        ∫ x : ℝ in
            Set.Icc setup.queryLowerMillimeters setup.queryUpperMillimeters,
          positionDensityPerMillimeter setup x := by
    rw [requestedPositionProbability, requestedPositionRegion]
    exact hBorn.probabilityOfMeasurableEvent _ measurableSet_Icc
  calc
    requestedPositionProbability setup =
        ∫ x : ℝ in
            Set.Icc setup.queryLowerMillimeters setup.queryUpperMillimeters,
          positionDensityPerMillimeter setup x := hEventIntegral
    _ = ∫ x : ℝ in
          Set.Icc setup.queryLowerMillimeters setup.queryUpperMillimeters,
        setup.amplitudeScaleCPerSqrtMillimeter ^ 2 * x ^ 2 / 16 := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
          intro x hx
          apply hDensityInside x
          · exact le_trans
              hPhysical.queryLiesInsideConfinement.1 hx.1
          · exact le_trans hx.2
              hPhysical.queryLiesInsideConfinement.2
    _ = intervalIntegral
          (fun x : ℝ =>
            setup.amplitudeScaleCPerSqrtMillimeter ^ 2 * x ^ 2 / 16)
          setup.queryLowerMillimeters setup.queryUpperMillimeters volume := by
            rw [intervalIntegral.integral_of_le hPhysical.orderedQuery,
              ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ = intervalIntegral
          (fun x : ℝ =>
            (setup.amplitudeScaleCPerSqrtMillimeter ^ 2 / 16) * x ^ 2)
          setup.queryLowerMillimeters setup.queryUpperMillimeters volume := by
            apply intervalIntegral.integral_congr
            intro x _
            ring
    _ = (setup.amplitudeScaleCPerSqrtMillimeter ^ 2 / 16) *
        intervalIntegral (fun x : ℝ => x ^ 2)
          setup.queryLowerMillimeters setup.queryUpperMillimeters volume :=
      intervalIntegral.integral_const_mul _ _
    _ = (1 : ℝ) / 8 := by
      rw [hcSq, integral_pow, hScenario.queryLowerIsNegativeTwo,
        hScenario.queryUpperIsPositiveTwo]
      norm_num

/-!
The probability of finding the particle between `-2 mm` and `2 mm` is
`1/8 = 0.125`, and choice C is the unique displayed match.

This declaration formalizes blueprint label
`thm:physics:phyx_mini_0652:target`.
-/
theorem problem_phyx_mini_0652
    (setup : ConfinedParticlePositionSetup)
    (hScenario : MatchesConfinedParticleScenario setup)
    (hFigure : MatchesSuppliedWaveFunctionFigure setup)
    (hPhysical : HasPhysicalWaveFunctionParameters setup)
    (hBorn : SatisfiesNormalizedBornPositionLaw setup) :
    requestedPositionProbability setup = (1 : ℝ) / 8 ∧
      IsUniqueMatchingDisplayedProbability setup recordedDatasetAnswer := by
  have hProbability :
      requestedPositionProbability setup = (1 : ℝ) / 8 :=
    centralIntervalProbability_eq_oneEighth
      setup hScenario hFigure hPhysical hBorn
  refine ⟨hProbability, ?_⟩
  rw [recordedDatasetAnswer]
  refine ⟨?_, ?_⟩
  · simpa [MatchesDisplayedProbability, displayedProbability]
      using hProbability
  · intro other hOther
    cases other with
    | A =>
        norm_num [MatchesDisplayedProbability, displayedProbability,
          hProbability] at hOther
    | B =>
        norm_num [MatchesDisplayedProbability, displayedProbability,
          hProbability] at hOther
    | C => rfl
    | D =>
        norm_num [MatchesDisplayedProbability, displayedProbability,
          hProbability] at hOther

end PhyXMiniProblems.ProblemPhyXMini0652
