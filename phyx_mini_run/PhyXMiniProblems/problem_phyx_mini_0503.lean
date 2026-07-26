import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0503

open MeasureTheory

/-!
# Neutron position probability from a plotted wave-function density

The figure plots `|ψ(x)|²` for a neutron against a signed position coordinate
measured in femtometers.  The curve is a symmetric V: it vanishes at the
origin, rises linearly to the height labelled `a` at `x = ±4 fm`, and is zero
beyond those endpoints.  The question asks for the probability of
`|x| ≥ 2 fm`.

Real numbers below are explicitly scalar readouts in the units printed on the
figure.  The quantum state is retained as a complex wave-function amplitude
together with a normalized Mathlib probability measure.
-/

/-! ## Quantum state, coordinate unit, and figure vocabulary -/

/-- Particle species distinguished by the physical scenario. -/
inductive ParticleSpecies where
  | neutron
  | other
  deriving DecidableEq, Repr

/-- Literal labels printed on the supplied probability-density graph. -/
inductive FigureLabel where
  | waveFunctionDensity
  | positionInFemtometers
  | peakDensityA
  deriving DecidableEq, Fintype, Repr

/-- The five signed position-coordinate ticks visible on the horizontal axis. -/
inductive HorizontalTick where
  | negFour
  | negTwo
  | zero
  | two
  | four
  deriving DecidableEq, Fintype, Repr

/-- Independent data retained from the primary raster.

The plotted values have the dimensional role of inverse-femtometer density
readouts.  No event probability or answer choice is stored in the figure.
-/
structure SuppliedProbabilityDensityFigure where
  printedText : FigureLabel → String
  coordinateAtTick : HorizontalTick → ℝ
  plottedDensityReadout : ℝ → ℝ
  curveIsSymmetricAboutVerticalAxis : Bool
  curveIsLinearOnEachSideOfOrigin : Bool
  curveDropsVerticallyAtEndpoints : Bool

/-- A one-dimensional position model for the neutron.

The complex function is the pointwise wave-function amplitude in the selected
coordinate unit.  Its squared norm is a density readout, while
`positionProbability` is normalized by its `ProbabilityMeasure` type.
-/
structure OneDimensionalQuantumPositionSetup where
  particle : ParticleSpecies
  coordinateUnit : LengthUnit
  waveFunctionAmplitudeReadout : ℝ → ℂ
  positionProbability : ProbabilityMeasure ℝ
  supportHalfWidthCoordinate : ℝ
  queriedAbsoluteCoordinateCutoff : ℝ
  peakDensityReadout : ℝ
  figure : SuppliedProbabilityDensityFigure

/-- The probability-density readout `|ψ(x)|²` at a signed coordinate in the
selected length unit. -/
def positionDensityReadout
    (setup : OneDimensionalQuantumPositionSetup) (x : ℝ) : ℝ :=
  Complex.normSq (setup.waveFunctionAmplitudeReadout x)

/-- Positions whose absolute coordinate is at least the supplied cutoff. -/
def outsideCentralRegion (cutoffCoordinate : ℝ) : Set ℝ :=
  {x | cutoffCoordinate ≤ |x|}

/-- The event whose probability is requested in the problem. -/
def requestedPositionEvent
    (setup : OneDimensionalQuantumPositionSetup) : Set ℝ :=
  outsideCentralRegion setup.queriedAbsoluteCoordinateCutoff

/-- The requested dimensionless probability, expressed as a real readout. -/
def requestedPositionProbability
    (setup : OneDimensionalQuantumPositionSetup) : ℝ :=
  (((setup.positionProbability : Measure ℝ)
      (requestedPositionEvent setup)).toReal)

/-! ## Scenario, source readouts, figure evidence, and governing law -/

/-- The prose specifies a neutron and the graph specifies femtometer
coordinates. -/
structure MatchesNeutronPositionScenario
    (setup : OneDimensionalQuantumPositionSetup) : Prop where
  particleIsNeutron : setup.particle = .neutron
  horizontalCoordinateUsesFemtometers :
    setup.coordinateUnit = LengthUnit.femtometers

/-- Numerical and textual data read directly from the question and raster.

The endpoint `4`, query cutoff `2`, axis ticks, and printed labels occur here,
but the requested event probability does not.
-/
structure MatchesProblemAndFigureReadouts
    (setup : OneDimensionalQuantumPositionSetup) : Prop where
  supportHalfWidthIsFour :
    setup.supportHalfWidthCoordinate = 4
  queriedCutoffIsTwo :
    setup.queriedAbsoluteCoordinateCutoff = 2
  tickNegFour : setup.figure.coordinateAtTick .negFour = -4
  tickNegTwo : setup.figure.coordinateAtTick .negTwo = -2
  tickZero : setup.figure.coordinateAtTick .zero = 0
  tickTwo : setup.figure.coordinateAtTick .two = 2
  tickFour : setup.figure.coordinateAtTick .four = 4
  densityAxisText :
    setup.figure.printedText .waveFunctionDensity = "|ψ(x)|²"
  positionAxisText :
    setup.figure.printedText .positionInFemtometers = "x (fm)"
  peakLabelText :
    setup.figure.printedText .peakDensityA = "a"

/-- The supplied V-shaped graph, transcribed as a piecewise-linear density.

Inside the endpoints the height is `a |x| / supportHalfWidth`; outside it is
zero.  The first field identifies the plotted curve with this setup's
wave-function density rather than with an unrelated scalar function.
-/
structure MatchesSuppliedProbabilityDensityFigure
    (setup : OneDimensionalQuantumPositionSetup) : Prop where
  graphMatchesWaveFunctionDensity :
    ∀ x, setup.figure.plottedDensityReadout x =
      positionDensityReadout setup x
  vShapedPiecewiseLinearCurve :
    ∀ x, setup.figure.plottedDensityReadout x =
      if |x| ≤ setup.supportHalfWidthCoordinate then
        setup.peakDensityReadout * |x| /
          setup.supportHalfWidthCoordinate
      else 0
  symmetricAboutVerticalAxis :
    setup.figure.curveIsSymmetricAboutVerticalAxis = true
  linearOnEachSideOfOrigin :
    setup.figure.curveIsLinearOnEachSideOfOrigin = true
  verticalEndpointDrops :
    setup.figure.curveDropsVerticallyAtEndpoints = true

/-- Positivity and ordering conditions implicit in a physical density graph. -/
structure HasPhysicalProbabilityDensityParameters
    (setup : OneDimensionalQuantumPositionSetup) : Prop where
  supportHalfWidthPositive :
    0 < setup.supportHalfWidthCoordinate
  queriedCutoffNonnegative :
    0 ≤ setup.queriedAbsoluteCoordinateCutoff
  queriedCutoffInsideSupport :
    setup.queriedAbsoluteCoordinateCutoff <
      setup.supportHalfWidthCoordinate
  peakDensityPositive :
    0 < setup.peakDensityReadout

/-- The one-dimensional Born rule for arbitrary measurable position events.

This is a governing law, not a statement of the probability of the particular
event `|x| ≥ 2 fm`.
-/
structure SatisfiesOneDimensionalBornRule
    (setup : OneDimensionalQuantumPositionSetup) : Prop where
  densityIsIntegrable :
    Integrable (positionDensityReadout setup)
  probabilityOfMeasurableEvent :
    ∀ event : Set ℝ, MeasurableSet event →
      (((setup.positionProbability : Measure ℝ) event).toReal) =
        ∫ x in event, positionDensityReadout setup x

/-! ## Displayed choices and formal targets -/

/-- Labels of the four probabilities displayed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless probability printed beside each answer label. -/
def displayedProbability : AnswerChoice → ℝ
  | .A => 13 / 20
  | .B => 11 / 20
  | .C => 3 / 4
  | .D => 1 / 2

/-- A displayed choice agrees exactly with the modeled event probability. -/
def MatchesDisplayedProbability
    (setup : OneDimensionalQuantumPositionSetup)
    (choice : AnswerChoice) : Prop :=
  requestedPositionProbability setup = displayedProbability choice

/-- A choice is the unique displayed probability agreeing with the model. -/
def IsUniqueMatchingAnswerChoice
    (setup : OneDimensionalQuantumPositionSetup)
    (choice : AnswerChoice) : Prop :=
  MatchesDisplayedProbability setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedProbability setup other → other = choice

/-- Normalization, the Born rule, and the two congruent triangular halves of
the graph force the endpoint label `a` to read `1/4 fm⁻¹`.

This is a derived intermediate result, not a figure premise.
-/
lemma peakDensityReadout_eq_one_fourth
    (setup : OneDimensionalQuantumPositionSetup)
    (hReadouts : MatchesProblemAndFigureReadouts setup)
    (hFigure : MatchesSuppliedProbabilityDensityFigure setup)
    (hPhysical : HasPhysicalProbabilityDensityParameters setup)
    (hBorn : SatisfiesOneDimensionalBornRule setup) :
    setup.peakDensityReadout = (1 / 4 : ℝ) := by
  have hDensity (x : ℝ) : positionDensityReadout setup x =
      if |x| ≤ (4 : ℝ) then
        setup.peakDensityReadout * |x| / 4
      else 0 := by
    rw [← hFigure.graphMatchesWaveFunctionDensity x,
      hFigure.vShapedPiecewiseLinearCurve x,
      hReadouts.supportHalfWidthIsFour]
  have hShapeIntegral (a : ℝ) :
      (∫ x : ℝ, if |x| ≤ (4 : ℝ) then a * |x| / 4 else 0) =
        4 * a := by
    have hset : {x : ℝ | |x| ≤ (4 : ℝ)} = Set.Icc (-4) 4 := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
    change (∫ x : ℝ, ({x : ℝ | |x| ≤ (4 : ℝ)}).indicator
      (fun x => a * |x| / 4) x) = 4 * a
    rw [MeasureTheory.integral_indicator]
    · rw [hset, MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (-4 : ℝ) ≤ 4)]
      have hcont : Continuous (fun x : ℝ => a * |x| / 4) :=
        (continuous_const.mul continuous_abs).div_const 4
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable (-4) 0)
        (hcont.intervalIntegrable 0 4)]
      have hneg :
          (∫ x : ℝ in (-4)..0, a * |x| / 4) =
            ∫ x : ℝ in (-4)..0, (-a / 4) * x := by
        apply intervalIntegral.integral_congr
        intro x hx
        norm_num [Set.uIcc_of_le] at hx
        change a * |x| / 4 = (-a / 4) * x
        rw [abs_of_nonpos hx.2]
        ring
      have hpos :
          (∫ x : ℝ in 0..4, a * |x| / 4) =
            ∫ x : ℝ in 0..4, (a / 4) * x := by
        apply intervalIntegral.integral_congr
        intro x hx
        norm_num [Set.uIcc_of_le] at hx
        change a * |x| / 4 = (a / 4) * x
        rw [abs_of_nonneg hx.1]
        ring
      rw [hneg, hpos, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, integral_id, integral_id]
      ring
    · rw [hset]
      exact measurableSet_Icc
  have hNormalization :
      (∫ x : ℝ, positionDensityReadout setup x) = 1 := by
    simpa using
      (hBorn.probabilityOfMeasurableEvent
        Set.univ MeasurableSet.univ).symm
  rw [show (∫ x : ℝ, positionDensityReadout setup x) =
      ∫ x : ℝ, if |x| ≤ (4 : ℝ) then
        setup.peakDensityReadout * |x| / 4 else 0 by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall hDensity] at hNormalization
  rw [hShapeIntegral] at hNormalization
  linarith

/-- The regions `2 fm ≤ |x| ≤ 4 fm` are two congruent trapezoids whose
combined area is three quarters of the normalized V-shaped density.  Thus the
requested probability is `0.75`, uniquely selecting answer C.

This formalizes blueprint label `thm:physics:phyx_mini_0503:target`.
-/
theorem problem_phyx_mini_0503
    (setup : OneDimensionalQuantumPositionSetup)
    (hScenario : MatchesNeutronPositionScenario setup)
    (hReadouts : MatchesProblemAndFigureReadouts setup)
    (hFigure : MatchesSuppliedProbabilityDensityFigure setup)
    (hPhysical : HasPhysicalProbabilityDensityParameters setup)
    (hBorn : SatisfiesOneDimensionalBornRule setup) :
    requestedPositionProbability setup = (3 / 4 : ℝ) ∧
      IsUniqueMatchingAnswerChoice setup .C := by
  have hPeak : setup.peakDensityReadout = (1 / 4 : ℝ) :=
    peakDensityReadout_eq_one_fourth
      setup hReadouts hFigure hPhysical hBorn
  have hDensity (x : ℝ) : positionDensityReadout setup x =
      if |x| ≤ (4 : ℝ) then
        setup.peakDensityReadout * |x| / 4
      else 0 := by
    rw [← hFigure.graphMatchesWaveFunctionDensity x,
      hFigure.vShapedPiecewiseLinearCurve x,
      hReadouts.supportHalfWidthIsFour]
  have hEvent :
      requestedPositionEvent setup = {x : ℝ | (2 : ℝ) ≤ |x|} := by
    ext x
    simp only [requestedPositionEvent, outsideCentralRegion,
      Set.mem_setOf_eq, hReadouts.queriedCutoffIsTwo]
  have hEventMeasurable : MeasurableSet (requestedPositionEvent setup) := by
    rw [hEvent]
    exact measurableSet_le measurable_const continuous_abs.measurable
  have hOuterIntegral (a : ℝ) :
      (∫ x : ℝ in {x : ℝ | (2 : ℝ) ≤ |x|},
        if |x| ≤ (4 : ℝ) then a * |x| / 4 else 0) =
          3 * a := by
    let support : Set ℝ := {x : ℝ | |x| ≤ (4 : ℝ)}
    let outer : Set ℝ := Set.Icc (-4) (-2) ∪ Set.Icc 2 4
    have hSupportMeasurable : MeasurableSet support := by
      dsimp [support]
      exact measurableSet_le continuous_abs.measurable measurable_const
    have hIntersection :
        {x : ℝ | (2 : ℝ) ≤ |x|} ∩ support = outer := by
      ext x
      simp only [support, outer, Set.mem_inter_iff, Set.mem_setOf_eq,
        Set.mem_union, Set.mem_Icc]
      rw [abs_le]
      constructor
      · rintro ⟨houter, hsneg, hspos⟩
        rw [le_abs] at houter
        rcases houter with hright | hleft
        · exact Or.inr ⟨hright, hspos⟩
        · exact Or.inl ⟨hsneg, by linarith⟩
      · rintro (hleft | hright)
        · exact
            ⟨(le_abs).2 (Or.inr (by linarith)),
              hleft.1, by linarith⟩
        · exact
            ⟨(le_abs).2 (Or.inl hright.1),
              by linarith, hright.2⟩
    change (∫ x : ℝ in {x : ℝ | (2 : ℝ) ≤ |x|},
      support.indicator (fun x => a * |x| / 4) x) = 3 * a
    rw [MeasureTheory.setIntegral_indicator hSupportMeasurable,
      hIntersection]
    have hcont : Continuous (fun x : ℝ => a * |x| / 4) :=
      (continuous_const.mul continuous_abs).div_const 4
    rw [MeasureTheory.setIntegral_union]
    · rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le
          (by norm_num : (-4 : ℝ) ≤ -2),
        MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le
          (by norm_num : (2 : ℝ) ≤ 4)]
      have hneg :
          (∫ x : ℝ in (-4)..(-2), a * |x| / 4) =
            ∫ x : ℝ in (-4)..(-2), (-a / 4) * x := by
        apply intervalIntegral.integral_congr
        intro x hx
        norm_num [Set.uIcc_of_le] at hx
        change a * |x| / 4 = (-a / 4) * x
        rw [abs_of_nonpos]
        · ring
        · linarith
      have hpos :
          (∫ x : ℝ in 2..4, a * |x| / 4) =
            ∫ x : ℝ in 2..4, (a / 4) * x := by
        apply intervalIntegral.integral_congr
        intro x hx
        norm_num [Set.uIcc_of_le] at hx
        change a * |x| / 4 = (a / 4) * x
        rw [abs_of_nonneg]
        · ring
        · linarith
      rw [hneg, hpos, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, integral_id, integral_id]
      ring
    · refine Set.disjoint_left.2 ?_
      intro x hxneg hxpos
      linarith [hxneg.2, hxpos.1]
    · exact measurableSet_Icc
    · exact hcont.continuousOn.integrableOn_compact isCompact_Icc
    · exact hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hProbability :
      requestedPositionProbability setup = (3 / 4 : ℝ) := by
    rw [requestedPositionProbability,
      hBorn.probabilityOfMeasurableEvent
        (requestedPositionEvent setup) hEventMeasurable]
    calc
      (∫ x : ℝ in requestedPositionEvent setup,
          positionDensityReadout setup x) =
          ∫ x : ℝ in requestedPositionEvent setup,
            if |x| ≤ (4 : ℝ) then
              setup.peakDensityReadout * |x| / 4 else 0 := by
                apply MeasureTheory.setIntegral_congr_fun hEventMeasurable
                intro x _
                exact hDensity x
      _ = ∫ x : ℝ in requestedPositionEvent setup,
            if |x| ≤ (4 : ℝ) then
              (1 / 4 : ℝ) * |x| / 4 else 0 := by rw [hPeak]
      _ = 3 * (1 / 4 : ℝ) := by
        rw [hEvent]
        exact hOuterIntegral (1 / 4)
      _ = (3 / 4 : ℝ) := by norm_num
  refine ⟨hProbability, ?_⟩
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

end PhyXMiniProblems.ProblemPhyXMini0503
