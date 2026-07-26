import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

/-!
# Potential difference from an electric-field graph

The primary image plots the signed `x`-component of an electric field against
the `x` coordinate.  Its magenta straight segment runs from
`(0 m, -100 V/m)` through `(1 m, 0 V/m)` to `(3 m, 200 V/m)`.  The question
asks for `V(3 m) - V(1 m)`.

Positions, scalar electric potentials, and signed electric-field components
are unit-independent Physlib quantities.  Real numbers below occur only as
coherent-SI readouts, graph coordinates, or displayed answer values.  The
full one-dimensional vector field is retained as
`Electromagnetism.ElectricField 1`.

Assumption/target split:

* `MatchesSuppliedElectricFieldGraph` records the axis labels, ranges, grid,
  colour, and endpoint/intermediate values visible in the raster;
* `TraceIsStraightLineInterpolation` gives mathematical content to the drawn
  straight segment without inserting the requested potential difference;
* `ElectricFieldReadoutMatchesFigure` connects both the dimensionful signed
  component and Physlib vector field to the plotted trace;
* `MatchesQuestionPositions` records `x_i = 1 m` and `x_f = 3 m`;
* `SatisfiesElectrostaticPotentialDifferenceLaw` is the governing law
  `V(b) - V(a) = -∫_a^b E_x(x) dx`; and
* the value `-200 V` and recorded answer D occur only in conclusions or in the
  displayed-answer metadata.

There are no previous-part results.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0868

open CarriesDimension Dimension

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- A signed physical coordinate along the graph's horizontal `x`-axis. -/
abbrev PositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- The dimension `M L² T⁻² C⁻¹` of electric potential. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A signed physical scalar electric potential. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- The dimension `M L T⁻² C⁻¹`, equivalently volts per metre, of `E_x`. -/
def electricFieldComponentDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A signed physical Cartesian electric-field component. -/
abbrev ElectricFieldComponentQuantity : Type :=
  Dimensionful (WithDim electricFieldComponentDimension ℝ)

/-- Coherent-SI readout of a signed position in metres. -/
def positionInMeters (position : PositionQuantity) : ℝ :=
  (position UnitChoices.SI).val

/-- Construct a physical position from a coherent-SI metre coordinate. -/
def positionFromMeters (xMeters : ℝ) : PositionQuantity :=
  toDimensionful UnitChoices.SI (show WithDim L𝓭 ℝ from ⟨xMeters⟩)

/-- Coherent-SI readout of an electric potential in volts. -/
def electricPotentialInVolts
    (potential : ElectricPotentialQuantity) : ℝ :=
  (potential UnitChoices.SI).val

/-- Coherent-SI readout of a signed field component in volts per metre. -/
def electricFieldComponentInVoltsPerMeter
    (component : ElectricFieldComponentQuantity) : ℝ :=
  (component UnitChoices.SI).val

/-!
The one-dimensional Physlib spatial coordinate chart used for the graph.  Its
sole coordinate is explicitly interpreted in metres by the calibration
predicate below.
-/
def spacePointAtMeterCoordinate (xMeters : ℝ) : Space 1 :=
  ⟨fun _ => xMeters⟩

/-! ## Primary-figure vocabulary and physical setup -/

/-- The two coordinate axes visible in image `868.png`. -/
inductive FigureAxis where
  | position
  | electricFieldX
  deriving DecidableEq, Fintype, Repr

/-- The colour of the single plotted field trace. -/
inductive TraceColor where
  | magenta
  | other
  deriving DecidableEq, Repr

/-!
Literal graph data.  The function is the signed `E_x` ordinate, measured in
volts per metre, at a horizontal coordinate measured in metres.
-/
structure ElectricFieldGraphFigure where
  axisLabel : FigureAxis → String
  horizontalAxisMinimumInMeters : ℝ
  horizontalAxisMaximumInMeters : ℝ
  verticalAxisMinimumInVoltsPerMeter : ℝ
  verticalAxisMaximumInVoltsPerMeter : ℝ
  horizontalGridSpacingInMeters : ℝ
  verticalGridSpacingInVoltsPerMeter : ℝ
  plottedFieldXInVoltsPerMeterAt : ℝ → ℝ
  traceColor : TraceColor
  traceIsStraight : Bool
  rectangularGridShown : Bool

/-!
Independent physical observables in the electrostatic setup.  Neither the
potential field nor either electric-field representation is defined from an
answer choice or from the requested `-200 V` value.
-/
structure ElectricFieldPotentialSetup where
  figure : ElectricFieldGraphFigure
  initialPosition : PositionQuantity
  finalPosition : PositionQuantity
  electricPotentialAt : PositionQuantity → ElectricPotentialQuantity
  electricFieldXAt : PositionQuantity → ElectricFieldComponentQuantity
  electricField : Electromagnetism.ElectricField 1
  observationTime : Time

/-! ## Figure/data readouts and governing laws -/

/-- Axis presentation and exact tick-intersection readouts from the raster. -/
structure MatchesSuppliedElectricFieldGraph
    (setup : ElectricFieldPotentialSetup) : Prop where
  horizontalAxisLabel : setup.figure.axisLabel .position = "x (m)"
  verticalAxisLabel : setup.figure.axisLabel .electricFieldX = "Eₓ (V/m)"
  horizontalAxisMinimum :
    setup.figure.horizontalAxisMinimumInMeters = 0
  horizontalAxisMaximum :
    setup.figure.horizontalAxisMaximumInMeters = 3
  verticalAxisMinimum :
    setup.figure.verticalAxisMinimumInVoltsPerMeter = -100
  verticalAxisMaximum :
    setup.figure.verticalAxisMaximumInVoltsPerMeter = 200
  horizontalGridSpacing :
    setup.figure.horizontalGridSpacingInMeters = 1
  verticalGridSpacing :
    setup.figure.verticalGridSpacingInVoltsPerMeter = 100
  leftEndpoint :
    setup.figure.plottedFieldXInVoltsPerMeterAt 0 = -100
  zeroCrossingAtOneMeter :
    setup.figure.plottedFieldXInVoltsPerMeterAt 1 = 0
  rightEndpoint :
    setup.figure.plottedFieldXInVoltsPerMeterAt 3 = 200
  magentaTrace : setup.figure.traceColor = .magenta
  straightTrace : setup.figure.traceIsStraight = true
  rectangularGrid : setup.figure.rectangularGridShown = true

/-- Affine interpolation through two endpoint coordinates. -/
def linearInterpolation
    (x₀ y₀ x₁ y₁ x : ℝ) : ℝ :=
  y₀ + (x - x₀) * (y₁ - y₀) / (x₁ - x₀)

/-!
Mathematical interpretation of the image's straight trace on the displayed
domain.  Its endpoint ordinates remain fields of the figure and are calibrated
separately, so this predicate contains no potential-difference conclusion.
-/
structure TraceIsStraightLineInterpolation
    (setup : ElectricFieldPotentialSetup) : Prop where
  traceInterpolation : ∀ xMeters : ℝ,
    setup.figure.horizontalAxisMinimumInMeters ≤ xMeters →
    xMeters ≤ setup.figure.horizontalAxisMaximumInMeters →
      setup.figure.plottedFieldXInVoltsPerMeterAt xMeters =
        linearInterpolation
          setup.figure.horizontalAxisMinimumInMeters
          (setup.figure.plottedFieldXInVoltsPerMeterAt
            setup.figure.horizontalAxisMinimumInMeters)
          setup.figure.horizontalAxisMaximumInMeters
          (setup.figure.plottedFieldXInVoltsPerMeterAt
            setup.figure.horizontalAxisMaximumInMeters)
          xMeters

/-!
Calibration of the graph against the dimensionful field component and the
`x` component of Physlib's one-dimensional vector field.  Physlib field
components are interpreted here as coherent-SI volts-per-metre readouts.
-/
structure ElectricFieldReadoutMatchesFigure
    (setup : ElectricFieldPotentialSetup) : Prop where
  dimensionfulComponentMatchesTrace : ∀ xMeters : ℝ,
    setup.figure.horizontalAxisMinimumInMeters ≤ xMeters →
    xMeters ≤ setup.figure.horizontalAxisMaximumInMeters →
      electricFieldComponentInVoltsPerMeter
          (setup.electricFieldXAt (positionFromMeters xMeters)) =
        setup.figure.plottedFieldXInVoltsPerMeterAt xMeters
  physlibFieldMatchesDimensionfulComponent : ∀ xMeters : ℝ,
    setup.figure.horizontalAxisMinimumInMeters ≤ xMeters →
    xMeters ≤ setup.figure.horizontalAxisMaximumInMeters →
      (setup.electricField setup.observationTime
          (spacePointAtMeterCoordinate xMeters)) 0 =
        electricFieldComponentInVoltsPerMeter
          (setup.electricFieldXAt (positionFromMeters xMeters))

/-- The two endpoint coordinates named by the question. -/
structure MatchesQuestionPositions
    (setup : ElectricFieldPotentialSetup) : Prop where
  initialPositionMeters : positionInMeters setup.initialPosition = 1
  finalPositionMeters : positionInMeters setup.finalPosition = 3

/-- Signed potential difference `V(final) - V(initial)`, read in volts. -/
def potentialDifferenceInVolts
    (setup : ElectricFieldPotentialSetup)
    (initial final : PositionQuantity) : ℝ :=
  electricPotentialInVolts (setup.electricPotentialAt final) -
    electricPotentialInVolts (setup.electricPotentialAt initial)

/-!
The electrostatic relation between potential difference and electric field,
stated for every ordered pair of positions.  This is a governing law; it does
not assert the requested value for the particular pair `1 m` and `3 m`.
-/
structure SatisfiesElectrostaticPotentialDifferenceLaw
    (setup : ElectricFieldPotentialSetup) : Prop where
  potentialDifferenceIsNegativeFieldIntegral :
    ∀ initial final : PositionQuantity,
      positionInMeters initial ≤ positionInMeters final →
        potentialDifferenceInVolts setup initial final =
          -∫ xMeters in positionInMeters initial..positionInMeters final,
            electricFieldComponentInVoltsPerMeter
              (setup.electricFieldXAt (positionFromMeters xMeters))

/-! ## Displayed choices and current target -/

/-- Labels attached to the four displayed potential-difference answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Potential difference in volts printed beside each answer label. -/
def displayedPotentialDifferenceInVolts : AnswerChoice → ℝ
  | .A => 120
  | .B => -140
  | .C => -2000
  | .D => -200

/-- Dataset metadata recording answer D; this is not a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
The negative area under the field graph from `1 m` to `3 m` is `-200 V`.
This derived relation is the substantive numerical question, not an assumption.
-/
lemma potentialDifference_from_one_to_three
    (setup : ElectricFieldPotentialSetup)
    (hFigure : MatchesSuppliedElectricFieldGraph setup)
    (hStraight : TraceIsStraightLineInterpolation setup)
    (hCalibration : ElectricFieldReadoutMatchesFigure setup)
    (hPositions : MatchesQuestionPositions setup)
    (hLaw : SatisfiesElectrostaticPotentialDifferenceLaw setup) :
    potentialDifferenceInVolts
      setup setup.initialPosition setup.finalPosition = -200 := by
  have hPositionOrder :
      positionInMeters setup.initialPosition ≤
        positionInMeters setup.finalPosition := by
    rw [hPositions.initialPositionMeters, hPositions.finalPositionMeters]
    norm_num
  have hPotential :=
    hLaw.potentialDifferenceIsNegativeFieldIntegral
      setup.initialPosition setup.finalPosition hPositionOrder
  rw [hPositions.initialPositionMeters, hPositions.finalPositionMeters] at hPotential
  have hFieldOn : Set.EqOn
      (fun xMeters : ℝ =>
        electricFieldComponentInVoltsPerMeter
          (setup.electricFieldXAt (positionFromMeters xMeters)))
      (fun xMeters : ℝ => 100 * xMeters - 100)
      (Set.uIcc (1 : ℝ) 3) := by
    intro xMeters hx
    rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at hx
    have hxLower :
        setup.figure.horizontalAxisMinimumInMeters ≤ xMeters := by
      rw [hFigure.horizontalAxisMinimum]
      linarith [hx.1]
    have hxUpper :
        xMeters ≤ setup.figure.horizontalAxisMaximumInMeters := by
      rw [hFigure.horizontalAxisMaximum]
      exact hx.2
    calc
      electricFieldComponentInVoltsPerMeter
          (setup.electricFieldXAt (positionFromMeters xMeters)) =
          setup.figure.plottedFieldXInVoltsPerMeterAt xMeters :=
        hCalibration.dimensionfulComponentMatchesTrace xMeters hxLower hxUpper
      _ = linearInterpolation
            setup.figure.horizontalAxisMinimumInMeters
            (setup.figure.plottedFieldXInVoltsPerMeterAt
              setup.figure.horizontalAxisMinimumInMeters)
            setup.figure.horizontalAxisMaximumInMeters
            (setup.figure.plottedFieldXInVoltsPerMeterAt
              setup.figure.horizontalAxisMaximumInMeters)
            xMeters :=
        hStraight.traceInterpolation xMeters hxLower hxUpper
      _ = 100 * xMeters - 100 := by
        rw [hFigure.horizontalAxisMinimum, hFigure.horizontalAxisMaximum,
          hFigure.leftEndpoint, hFigure.rightEndpoint]
        norm_num [linearInterpolation]
        ring
  have hIntegralCongr :
      (∫ xMeters : ℝ in (1 : ℝ)..3,
        electricFieldComponentInVoltsPerMeter
          (setup.electricFieldXAt (positionFromMeters xMeters))) =
        ∫ xMeters : ℝ in (1 : ℝ)..3, 100 * xMeters - 100 :=
    intervalIntegral.integral_congr (μ := MeasureTheory.volume) hFieldOn
  let F : ℝ → ℝ :=
    (fun y => 50 * (id ^ 2) y) - fun y => 100 * id y
  let f : ℝ → ℝ :=
    fun x => 50 * ((2 : ℝ) * id x ^ (2 - 1) * 1) - 100 * 1
  have hderiv (x : ℝ) : HasDerivAt F (f x) x := by
    dsimp only [F, f]
    exact (((hasDerivAt_id x).pow 2).const_mul 50).sub
      ((hasDerivAt_id x).const_mul 100)
  have hAffineIntegral :
      (∫ x : ℝ in (1 : ℝ)..3, 100 * x - 100) = 200 := by
    calc
      (∫ x : ℝ in (1 : ℝ)..3, 100 * x - 100) =
          ∫ x : ℝ in (1 : ℝ)..3, f x := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp only [f, id_eq, Nat.reduceSub, pow_one, mul_one]
        ring
      _ = F 3 - F 1 := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro x hx
          exact hderiv x
        · exact (by fun_prop : Continuous f).intervalIntegrable 1 3
      _ = 200 := by
        norm_num [F, id, Pi.sub_apply]
  calc
    potentialDifferenceInVolts
        setup setup.initialPosition setup.finalPosition =
        -(∫ xMeters in (1 : ℝ)..3,
          electricFieldComponentInVoltsPerMeter
            (setup.electricFieldXAt (positionFromMeters xMeters))) := hPotential
    _ = -(∫ xMeters in (1 : ℝ)..3, 100 * xMeters - 100) := by
      rw [hIntegralCongr]
    _ = -200 := by rw [hAffineIntegral]

/-!
Blueprint label: `thm:physics:phyx_mini_0868:target`.

The potential at `3 m` minus the potential at `1 m` is `-200 V`, and D is the
unique displayed answer with that value.
-/
theorem problem_phyx_mini_0868
    (setup : ElectricFieldPotentialSetup)
    (hFigure : MatchesSuppliedElectricFieldGraph setup)
    (hStraight : TraceIsStraightLineInterpolation setup)
    (hCalibration : ElectricFieldReadoutMatchesFigure setup)
    (hPositions : MatchesQuestionPositions setup)
    (hLaw : SatisfiesElectrostaticPotentialDifferenceLaw setup) :
    potentialDifferenceInVolts
        setup setup.initialPosition setup.finalPosition = -200 ∧
      potentialDifferenceInVolts
        setup setup.initialPosition setup.finalPosition =
          displayedPotentialDifferenceInVolts .D ∧
      ∀ choice : AnswerChoice,
        potentialDifferenceInVolts
            setup setup.initialPosition setup.finalPosition =
              displayedPotentialDifferenceInVolts choice ↔
          choice = .D := by
  have hValue :=
    potentialDifference_from_one_to_three
      setup hFigure hStraight hCalibration hPositions hLaw
  refine ⟨hValue, ?_, ?_⟩
  · simpa [displayedPotentialDifferenceInVolts] using hValue
  · intro choice
    rw [hValue]
    cases choice <;> norm_num [displayedPotentialDifferenceInVolts] <;> decide

end PhyXMiniProblems.ProblemPhyXMini0868
