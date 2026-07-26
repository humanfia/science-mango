import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0869

open Dimension MeasureTheory

/-!
# Electric potential from a graph of the x-component of electric field

The primary image plots `E_x` in volts per metre against `x` in metres.  The
trace is constant at `200 V/m` from `x = 0` through `x = 2`, then decreases
linearly to `0 V/m` at `x = 3`.  The prose gives the potential at the origin as
`-50 V`.

Physical potential and electric-field components are unit-independent
`Dimensionful` quantities.  Real numbers below are only coherent-SI readouts,
coordinates measured in metres, or displayed multiple-choice values.  The
one-dimensional component is also calibrated against Physlib's
spacetime-dependent `Electromagnetism.ElectricField 1`.

Assumption/target split:

* governing laws: the field is electrostatic along the plotted line and
  `V(b) - V(a) = - integral_a^b E_x(x) dx` in coherent SI units;
* previous-part results: none;
* figure/data readouts: the two axis roles and labels, ticks, magenta trace,
  grid, the `200 V/m` plateau on `[0, 2]`, the affine fall to zero on `[2, 3]`,
  and the stated origin potential `-50 V`;
* current target conclusions: the field area on `[0, 3]` is `150 V`, the
  potential at `x = 3 m` is `-200 V`, and answer D is the unique displayed
  match.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- The dimension `M L^2 T^-2 C^-1` of electric potential. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `M L T^-2 C^-1` of an electric-field component. -/
def electricFieldComponentDimension : Dimension :=
  electricPotentialDimension * L𝓭⁻¹

/-- A signed, unit-independent electric potential. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- A signed, unit-independent Cartesian component of electric field. -/
abbrev SignedElectricFieldComponentQuantity : Type :=
  Dimensionful (WithDim electricFieldComponentDimension ℝ)

/-- Coherent-SI readout of an electric potential, in volts. -/
def electricPotentialInVolts (potential : ElectricPotentialQuantity) : ℝ :=
  (potential UnitChoices.SI).val

/-- Coherent-SI readout of a signed electric-field component, in volts per metre. -/
def electricFieldComponentInVoltsPerMeter
    (component : SignedElectricFieldComponentQuantity) : ℝ :=
  (component UnitChoices.SI).val

/-! ## Figure labels and the physical setup -/

/-- The two coordinate axes visible in the supplied graph. -/
inductive PlotAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical role attached to a graph axis. -/
inductive PlotAxisRole where
  | positionInMeters
  | electricFieldXInVoltsPerMeter
  deriving DecidableEq, Repr

/-- Color category of the plotted trace. -/
inductive TraceColor where
  | magenta
  | other
  deriving DecidableEq, Repr

/-!
Literal diagram metadata.  All coordinates and tick values are scalar readouts
in the units printed on the corresponding axis; the physical field values are
connected to them separately in `MatchesPrimaryElectricFieldGraph`.
-/
structure ElectricFieldGraphFigure where
  axisRole : PlotAxis → PlotAxisRole
  printedAxisLabel : PlotAxis → String
  smallestPrintedTick : PlotAxis → ℝ
  largestPrintedTick : PlotAxis → ℝ
  printedMajorTickIncrement : PlotAxis → ℝ
  traceStartCoordinateMeters : ℝ
  traceCornerCoordinateMeters : ℝ
  traceEndCoordinateMeters : ℝ
  plateauFieldReadoutVoltsPerMeter : ℝ
  endpointFieldReadoutVoltsPerMeter : ℝ
  traceColor : TraceColor
  hasRectangularGrid : Bool
  firstSegmentIsHorizontal : Bool
  secondSegmentIsStraight : Bool

/-!
The physical electrostatic system sampled by the graph.  Its scalar fields are
independent data, not definitions in terms of `-200` or answer D.
-/
structure ElectrostaticLineSetup where
  electricPotentialAtMeterCoordinate : ℝ → ElectricPotentialQuantity
  electricFieldXAtMeterCoordinate : ℝ → SignedElectricFieldComponentQuantity
  ambientElectricField : Electromagnetism.ElectricField 1
  observationTime : Time
  pointAtMeterCoordinate : ℝ → Space 1
  figure : ElectricFieldGraphFigure
  isElectrostatic : Bool

/-! ## Scenario, field calibration, figure evidence, and governing law -/

/-- The prose identifies the system as electrostatic. -/
structure MatchesElectrostaticScenario (setup : ElectrostaticLineSetup) : Prop where
  electrostatic : setup.isElectrostatic = true

/-!
Calibration of the typed scalar component against Physlib's one-dimensional
electric field along the plotted spatial line.  The raw Physlib vector
component is interpreted in coherent SI units.  Time independence states the
electrostatic condition rather than any numerical target value.
-/
structure CalibratesPhyslibElectricField (setup : ElectrostaticLineSetup) : Prop where
  pointHasShownMeterCoordinate : ∀ x : ℝ,
    setup.pointAtMeterCoordinate x (0 : Fin 1) = x
  observedXComponent : ∀ x : ℝ,
    setup.ambientElectricField setup.observationTime
          (setup.pointAtMeterCoordinate x) (0 : Fin 1) =
      electricFieldComponentInVoltsPerMeter
        (setup.electricFieldXAtMeterCoordinate x)
  timeIndependentAlongPlottedLine : ∀ (time : Time) (x : ℝ),
    setup.ambientElectricField time (setup.pointAtMeterCoordinate x) (0 : Fin 1) =
      setup.ambientElectricField setup.observationTime
        (setup.pointAtMeterCoordinate x) (0 : Fin 1)

/-!
Axis data and trace values read from the primary raster.  The affine formula
on `[2, 3]` expresses the visible straight segment from `(2, 200)` to `(3, 0)`.
It describes the supplied field graph only; it does not state a potential.
-/
structure MatchesPrimaryElectricFieldGraph (setup : ElectrostaticLineSetup) : Prop where
  horizontalRole : setup.figure.axisRole .horizontal = .positionInMeters
  verticalRole :
    setup.figure.axisRole .vertical = .electricFieldXInVoltsPerMeter
  horizontalAxisLabel : setup.figure.printedAxisLabel .horizontal = "x (m)"
  verticalAxisLabel : setup.figure.printedAxisLabel .vertical = "E_x (V/m)"
  horizontalFirstTick : setup.figure.smallestPrintedTick .horizontal = 0
  horizontalLastTick : setup.figure.largestPrintedTick .horizontal = 3
  horizontalTickStep : setup.figure.printedMajorTickIncrement .horizontal = 1
  verticalFirstTick : setup.figure.smallestPrintedTick .vertical = 0
  verticalLastTick : setup.figure.largestPrintedTick .vertical = 200
  verticalTickStep : setup.figure.printedMajorTickIncrement .vertical = 100
  traceStartsAtOrigin : setup.figure.traceStartCoordinateMeters = 0
  traceCornerAtTwoMeters : setup.figure.traceCornerCoordinateMeters = 2
  traceEndsAtThreeMeters : setup.figure.traceEndCoordinateMeters = 3
  plateauReadout : setup.figure.plateauFieldReadoutVoltsPerMeter = 200
  endpointReadout : setup.figure.endpointFieldReadoutVoltsPerMeter = 0
  magentaTrace : setup.figure.traceColor = .magenta
  rectangularGrid : setup.figure.hasRectangularGrid = true
  horizontalFirstSegment : setup.figure.firstSegmentIsHorizontal = true
  straightSecondSegment : setup.figure.secondSegmentIsStraight = true
  constantTrace : ∀ x : ℝ,
    0 ≤ x → x ≤ 2 →
      electricFieldComponentInVoltsPerMeter
          (setup.electricFieldXAtMeterCoordinate x) = 200
  affineDescendingTrace : ∀ x : ℝ,
    2 ≤ x → x ≤ 3 →
      electricFieldComponentInVoltsPerMeter
          (setup.electricFieldXAtMeterCoordinate x) = 200 * (3 - x)

/-- The stated datum that the potential at the origin is `-50 V`. -/
structure UsesStatedOriginPotential (setup : ElectrostaticLineSetup) : Prop where
  originPotentialReadout :
    electricPotentialInVolts (setup.electricPotentialAtMeterCoordinate 0) = -50

/-!
The electrostatic potential-difference law on the plotted interval,

`V(b) - V(a) = - integral_a^b E_x(x) dx`.

The integration variable is the displayed metre coordinate, so integrating a
`V/m` readout produces a voltage readout.  The law is quantified over every
subinterval of `[0, 3]`; it does not assume the requested endpoint value.
-/
structure SatisfiesElectrostaticPotentialDifferenceLaw
    (setup : ElectrostaticLineSetup) : Prop where
  fieldIntegrableOnPlottedInterval :
    IntervalIntegrable
      (fun x => electricFieldComponentInVoltsPerMeter
        (setup.electricFieldXAtMeterCoordinate x)) volume 0 3
  potentialDifferenceFromField : ∀ a b : ℝ,
    0 ≤ a → a ≤ b → b ≤ 3 →
      electricPotentialInVolts (setup.electricPotentialAtMeterCoordinate b) -
          electricPotentialInVolts (setup.electricPotentialAtMeterCoordinate a) =
        -∫ x in a..b,
          electricFieldComponentInVoltsPerMeter
            (setup.electricFieldXAtMeterCoordinate x)

/-! ## Displayed choices and current conclusions -/

/-- Labels attached to the four displayed potential choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Potential readout printed beside an answer label, in volts. -/
def displayedPotentialInVolts : AnswerChoice → ℝ
  | .A => 120
  | .B => -140
  | .C => -2000
  | .D => -200

/-- A displayed choice agrees with the potential at the plotted endpoint. -/
def choiceMatchesTarget
    (setup : ElectrostaticLineSetup) (choice : AnswerChoice) : Prop :=
  electricPotentialInVolts
      (setup.electricPotentialAtMeterCoordinate
        setup.figure.traceEndCoordinateMeters) =
    displayedPotentialInVolts choice

/-- The signed area under the supplied `E_x` graph from `0 m` to `3 m` is `150 V`. -/
lemma electricFieldAreaFromPrimaryGraph_eq_oneHundredFiftyVolts
    (setup : ElectrostaticLineSetup)
    (hFigure : MatchesPrimaryElectricFieldGraph setup) :
    (∫ x in (0 : ℝ)..3,
      electricFieldComponentInVoltsPerMeter
        (setup.electricFieldXAtMeterCoordinate x)) = 150 := by
  let fieldReadout : ℝ → ℝ := fun x =>
    electricFieldComponentInVoltsPerMeter
      (setup.electricFieldXAtMeterCoordinate x)
  have hIntegrableZeroTwo :
      IntervalIntegrable fieldReadout volume 0 2 := by
    apply
      ((continuous_const :
        Continuous (fun _ : ℝ => (200 : ℝ))).intervalIntegrable 0 2).congr
    intro x hx
    rw [Set.uIoc_of_le (by norm_num)] at hx
    exact
      (hFigure.constantTrace x (le_of_lt hx.1) hx.2).symm
  have hIntegrableTwoThree :
      IntervalIntegrable fieldReadout volume 2 3 := by
    have hContinuous :
        Continuous (fun x : ℝ => (200 : ℝ) * (3 - x)) := by
      fun_prop
    apply (hContinuous.intervalIntegrable 2 3).congr
    intro x hx
    rw [Set.uIoc_of_le (by norm_num)] at hx
    exact
      (hFigure.affineDescendingTrace x (le_of_lt hx.1) hx.2).symm
  have hIntegralZeroTwo :
      (∫ x in (0 : ℝ)..2, fieldReadout x) = 400 := by
    calc
      (∫ x in (0 : ℝ)..2, fieldReadout x) =
          ∫ _ in (0 : ℝ)..2, (200 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [Set.uIcc_of_le (by norm_num)] at hx
            exact hFigure.constantTrace x hx.1 hx.2
      _ = 400 := by norm_num
  have hIntegralTwoThree :
      (∫ x in (2 : ℝ)..3, fieldReadout x) = 100 := by
    calc
      (∫ x in (2 : ℝ)..3, fieldReadout x) =
          ∫ x in (2 : ℝ)..3, (200 : ℝ) * (3 - x) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [Set.uIcc_of_le (by norm_num)] at hx
            exact hFigure.affineDescendingTrace x hx.1 hx.2
      _ = 100 := by
        have hderiv : ∀ x ∈ Set.uIcc (2 : ℝ) 3,
            HasDerivAt (fun x : ℝ => 600 * x - 100 * x ^ 2)
              (200 * (3 - x)) x := by
          intro x _
          have h :=
            ((hasDerivAt_id x).const_mul 600).sub
              (((hasDerivAt_id x).pow 2).const_mul 100)
          convert h using 1
          all_goals try rfl
          norm_num [id]
          ring
        have hIntegrable :
            IntervalIntegrable (fun x : ℝ => 200 * (3 - x))
              volume 2 3 := by
          apply Continuous.intervalIntegrable
          fun_prop
        have h :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt
            (f := fun x : ℝ => 600 * x - 100 * x ^ 2)
            hderiv hIntegrable
        norm_num at h ⊢
        exact h
  have hActualArea :
      (∫ x in (0 : ℝ)..3, fieldReadout x) = 500 := by
    calc
      (∫ x in (0 : ℝ)..3, fieldReadout x) =
          (∫ x in (0 : ℝ)..2, fieldReadout x) +
            ∫ x in (2 : ℝ)..3, fieldReadout x := by
              exact
                (intervalIntegral.integral_add_adjacent_intervals
                  hIntegrableZeroTwo hIntegrableTwoThree).symm
      _ = 500 := by
        rw [hIntegralZeroTwo, hIntegralTwoThree]
        norm_num
  change (∫ x in (0 : ℝ)..3, fieldReadout x) = 150
  have hImpossibleNumericEquality : (500 : ℝ) = 150 := by
    -- The frozen conclusion conflicts with the 400 V rectangle plus 100 V triangle.
    sorry
  exact hActualArea.trans hImpossibleNumericEquality

/-!
The requested potential at `x = 3 m` is `-200 V`.  This is the Lean
declaration corresponding to blueprint label
`thm:physics:phyx_mini_0869:target`.
-/
theorem electricPotentialAtThreeMeters_eq_negTwoHundredVolts
    (setup : ElectrostaticLineSetup)
    (hScenario : MatchesElectrostaticScenario setup)
    (hCalibration : CalibratesPhyslibElectricField setup)
    (hFigure : MatchesPrimaryElectricFieldGraph setup)
    (hOrigin : UsesStatedOriginPotential setup)
    (hLaw : SatisfiesElectrostaticPotentialDifferenceLaw setup) :
    electricPotentialInVolts
      (setup.electricPotentialAtMeterCoordinate 3) = -200 := by
  let fieldReadout : ℝ → ℝ := fun x =>
    electricFieldComponentInVoltsPerMeter
      (setup.electricFieldXAtMeterCoordinate x)
  have hIntegrableZeroTwo :
      IntervalIntegrable fieldReadout volume 0 2 := by
    apply hLaw.fieldIntegrableOnPlottedInterval.mono_set
    apply Set.uIcc_subset_uIcc
    · rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    · rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
  have hIntegrableTwoThree :
      IntervalIntegrable fieldReadout volume 2 3 := by
    apply hLaw.fieldIntegrableOnPlottedInterval.mono_set
    apply Set.uIcc_subset_uIcc
    · rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    · rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
  have hIntegralZeroTwo :
      (∫ x in (0 : ℝ)..2, fieldReadout x) = 400 := by
    calc
      (∫ x in (0 : ℝ)..2, fieldReadout x) =
          ∫ _ in (0 : ℝ)..2, (200 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [Set.uIcc_of_le (by norm_num)] at hx
            exact hFigure.constantTrace x hx.1 hx.2
      _ = 400 := by norm_num
  have hIntegralTwoThree :
      (∫ x in (2 : ℝ)..3, fieldReadout x) = 100 := by
    calc
      (∫ x in (2 : ℝ)..3, fieldReadout x) =
          ∫ x in (2 : ℝ)..3, (200 : ℝ) * (3 - x) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [Set.uIcc_of_le (by norm_num)] at hx
            exact hFigure.affineDescendingTrace x hx.1 hx.2
      _ = 100 := by
        have hderiv : ∀ x ∈ Set.uIcc (2 : ℝ) 3,
            HasDerivAt (fun x : ℝ => 600 * x - 100 * x ^ 2)
              (200 * (3 - x)) x := by
          intro x _
          have h :=
            ((hasDerivAt_id x).const_mul 600).sub
              (((hasDerivAt_id x).pow 2).const_mul 100)
          convert h using 1
          all_goals try rfl
          norm_num [id]
          ring
        have hIntegrable :
            IntervalIntegrable (fun x : ℝ => 200 * (3 - x))
              volume 2 3 := by
          apply Continuous.intervalIntegrable
          fun_prop
        have h :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt
            (f := fun x : ℝ => 600 * x - 100 * x ^ 2)
            hderiv hIntegrable
        norm_num at h ⊢
        exact h
  have hActualArea :
      (∫ x in (0 : ℝ)..3, fieldReadout x) = 500 := by
    calc
      (∫ x in (0 : ℝ)..3, fieldReadout x) =
          (∫ x in (0 : ℝ)..2, fieldReadout x) +
            ∫ x in (2 : ℝ)..3, fieldReadout x := by
              exact
                (intervalIntegral.integral_add_adjacent_intervals
                  hIntegrableZeroTwo hIntegrableTwoThree).symm
      _ = 500 := by
        rw [hIntegralZeroTwo, hIntegralTwoThree]
        norm_num
  have hPotentialDifference :=
    hLaw.potentialDifferenceFromField 0 3
      (by norm_num) (by norm_num) (by norm_num)
  change
    electricPotentialInVolts
        (setup.electricPotentialAtMeterCoordinate 3) -
      electricPotentialInVolts
        (setup.electricPotentialAtMeterCoordinate 0) =
      -(∫ x in (0 : ℝ)..3, fieldReadout x) at hPotentialDifference
  have hActualPotential :
      electricPotentialInVolts
        (setup.electricPotentialAtMeterCoordinate 3) = -550 := by
    rw [hActualArea, hOrigin.originPotentialReadout] at hPotentialDifference
    linarith
  have hImpossibleNumericEquality : (-550 : ℝ) = -200 := by
    -- The governing law and encoded graph instead force the endpoint potential to be -550 V.
    sorry
  exact hActualPotential.trans hImpossibleNumericEquality

/-- Answer D is the unique displayed choice matching the derived endpoint potential. -/
theorem answerD_isUniqueDisplayedMatch
    (setup : ElectrostaticLineSetup)
    (hScenario : MatchesElectrostaticScenario setup)
    (hCalibration : CalibratesPhyslibElectricField setup)
    (hFigure : MatchesPrimaryElectricFieldGraph setup)
    (hOrigin : UsesStatedOriginPotential setup)
    (hLaw : SatisfiesElectrostaticPotentialDifferenceLaw setup) :
    choiceMatchesTarget setup .D ∧
      ∀ choice : AnswerChoice, choiceMatchesTarget setup choice → choice = .D := by
  let fieldReadout : ℝ → ℝ := fun x =>
    electricFieldComponentInVoltsPerMeter
      (setup.electricFieldXAtMeterCoordinate x)
  have hIntegrableZeroTwo :
      IntervalIntegrable fieldReadout volume 0 2 := by
    apply hLaw.fieldIntegrableOnPlottedInterval.mono_set
    apply Set.uIcc_subset_uIcc
    · rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    · rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
  have hIntegrableTwoThree :
      IntervalIntegrable fieldReadout volume 2 3 := by
    apply hLaw.fieldIntegrableOnPlottedInterval.mono_set
    apply Set.uIcc_subset_uIcc
    · rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    · rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
  have hIntegralZeroTwo :
      (∫ x in (0 : ℝ)..2, fieldReadout x) = 400 := by
    calc
      (∫ x in (0 : ℝ)..2, fieldReadout x) =
          ∫ _ in (0 : ℝ)..2, (200 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [Set.uIcc_of_le (by norm_num)] at hx
            exact hFigure.constantTrace x hx.1 hx.2
      _ = 400 := by norm_num
  have hIntegralTwoThree :
      (∫ x in (2 : ℝ)..3, fieldReadout x) = 100 := by
    calc
      (∫ x in (2 : ℝ)..3, fieldReadout x) =
          ∫ x in (2 : ℝ)..3, (200 : ℝ) * (3 - x) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [Set.uIcc_of_le (by norm_num)] at hx
            exact hFigure.affineDescendingTrace x hx.1 hx.2
      _ = 100 := by
        have hderiv : ∀ x ∈ Set.uIcc (2 : ℝ) 3,
            HasDerivAt (fun x : ℝ => 600 * x - 100 * x ^ 2)
              (200 * (3 - x)) x := by
          intro x _
          have h :=
            ((hasDerivAt_id x).const_mul 600).sub
              (((hasDerivAt_id x).pow 2).const_mul 100)
          convert h using 1
          all_goals try rfl
          norm_num [id]
          ring
        have hIntegrable :
            IntervalIntegrable (fun x : ℝ => 200 * (3 - x))
              volume 2 3 := by
          apply Continuous.intervalIntegrable
          fun_prop
        have h :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt
            (f := fun x : ℝ => 600 * x - 100 * x ^ 2)
            hderiv hIntegrable
        norm_num at h ⊢
        exact h
  have hActualArea :
      (∫ x in (0 : ℝ)..3, fieldReadout x) = 500 := by
    calc
      (∫ x in (0 : ℝ)..3, fieldReadout x) =
          (∫ x in (0 : ℝ)..2, fieldReadout x) +
            ∫ x in (2 : ℝ)..3, fieldReadout x := by
              exact
                (intervalIntegral.integral_add_adjacent_intervals
                  hIntegrableZeroTwo hIntegrableTwoThree).symm
      _ = 500 := by
        rw [hIntegralZeroTwo, hIntegralTwoThree]
        norm_num
  have hPotentialDifference :=
    hLaw.potentialDifferenceFromField 0 3
      (by norm_num) (by norm_num) (by norm_num)
  change
    electricPotentialInVolts
        (setup.electricPotentialAtMeterCoordinate 3) -
      electricPotentialInVolts
        (setup.electricPotentialAtMeterCoordinate 0) =
      -(∫ x in (0 : ℝ)..3, fieldReadout x) at hPotentialDifference
  have hActualPotential :
      electricPotentialInVolts
        (setup.electricPotentialAtMeterCoordinate 3) = -550 := by
    rw [hActualArea, hOrigin.originPotentialReadout] at hPotentialDifference
    linarith
  have hNoDisplayedChoiceMatches :
      ∀ choice : AnswerChoice, ¬ choiceMatchesTarget setup choice := by
    intro choice hMatch
    unfold choiceMatchesTarget at hMatch
    rw [hFigure.traceEndsAtThreeMeters, hActualPotential] at hMatch
    cases choice <;> norm_num [displayedPotentialInVolts] at hMatch
  constructor
  · have hImpossibleChoiceDMatch : choiceMatchesTarget setup .D := by
      -- The requested conjunct contradicts the independently derived -550 V endpoint.
      sorry
    exact hImpossibleChoiceDMatch
  · intro choice hMatch
    exact (hNoDisplayedChoiceMatches choice hMatch).elim

end PhyXMiniProblems.ProblemPhyXMini0869
