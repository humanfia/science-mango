import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0962

open Dimension

/-!
# Total magnetic field beside a long straight wire

A long straight wire is aligned with the `y`-axis and carries an `8.00 A`
current in the negative-`y` direction.  A uniform background magnetic field of
magnitude `1.50 * 10⁻⁶ T` points in the positive-`x` direction.  The requested
field is evaluated at the figure point `b`, whose coherent-SI coordinates are
`(x,y,z) = (1,0,0) m`.

The right-hand rule makes the wire field point in the positive-`z` direction
at `b`.  Thus the wire and background contributions are perpendicular.  The
exact resultant magnitude is `sqrt 481 / 10 * 10⁻⁶ T`, which is displayed as
`2.19 * 10⁻⁶ T` in answer choice B.

Physical magnitudes use Physlib's unit-independent `Dimensionful` quantities.
Real numbers are used only for coherent-SI readouts, coordinate readouts, and
the dimensionless multiple-choice labels.  Magnetic vector fields retain
Physlib's spacetime-dependent `Electromagnetism.MagneticField 3` type.

Assumption/target split:

* governing laws: the elementary infinite-straight-wire field law
  `B = μ₀ I / (2 π r)` with direction `I-hat × r-hat`, uniformity of the
  applied field, magnetic-field superposition, and calibration of the scalar
  total-field magnitude by the norm of the total vector field;
* previous-part results: none;
* figure/data readouts: the wire and axes, two downward current arrows, the
  positive-`x` applied-field arrow near `c`, labelled points `a`, `b`, `c`,
  `I = 8 A`, `B₀ = 1.50 * 10⁻⁶ T`, and `b = (1,0,0) m`;
* current target conclusions: the total vector at `b`, its exact magnitude,
  agreement at the displayed precision with `2.19 * 10⁻⁶ T`, and the fact
  that choice B is closest among the displayed choices.

No target magnitude or answer-choice correctness claim occurs in the setup or
in any premise structure.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- Electric current has physical dimension charge per time. -/
def electricCurrentDimension : Dimension := C𝓭 * T𝓭⁻¹

/-- Magnetic flux density has the tesla dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Magnetic permeability has dimension `N A⁻² = M L C⁻²`. -/
def magneticPermeabilityDimension : Dimension :=
  M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- A coherent-SI three-dimensional vector readout. -/
abbrev SpatialVector : Type := EuclideanSpace ℝ (Fin 3)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent electric-current magnitude. -/
abbrev ElectricCurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative, unit-independent magnetic-permeability magnitude. -/
abbrev MagneticPermeabilityMagnitude : Type :=
  Dimensionful (WithDim magneticPermeabilityDimension NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def coherentSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Coherent-SI length readout in metres. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  coherentSIReadout length

/-- Coherent-SI current readout in amperes. -/
def currentInAmperes (current : ElectricCurrentMagnitude) : ℝ :=
  coherentSIReadout current

/-- Coherent-SI magnetic-flux-density readout in teslas. -/
def magneticFluxDensityInTeslas
    (fieldMagnitude : MagneticFluxDensityMagnitude) : ℝ :=
  coherentSIReadout fieldMagnitude

/-- Coherent-SI permeability readout in newtons per ampere squared. -/
def magneticPermeabilityInNewtonsPerAmpereSquared
    (permeability : MagneticPermeabilityMagnitude) : ℝ :=
  coherentSIReadout permeability

/-! ## Cartesian geometry and primary-figure vocabulary -/

/-- The three Cartesian axes visible in the primary raster. -/
inductive CoordinateAxis where
  | x
  | y
  | z
  deriving DecidableEq, Fintype, Repr

/-- Standard coherent-SI unit vector associated with a Cartesian axis. -/
def axisVector : CoordinateAxis → SpatialVector
  | .x => EuclideanSpace.single (0 : Fin 3) 1
  | .y => EuclideanSpace.single (1 : Fin 3) 1
  | .z => EuclideanSpace.single (2 : Fin 3) 1

/-- The six oriented Cartesian axis directions used by the setup and figure. -/
inductive AxisDirection where
  | positiveX
  | negativeX
  | positiveY
  | negativeY
  | positiveZ
  | negativeZ
  deriving DecidableEq, Fintype, Repr

/-- Unit vector associated with an oriented Cartesian direction. -/
def axisDirectionVector : AxisDirection → SpatialVector
  | .positiveX => axisVector .x
  | .negativeX => -axisVector .x
  | .positiveY => axisVector .y
  | .negativeY => -axisVector .y
  | .positiveZ => axisVector .z
  | .negativeZ => -axisVector .z

/-- The ordinary right-handed cross product on coherent-SI spatial vectors. -/
def spatialCross (left right : SpatialVector) : SpatialVector :=
  WithLp.toLp 2 (crossProduct left.ofLp right.ofLp)

/-- Interpret a coherent-SI metre coordinate vector as a Physlib space point. -/
def spacePointOfMeters (vector : SpatialVector) : Space 3 :=
  ⟨vector.ofLp⟩

/-- Coordinate plane in which all three labelled observation points lie. -/
inductive CoordinatePlane where
  | xy
  | yz
  | xz
  deriving DecidableEq, Repr

/-- Point labels printed in the supplied image. -/
inductive FigurePointLabel where
  | a
  | b
  | c
  deriving DecidableEq, Fintype, Repr

/-- Idealization used for the current-carrying wire. -/
inductive StraightWireModel where
  | longStraightIdealizedAsInfinite
  | finiteStraight
  deriving DecidableEq, Repr

/-- Literal qualitative content of the primary image `962.png`. -/
structure StraightWireFigure where
  axisShown : CoordinateAxis → Bool
  pointShown : FigurePointLabel → Bool
  wireShown : Bool
  wireAxis : CoordinateAxis
  currentArrowCount : ℕ
  currentArrowDirection : AxisDirection
  uniformFieldArrowShown : Bool
  uniformFieldArrowDirection : AxisDirection
  uniformFieldArrowTailNearPointC : Bool
  pointAOnPositiveZAxis : Bool
  pointBOnPositiveXAxis : Bool
  pointCNearWire : Bool

/-! ## Physical setup and source evidence -/

/-!
Independent physical quantities and fields.  In particular,
`totalFieldMagnitude` is not defined from any answer choice or from the target
closed form.
-/
structure StraightWireFieldSetup where
  currentMagnitude : ElectricCurrentMagnitude
  vacuumPermeability : MagneticPermeabilityMagnitude
  uniformFieldMagnitude : MagneticFluxDensityMagnitude
  observationDistanceFromWire : LengthMagnitude
  wireMagneticField : Electromagnetism.MagneticField 3
  uniformMagneticField : Electromagnetism.MagneticField 3
  totalMagneticField : Electromagnetism.MagneticField 3
  totalFieldMagnitude : MagneticFluxDensityMagnitude
  observationTime : Time
  observationPoint : Space 3
  wireModel : StraightWireModel
  wireAxis : CoordinateAxis
  wirePassesThroughOrigin : Bool
  currentDirection : AxisDirection
  uniformFieldDirection : AxisDirection
  radialDirectionAtObservation : AxisDirection
  observationPlane : CoordinatePlane
  observationPointLabel : FigurePointLabel
  figure : StraightWireFigure

/-- Qualitative geometry and directions stated in the prose. -/
structure MatchesStraightWireScenario
    (setup : StraightWireFieldSetup) : Prop where
  wireIsLongAndStraight :
    setup.wireModel = .longStraightIdealizedAsInfinite
  wireLiesOnYAxis : setup.wireAxis = .y
  wireGoesThroughOrigin : setup.wirePassesThroughOrigin = true
  currentFlowsInNegativeY : setup.currentDirection = .negativeY
  appliedFieldPointsPositiveX :
    setup.uniformFieldDirection = .positiveX
  observationIsRadiallyPositiveX :
    setup.radialDirectionAtObservation = .positiveX
  observationLiesInXZPlane : setup.observationPlane = .xz
  requestedPointIsB : setup.observationPointLabel = .b

/-!
Primary-raster evidence.  It contains directions and label placement only,
with no total-field magnitude or answer-choice assertion.
-/
structure MatchesPrimaryStraightWireFigure
    (setup : StraightWireFieldSetup) : Prop where
  xAxisShown : setup.figure.axisShown .x = true
  yAxisShown : setup.figure.axisShown .y = true
  zAxisShown : setup.figure.axisShown .z = true
  pointAShown : setup.figure.pointShown .a = true
  pointBShown : setup.figure.pointShown .b = true
  pointCShown : setup.figure.pointShown .c = true
  wireIsShown : setup.figure.wireShown = true
  displayedWireFollowsYAxis : setup.figure.wireAxis = .y
  twoCurrentArrows : setup.figure.currentArrowCount = 2
  currentArrowsPointDown :
    setup.figure.currentArrowDirection = .negativeY
  appliedFieldArrowShown : setup.figure.uniformFieldArrowShown = true
  appliedFieldArrowPointsPositiveX :
    setup.figure.uniformFieldArrowDirection = .positiveX
  appliedFieldArrowBeginsNearC :
    setup.figure.uniformFieldArrowTailNearPointC = true
  pointAIsOnPositiveZAxis : setup.figure.pointAOnPositiveZAxis = true
  pointBIsOnPositiveXAxis : setup.figure.pointBOnPositiveXAxis = true
  pointCIsNearWire : setup.figure.pointCNearWire = true

/-!
Numerical source data, recorded as exact coherent-SI readouts.  These fields
state only the problem inputs and the standard value of `μ₀`; they do not
state the requested total field.
-/
structure HasStraightWireProblemData
    (setup : StraightWireFieldSetup) : Prop where
  currentIsEightAmperes :
    currentInAmperes setup.currentMagnitude = 8
  uniformFieldIsOnePointFiveMicroteslas :
    magneticFluxDensityInTeslas setup.uniformFieldMagnitude =
      (3 : ℝ) / 2 * (10 : ℝ) ^ (-6 : ℤ)
  observationDistanceIsOneMeter :
    lengthInMeters setup.observationDistanceFromWire = 1
  vacuumPermeabilitySI :
    magneticPermeabilityInNewtonsPerAmpereSquared
        setup.vacuumPermeability =
      4 * Real.pi * (10 : ℝ) ^ (-7 : ℤ)
  observationCoordinatesInMeters :
    setup.observationPoint = spacePointOfMeters (axisVector .x)

/-- Positivity and nondegeneracy of the physical input magnitudes. -/
structure HasPhysicalStraightWireParameters
    (setup : StraightWireFieldSetup) : Prop where
  currentPositive : 0 < currentInAmperes setup.currentMagnitude
  permeabilityPositive :
    0 < magneticPermeabilityInNewtonsPerAmpereSquared
      setup.vacuumPermeability
  uniformFieldMagnitudePositive :
    0 < magneticFluxDensityInTeslas setup.uniformFieldMagnitude
  observationOffWire :
    0 < lengthInMeters setup.observationDistanceFromWire

/-!
The governing magnetostatic relations.  The first field is the standard
infinite-straight-wire law specialized only to the chosen observation point;
its cross product expresses the right-hand rule.  The remaining fields state
uniformity, superposition, and the meaning of the independent scalar magnitude.

No field asserts the resultant vector, its numerical norm, or a correct answer
choice.
-/
structure SatisfiesStraightWireMagnetostatics
    (setup : StraightWireFieldSetup) : Prop where
  infiniteStraightWireFieldLawAtObservation :
    setup.wireMagneticField setup.observationTime setup.observationPoint =
      (magneticPermeabilityInNewtonsPerAmpereSquared
            setup.vacuumPermeability *
          currentInAmperes setup.currentMagnitude /
          (2 * Real.pi *
            lengthInMeters setup.observationDistanceFromWire)) •
        spatialCross
          (axisDirectionVector setup.currentDirection)
          (axisDirectionVector setup.radialDirectionAtObservation)
  appliedFieldIsUniform : ∀ time position,
    setup.uniformMagneticField time position =
      magneticFluxDensityInTeslas setup.uniformFieldMagnitude •
        axisDirectionVector setup.uniformFieldDirection
  magneticFieldsSuperpose : ∀ time position,
    setup.totalMagneticField time position =
      setup.uniformMagneticField time position +
        setup.wireMagneticField time position
  totalMagnitudeIsVectorNorm :
    magneticFluxDensityInTeslas setup.totalFieldMagnitude =
      ‖setup.totalMagneticField
        setup.observationTime setup.observationPoint‖

/-! ## Multiple-choice metadata and requested result -/

/-- Labels printed beside the four supplied answer values. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Literal answer-choice magnetic-field readout in teslas. -/
def displayedFieldMagnitudeInTeslas : AnswerChoice → ℝ
  | .A => (31 : ℝ) / 10 * (10 : ℝ) ^ (-6 : ℤ)
  | .B => (219 : ℝ) / 100 * (10 : ℝ) ^ (-6 : ℤ)
  | .C => (199 : ℝ) / 100 * (10 : ℝ) ^ (-6 : ℤ)
  | .D => (8 : ℝ) / 5 * (10 : ℝ) ^ (-6 : ℤ)

/-- Dataset answer label retained as metadata, not as a physics premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- Agreement within half of `0.01 μT`, the displayed answer precision. -/
def AgreesAtDisplayedPrecision
    (setup : StraightWireFieldSetup) (choice : AnswerChoice) : Prop :=
  abs (magneticFluxDensityInTeslas setup.totalFieldMagnitude -
      displayedFieldMagnitudeInTeslas choice) ≤
    (1 : ℝ) / 200 * (10 : ℝ) ^ (-6 : ℤ)

/-- A displayed choice is closest to the independent total-field readout. -/
def IsClosestDisplayedAnswer
    (setup : StraightWireFieldSetup) (choice : AnswerChoice) : Prop :=
  ∀ alternative : AnswerChoice,
    abs (magneticFluxDensityInTeslas setup.totalFieldMagnitude -
        displayedFieldMagnitudeInTeslas choice) ≤
      abs (magneticFluxDensityInTeslas setup.totalFieldMagnitude -
        displayedFieldMagnitudeInTeslas alternative)

/-!
Blueprint theorem `thm:physics:phyx_mini_0962:target`.

At point `b`, the uniform contribution is `1.50 μT e_x` and the wire
contribution is `1.60 μT e_z`.  Their vector sum therefore has magnitude
`sqrt 481 / 10 μT`, which rounds to choice B, `2.19 μT`.
-/
theorem problem_phyx_mini_0962
    (setup : StraightWireFieldSetup)
    (_scenario : MatchesStraightWireScenario setup)
    (_figure : MatchesPrimaryStraightWireFigure setup)
    (_data : HasStraightWireProblemData setup)
    (_physical : HasPhysicalStraightWireParameters setup)
    (_laws : SatisfiesStraightWireMagnetostatics setup) :
    setup.totalMagneticField
        setup.observationTime setup.observationPoint =
        ((3 : ℝ) / 2 * (10 : ℝ) ^ (-6 : ℤ)) • axisVector .x +
          ((8 : ℝ) / 5 * (10 : ℝ) ^ (-6 : ℤ)) • axisVector .z ∧
      magneticFluxDensityInTeslas setup.totalFieldMagnitude =
        Real.sqrt 481 / 10 * (10 : ℝ) ^ (-6 : ℤ) ∧
      AgreesAtDisplayedPrecision setup .B ∧
      IsClosestDisplayedAnswer setup .B := by
  have hCross :
      spatialCross (axisDirectionVector .negativeY)
          (axisDirectionVector .positiveX) =
        axisVector .z := by
    ext i
    fin_cases i
    all_goals
      simp [spatialCross, axisDirectionVector, axisVector,
        EuclideanSpace.single, crossProduct]
  have hWire :
      setup.wireMagneticField
          setup.observationTime setup.observationPoint =
        ((8 : ℝ) / 5 * (10 : ℝ) ^ (-6 : ℤ)) • axisVector .z := by
    rw [_laws.infiniteStraightWireFieldLawAtObservation,
      _scenario.currentFlowsInNegativeY,
      _scenario.observationIsRadiallyPositiveX,
      _data.vacuumPermeabilitySI,
      _data.currentIsEightAmperes,
      _data.observationDistanceIsOneMeter,
      hCross]
    congr 1
    field_simp [ne_of_gt Real.pi_pos]
    ring
  have hUniform :
      setup.uniformMagneticField
          setup.observationTime setup.observationPoint =
        ((3 : ℝ) / 2 * (10 : ℝ) ^ (-6 : ℤ)) • axisVector .x := by
    rw [_laws.appliedFieldIsUniform,
      _data.uniformFieldIsOnePointFiveMicroteslas,
      _scenario.appliedFieldPointsPositiveX]
    rfl
  have hTotal :
      setup.totalMagneticField
          setup.observationTime setup.observationPoint =
        ((3 : ℝ) / 2 * (10 : ℝ) ^ (-6 : ℤ)) • axisVector .x +
          ((8 : ℝ) / 5 * (10 : ℝ) ^ (-6 : ℤ)) • axisVector .z := by
    rw [_laws.magneticFieldsSuperpose, hUniform, hWire]
  have hMicroPositive : 0 < (10 : ℝ) ^ (-6 : ℤ) := by
    positivity
  have hSqrtNonnegative : 0 ≤ Real.sqrt 481 :=
    Real.sqrt_nonneg _
  have hSqrtSq : (Real.sqrt 481) ^ 2 = 481 :=
    Real.sq_sqrt (by norm_num)
  have hMagnitude :
      magneticFluxDensityInTeslas setup.totalFieldMagnitude =
        Real.sqrt 481 / 10 * (10 : ℝ) ^ (-6 : ℤ) := by
    rw [_laws.totalMagnitudeIsVectorNorm, hTotal]
    let unitVector : SpatialVector :=
      ((3 : ℝ) / 2) • axisVector .x +
        ((8 : ℝ) / 5) • axisVector .z
    have hUnitNormSq : ‖unitVector‖ ^ 2 = (481 : ℝ) / 100 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [unitVector, axisVector, EuclideanSpace.single,
        Fin.sum_univ_succ]
      norm_num
    have hUnitNorm :
        ‖unitVector‖ = Real.sqrt 481 / 10 := by
      nlinarith [norm_nonneg unitVector]
    have hFactor :
        ((3 : ℝ) / 2 * (10 : ℝ) ^ (-6 : ℤ)) • axisVector .x +
            ((8 : ℝ) / 5 * (10 : ℝ) ^ (-6 : ℤ)) • axisVector .z =
          ((10 : ℝ) ^ (-6 : ℤ)) • unitVector := by
      dsimp [unitVector]
      rw [smul_add, smul_smul, smul_smul]
      congr 1 <;> ring_nf
    rw [hFactor, norm_smul, hUnitNorm, Real.norm_eq_abs,
      abs_of_pos hMicroPositive]
    ring
  have hSqrtLower : (219 : ℝ) / 10 < Real.sqrt 481 := by
    nlinarith
  have hSqrtUpper : Real.sqrt 481 < (439 : ℝ) / 20 := by
    nlinarith
  have hAnswerBDifferenceNonnegative :
      0 ≤ Real.sqrt 481 / 10 - (219 : ℝ) / 100 := by
    linarith
  have hAnswerADifferenceNonpositive :
      Real.sqrt 481 / 10 - (31 : ℝ) / 10 ≤ 0 := by
    linarith
  have hAnswerCDifferenceNonnegative :
      0 ≤ Real.sqrt 481 / 10 - (199 : ℝ) / 100 := by
    linarith
  have hAnswerDDifferenceNonnegative :
      0 ≤ Real.sqrt 481 / 10 - (8 : ℝ) / 5 := by
    linarith
  have hAbsScale (a b : ℝ) :
      abs (a * (10 : ℝ) ^ (-6 : ℤ) -
          b * (10 : ℝ) ^ (-6 : ℤ)) =
        abs (a - b) * (10 : ℝ) ^ (-6 : ℤ) := by
    rw [← sub_mul, abs_mul, abs_of_pos hMicroPositive]
  refine ⟨hTotal, hMagnitude, ?_, ?_⟩
  · rw [AgreesAtDisplayedPrecision, hMagnitude]
    simp only [displayedFieldMagnitudeInTeslas]
    rw [hAbsScale, mul_le_mul_iff_of_pos_right hMicroPositive,
      abs_of_nonneg hAnswerBDifferenceNonnegative]
    linarith
  · rw [IsClosestDisplayedAnswer, hMagnitude]
    intro alternative
    fin_cases alternative
    · simp only [displayedFieldMagnitudeInTeslas]
      rw [hAbsScale, hAbsScale,
        mul_le_mul_iff_of_pos_right hMicroPositive,
        abs_of_nonneg hAnswerBDifferenceNonnegative,
        abs_of_nonpos hAnswerADifferenceNonpositive]
      linarith
    · simp only [displayedFieldMagnitudeInTeslas]
      exact le_rfl
    · simp only [displayedFieldMagnitudeInTeslas]
      rw [hAbsScale, hAbsScale,
        mul_le_mul_iff_of_pos_right hMicroPositive,
        abs_of_nonneg hAnswerBDifferenceNonnegative,
        abs_of_nonneg hAnswerCDifferenceNonnegative]
      linarith
    · simp only [displayedFieldMagnitudeInTeslas]
      rw [hAbsScale, hAbsScale,
        mul_le_mul_iff_of_pos_right hMicroPositive,
        abs_of_nonneg hAnswerBDifferenceNonnegative,
        abs_of_nonneg hAnswerDDifferenceNonnegative]
      linarith

end PhyXMiniProblems.ProblemPhyXMini0962
