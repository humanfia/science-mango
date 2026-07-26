import Mathlib
import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0583

open Dimension MeasureTheory

/-!
# Detection probability in a two-dimensional infinite square corral

The primary image shows a square corral in the positive `xy` quadrant and a
small square labelled `Probe` near its upper-left corner.  The prose calibrates
the edge as `150 pm`, the probe center as `(0.200 L, 0.800 L)`, and both probe
widths as `5.00 pm`.  The requested state is the square-well mode `E_(1,3)`.

Physical lengths are dimensionful Physlib quantities.  Real scalars are used
only for explicitly named picometre-coordinate readouts, inverse-picometre
wave-amplitude readouts, dimensionless probabilities, and answer displays.

Assumption/target split:

* governing laws: the normalized two-dimensional infinite-square-well mode
  formula and Born's position-probability law;
* previous-part results: none;
* figure/data readouts: square infinite corral, electron, `L = 150 pm`, probe
  center `(L/5, 4L/5)`, probe widths `5 pm`, and mode numbers `(1,3)`;
* target conclusions: the probe probability rounds to `1.4 * 10^(-3)` and
  therefore selects answer choice C.
-/

/-! ## Dimensionful lengths and coordinate readouts -/

/-- A nonnegative physical length, independent of the chosen unit system. -/
abbrev LengthMagnitude : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical position along one Cartesian axis. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Read a nonnegative physical length in a selected Physlib length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthMagnitude) : ℝ :=
  ((length ({UnitChoices.SI with length := unit} : UnitChoices)).val : ℝ)

/-- Read a signed Cartesian position in a selected Physlib length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (position : SignedLengthQuantity) : ℝ :=
  (position ({UnitChoices.SI with length := unit} : UnitChoices)).val

/-- Picometre readout of a physical length. -/
def lengthInPicometers (length : LengthMagnitude) : ℝ :=
  lengthReadout LengthUnit.picometers length

/-- Picometre readout of a signed Cartesian position. -/
def signedLengthInPicometers (position : SignedLengthQuantity) : ℝ :=
  signedLengthReadout LengthUnit.picometers position

/-! ## Physical setup and primary-image vocabulary -/

/-- The particle species named in the problem. -/
inductive QuantumParticleKind where
  | electron
  deriving DecidableEq, Repr

/-- The idealized confinement represented by the blue square boundary. -/
inductive CorralConfinement where
  | twoDimensionalInfiniteSquare
  deriving DecidableEq, Repr

/-- The two Cartesian labels printed on the image axes. -/
inductive CartesianAxisLabel where
  | x
  | y
  deriving DecidableEq, Repr

/-- The geometric shape of the confining boundary and of the probe. -/
inductive FigureShape where
  | square
  deriving DecidableEq, Repr

/-- Quantum numbers in the `x` and `y` directions for a square-corral mode. -/
structure InfiniteSquareCorralMode where
  xQuantumNumber : ℕ
  yQuantumNumber : ℕ

/-- A physical square position probe with a center and full widths. -/
structure SquarePositionProbe where
  centerX : SignedLengthQuantity
  centerY : SignedLengthQuantity
  xWidth : LengthMagnitude
  yWidth : LengthMagnitude

/-- Qualitative labels and shapes visible in the supplied image. -/
structure SquareCorralFigure where
  horizontalAxisLabel : CartesianAxisLabel
  verticalAxisLabel : CartesianAxisLabel
  corralBoundaryShape : FigureShape
  probeShape : FigureShape
  probeLabelIsPresent : Bool
  corralDrawnInPositiveQuadrant : Bool

/-!
The electron experiment, including a representative wavefunction on numerical
picometre coordinates and its genuine Physlib two-dimensional Hilbert-space
state.  The dependent fields ensure that the representative is square
integrable and denotes `stateVector`; the physical probability observable is a
separate normalized measure until Born's law is imposed below.
-/
structure SquareCorralExperiment where
  particleKind : QuantumParticleKind
  confinement : CorralConfinement
  edgeLength : LengthMagnitude
  probe : SquarePositionProbe
  mode : InfiniteSquareCorralMode
  figure : SquareCorralFigure
  waveAmplitudePerPicometer : Space 2 → ℂ
  waveAmplitudeMemLp :
    MeasureTheory.MemLp waveAmplitudePerPicometer 2
      (MeasureTheory.volume : MeasureTheory.Measure (Space 2))
  stateVector : QuantumMechanics.SpaceDHilbertSpace 2
  stateVectorIsRepresentative :
    stateVector = MeasureTheory.MemLp.toLp
      waveAmplitudePerPicometer waveAmplitudeMemLp
  positionProbability : MeasureTheory.ProbabilityMeasure (Space 2)

/-! ## Corral, probe region, and mode amplitude -/

/-- Numerical `x` coordinate in picometres. -/
def xPicometers (point : Space 2) : ℝ := point 0

/-- Numerical `y` coordinate in picometres. -/
def yPicometers (point : Space 2) : ℝ := point 1

/-- The closed square occupied by a corral whose edge readout is `L`. -/
def squareCorralRegionPicometers (edgePicometers : ℝ) : Set (Space 2) :=
  {point | 0 ≤ xPicometers point ∧ xPicometers point ≤ edgePicometers ∧
    0 ≤ yPicometers point ∧ yPicometers point ≤ edgePicometers}

/-- The closed rectangular region covered by the physical square probe. -/
def squareProbeRegionPicometers (probe : SquarePositionProbe) : Set (Space 2) :=
  let centerX := signedLengthInPicometers probe.centerX
  let centerY := signedLengthInPicometers probe.centerY
  let xWidth := lengthInPicometers probe.xWidth
  let yWidth := lengthInPicometers probe.yWidth
  {point |
    centerX - xWidth / 2 ≤ xPicometers point ∧
      xPicometers point ≤ centerX + xWidth / 2 ∧
    centerY - yWidth / 2 ≤ yPicometers point ∧
      yPicometers point ≤ centerY + yWidth / 2}

/-!
The normalized stationary wave-amplitude representative for an infinite square
corral in numerical picometre coordinates.  Inside the box it is
`(2/L) sin(n_x π x/L) sin(n_y π y/L)` and it vanishes outside.  This is a
general governing formula; it contains no requested probability or answer.
-/
def infiniteSquareCorralModeAmplitudePerPicometer
    (edgePicometers : ℝ)
    (mode : InfiniteSquareCorralMode)
    (point : Space 2) : ℂ := by
  classical
  exact if point ∈ squareCorralRegionPicometers edgePicometers then
    (((2 / edgePicometers) *
      Real.sin ((mode.xQuantumNumber : ℝ) * Real.pi *
        xPicometers point / edgePicometers) *
      Real.sin ((mode.yQuantumNumber : ℝ) * Real.pi *
        yPicometers point / edgePicometers) : ℝ) : ℂ)
  else
    0

/-! ## Governing laws and problem readouts -/

/-!
The infinite-corral eigenstate law and Born's rule.  The with-density equation
uses two-dimensional Lebesgue volume on numerical picometre coordinates, so
`Complex.normSq` has the reciprocal-square-picometre density role.
-/
structure SatisfiesInfiniteSquareCorralPhysics
    (experiment : SquareCorralExperiment) : Prop where
  edgeLengthIsPositive : 0 < lengthInPicometers experiment.edgeLength
  xQuantumNumberIsPositive : 0 < experiment.mode.xQuantumNumber
  yQuantumNumberIsPositive : 0 < experiment.mode.yQuantumNumber
  waveAmplitudeIsInfiniteCorralMode : ∀ point : Space 2,
    experiment.waveAmplitudePerPicometer point =
      infiniteSquareCorralModeAmplitudePerPicometer
        (lengthInPicometers experiment.edgeLength) experiment.mode point
  bornPositionLaw :
    experiment.positionProbability.toMeasure =
      (MeasureTheory.volume : MeasureTheory.Measure (Space 2)).withDensity
        (fun point ↦ ENNReal.ofReal
          (Complex.normSq (experiment.waveAmplitudePerPicometer point)))

/-!
Exact prose data and qualitative readouts from `583.png`.  These fields specify
the apparatus and the `E_(1,3)` state, but contain no detection probability,
rounding claim, or answer-choice value.
-/
structure MatchesProblemStatementAndFigure
    (experiment : SquareCorralExperiment) : Prop where
  particleIsElectron : experiment.particleKind = .electron
  confinementIsInfiniteSquareCorral :
    experiment.confinement = .twoDimensionalInfiniteSquare
  edgeLengthIs150Picometers :
    lengthInPicometers experiment.edgeLength = 150
  probeCenterXIsOneFifthEdge :
    signedLengthInPicometers experiment.probe.centerX =
      (1 : ℝ) / 5 * lengthInPicometers experiment.edgeLength
  probeCenterYIsFourFifthsEdge :
    signedLengthInPicometers experiment.probe.centerY =
      (4 : ℝ) / 5 * lengthInPicometers experiment.edgeLength
  probeXWidthIs5Picometers :
    lengthInPicometers experiment.probe.xWidth = 5
  probeYWidthIs5Picometers :
    lengthInPicometers experiment.probe.yWidth = 5
  stateHasXQuantumNumberOne : experiment.mode.xQuantumNumber = 1
  stateHasYQuantumNumberThree : experiment.mode.yQuantumNumber = 3
  horizontalAxisIsX : experiment.figure.horizontalAxisLabel = .x
  verticalAxisIsY : experiment.figure.verticalAxisLabel = .y
  corralBoundaryIsSquare : experiment.figure.corralBoundaryShape = .square
  probeIsSquare : experiment.figure.probeShape = .square
  imageLabelsProbe : experiment.figure.probeLabelIsPresent = true
  imagePlacesCorralInPositiveQuadrant :
    experiment.figure.corralDrawnInPositiveQuadrant = true

/-! ## Detection probability, answer choices, and target -/

/-- Dimensionless Born probability that the electron lies in the probe region. -/
def detectionProbability (experiment : SquareCorralExperiment) : ℝ :=
  (experiment.positionProbability.toMeasure
    (squareProbeRegionPicometers experiment.probe)).toReal

/-- The four labels displayed beside the multiple-choice probabilities. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Dimensionless probability printed for each answer choice. -/
def AnswerChoice.displayedProbability : AnswerChoice → ℝ
  | .A => 14 / 1000
  | .B => 28 / 10000
  | .C => 14 / 10000
  | .D => 7 / 10000

/-- Dataset metadata records C; this name is never used as a premise. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
Rounding to the nearest `10^(-4)`, the precision of the displayed value
`1.4 * 10^(-3)`.  The lower endpoint is included and the upper excluded.
-/
def RoundsToNearestTenThousandth
    (probability displayedValue : ℝ) : Prop :=
  displayedValue - 1 / 20000 ≤ probability ∧
    probability < displayedValue + 1 / 20000

/-- A choice matches when the modeled probability rounds to its display. -/
def MatchesAnswerChoice
    (experiment : SquareCorralExperiment) (choice : AnswerChoice) : Prop :=
  RoundsToNearestTenThousandth
    (detectionProbability experiment) choice.displayedProbability

/-!
For the stated square corral, probe, and `E_(1,3)` eigenstate, Born's rule gives
a probability which rounds to `1.4 * 10^(-3)`.
-/
lemma detectionProbability_rounds_to_one_point_four_times_ten_neg_three
    (experiment : SquareCorralExperiment)
    (hPhysics : SatisfiesInfiniteSquareCorralPhysics experiment)
    (hReadouts : MatchesProblemStatementAndFigure experiment) :
    RoundsToNearestTenThousandth
      (detectionProbability experiment) ((14 : ℝ) / 10000) := by
  have hEdge :
      lengthInPicometers experiment.edgeLength = 150 :=
    hReadouts.edgeLengthIs150Picometers
  have hCenterX :
      signedLengthInPicometers experiment.probe.centerX = 30 := by
    rw [hReadouts.probeCenterXIsOneFifthEdge, hEdge]
    norm_num
  have hCenterY :
      signedLengthInPicometers experiment.probe.centerY = 120 := by
    rw [hReadouts.probeCenterYIsFourFifthsEdge, hEdge]
    norm_num
  have hWidthX :
      lengthInPicometers experiment.probe.xWidth = 5 :=
    hReadouts.probeXWidthIs5Picometers
  have hWidthY :
      lengthInPicometers experiment.probe.yWidth = 5 :=
    hReadouts.probeYWidthIs5Picometers
  let rectangle : Set (ℝ × ℝ) :=
    Set.Icc ((55 : ℝ) / 2) ((65 : ℝ) / 2) ×ˢ
      Set.Icc ((235 : ℝ) / 2) ((245 : ℝ) / 2)
  let coordinateEquiv : Space 2 ≃ᵐ ℝ × ℝ :=
    (((Space.basis :
        OrthonormalBasis (Fin 2) ℝ (Space 2)).measurableEquiv.trans
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm).trans
        MeasurableEquiv.finTwoArrow)
  have hCoordinateEquivApply (point : Space 2) :
      coordinateEquiv point = (point 0, point 1) := by
    rfl
  have hCoordinateEquivSymmApplyZero (point : ℝ × ℝ) :
      coordinateEquiv.symm point 0 = point.1 := by
    have h := congrArg Prod.fst (coordinateEquiv.apply_symm_apply point)
    rw [hCoordinateEquivApply] at h
    exact h
  have hCoordinateEquivSymmApplyOne (point : ℝ × ℝ) :
      coordinateEquiv.symm point 1 = point.2 := by
    have h := congrArg Prod.snd (coordinateEquiv.apply_symm_apply point)
    rw [hCoordinateEquivApply] at h
    exact h
  have hCoordinateEquivMeasurePreserving :
      MeasureTheory.MeasurePreserving coordinateEquiv
        (MeasureTheory.volume : MeasureTheory.Measure (Space 2))
        (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) := by
    exact
      (MeasureTheory.volume_preserving_finTwoArrow ℝ).comp
        ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp
          (Fin 2)).comp
            (OrthonormalBasis.measurePreserving_measurableEquiv
              (Space.basis :
                OrthonormalBasis (Fin 2) ℝ (Space 2))))
  have hProbeRegion :
      squareProbeRegionPicometers experiment.probe =
        coordinateEquiv ⁻¹' rectangle := by
    ext point
    simp [rectangle, squareProbeRegionPicometers, hCenterX, hCenterY,
      hWidthX, hWidthY, xPicometers, yPicometers,
      hCoordinateEquivApply]
    constructor
    · rintro ⟨hxLower, hxUpper, hyLower, hyUpper⟩
      exact
        ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · rintro ⟨⟨hxLower, hyLower⟩, hxUpper, hyUpper⟩
      exact
        ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hRectangleMeasurable : MeasurableSet rectangle := by
    exact measurableSet_Icc.prod measurableSet_Icc
  have hProbeMeasurable :
      MeasurableSet (squareProbeRegionPicometers experiment.probe) := by
    rw [hProbeRegion]
    exact hRectangleMeasurable.preimage
      coordinateEquiv.measurable
  have hAmplitudeAEStronglyMeasurable :
      AEStronglyMeasurable experiment.waveAmplitudePerPicometer
        ((MeasureTheory.volume : MeasureTheory.Measure (Space 2)).restrict
          (squareProbeRegionPicometers experiment.probe)) :=
    experiment.waveAmplitudeMemLp.aestronglyMeasurable.mono_measure
      Measure.restrict_le_self
  have hDensityAEMeasurable :
      AEMeasurable
        (fun point : Space 2 ↦
          ENNReal.ofReal
            (Complex.normSq (experiment.waveAmplitudePerPicometer point)))
        ((MeasureTheory.volume : MeasureTheory.Measure (Space 2)).restrict
          (squareProbeRegionPicometers experiment.probe)) := by
    exact
      (Complex.continuous_normSq.comp_aestronglyMeasurable
        hAmplitudeAEStronglyMeasurable).aemeasurable.ennreal_ofReal
  have hProbabilityIntegral :
      detectionProbability experiment =
        ∫ point in squareProbeRegionPicometers experiment.probe,
          Complex.normSq (experiment.waveAmplitudePerPicometer point) := by
    unfold detectionProbability
    rw [hPhysics.bornPositionLaw,
      MeasureTheory.withDensity_apply _ hProbeMeasurable]
    calc
      (∫⁻ point in squareProbeRegionPicometers experiment.probe,
          ENNReal.ofReal
            (Complex.normSq
              (experiment.waveAmplitudePerPicometer point))).toReal =
          ∫ point in squareProbeRegionPicometers experiment.probe,
            (ENNReal.ofReal
              (Complex.normSq
                (experiment.waveAmplitudePerPicometer point))).toReal := by
            symm
            exact MeasureTheory.integral_toReal hDensityAEMeasurable (by simp)
      _ = ∫ point in squareProbeRegionPicometers experiment.probe,
          Complex.normSq (experiment.waveAmplitudePerPicometer point) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards
            intro point
            exact ENNReal.toReal_ofReal
              (Complex.normSq_nonneg
                (experiment.waveAmplitudePerPicometer point))
  rw [hProbabilityIntegral]
  have hSetIntegralAsProduct :
      (∫ point in squareProbeRegionPicometers experiment.probe,
          Complex.normSq (experiment.waveAmplitudePerPicometer point)) =
        ∫ point in rectangle,
          ((4 : ℝ) / 22500) *
            (Real.sin (Real.pi * point.1 / 150) ^ 2 *
              Real.sin (3 * Real.pi * point.2 / 150) ^ 2) := by
    calc
      (∫ point in squareProbeRegionPicometers experiment.probe,
          Complex.normSq (experiment.waveAmplitudePerPicometer point)) =
          ∫ point in
              coordinateEquiv ⁻¹' rectangle,
            Complex.normSq
              (experiment.waveAmplitudePerPicometer point) := by
                rw [hProbeRegion]
      _ = ∫ point in rectangle,
          Complex.normSq
            (experiment.waveAmplitudePerPicometer
              (coordinateEquiv.symm point)) := by
            simpa using
              (hCoordinateEquivMeasurePreserving.setIntegral_preimage_emb
                  coordinateEquiv.measurableEmbedding
                  (fun point : ℝ × ℝ ↦
                    Complex.normSq
                      (experiment.waveAmplitudePerPicometer
                        (coordinateEquiv.symm point)))
                  rectangle)
      _ = ∫ point in rectangle,
          ((4 : ℝ) / 22500) *
            (Real.sin (Real.pi * point.1 / 150) ^ 2 *
              Real.sin (3 * Real.pi * point.2 / 150) ^ 2) := by
            apply MeasureTheory.setIntegral_congr_fun hRectangleMeasurable
            intro point hpoint
            have hInside :
                coordinateEquiv.symm point ∈
                    squareCorralRegionPicometers 150 := by
              rcases hpoint with ⟨hx, hy⟩
              simp only [squareCorralRegionPicometers, Set.mem_setOf_eq,
                xPicometers, yPicometers,
                hCoordinateEquivSymmApplyZero,
                hCoordinateEquivSymmApplyOne]
              change
                0 ≤ point.1 ∧ point.1 ≤ 150 ∧
                  0 ≤ point.2 ∧ point.2 ≤ 150
              norm_num [rectangle] at hx hy ⊢
              exact
                ⟨by linarith [hx.1], by linarith [hx.2],
                  by linarith [hy.1], by linarith [hy.2]⟩
            change
              Complex.normSq
                  (experiment.waveAmplitudePerPicometer
                    (coordinateEquiv.symm point)) =
                (4 / 22500 : ℝ) *
                  (Real.sin (Real.pi * point.1 / 150) ^ 2 *
                    Real.sin (3 * Real.pi * point.2 / 150) ^ 2)
            rw [hPhysics.waveAmplitudeIsInfiniteCorralMode]
            simp only [infiniteSquareCorralModeAmplitudePerPicometer, hEdge,
              hReadouts.stateHasXQuantumNumberOne,
              hReadouts.stateHasYQuantumNumberThree, hInside, if_pos,
              Complex.normSq_ofReal, xPicometers, yPicometers,
              hCoordinateEquivSymmApplyZero,
              hCoordinateEquivSymmApplyOne]
            norm_num
            ring
  rw [hSetIntegralAsProduct]
  have hFactorizedIntegral :
      (∫ point in rectangle,
          ((4 : ℝ) / 22500) *
            (Real.sin (Real.pi * point.1 / 150) ^ 2 *
              Real.sin (3 * Real.pi * point.2 / 150) ^ 2)) =
        ((4 : ℝ) / 22500) *
          ((∫ x in Set.Icc ((55 : ℝ) / 2) ((65 : ℝ) / 2),
              Real.sin (Real.pi * x / 150) ^ 2) *
            (∫ y in Set.Icc ((235 : ℝ) / 2) ((245 : ℝ) / 2),
              Real.sin (3 * Real.pi * y / 150) ^ 2)) := by
    rw [MeasureTheory.integral_const_mul]
    simp only [rectangle]
    change
      (4 / 22500 : ℝ) *
          (∫ point in
              Set.Icc ((55 : ℝ) / 2) ((65 : ℝ) / 2) ×ˢ
                Set.Icc ((235 : ℝ) / 2) ((245 : ℝ) / 2),
            Real.sin (Real.pi * point.1 / 150) ^ 2 *
              Real.sin (3 * Real.pi * point.2 / 150) ^ 2
            ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
              (MeasureTheory.volume : MeasureTheory.Measure ℝ))) =
        (4 / 22500 : ℝ) *
          ((∫ x in Set.Icc ((55 : ℝ) / 2) ((65 : ℝ) / 2),
              Real.sin (Real.pi * x / 150) ^ 2) *
            (∫ y in Set.Icc ((235 : ℝ) / 2) ((245 : ℝ) / 2),
              Real.sin (3 * Real.pi * y / 150) ^ 2))
    exact congrArg (fun value : ℝ ↦ (4 / 22500 : ℝ) * value)
      (MeasureTheory.setIntegral_prod_mul
        (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
        (ν := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
        (fun x : ℝ ↦ Real.sin (Real.pi * x / 150) ^ 2)
        (fun y : ℝ ↦ Real.sin (3 * Real.pi * y / 150) ^ 2)
        (Set.Icc ((55 : ℝ) / 2) ((65 : ℝ) / 2))
        (Set.Icc ((235 : ℝ) / 2) ((245 : ℝ) / 2)))
  rw [hFactorizedIntegral]
  have hWaveNumberX : Real.pi / 150 ≠ 0 := by
    positivity
  have hXIntegral :
      (∫ x in Set.Icc ((55 : ℝ) / 2) ((65 : ℝ) / 2),
          Real.sin (Real.pi * x / 150) ^ 2) =
        (5 : ℝ) / 2 -
          75 / Real.pi * Real.cos (2 * Real.pi / 5) *
            Real.sin (Real.pi / 30) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num)]
    simp_rw [show ∀ x : ℝ,
      Real.pi * x / 150 = (Real.pi / 150) * x by
        intro x
        ring]
    rw [intervalIntegral.integral_comp_mul_left
      (fun y : ℝ ↦ Real.sin y ^ 2) hWaveNumberX]
    rw [integral_sin_sq]
    have hTrigX :
        Real.sin (11 * Real.pi / 60) * Real.cos (11 * Real.pi / 60) -
            Real.sin (13 * Real.pi / 60) * Real.cos (13 * Real.pi / 60) =
          -Real.cos (2 * Real.pi / 5) * Real.sin (Real.pi / 30) := by
      rw [show
          Real.sin (11 * Real.pi / 60) *
                Real.cos (11 * Real.pi / 60) =
              Real.sin (11 * Real.pi / 30) / 2 by
            rw [show 11 * Real.pi / 30 =
              2 * (11 * Real.pi / 60) by ring, Real.sin_two_mul]
            ring,
        show
          Real.sin (13 * Real.pi / 60) *
                Real.cos (13 * Real.pi / 60) =
              Real.sin (13 * Real.pi / 30) / 2 by
            rw [show 13 * Real.pi / 30 =
              2 * (13 * Real.pi / 60) by ring, Real.sin_two_mul]
            ring]
      rw [← sub_div]
      rw [Real.sin_sub_sin]
      rw [show (11 * Real.pi / 30 + 13 * Real.pi / 30) / 2 =
          2 * Real.pi / 5 by ring,
        show (11 * Real.pi / 30 - 13 * Real.pi / 30) / 2 =
          -(Real.pi / 30) by ring,
        Real.sin_neg]
      ring
    norm_num only [inv_smul_eq_iff₀ hWaveNumberX]
    rw [show Real.pi / 150 * (55 / 2) = 11 * Real.pi / 60 by ring,
      show Real.pi / 150 * (65 / 2) = 13 * Real.pi / 60 by ring,
      hTrigX]
    simp only [smul_eq_mul]
    field_simp [Real.pi_ne_zero]
    ring
  have hSqrtFiveSquared : Real.sqrt 5 ^ 2 = 5 := by
    exact Real.sq_sqrt (by norm_num)
  have hCosTwoPiFifths :
      Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
    rw [show 2 * Real.pi / 5 = 2 * (Real.pi / 5) by ring,
      Real.cos_two_mul, Real.cos_pi_div_five]
    nlinarith
  have hSinThreePiTenths :
      Real.sin (3 * Real.pi / 10) = (1 + Real.sqrt 5) / 4 := by
    rw [← Real.cos_pi_div_two_sub]
    rw [show Real.pi / 2 - 3 * Real.pi / 10 =
      Real.pi / 5 by ring, Real.cos_pi_div_five]
  have hSinPiTenth :
      Real.sin (Real.pi / 10) = (Real.sqrt 5 - 1) / 4 := by
    rw [← Real.cos_pi_div_two_sub]
    rw [show Real.pi / 2 - Real.pi / 10 =
      2 * Real.pi / 5 by ring, hCosTwoPiFifths]
  have hWaveNumberY : Real.pi / 50 ≠ 0 := by
    positivity
  have hYIntegral :
      (∫ y in Set.Icc ((235 : ℝ) / 2) ((245 : ℝ) / 2),
          Real.sin (3 * Real.pi * y / 150) ^ 2) =
        (5 : ℝ) / 2 + 25 / (4 * Real.pi) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num)]
    simp_rw [show ∀ y : ℝ,
      3 * Real.pi * y / 150 = (Real.pi / 50) * y by
        intro y
        ring]
    rw [intervalIntegral.integral_comp_mul_left
      (fun y : ℝ ↦ Real.sin y ^ 2) hWaveNumberY]
    rw [integral_sin_sq]
    have hTrigY :
        Real.sin (47 * Real.pi / 20) * Real.cos (47 * Real.pi / 20) -
            Real.sin (49 * Real.pi / 20) * Real.cos (49 * Real.pi / 20) =
          (1 : ℝ) / 4 := by
      rw [show
          Real.sin (47 * Real.pi / 20) *
                Real.cos (47 * Real.pi / 20) =
              Real.sin (47 * Real.pi / 10) / 2 by
            rw [show 47 * Real.pi / 10 =
              2 * (47 * Real.pi / 20) by ring, Real.sin_two_mul]
            ring,
        show
          Real.sin (49 * Real.pi / 20) *
                Real.cos (49 * Real.pi / 20) =
              Real.sin (49 * Real.pi / 10) / 2 by
            rw [show 49 * Real.pi / 10 =
              2 * (49 * Real.pi / 20) by ring, Real.sin_two_mul]
            ring]
      have hPeriod47 :
          Real.sin (47 * Real.pi / 10) =
            Real.sin (7 * Real.pi / 10) := by
        convert
          Real.sin_add_nat_mul_two_pi (7 * Real.pi / 10) 2 using 1 <;>
            ring
      have hPeriod49 :
          Real.sin (49 * Real.pi / 10) =
            Real.sin (9 * Real.pi / 10) := by
        convert
          Real.sin_add_nat_mul_two_pi (9 * Real.pi / 10) 2 using 1 <;>
            ring
      rw [hPeriod47, hPeriod49]
      rw [show 7 * Real.pi / 10 =
          Real.pi - 3 * Real.pi / 10 by ring,
        show 9 * Real.pi / 10 =
          Real.pi - Real.pi / 10 by ring,
        Real.sin_pi_sub, Real.sin_pi_sub,
        hSinThreePiTenths, hSinPiTenth]
      ring
    norm_num only [inv_smul_eq_iff₀ hWaveNumberY]
    rw [show Real.pi / 50 * (235 / 2) = 47 * Real.pi / 20 by ring,
      show Real.pi / 50 * (245 / 2) = 49 * Real.pi / 20 by ring,
      hTrigY]
    simp only [smul_eq_mul]
    field_simp [Real.pi_ne_zero]
    ring
  rw [hXIntegral, hYIntegral]
  let xFactor : ℝ :=
    (5 : ℝ) / 2 -
      75 / Real.pi * Real.cos (2 * Real.pi / 5) *
        Real.sin (Real.pi / 30)
  let yFactor : ℝ := (5 : ℝ) / 2 + 25 / (4 * Real.pi)
  change
    RoundsToNearestTenThousandth
      ((4 / 22500 : ℝ) * (xFactor * yFactor)) (14 / 10000)
  have hSqrtFiveLower : (11 : ℝ) / 5 < Real.sqrt 5 := by
    have hSqrtNonnegative : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    nlinarith only [hSqrtNonnegative, hSqrtFiveSquared]
  have hSqrtFiveUpper : Real.sqrt 5 < (56 : ℝ) / 25 := by
    have hSqrtNonnegative : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    nlinarith only [hSqrtNonnegative, hSqrtFiveSquared]
  have hCosLower : (3 : ℝ) / 10 < Real.cos (2 * Real.pi / 5) := by
    rw [hCosTwoPiFifths]
    linarith only [hSqrtFiveLower]
  have hCosUpper : Real.cos (2 * Real.pi / 5) < (31 : ℝ) / 100 := by
    rw [hCosTwoPiFifths]
    linarith only [hSqrtFiveUpper]
  have hSmallAnglePositive : 0 < Real.pi / 30 := by
    positivity
  have hSmallAngleUpper : Real.pi / 30 < (21 : ℝ) / 200 := by
    linarith only [Real.pi_lt_d2]
  have hSinUpper : Real.sin (Real.pi / 30) < (21 : ℝ) / 200 :=
    (Real.sin_lt hSmallAnglePositive).trans hSmallAngleUpper
  have hSmallAngleLower : (157 : ℝ) / 1500 < Real.pi / 30 := by
    linarith only [Real.pi_gt_d2]
  have hSmallAngleCubeUpper :
      (Real.pi / 30) ^ 3 < ((21 : ℝ) / 200) ^ 3 := by
    gcongr
  have hSinLower : (1 : ℝ) / 10 < Real.sin (Real.pi / 30) := by
    have hPolynomialLower :
        (1 : ℝ) / 10 <
          Real.pi / 30 - (Real.pi / 30) ^ 3 / 4 := by
      nlinarith only [hSmallAngleLower, hSmallAngleCubeUpper]
    exact hPolynomialLower.trans
      (Real.sin_gt_sub_cube hSmallAnglePositive
        (by linarith only [hSmallAngleUpper]))
  have hCoefficientPositive : 0 < 75 / Real.pi := by
    positivity
  have hCoefficientLower : (500 : ℝ) / 21 < 75 / Real.pi := by
    apply (lt_div_iff₀ Real.pi_pos).2
    nlinarith only [Real.pi_lt_d2]
  have hCoefficientUpper : 75 / Real.pi < (24 : ℝ) := by
    apply (div_lt_iff₀ Real.pi_pos).2
    nlinarith only [Real.pi_gt_d2]
  have hSubtractedTermUpper :
      75 / Real.pi * Real.cos (2 * Real.pi / 5) *
          Real.sin (Real.pi / 30) <
        (24 : ℝ) * ((31 : ℝ) / 100) * ((21 : ℝ) / 200) := by
    gcongr
  have hSubtractedTermLessThanFourFifths :
      75 / Real.pi * Real.cos (2 * Real.pi / 5) *
          Real.sin (Real.pi / 30) <
        (4 : ℝ) / 5 := by
    exact hSubtractedTermUpper.trans (by norm_num)
  have hSubtractedTermLower :
      (500 : ℝ) / 21 * ((3 : ℝ) / 10) * ((1 : ℝ) / 10) <
        75 / Real.pi * Real.cos (2 * Real.pi / 5) *
          Real.sin (Real.pi / 30) := by
    gcongr
  have hSubtractedTermGreaterThanFiveSevenths :
      (5 : ℝ) / 7 <
        75 / Real.pi * Real.cos (2 * Real.pi / 5) *
          Real.sin (Real.pi / 30) := by
    convert hSubtractedTermLower using 1 <;> norm_num
  have hXFactorLower : (17 : ℝ) / 10 < xFactor := by
    dsimp [xFactor]
    linarith only [hSubtractedTermLessThanFourFifths]
  have hXFactorUpper : xFactor < (25 : ℝ) / 14 := by
    dsimp [xFactor]
    linarith only [hSubtractedTermGreaterThanFiveSevenths]
  have hYFractionLower : (125 : ℝ) / 63 < 25 / (4 * Real.pi) := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * Real.pi)).2
    nlinarith only [Real.pi_lt_d2]
  have hYFractionUpper : 25 / (4 * Real.pi) < (2 : ℝ) := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * Real.pi)).2
    nlinarith only [Real.pi_gt_d2]
  have hYFactorLower : (112 : ℝ) / 25 < yFactor := by
    dsimp [yFactor]
    nlinarith only [hYFractionLower]
  have hYFactorUpper : yFactor < (9 : ℝ) / 2 := by
    dsimp [yFactor]
    linarith only [hYFractionUpper]
  have hProductLower :
      (243 : ℝ) / 32 < xFactor * yFactor := by
    calc
      (243 : ℝ) / 32 <
          ((17 : ℝ) / 10) * ((112 : ℝ) / 25) := by norm_num
      _ < xFactor * yFactor := by
        gcongr
  have hProductUpper :
      xFactor * yFactor < (261 : ℝ) / 32 := by
    calc
      xFactor * yFactor <
          ((25 : ℝ) / 14) * ((9 : ℝ) / 2) := by
        gcongr
      _ < (261 : ℝ) / 32 := by norm_num
  constructor
  · norm_num
    nlinarith only [hProductLower]
  · norm_num
    nlinarith only [hProductUpper]

/-!
The recorded answer is choice C.

This declaration corresponds to blueprint label
`thm:physics:phyx_mini_0583:target`.
-/
theorem problem_phyx_mini_0583
    (experiment : SquareCorralExperiment)
    (hPhysics : SatisfiesInfiniteSquareCorralPhysics experiment)
    (hReadouts : MatchesProblemStatementAndFigure experiment) :
    MatchesAnswerChoice experiment .C := by
  simpa [MatchesAnswerChoice, AnswerChoice.displayedProbability] using
    detectionProbability_rounds_to_one_point_four_times_ten_neg_three
      experiment hPhysics hReadouts

end PhyXMiniProblems.ProblemPhyXMini0583
