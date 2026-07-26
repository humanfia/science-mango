import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0936

open Dimension

/-!
# Induced emf in a tilted circular coil

A circular `500`-turn coil of radius `4.00 cm` lies in a spatially uniform
magnetic field.  The field points from the north pole to the south pole and
makes an angle of `60 degrees` with the plane of the coil (hence `30 degrees`
with the displayed positive area normal).  Its magnitude decreases at
`0.200 T/s`.

Physical lengths, areas, magnetic quantities, fluxes, and emfs are represented
by Physlib `Dimensionful` quantities.  Real numbers occur only as coherent-SI
readouts, dimensionless angle representatives in radians, and displayed
answer-choice values.  The applied field additionally retains Physlib's
spacetime-dependent vector-field type.

Assumption/target split:

* governing laws: circular area, calibration of the uniform vector field,
  uniform-field flux and flux-rate formulas, Faraday's law, and the generic
  sign convention expressing Lenz's law;
* previous-part results: none;
* figure/data readouts: `500` turns, radius `4.00 cm`, field rate
  `-0.200 T/s`, the `60 degree` plane/field and `30 degree` normal/field
  angles, north on the left, south on the right, and field arrows from left
  to right;
* current target conclusions: the exact induced-emf magnitude, its unique
  nearest displayed value B (`0.435 V`), and its counterclockwise sense when
  viewed from the tip of the displayed positive area normal.

None of the three target conclusions is a setup field or premise.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The dimension `M T^-1 C^-1` of magnetic flux density (tesla). -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `M T^-2 C^-1` of a magnetic-flux-density rate. -/
def magneticFluxDensityRateDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `M L^2 T^-1 C^-1` of magnetic flux (weber). -/
def magneticFluxDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `M L^2 T^-2 C^-1` shared by flux rate and emf (volt). -/
def electromotiveForceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical area. -/
abbrev AreaMagnitude : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭) NNReal)

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A signed, unit-independent rate of change of magnetic flux density. -/
abbrev SignedMagneticFluxDensityRate : Type :=
  Dimensionful (WithDim magneticFluxDensityRateDimension ℝ)

/-- A signed magnetic flux through one oriented turn of the coil. -/
abbrev SignedMagneticFlux : Type :=
  Dimensionful (WithDim magneticFluxDimension ℝ)

/-- A signed rate of magnetic flux through one oriented turn. -/
abbrev SignedMagneticFluxRate : Type :=
  Dimensionful (WithDim electromotiveForceDimension ℝ)

/-- A signed induced electromotive force around the oriented winding. -/
abbrev SignedElectromotiveForce : Type :=
  Dimensionful (WithDim electromotiveForceDimension ℝ)

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical length in centimetres. -/
def lengthInCentimeters (length : LengthMagnitude) : ℝ :=
  100 * lengthInMeters length

/-- Read a physical area in coherent-SI square metres. -/
def areaInSquareMeters (area : AreaMagnitude) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Read magnetic flux density in coherent-SI teslas. -/
def magneticFluxDensityInTeslas
    (field : MagneticFluxDensityMagnitude) : ℝ :=
  ((field UnitChoices.SI).val : ℝ)

/-- Read a signed magnetic-flux-density rate in teslas per second. -/
def magneticFluxDensityRateInTeslasPerSecond
    (rate : SignedMagneticFluxDensityRate) : ℝ :=
  (rate UnitChoices.SI).val

/-- Read signed magnetic flux in coherent-SI webers. -/
def signedMagneticFluxInWebers (flux : SignedMagneticFlux) : ℝ :=
  (flux UnitChoices.SI).val

/-- Read a signed magnetic-flux rate in webers per second. -/
def signedMagneticFluxRateInWebersPerSecond
    (rate : SignedMagneticFluxRate) : ℝ :=
  (rate UnitChoices.SI).val

/-- Read a signed induced emf in coherent-SI volts. -/
def signedEmfInVolts (emf : SignedElectromotiveForce) : ℝ :=
  (emf UnitChoices.SI).val

/-! ## Apparatus, orientation, and primary-raster vocabulary -/

/-- The two labeled pole pieces in the supplied image. -/
inductive MagnetPole where
  | north
  | south
  deriving DecidableEq, Repr

/-- Left and right sides of the primary image. -/
inductive HorizontalSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- Horizontal arrow directions used by the field lines. -/
inductive HorizontalDirection where
  | leftToRight
  | rightToLeft
  deriving DecidableEq, Repr

/-!
An oriented traversal of the coil.  The viewpoint is from the tip of the
positive area-normal vector looking back toward the coil.
-/
inductive CoilTraversalSense where
  | counterclockwiseViewedFromAreaNormalTip
  | clockwiseViewedFromAreaNormalTip
  deriving DecidableEq, Repr

/-!
The sign attached to an oriented traversal.  This is an orientation convention,
not a prediction of the requested direction.
-/
def CoilTraversalSense.orientationSign : CoilTraversalSense → ℝ
  | .counterclockwiseViewedFromAreaNormalTip => 1
  | .clockwiseViewedFromAreaNormalTip => -1

/-!
Literal presentation data transcribed from image `936.png`.  The diagonal
segment is the edge-on depiction of the circular coil plane, with hatched
endcaps; the arrow labeled `A` is its positive area normal.
-/
structure CircularCoilFigure where
  poleAtSide : HorizontalSide → MagnetPole
  fieldLinesShown : Bool
  fieldArrowDirection : HorizontalDirection
  coilShownEdgeOn : Bool
  coilEndcapsShown : Bool
  areaNormalArrowShown : Bool
  magneticFieldVectorLabelShown : Bool
  areaVectorLabelShown : Bool
  radiusLabelCentimeters : ℝ
  planeToFieldAngleLabelRadians : ℝ
  normalToFieldAngleLabelRadians : ℝ

/-!
Independent physical quantities for the experiment at the instant in question.
Neither the signed emf nor its traversal sense is defined from an answer
choice or from the requested final relation.
-/
structure CircularCoilInductionSetup where
  magneticField : Electromagnetism.MagneticField 3
  northToSouthDirection : EuclideanSpace ℝ (Fin 3)
  uniformFieldRegion : Set (Time × Space 3)
  observationTime : Time
  turnCount : ℕ
  coilRadius : LengthMagnitude
  coilArea : AreaMagnitude
  planeToFieldAngle : Real.Angle
  positiveNormalToFieldAngle : Real.Angle
  magneticFluxDensityMagnitude : MagneticFluxDensityMagnitude
  magneticFluxDensityRate : SignedMagneticFluxDensityRate
  magneticFluxPerTurn : SignedMagneticFlux
  magneticFluxRatePerTurn : SignedMagneticFluxRate
  inducedEmf : SignedElectromotiveForce
  inducedEmfSense : CoilTraversalSense
  figure : CircularCoilFigure

/-! ## Figure evidence, problem data, and governing laws -/

/-!
Primary-image evidence.  These fields contain only literal labels and
qualitative directions visible in the raster.
-/
structure MatchesPrimaryCircularCoilFigure
    (setup : CircularCoilInductionSetup) : Prop where
  northPoleIsLeft : setup.figure.poleAtSide .left = .north
  southPoleIsRight : setup.figure.poleAtSide .right = .south
  fieldLinesAreShown : setup.figure.fieldLinesShown = true
  fieldPointsFromNorthToSouth :
    setup.figure.fieldArrowDirection = .leftToRight
  coilPlaneIsShownEdgeOn : setup.figure.coilShownEdgeOn = true
  coilEndcapsAreShown : setup.figure.coilEndcapsShown = true
  positiveAreaNormalIsShown : setup.figure.areaNormalArrowShown = true
  fieldVectorLabelIsShown :
    setup.figure.magneticFieldVectorLabelShown = true
  areaVectorLabelIsShown : setup.figure.areaVectorLabelShown = true
  printedRadius : setup.figure.radiusLabelCentimeters = 4
  printedPlaneToFieldAngle :
    setup.figure.planeToFieldAngleLabelRadians = Real.pi / 3
  printedNormalToFieldAngle :
    setup.figure.normalToFieldAngleLabelRadians = Real.pi / 6

/-!
Numerical and geometric data stated in the prose and tied to the physical
setup.  The negative SI rate encodes the word "decreases".
-/
structure MatchesCircularCoilProblemData
    (setup : CircularCoilInductionSetup) : Prop where
  fiveHundredTurns : setup.turnCount = 500
  radiusMatchesCentimeterLabel :
    lengthInCentimeters setup.coilRadius =
      setup.figure.radiusLabelCentimeters
  planeAngleMatchesFigure :
    setup.planeToFieldAngle =
      (setup.figure.planeToFieldAngleLabelRadians : Real.Angle)
  normalAngleMatchesFigure :
    setup.positiveNormalToFieldAngle =
      (setup.figure.normalToFieldAngleLabelRadians : Real.Angle)
  fieldDecreasesAtPointTwoTeslasPerSecond :
    magneticFluxDensityRateInTeslasPerSecond
        setup.magneticFluxDensityRate = -(1 / 5 : ℝ)

/-- Positivity and non-vacuity conditions for the physical apparatus. -/
structure HasPhysicalCircularCoilParameters
    (setup : CircularCoilInductionSetup) : Prop where
  turnCountPositive : 0 < setup.turnCount
  radiusPositive : 0 < lengthInMeters setup.coilRadius
  areaPositive : 0 < areaInSquareMeters setup.coilArea
  fieldMagnitudePositive :
    0 < magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude
  fieldRegionNonempty : setup.uniformFieldRegion.Nonempty

/-!
The Physlib vector field has the stated scalar magnitude everywhere in the
uniform region at the observation time.
-/
structure HasUniformAppliedMagneticField
    (setup : CircularCoilInductionSetup) : Prop where
  northToSouthDirectionIsUnit :
    ‖setup.northToSouthDirection‖ = 1
  uniformVectorAtObservation : ∀ position,
    (setup.observationTime, position) ∈ setup.uniformFieldRegion →
      setup.magneticField setup.observationTime position =
        magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude •
          setup.northToSouthDirection

/-- The geometric area of a circular coil is `pi r^2`. -/
structure SatisfiesCircularCoilAreaLaw
    (setup : CircularCoilInductionSetup) : Prop where
  areaOfCircle :
    areaInSquareMeters setup.coilArea =
      Real.pi * lengthInMeters setup.coilRadius ^ 2

/-!
For a uniform field at fixed coil orientation, the signed flux through one
turn is `B A cos(theta)` and its instantaneous rate is
`(dB/dt) A cos(theta)`, where `theta` is measured from the positive area
normal.  These are general flux laws and contain no final emf value.
-/
structure SatisfiesUniformFieldFluxLaws
    (setup : CircularCoilInductionSetup) : Prop where
  fluxPerTurnLaw :
    signedMagneticFluxInWebers setup.magneticFluxPerTurn =
      magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
        areaInSquareMeters setup.coilArea *
          Real.Angle.cos setup.positiveNormalToFieldAngle
  fluxRatePerTurnLaw :
    signedMagneticFluxRateInWebersPerSecond
        setup.magneticFluxRatePerTurn =
      magneticFluxDensityRateInTeslasPerSecond
          setup.magneticFluxDensityRate *
        areaInSquareMeters setup.coilArea *
          Real.Angle.cos setup.positiveNormalToFieldAngle

/-!
Faraday's law relates the independent signed emf to the per-turn flux rate.
The second field is the generic orientation-sign convention for the emf; it
does not select either traversal direction in advance.
-/
structure SatisfiesFaradayLenzLaw
    (setup : CircularCoilInductionSetup) : Prop where
  faradayLaw :
    signedEmfInVolts setup.inducedEmf =
      -(setup.turnCount : ℝ) *
        signedMagneticFluxRateInWebersPerSecond
          setup.magneticFluxRatePerTurn
  orientedEmfSignLaw :
    setup.inducedEmfSense.orientationSign *
        |signedEmfInVolts setup.inducedEmf| =
      signedEmfInVolts setup.inducedEmf

/-! ## Displayed choices and final conclusion -/

/-- Labels of the four displayed voltage choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Voltage magnitude printed beside each displayed answer label. -/
def AnswerChoice.emfMagnitudeInVolts : AnswerChoice → ℝ
  | .A => 456 / 1000
  | .B => 435 / 1000
  | .C => 544 / 1000
  | .D => 231 / 1000

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
A choice is uniquely nearest to a computed magnitude when it has strictly
smaller absolute error than every differently labeled choice.
-/
def IsUniqueNearestDisplayedChoice
    (computedVolts : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |computedVolts - choice.emfMagnitudeInVolts| <
      |computedVolts - other.emfMagnitudeInVolts|

/-!
The induced emf has exact magnitude
`500 * pi * (0.04 m)^2 * (0.200 T/s) * sin(60 degrees)`.
It is therefore uniquely nearest to `0.435 V`, answer B.  Because the positive
normal component of the north-to-south field is decreasing, Faraday--Lenz and
the displayed area-normal convention give a counterclockwise emf when viewed
from the tip of that normal.

This is the Lean declaration corresponding to
`thm:physics:phyx_mini_0936:target`.
-/
theorem problem_phyx_mini_0936
    (setup : CircularCoilInductionSetup)
    (_figure : MatchesPrimaryCircularCoilFigure setup)
    (_data : MatchesCircularCoilProblemData setup)
    (_physical : HasPhysicalCircularCoilParameters setup)
    (_uniformField : HasUniformAppliedMagneticField setup)
    (_areaLaw : SatisfiesCircularCoilAreaLaw setup)
    (_fluxLaws : SatisfiesUniformFieldFluxLaws setup)
    (_faradayLenz : SatisfiesFaradayLenzLaw setup) :
    |signedEmfInVolts setup.inducedEmf| =
        500 * Real.pi * ((4 : ℝ) / 100) ^ 2 *
          (1 / 5 : ℝ) * Real.sin (Real.pi / 3) ∧
      IsUniqueNearestDisplayedChoice
        |signedEmfInVolts setup.inducedEmf| recordedDatasetAnswer ∧
      setup.inducedEmfSense =
        .counterclockwiseViewedFromAreaNormalTip := by
  let exactEmf : ℝ :=
    500 * Real.pi * ((4 : ℝ) / 100) ^ 2 *
      (1 / 5 : ℝ) * Real.sin (Real.pi / 3)
  have radiusInMeters :
      lengthInMeters setup.coilRadius = (4 : ℝ) / 100 := by
    have radiusData := _data.radiusMatchesCentimeterLabel
    rw [_figure.printedRadius] at radiusData
    simp only [lengthInCentimeters] at radiusData
    linarith only [radiusData]
  have normalAngle :
      setup.positiveNormalToFieldAngle =
        ((Real.pi / 6 : ℝ) : Real.Angle) := by
    rw [_data.normalAngleMatchesFigure,
      _figure.printedNormalToFieldAngle]
  have fluxRate :
      signedMagneticFluxRateInWebersPerSecond
          setup.magneticFluxRatePerTurn =
        -(1 / 5 : ℝ) *
          (Real.pi * ((4 : ℝ) / 100) ^ 2) *
            Real.sin (Real.pi / 3) := by
    rw [_fluxLaws.fluxRatePerTurnLaw,
      _data.fieldDecreasesAtPointTwoTeslasPerSecond,
      _areaLaw.areaOfCircle, radiusInMeters, normalAngle,
      Real.Angle.cos_coe, Real.cos_pi_div_six,
      ← Real.sin_pi_div_three]
  have emfValue :
      signedEmfInVolts setup.inducedEmf = exactEmf := by
    rw [_faradayLenz.faradayLaw, _data.fiveHundredTurns, fluxRate]
    simp only [Nat.cast_ofNat]
    dsimp [exactEmf]
    ring
  have exactEmfReduced :
      exactEmf = 2 * Real.pi * Real.sqrt 3 / 25 := by
    dsimp [exactEmf]
    rw [Real.sin_pi_div_three]
    ring
  have exactEmfPositive : 0 < exactEmf := by
    rw [exactEmfReduced]
    positivity
  have emfMagnitude :
      |signedEmfInVolts setup.inducedEmf| = exactEmf := by
    rw [emfValue, abs_of_pos exactEmfPositive]

  have sqrtThreeSquared : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
    norm_num
  have sqrtThreeNonnegative : 0 ≤ Real.sqrt 3 :=
    Real.sqrt_nonneg 3
  have sqrtThreeLower : (5 : ℝ) / 3 < Real.sqrt 3 := by
    nlinarith only [sqrtThreeSquared, sqrtThreeNonnegative]
  have sqrtThreeUpper : Real.sqrt 3 < (1733 : ℝ) / 1000 := by
    nlinarith only [sqrtThreeSquared, sqrtThreeNonnegative]

  have sinPiOverSixteen :
      Real.sin (Real.pi / 16) =
        Real.sqrt (2 - Real.sqrtTwoAddSeries 0 2) / 2 := by
    convert Real.sin_pi_over_two_pow_succ 2 using 1
    all_goals norm_num
  have piOverSixteenPositive : 0 < Real.pi / 16 := by positivity
  have piOverSixteenAtMostOne : Real.pi / 16 ≤ 1 := by
    nlinarith only [Real.pi_le_four]
  have sineTaylorLower :=
    Real.sin_gt_sub_cube piOverSixteenPositive piOverSixteenAtMostOne
  rw [sinPiOverSixteen] at sineTaylorLower
  have cubicRemainderUpper :
      (Real.pi / 16) ^ 3 / 4 ≤ ((4 : ℝ) / 16) ^ 3 / 4 := by
    gcongr
    exact Real.pi_le_four
  have piSeriesUpper :
      Real.pi <
        8 * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 2) + 1 / 16 := by
    nlinarith only [sineTaylorLower, cubicRemainderUpper]

  have sqrtTwoSquared : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    norm_num
  have sqrtTwoNonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have sqrtTwoLower : (141 : ℝ) / 100 < Real.sqrt 2 := by
    nlinarith only [sqrtTwoSquared, sqrtTwoNonnegative]
  have sqrtTwoUpper : Real.sqrt 2 < 2 := by
    nlinarith only [sqrtTwoSquared, sqrtTwoNonnegative]
  have nestedRootSquared :
      (Real.sqrt (2 + Real.sqrt 2)) ^ 2 = 2 + Real.sqrt 2 := by
    rw [Real.sq_sqrt]
    positivity
  have nestedRootNonnegative : 0 ≤ Real.sqrt (2 + Real.sqrt 2) :=
    Real.sqrt_nonneg _
  have nestedRootLower :
      (1477 : ℝ) / 800 < Real.sqrt (2 + Real.sqrt 2) := by
    nlinarith only [nestedRootSquared, nestedRootNonnegative, sqrtTwoLower]
  have nestedRootUpper : Real.sqrt (2 + Real.sqrt 2) < 2 := by
    nlinarith only [nestedRootSquared, nestedRootNonnegative, sqrtTwoUpper]
  have outerRootSquared :
      (Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2))) ^ 2 =
        2 - Real.sqrt (2 + Real.sqrt 2) := by
    rw [Real.sq_sqrt]
    exact sub_nonneg.mpr nestedRootUpper.le
  have outerRootNonnegative :
      0 ≤ Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) :=
    Real.sqrt_nonneg _
  have outerRootUpper :
      Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) <
        (251 : ℝ) / 640 := by
    nlinarith only [outerRootSquared, outerRootNonnegative, nestedRootLower]
  have piUpper : Real.pi < (16 : ℝ) / 5 := by
    rw [Real.sqrtTwoAddSeries_two] at piSeriesUpper
    nlinarith only [piSeriesUpper, outerRootUpper]
  have piLower : (3 : ℝ) < Real.pi := by
    have sineBelowArgument :=
      Real.sin_lt (show 0 < Real.pi / 6 by positivity)
    rw [Real.sin_pi_div_six] at sineBelowArgument
    nlinarith only [sineBelowArgument]

  have piSqrtThreeLower :
      (3 : ℝ) * ((5 : ℝ) / 3) < Real.pi * Real.sqrt 3 := by
    calc
      (3 : ℝ) * ((5 : ℝ) / 3) <
          Real.pi * ((5 : ℝ) / 3) := by
            exact mul_lt_mul_of_pos_right piLower (by norm_num)
      _ < Real.pi * Real.sqrt 3 := by
        exact mul_lt_mul_of_pos_left sqrtThreeLower Real.pi_pos
  have piSqrtThreeUpper :
      Real.pi * Real.sqrt 3 <
        (16 : ℝ) / 5 * ((1733 : ℝ) / 1000) := by
    calc
      Real.pi * Real.sqrt 3 <
          (16 : ℝ) / 5 * Real.sqrt 3 := by
            exact mul_lt_mul_of_pos_right piUpper
              (Real.sqrt_pos.2 (by norm_num))
      _ < (16 : ℝ) / 5 * ((1733 : ℝ) / 1000) := by
        exact mul_lt_mul_of_pos_left sqrtThreeUpper (by norm_num)
  have exactEmfLower : (2 : ℝ) / 5 < exactEmf := by
    rw [exactEmfReduced]
    calc
      (2 : ℝ) / 5 =
          (2 / 25 : ℝ) * ((3 : ℝ) * ((5 : ℝ) / 3)) := by norm_num
      _ < (2 / 25 : ℝ) * (Real.pi * Real.sqrt 3) := by
        exact mul_lt_mul_of_pos_left piSqrtThreeLower (by norm_num)
      _ = 2 * Real.pi * Real.sqrt 3 / 25 := by ring
  have exactEmfUpper : exactEmf < (89 : ℝ) / 200 := by
    rw [exactEmfReduced]
    calc
      2 * Real.pi * Real.sqrt 3 / 25 =
          (2 / 25 : ℝ) * (Real.pi * Real.sqrt 3) := by ring
      _ < (2 / 25 : ℝ) *
          ((16 : ℝ) / 5 * ((1733 : ℝ) / 1000)) := by
        exact mul_lt_mul_of_pos_left piSqrtThreeUpper (by norm_num)
      _ < (89 : ℝ) / 200 := by norm_num

  refine ⟨emfMagnitude, ?_, ?_⟩
  · rw [emfMagnitude]
    unfold IsUniqueNearestDisplayedChoice recordedDatasetAnswer
    intro other otherNotB
    cases other with
    | A =>
        simp only [AnswerChoice.emfMagnitudeInVolts]
        have rightError :
            |exactEmf - (456 : ℝ) / 1000| =
              (456 : ℝ) / 1000 - exactEmf := by
          rw [abs_of_nonpos (by linarith only [exactEmfUpper])]
          ring
        rw [rightError, abs_lt]
        constructor <;> linarith only [exactEmfUpper]
    | B =>
        exact (otherNotB rfl).elim
    | C =>
        simp only [AnswerChoice.emfMagnitudeInVolts]
        have rightError :
            |exactEmf - (544 : ℝ) / 1000| =
              (544 : ℝ) / 1000 - exactEmf := by
          rw [abs_of_nonpos (by linarith only [exactEmfUpper])]
          ring
        rw [rightError, abs_lt]
        constructor <;> linarith only [exactEmfUpper]
    | D =>
        simp only [AnswerChoice.emfMagnitudeInVolts]
        have rightError :
            |exactEmf - (231 : ℝ) / 1000| =
              exactEmf - (231 : ℝ) / 1000 := by
          rw [abs_of_nonneg (by linarith only [exactEmfLower])]
        rw [rightError, abs_lt]
        constructor <;> linarith only [exactEmfLower]
  · cases senseEquation : setup.inducedEmfSense with
    | counterclockwiseViewedFromAreaNormalTip =>
        rfl
    | clockwiseViewedFromAreaNormalTip =>
        have orientedSign := _faradayLenz.orientedEmfSignLaw
        rw [senseEquation, emfValue, abs_of_pos exactEmfPositive] at orientedSign
        simp only [CoilTraversalSense.orientationSign, neg_one_mul] at orientedSign
        linarith only [orientedSign, exactEmfPositive]

end PhyXMiniProblems.ProblemPhyXMini0936
