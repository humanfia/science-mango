import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.SpaceAndTime.Space.CrossProduct
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0950

open Dimension

/-!
# Net magnetic force on a loudspeaker voice coil

A circular voice coil has `50` turns, diameter `1.56 cm`, and current
`0.950 A`.  Its axis is the positive `y`-axis.  At each wire point the
magnetic flux density has magnitude `0.220 T` and is tilted `60 degrees`
outward from the positive axial normal.  The current is counterclockwise when
viewed from the positive `y`-axis.

Physical scalar magnitudes and the net force vector use Physlib's
unit-independent `Dimensionful (WithDim ...)` representation.  Real numbers
occur only as coherent-SI readouts, dimensionless angles, and literal figure
or answer-choice values.  Physlib's spacetime-dependent magnetic-field type
and Euclidean cross product retain the vector content of the Lorentz law.

Assumption/target split:

* governing laws: circular-loop geometry, the axisymmetric field profile, and
  the magnetic Lorentz line integral `I ∮ dℓ × B`, summed over all turns;
* previous-part results: none;
* figure/data readouts: `50` turns, `1.56 cm`, `0.950 A`, `0.220 T`, the
  `60 degree` outward tilt, the `y`-axis, the two symmetric `B` arrows, and
  counterclockwise current viewed from positive `y`;
* current target conclusions: the exact net-force vector, its magnitude,
  its negative-`y` direction, and selection of displayed answer B
  (`-0.444 N` after rounding).

No premise below states the exact force formula or any answer-choice value.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- Three-dimensional Euclidean vectors used for coherent-unit readouts. -/
abbrev SpatialVector : Type := EuclideanSpace ℝ (Fin 3)

/-- Electric current has physical dimension `C T⁻¹`. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Magnetic flux density (tesla) has physical dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Force (newton) has physical dimension `M L T⁻²`. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent electric-current magnitude. -/
abbrev CurrentMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitudeQuantity : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A signed, unit-independent spatial force vector. -/
abbrev ForceVectorQuantity : Type :=
  Dimensionful (WithDim forceDimension SpatialVector)

/-- Read a nonnegative physical quantity in coherent SI units. -/
def nonnegativeSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a dimensionful spatial vector in coherent SI components. -/
def vectorSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension SpatialVector)) : SpatialVector :=
  (quantity UnitChoices.SI).val

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Centimetre readout used by the diameter stated in the problem. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Ampere readout of the current magnitude. -/
def currentInAmperes (current : CurrentMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout current

/-- Tesla readout of the magnetic-flux-density magnitude. -/
def magneticFluxDensityInTeslas
    (density : MagneticFluxDensityMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout density

/-- Cartesian newton readout of the net magnetic force. -/
def forceVectorInNewtons (force : ForceVectorQuantity) : SpatialVector :=
  vectorSIReadout force

/-- Magnitude in newtons of a dimensionful force vector. -/
def forceMagnitudeInNewtons (force : ForceVectorQuantity) : ℝ :=
  ‖forceVectorInNewtons force‖

/-! ## Coordinate geometry and current orientation -/

/-- Coordinate `0`, the horizontal `x`-axis shown in the raster. -/
def xAxisIndex : Fin 3 := 0

/-- Coordinate `1`, the loudspeaker and coil `y`-axis. -/
def yAxisIndex : Fin 3 := 1

/-- Coordinate `2`, completing the right-handed Cartesian frame. -/
def zAxisIndex : Fin 3 := 2

/-- Positive Cartesian `x` unit vector. -/
def xHat : SpatialVector :=
  EuclideanSpace.single xAxisIndex 1

/-- Positive axial `y` unit vector. -/
def yHat : SpatialVector :=
  EuclideanSpace.single yAxisIndex 1

/-- Positive Cartesian `z` unit vector. -/
def zHat : SpatialVector :=
  EuclideanSpace.single zAxisIndex 1

/-!
The outward radial unit vector in the coil's `x-z` plane.  The minus sign on
the `z` component fixes the view from positive `y`: increasing `azimuth`
moves counterclockwise on the viewer's page.
-/
def outwardRadialDirection (azimuth : ℝ) : SpatialVector :=
  Real.cos azimuth • xHat - Real.sin azimuth • zHat

/-- Unit tangent for counterclockwise current as viewed from positive `y`. -/
def counterclockwiseTangentDirection (azimuth : ℝ) : SpatialVector :=
  -(Real.sin azimuth) • xHat - Real.cos azimuth • zHat

/-- Mathlib's cross product transported to Physlib's Euclidean vectors. -/
def spatialCross (left right : SpatialVector) : SpatialVector :=
  WithLp.toLp 2 (crossProduct left.ofLp right.ofLp)

/-! ## Physical roles and primary-raster vocabulary -/

/-- The two labelled coordinate axes visible in image `950.png`. -/
inductive DiagramAxis where
  | x
  | y
  deriving DecidableEq, Fintype, Repr

/-- The two symmetric magnetic-field arrows drawn beside the coil. -/
inductive FieldArrowSide where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- Qualitative arrow directions used to transcribe the primary raster. -/
inductive FigureArrowDirection where
  | right
  | upperLeft
  | upperRight
  deriving DecidableEq, Repr

/-- Sense of current around the coil when viewed from the positive axis. -/
inductive CirculationSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- Expected direction of each blue field arrow in the side view. -/
def expectedFieldArrowDirection : FieldArrowSide → FigureArrowDirection
  | .left => .upperLeft
  | .right => .upperRight

/-!
Literal and qualitative content of the supplied raster.  The real-valued
angle labels are figure readouts in degrees, not solved force quantities.
-/
structure VoiceCoilFigure where
  cylinderShown : Bool
  coilShownWrappedAroundCylinder : Bool
  coordinateAxisShown : DiagramAxis → Bool
  cylinderAxis : DiagramAxis
  currentArrowShown : Bool
  currentArrowLabelledI : Bool
  visibleCurrentArrowDirection : FigureArrowDirection
  magneticFieldArrowShown : FieldArrowSide → Bool
  magneticFieldArrowLabelledB : FieldArrowSide → Bool
  magneticFieldArrowDirection : FieldArrowSide → FigureArrowDirection
  angleArcShown : FieldArrowSide → Bool
  angleMeasuredFromCylinderAxis : FieldArrowSide → Bool
  printedAngleDegrees : FieldArrowSide → ℝ

/-!
Independent physical data for the voice coil.  In particular,
`netMagneticForce` is not defined from a force formula or answer choice.
-/
structure VoiceCoilSetup where
  figure : VoiceCoilFigure
  turnCount : ℕ
  coilDiameter : LengthQuantity
  currentMagnitude : CurrentMagnitudeQuantity
  magneticFieldMagnitude : MagneticFluxDensityMagnitudeQuantity
  fieldTiltFromPositiveAxisRadians : ℝ
  coilAxis : DiagramAxis
  currentSenseViewedFromPositiveY : CirculationSense
  magneticField : Electromagnetism.MagneticField 3
  observationTime : Time
  coilCenter : Space 3
  pointOnWire : ℝ → Space 3
  currentTangentDirection : ℝ → SpatialVector
  netMagneticForce : ForceVectorQuantity

/-! ## Scenario, figure evidence, and physical input data -/

/-- Prose-level axis and circulation assignments. -/
structure MatchesVoiceCoilScenario (setup : VoiceCoilSetup) : Prop where
  axisIsY : setup.coilAxis = .y
  currentIsCounterclockwiseFromPositiveY :
    setup.currentSenseViewedFromPositiveY = .counterclockwise

/-!
Primary-image evidence: the cylinder and coil, labelled axes, rightward front
current arrow, symmetric outward/upward `B` arrows, and two `60 degree` arcs.
-/
structure MatchesPrimaryVoiceCoilFigure (setup : VoiceCoilSetup) : Prop where
  cylinderIsShown : setup.figure.cylinderShown = true
  coilIsShown : setup.figure.coilShownWrappedAroundCylinder = true
  bothCoordinateAxesAreShown :
    ∀ axis, setup.figure.coordinateAxisShown axis = true
  picturedCylinderAxisIsY : setup.figure.cylinderAxis = .y
  currentArrowIsShown : setup.figure.currentArrowShown = true
  currentArrowHasILabel : setup.figure.currentArrowLabelledI = true
  frontCurrentArrowPointsRight :
    setup.figure.visibleCurrentArrowDirection = .right
  bothFieldArrowsAreShown :
    ∀ side, setup.figure.magneticFieldArrowShown side = true
  bothFieldArrowsHaveBLabels :
    ∀ side, setup.figure.magneticFieldArrowLabelledB side = true
  symmetricFieldArrowDirections :
    ∀ side,
      setup.figure.magneticFieldArrowDirection side =
        expectedFieldArrowDirection side
  bothAngleArcsAreShown :
    ∀ side, setup.figure.angleArcShown side = true
  anglesUseCylinderAxisAsReference :
    ∀ side, setup.figure.angleMeasuredFromCylinderAxis side = true
  bothPrintedAnglesAreSixtyDegrees :
    ∀ side, setup.figure.printedAngleDegrees side = 60

/-!
Numerical values stated in the prose.  The angle is converted from degrees to
radians.  No force value or answer-choice label occurs in this record.
-/
structure MatchesProblemReadouts (setup : VoiceCoilSetup) : Prop where
  turns : setup.turnCount = 50
  diameterCentimeters : lengthInCentimeters setup.coilDiameter = 1.56
  currentAmperes : currentInAmperes setup.currentMagnitude = 0.950
  magneticFieldTeslas :
    magneticFluxDensityInTeslas setup.magneticFieldMagnitude = 0.220
  fieldTiltIsSixtyDegrees :
    setup.fieldTiltFromPositiveAxisRadians = Real.pi / 3

/-- Positivity and angular nondegeneracy of the physical setup. -/
structure HasPhysicalVoiceCoilParameters (setup : VoiceCoilSetup) : Prop where
  atLeastOneTurn : 0 < setup.turnCount
  diameterPositive : 0 < lengthInMeters setup.coilDiameter
  currentPositive : 0 < currentInAmperes setup.currentMagnitude
  magneticFieldPositive :
    0 < magneticFluxDensityInTeslas setup.magneticFieldMagnitude
  fieldTiltAcute :
    0 < setup.fieldTiltFromPositiveAxisRadians ∧
      setup.fieldTiltFromPositiveAxisRadians < Real.pi / 2

/-! ## Circular geometry, field model, and Lorentz-force law -/

/-!
The wire is a circle of the stated radius in the plane normal to `y`, and its
current tangent has the counterclockwise orientation fixed above.
-/
structure SatisfiesCircularVoiceCoilGeometry (setup : VoiceCoilSetup) : Prop where
  wirePosition : ∀ azimuth : ℝ,
    setup.pointOnWire azimuth =
      ((lengthInMeters setup.coilDiameter / 2) •
        outwardRadialDirection azimuth) +ᵥ setup.coilCenter
  currentTangent : ∀ azimuth : ℝ,
    setup.currentTangentDirection azimuth =
      counterclockwiseTangentDirection azimuth

/-!
At every point of the wire, the field has the stated constant magnitude.  Its
axial component points along positive `y`, while its transverse component is
radially outward and makes the stated angle from the axial normal.
-/
structure ModelsAxisymmetricVoiceCoilMagneticField
    (setup : VoiceCoilSetup) : Prop where
  fieldOnWire : ∀ azimuth : ℝ,
    setup.magneticField setup.observationTime (setup.pointOnWire azimuth) =
      magneticFluxDensityInTeslas setup.magneticFieldMagnitude •
        (Real.cos setup.fieldTiltFromPositiveAxisRadians • yHat +
          Real.sin setup.fieldTiltFromPositiveAxisRadians •
            outwardRadialDirection azimuth)
  constantFieldMagnitude : ∀ azimuth : ℝ,
    ‖setup.magneticField setup.observationTime (setup.pointOnWire azimuth)‖ =
      magneticFluxDensityInTeslas setup.magneticFieldMagnitude

/-!
The governing magnetic Lorentz law.  The interval integral parameterizes one
turn by azimuth; `diameter / 2` converts its unit tangent to `dℓ`, and the
outer scalar multiplication sums the identical force over all turns.

This is a line-integral law in the independently supplied field.  It does not
state the evaluated axial-force formula requested by the problem.
-/
structure SatisfiesVoiceCoilMagneticLorentzForceLaw
    (setup : VoiceCoilSetup) : Prop where
  netForceIsTurnSumOfLineIntegral :
    forceVectorInNewtons setup.netMagneticForce =
      (setup.turnCount : ℝ) •
        (∫ azimuth : ℝ in 0..2 * Real.pi,
          (currentInAmperes setup.currentMagnitude *
            (lengthInMeters setup.coilDiameter / 2)) •
              spatialCross
                (setup.currentTangentDirection azimuth)
                (setup.magneticField setup.observationTime
                  (setup.pointOnWire azimuth)))

/-! ## Exact result, direction, and displayed answers -/

/-!
The positive magnitude obtained after evaluating the line integral.  This
helper depends only on input readouts and does not define the independent
`netMagneticForce` field.
-/
def exactForceMagnitudeInNewtons (setup : VoiceCoilSetup) : ℝ :=
  setup.turnCount * currentInAmperes setup.currentMagnitude * Real.pi *
    lengthInMeters setup.coilDiameter *
      magneticFluxDensityInTeslas setup.magneticFieldMagnitude *
        Real.sin setup.fieldTiltFromPositiveAxisRadians

/-- The signed component of the net force along the pictured `y`-axis. -/
def signedAxialForceInNewtons (setup : VoiceCoilSetup) : ℝ :=
  forceVectorInNewtons setup.netMagneticForce yAxisIndex

/-- A nonzero force vector points along the negative `y`-axis. -/
def PointsAlongNegativeYAxis (force : SpatialVector) : Prop :=
  ∃ magnitude : ℝ, 0 < magnitude ∧ force = (-magnitude) • yHat

/-- The four answer labels displayed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Signed axial force in newtons printed beside each answer choice. -/
def AnswerChoice.signedForceInNewtons : AnswerChoice → ℝ
  | .A => 0.454
  | .B => -0.444
  | .C => 0.434
  | .D => -0.456

/-- Answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .B

/-- Absolute error from a displayed signed axial-force value. -/
def answerChoiceErrorInNewtons
    (setup : VoiceCoilSetup) (choice : AnswerChoice) : ℝ :=
  |signedAxialForceInNewtons setup - choice.signedForceInNewtons|

/-- Agreement with a force value printed to the nearest `0.001 N`. -/
def MatchesDisplayedSignedForce
    (setup : VoiceCoilSetup) (choice : AnswerChoice) : Prop :=
  answerChoiceErrorInNewtons setup choice ≤ (1 : ℝ) / 2000

/-- A displayed signed force is strictly closer than every alternative. -/
def IsUniqueClosestSignedForceChoice
    (setup : VoiceCoilSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    answerChoiceErrorInNewtons setup choice <
      answerChoiceErrorInNewtons setup other

/-!
The Lorentz line integral evaluates to a force along negative `y`.  Its
magnitude is about `0.443528 N`, so the signed axial component rounds to
`-0.444 N`, answer B.

Blueprint: `thm:physics:phyx_mini_0950:target`.
-/
theorem problem_phyx_mini_0950
    (setup : VoiceCoilSetup)
    (_scenario : MatchesVoiceCoilScenario setup)
    (_figure : MatchesPrimaryVoiceCoilFigure setup)
    (_readouts : MatchesProblemReadouts setup)
    (_physical : HasPhysicalVoiceCoilParameters setup)
    (_geometry : SatisfiesCircularVoiceCoilGeometry setup)
    (_field : ModelsAxisymmetricVoiceCoilMagneticField setup)
    (_lorentz : SatisfiesVoiceCoilMagneticLorentzForceLaw setup) :
    forceVectorInNewtons setup.netMagneticForce =
        (-exactForceMagnitudeInNewtons setup) • yHat ∧
      forceMagnitudeInNewtons setup.netMagneticForce =
        exactForceMagnitudeInNewtons setup ∧
      PointsAlongNegativeYAxis
        (forceVectorInNewtons setup.netMagneticForce) ∧
      MatchesDisplayedSignedForce setup .B ∧
      IsUniqueClosestSignedForceChoice setup .B := by
  have hCross (azimuth : ℝ) :
      spatialCross (counterclockwiseTangentDirection azimuth)
          (magneticFluxDensityInTeslas setup.magneticFieldMagnitude •
            (Real.cos setup.fieldTiltFromPositiveAxisRadians • yHat +
              Real.sin setup.fieldTiltFromPositiveAxisRadians •
                outwardRadialDirection azimuth)) =
        (magneticFluxDensityInTeslas setup.magneticFieldMagnitude *
            Real.cos setup.fieldTiltFromPositiveAxisRadians) •
            outwardRadialDirection azimuth -
          (magneticFluxDensityInTeslas setup.magneticFieldMagnitude *
            Real.sin setup.fieldTiltFromPositiveAxisRadians) • yHat := by
    ext i
    fin_cases i <;>
      simp [spatialCross, counterclockwiseTangentDirection,
        outwardRadialDirection, xHat, yHat, zHat, xAxisIndex, yAxisIndex,
        zAxisIndex, crossProduct]
    · ring
    · calc
        -(Real.sin azimuth *
              (magneticFluxDensityInTeslas setup.magneticFieldMagnitude *
                (Real.sin setup.fieldTiltFromPositiveAxisRadians *
                  Real.sin azimuth))) -
            Real.cos azimuth *
              (magneticFluxDensityInTeslas setup.magneticFieldMagnitude *
                (Real.sin setup.fieldTiltFromPositiveAxisRadians *
                  Real.cos azimuth)) =
          -(magneticFluxDensityInTeslas setup.magneticFieldMagnitude *
              Real.sin setup.fieldTiltFromPositiveAxisRadians) *
            (Real.sin azimuth ^ 2 + Real.cos azimuth ^ 2) := by ring
        _ = -(magneticFluxDensityInTeslas setup.magneticFieldMagnitude *
              Real.sin setup.fieldTiltFromPositiveAxisRadians) := by
          rw [Real.sin_sq_add_cos_sq]
          ring
    · ring
  have hLineIntegral :
      (∫ azimuth : ℝ in 0..2 * Real.pi,
        (currentInAmperes setup.currentMagnitude *
          (lengthInMeters setup.coilDiameter / 2)) •
            spatialCross
              (counterclockwiseTangentDirection azimuth)
              (magneticFluxDensityInTeslas setup.magneticFieldMagnitude •
                (Real.cos setup.fieldTiltFromPositiveAxisRadians • yHat +
                  Real.sin setup.fieldTiltFromPositiveAxisRadians •
                    outwardRadialDirection azimuth))) =
        (-(currentInAmperes setup.currentMagnitude *
            lengthInMeters setup.coilDiameter * Real.pi *
            magneticFluxDensityInTeslas setup.magneticFieldMagnitude *
            Real.sin setup.fieldTiltFromPositiveAxisRadians)) • yHat := by
    simp_rw [hCross, outwardRadialDirection, smul_sub, smul_smul]
    rw [intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    rw [intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp only [intervalIntegral.integral_smul_const,
      intervalIntegral.integral_const_mul, integral_cos, integral_sin,
      intervalIntegral.integral_const]
    ext i
    fin_cases i <;>
      simp [xHat, yHat, zHat, xAxisIndex, yAxisIndex, zAxisIndex] <;>
      ring
  have hForce :
      forceVectorInNewtons setup.netMagneticForce =
        (-exactForceMagnitudeInNewtons setup) • yHat := by
    calc
      forceVectorInNewtons setup.netMagneticForce =
          (setup.turnCount : ℝ) •
            (∫ azimuth : ℝ in 0..2 * Real.pi,
              (currentInAmperes setup.currentMagnitude *
                (lengthInMeters setup.coilDiameter / 2)) •
                  spatialCross
                    (setup.currentTangentDirection azimuth)
                    (setup.magneticField setup.observationTime
                      (setup.pointOnWire azimuth))) :=
        _lorentz.netForceIsTurnSumOfLineIntegral
      _ = (setup.turnCount : ℝ) •
          (∫ azimuth : ℝ in 0..2 * Real.pi,
            (currentInAmperes setup.currentMagnitude *
              (lengthInMeters setup.coilDiameter / 2)) •
                spatialCross
                  (counterclockwiseTangentDirection azimuth)
                  (magneticFluxDensityInTeslas
                      setup.magneticFieldMagnitude •
                    (Real.cos setup.fieldTiltFromPositiveAxisRadians • yHat +
                      Real.sin setup.fieldTiltFromPositiveAxisRadians •
                        outwardRadialDirection azimuth))) := by
        congr 2
        funext azimuth
        rw [_geometry.currentTangent, _field.fieldOnWire]
      _ = (setup.turnCount : ℝ) •
          ((-(currentInAmperes setup.currentMagnitude *
              lengthInMeters setup.coilDiameter * Real.pi *
              magneticFluxDensityInTeslas setup.magneticFieldMagnitude *
              Real.sin setup.fieldTiltFromPositiveAxisRadians)) • yHat) := by
        rw [hLineIntegral]
      _ = (-exactForceMagnitudeInNewtons setup) • yHat := by
        rw [smul_smul]
        unfold exactForceMagnitudeInNewtons
        ring
  have hTurns : setup.turnCount = 50 := _readouts.turns
  have hDiameter :
      lengthInMeters setup.coilDiameter = (39 / 2500 : ℝ) := by
    have h := _readouts.diameterCentimeters
    norm_num [lengthInCentimeters] at h ⊢
    linarith
  have hCurrent :
      currentInAmperes setup.currentMagnitude = (19 / 20 : ℝ) := by
    have h := _readouts.currentAmperes
    norm_num at h ⊢
    exact h
  have hField :
      magneticFluxDensityInTeslas setup.magneticFieldMagnitude =
        (11 / 50 : ℝ) := by
    have h := _readouts.magneticFieldTeslas
    norm_num at h ⊢
    exact h
  have hTilt :
      setup.fieldTiltFromPositiveAxisRadians = Real.pi / 3 :=
    _readouts.fieldTiltIsSixtyDegrees
  have hExact :
      exactForceMagnitudeInNewtons setup =
        (8151 / 100000 : ℝ) * Real.pi * Real.sqrt 3 := by
    rw [exactForceMagnitudeInNewtons, hTurns, hCurrent, hDiameter, hField,
      hTilt, Real.sin_pi_div_three]
    norm_num
    ring
  have hSqrtSquare : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hSqrtNonnegative : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hSqrtLower : (1.7320508 : ℝ) < Real.sqrt 3 := by
    nlinarith only [hSqrtSquare, hSqrtNonnegative]
  have hSqrtUpper : Real.sqrt 3 < (1.7320509 : ℝ) := by
    nlinarith only [hSqrtSquare, hSqrtNonnegative]
  have hProductLower :
      (3.141592 : ℝ) * 1.7320508 < Real.pi * Real.sqrt 3 :=
    mul_lt_mul Real.pi_gt_d6 hSqrtLower.le (by norm_num) Real.pi_pos.le
  have hProductUpper :
      Real.pi * Real.sqrt 3 < (3.141593 : ℝ) * 1.7320509 :=
    mul_lt_mul Real.pi_lt_d6 hSqrtUpper.le
      (Real.sqrt_pos.2 (by norm_num)) (by norm_num)
  have hExactLower :
      (0.443527 : ℝ) < exactForceMagnitudeInNewtons setup := by
    rw [hExact]
    nlinarith only [hProductLower]
  have hExactUpper :
      exactForceMagnitudeInNewtons setup < (0.443529 : ℝ) := by
    rw [hExact]
    nlinarith only [hProductUpper]
  have hExactPositive : 0 < exactForceMagnitudeInNewtons setup := by
    linarith
  have hMagnitude :
      forceMagnitudeInNewtons setup.netMagneticForce =
        exactForceMagnitudeInNewtons setup := by
    rw [forceMagnitudeInNewtons, hForce, norm_smul]
    simp [yHat, yAxisIndex, abs_of_pos hExactPositive]
  have hDirection :
      PointsAlongNegativeYAxis
        (forceVectorInNewtons setup.netMagneticForce) := by
    exact ⟨exactForceMagnitudeInNewtons setup, hExactPositive, hForce⟩
  have hSigned :
      signedAxialForceInNewtons setup =
        -exactForceMagnitudeInNewtons setup := by
    simp [signedAxialForceInNewtons, hForce, yHat, yAxisIndex]
  have hDisplayed : MatchesDisplayedSignedForce setup .B := by
    rw [MatchesDisplayedSignedForce, answerChoiceErrorInNewtons, hSigned]
    norm_num [AnswerChoice.signedForceInNewtons]
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hClosest : IsUniqueClosestSignedForceChoice setup .B := by
    intro other hOther
    fin_cases other
    · rw [answerChoiceErrorInNewtons, answerChoiceErrorInNewtons, hSigned]
      norm_num [AnswerChoice.signedForceInNewtons]
      rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · exact (hOther rfl).elim
    · rw [answerChoiceErrorInNewtons, answerChoiceErrorInNewtons, hSigned]
      norm_num [AnswerChoice.signedForceInNewtons]
      rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · rw [answerChoiceErrorInNewtons, answerChoiceErrorInNewtons, hSigned]
      norm_num [AnswerChoice.signedForceInNewtons]
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
  exact ⟨hForce, hMagnitude, hDirection, hDisplayed, hClosest⟩

end PhyXMiniProblems.ProblemPhyXMini0950
