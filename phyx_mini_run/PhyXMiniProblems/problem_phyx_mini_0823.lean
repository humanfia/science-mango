import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Torque applied to a pipe fitting with a cheater pipe

The primary image places the fitting center at the right-hand end of the
wrench.  The force-application point is `0.80 m` up and to the left along a
handle making a `19°` angle with the horizontal.  The plumber's `900 N` weight
acts vertically downward there.  With positive `x` rightward and positive `y`
upward, the moment `r × F` points along positive `z`, out of the page, and is
therefore counterclockwise in the displayed view.

Physical lengths, positions, forces, and torques use Physlib's unit-independent
`Dimensionful (WithDim ...)` representation.  Real scalars and vectors below
are only coherent-unit readouts, angle readouts, or literal figure/answer data.

Assumption/target boundary:

* `MatchesProblemStatement` contains the stated `900 N`, `0.80 m`, and `19°`
  data and the use of a cheater pipe.
* `MatchesPrimaryFigure` transcribes only visible components, labels,
  incidences, and arrow directions from image `823.png`.
* `MatchesHandleGeometry` and `MatchesDownwardForceGeometry` turn those source
  readouts into Cartesian position and force components.
* `SatisfiesTorqueLaw` states the governing law `τ = r × F` in every coherent
  unit system.
* There are no previous-part results.
* The exact torque, its counterclockwise direction, and its agreement with the
  rounded `680 N m` answer occur only in `problem_phyx_mini_0823`.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0823

open Dimension

/-! ## Dimensionful quantities and coherent-unit readouts -/

/-- Three-dimensional Euclidean vectors used for coherent-unit readouts. -/
abbrev SpatialVector : Type :=
  EuclideanSpace ℝ (Fin 3)

/-- Force has physical dimension `M L T⁻²`. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Torque has physical dimension `M L² T⁻²`. -/
def torqueDimension : Dimension :=
  L𝓭 * forceDimension

/-- A unit-independent nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A unit-independent spatial position with length dimension. -/
abbrev PositionVectorQuantity : Type :=
  Dimensionful (WithDim L𝓭 SpatialVector)

/-- A unit-independent spatial force vector. -/
abbrev ForceVectorQuantity : Type :=
  Dimensionful (WithDim forceDimension SpatialVector)

/-- A unit-independent spatial torque vector about the fitting center. -/
abbrev TorqueVectorQuantity : Type :=
  Dimensionful (WithDim torqueDimension SpatialVector)

/-- Read a nonnegative physical scalar in a coherent unit system. -/
def nonnegativeReadout {d : Dimension}
    (units : UnitChoices)
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Read a physical vector in a coherent unit system. -/
def vectorReadout {d : Dimension}
    (units : UnitChoices)
    (quantity : Dimensionful (WithDim d SpatialVector)) : SpatialVector :=
  (quantity units).val

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI length

/-- Cartesian metre readout of a position. -/
def positionInMeters (position : PositionVectorQuantity) : SpatialVector :=
  vectorReadout UnitChoices.SI position

/-- Cartesian newton readout of a force. -/
def forceInNewtons (force : ForceVectorQuantity) : SpatialVector :=
  vectorReadout UnitChoices.SI force

/-- Euclidean magnitude, in newtons, of a physical force. -/
def forceMagnitudeInNewtons (force : ForceVectorQuantity) : ℝ :=
  ‖forceInNewtons force‖

/-- Cartesian newton-metre readout of a torque. -/
def torqueInNewtonMeters (torque : TorqueVectorQuantity) : SpatialVector :=
  vectorReadout UnitChoices.SI torque

/-- Euclidean magnitude, in newton-metres, of a physical torque. -/
def torqueMagnitudeInNewtonMeters (torque : TorqueVectorQuantity) : ℝ :=
  ‖torqueInNewtonMeters torque‖

/-- The ordinary three-dimensional cross product transported to Euclidean space. -/
def spatialCross (left right : SpatialVector) : SpatialVector :=
  WithLp.toLp 2 (crossProduct left.ofLp right.ofLp)

/-- Dimensionless Cartesian unit vector pointing rightward in the image. -/
def xHat : SpatialVector :=
  EuclideanSpace.single (0 : Fin 3) 1

/-- Dimensionless Cartesian unit vector pointing upward in the image. -/
def yHat : SpatialVector :=
  EuclideanSpace.single (1 : Fin 3) 1

/-- Dimensionless Cartesian unit vector pointing out of the page. -/
def zHat : SpatialVector :=
  EuclideanSpace.single (2 : Fin 3) 1

/-! ## Physical roles and primary-image vocabulary -/

/-- The two distinguished points needed for the lever arm about the fitting. -/
inductive WrenchPoint where
  | fittingCenter
  | forceApplicationPoint
  deriving DecidableEq, Fintype, Repr

/-- Individually visible components of the supplied bitmap. -/
inductive FigureComponent where
  | plumberFoot
  | orangeWrenchAndCheater
  | greyPipeFitting
  | downwardForceArrow
  | dashedHorizontalReference
  | angleArc
  deriving DecidableEq, Fintype, Repr

/-- Literal calibrated labels printed in the supplied bitmap. -/
inductive FigureLabel where
  | force900Newtons
  | distance0Point80Meters
  | angle19Degrees
  deriving DecidableEq, Fintype, Repr

/-- Qualitative direction of the applied-force arrow. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- The method used to extend the wrench handle. -/
inductive HandleExtension where
  | none
  | scrapPipeCheater
  deriving DecidableEq, Repr

/-- Rotation sense in the side view, with positive `z` pointing out of the page. -/
inductive TorqueSense where
  | clockwise
  | counterclockwise
  | zero
  deriving DecidableEq, Repr

/-- Literal labels and incidences transcribed from image `823.png`. -/
structure SuppliedWrenchFigure where
  showsComponent : FigureComponent → Bool
  showsLabel : FigureLabel → Bool
  forceArrowTail : WrenchPoint
  forceArrowDirection : VerticalDirection
  distanceLabelEndpoints : WrenchPoint × WrenchPoint
  distanceLabelInMeters : ℝ
  angleArcVertex : WrenchPoint
  angleLabelInDegrees : ℝ
  forceLabelInNewtons : ℝ
  forceApplicationPointIsLeftOfFitting : Bool
  forceApplicationPointIsAboveFitting : Bool

/--
Independent physical quantities in the wrench experiment.  In particular,
`torqueAboutFitting` is not defined from a displayed answer; the governing law
below constrains it.
-/
structure PipeFittingTorqueSetup where
  handleExtension : HandleExtension
  forceApplicationDistance : LengthQuantity
  handleAngleAboveHorizontalRadians : ℝ
  positionOf : WrenchPoint → PositionVectorQuantity
  appliedWeightForce : ForceVectorQuantity
  torqueAboutFitting : TorqueVectorQuantity
  figure : SuppliedWrenchFigure

/-! ## Source data, geometry, and governing law -/

/-- Numerical and categorical data explicitly stated in the problem prose. -/
structure MatchesProblemStatement (setup : PipeFittingTorqueSetup) : Prop where
  usesScrapPipeCheater : setup.handleExtension = .scrapPipeCheater
  forceApplicationDistanceMeters :
    lengthInMeters setup.forceApplicationDistance = 4 / 5
  appliedWeightMagnitudeNewtons :
    forceMagnitudeInNewtons setup.appliedWeightForce = 900
  handleAngleRadians :
    setup.handleAngleAboveHorizontalRadians = 19 * Real.pi / 180

/--
Primary-image evidence: visible objects, all three numerical labels, the
downward force arrow at the left endpoint, and the up-left placement of that
endpoint relative to the fitting.  No torque value or answer choice occurs
here.
-/
structure MatchesPrimaryFigure (setup : PipeFittingTorqueSetup) : Prop where
  everyComponentShown :
    ∀ component, setup.figure.showsComponent component = true
  everyLabelShown :
    ∀ label, setup.figure.showsLabel label = true
  forceArrowStartsAtApplicationPoint :
    setup.figure.forceArrowTail = .forceApplicationPoint
  forceArrowPointsDownward :
    setup.figure.forceArrowDirection = .downward
  distanceLabelJoinsApplicationPointToFitting :
    setup.figure.distanceLabelEndpoints =
      (.forceApplicationPoint, .fittingCenter)
  displayedDistanceMeters : setup.figure.distanceLabelInMeters = 4 / 5
  distanceLabelMeasuresPhysicalLeverArm :
    setup.figure.distanceLabelInMeters =
      lengthInMeters setup.forceApplicationDistance
  angleArcIsAtFitting : setup.figure.angleArcVertex = .fittingCenter
  displayedAngleDegrees : setup.figure.angleLabelInDegrees = 19
  angleLabelMeasuresPhysicalAngle :
    setup.handleAngleAboveHorizontalRadians =
      setup.figure.angleLabelInDegrees * Real.pi / 180
  displayedForceNewtons : setup.figure.forceLabelInNewtons = 900
  forceLabelMeasuresPhysicalForce :
    setup.figure.forceLabelInNewtons =
      forceMagnitudeInNewtons setup.appliedWeightForce
  applicationPointIsLeftOfFitting :
    setup.figure.forceApplicationPointIsLeftOfFitting = true
  applicationPointIsAboveFitting :
    setup.figure.forceApplicationPointIsAboveFitting = true

/--
Cartesian realization of the pictured handle.  From the fitting center the
force point lies up-left: its horizontal component is negative and its
vertical component is positive.  This is geometry only, not a torque result.
-/
structure MatchesHandleGeometry (setup : PipeFittingTorqueSetup) : Prop where
  fittingCenterAtOrigin :
    positionInMeters (setup.positionOf .fittingCenter) = 0
  applicationPointPosition :
    positionInMeters (setup.positionOf .forceApplicationPoint) =
      (-(lengthInMeters setup.forceApplicationDistance *
          Real.cos setup.handleAngleAboveHorizontalRadians)) • xHat +
        (lengthInMeters setup.forceApplicationDistance *
          Real.sin setup.handleAngleAboveHorizontalRadians) • yHat

/-- Cartesian force direction corresponding to the vertical red arrow. -/
structure MatchesDownwardForceGeometry
    (setup : PipeFittingTorqueSetup) : Prop where
  appliedForceIsVerticalAndDownward :
    forceInNewtons setup.appliedWeightForce =
      (-forceMagnitudeInNewtons setup.appliedWeightForce) • yHat

/--
The governing moment-of-force law in every coherent unit system.  The lever
arm is measured from the fitting center to the force-application point.  This
law contains no numerical torque answer.
-/
structure SatisfiesTorqueLaw (setup : PipeFittingTorqueSetup) : Prop where
  torqueIsLeverArmCrossForce :
    ∀ units : UnitChoices,
      vectorReadout units setup.torqueAboutFitting =
        spatialCross
          (vectorReadout units (setup.positionOf .forceApplicationPoint) -
            vectorReadout units (setup.positionOf .fittingCenter))
          (vectorReadout units setup.appliedWeightForce)

/-! ## Displayed choices and current target -/

/-- Labels of the four multiple-choice magnitudes. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Torque magnitude printed beside each answer label, in newton-metres. -/
def displayedTorqueMagnitudeInNewtonMeters : AnswerChoice → ℝ
  | .A => 700
  | .B => 680
  | .C => 340
  | .D => 350

/-- The answer label recorded in the dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .B

/--
Agreement with a whole-ten newton-metre display value: the exact magnitude is
within half of one `10 N m` display increment.
-/
def AgreesAtTenNewtonMeterPrecision
    (setup : PipeFittingTorqueSetup) (choice : AnswerChoice) : Prop :=
  |torqueMagnitudeInNewtonMeters setup.torqueAboutFitting -
      displayedTorqueMagnitudeInNewtonMeters choice| < 5

/-- Rotation sense read from the sign of the out-of-page torque component. -/
def torqueSense (torque : TorqueVectorQuantity) : TorqueSense :=
  if 0 < torqueInNewtonMeters torque (2 : Fin 3) then
    .counterclockwise
  else if torqueInNewtonMeters torque (2 : Fin 3) < 0 then
    .clockwise
  else
    .zero

/--
The applied torque is
`720 cos (19°) N m` along positive `z`, hence counterclockwise.  Its magnitude
agrees at the displayed precision with `680 N m`, the recorded answer B.

Blueprint: `thm:physics:phyx_mini_0823:target`.
-/
theorem problem_phyx_mini_0823
    (setup : PipeFittingTorqueSetup)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryFigure setup)
    (_handleGeometry : MatchesHandleGeometry setup)
    (_forceGeometry : MatchesDownwardForceGeometry setup)
    (_torqueLaw : SatisfiesTorqueLaw setup) :
    torqueInNewtonMeters setup.torqueAboutFitting =
        (720 * Real.cos (19 * Real.pi / 180)) • zHat ∧
      torqueMagnitudeInNewtonMeters setup.torqueAboutFitting =
        720 * Real.cos (19 * Real.pi / 180) ∧
      torqueSense setup.torqueAboutFitting = .counterclockwise ∧
      AgreesAtTenNewtonMeterPrecision setup recordedAnswerChoice := by
  have hTorqueVector :
      torqueInNewtonMeters setup.torqueAboutFitting =
        (720 * Real.cos (19 * Real.pi / 180)) • zHat := by
    rw [torqueInNewtonMeters,
      _torqueLaw.torqueIsLeverArmCrossForce UnitChoices.SI]
    rw [show
          vectorReadout UnitChoices.SI
              (setup.positionOf .forceApplicationPoint) =
            (-(lengthInMeters setup.forceApplicationDistance *
                Real.cos setup.handleAngleAboveHorizontalRadians)) • xHat +
              (lengthInMeters setup.forceApplicationDistance *
                Real.sin setup.handleAngleAboveHorizontalRadians) • yHat by
          exact _handleGeometry.applicationPointPosition,
      show
          vectorReadout UnitChoices.SI
              (setup.positionOf .fittingCenter) = 0 by
          exact _handleGeometry.fittingCenterAtOrigin,
      show
          vectorReadout UnitChoices.SI setup.appliedWeightForce =
            (-forceMagnitudeInNewtons setup.appliedWeightForce) • yHat by
          exact _forceGeometry.appliedForceIsVerticalAndDownward,
      _problem.forceApplicationDistanceMeters,
      _problem.appliedWeightMagnitudeNewtons,
      _problem.handleAngleRadians]
    ext i
    fin_cases i
    all_goals
      simp [spatialCross, xHat, yHat, zHat, EuclideanSpace.single,
        crossProduct]
    all_goals ring
  have hCosPos : 0 < Real.cos (19 * Real.pi / 180) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  have hMagnitude :
      torqueMagnitudeInNewtonMeters setup.torqueAboutFitting =
        720 * Real.cos (19 * Real.pi / 180) := by
    rw [torqueMagnitudeInNewtonMeters, hTorqueVector, norm_smul,
      Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) hCosPos)]
    norm_num [zHat, EuclideanSpace.single]
  have hSense :
      torqueSense setup.torqueAboutFitting = .counterclockwise := by
    simp [torqueSense, hTorqueVector, zHat, EuclideanSpace.single,
      mul_pos (by norm_num : (0 : ℝ) < 720) hCosPos]
  refine ⟨hTorqueVector, hMagnitude, hSense, ?_⟩
  rw [AgreesAtTenNewtonMeterPrecision, hMagnitude]
  simp only [recordedAnswerChoice, displayedTorqueMagnitudeInNewtonMeters]
  rw [abs_lt]
  have hcos20Half : (1 / 2 : ℝ) < Real.cos (Real.pi / 9) := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi
      (by positivity) (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos])
  have hcos20Cubic :
      4 * Real.cos (Real.pi / 9) ^ 3 -
          3 * Real.cos (Real.pi / 9) =
        1 / 2 := by
    have htriple := Real.cos_three_mul (Real.pi / 9)
    rw [show 3 * (Real.pi / 9) = Real.pi / 3 by ring,
      Real.cos_pi_div_three] at htriple
    linarith
  have hcos20Lower : (15 / 16 : ℝ) < Real.cos (Real.pi / 9) := by
    by_contra h
    have hle :
        Real.cos (Real.pi / 9) ≤ (15 / 16 : ℝ) := le_of_not_gt h
    have hfactorPositive :
        0 < 4 * ((15 / 16 : ℝ) ^ 2 +
            (15 / 16 : ℝ) * Real.cos (Real.pi / 9) +
            Real.cos (Real.pi / 9) ^ 2) -
          3 := by
      nlinarith [sq_nonneg (Real.cos (Real.pi / 9) - 1 / 2)]
    have hproduct :
        0 ≤ ((15 / 16 : ℝ) - Real.cos (Real.pi / 9)) *
          (4 * ((15 / 16 : ℝ) ^ 2 +
              (15 / 16 : ℝ) * Real.cos (Real.pi / 9) +
              Real.cos (Real.pi / 9) ^ 2) -
            3) :=
      mul_nonneg (sub_nonneg.mpr hle) hfactorPositive.le
    nlinarith
  have hCosLowerCompare :
      Real.cos (Real.pi / 9) <
        Real.cos (19 * Real.pi / 180) := by
    exact Real.cos_lt_cos_of_nonneg_of_le_pi
      (by positivity) (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos])
  have hcos10 :
      Real.cos (Real.pi / 10) =
        Real.sqrt ((1 + Real.cos (Real.pi / 5)) / 2) := by
    convert Real.cos_half (x := Real.pi / 5)
      (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]) using 1
    all_goals ring_nf
  have hsqrt5Upper : Real.sqrt 5 < (56 / 25 : ℝ) := by
    apply (sq_lt_sq₀ (Real.sqrt_nonneg 5) (by norm_num)).mp
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  have hcos10Upper :
      Real.cos (Real.pi / 10) < (137 / 144 : ℝ) := by
    rw [hcos10, Real.cos_pi_div_five]
    have hradNonneg :
        (0 : ℝ) ≤ (1 + (1 + Real.sqrt 5) / 4) / 2 := by
      positivity
    have hsquare := Real.sq_sqrt hradNonneg
    apply (sq_lt_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
    nlinarith
  have hCosUpperCompare :
      Real.cos (19 * Real.pi / 180) <
        Real.cos (Real.pi / 10) := by
    exact Real.cos_lt_cos_of_nonneg_of_le_pi
      (by positivity) (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos])
  constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0823
