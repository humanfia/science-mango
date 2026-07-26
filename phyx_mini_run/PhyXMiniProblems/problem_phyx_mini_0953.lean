import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0953

open Dimension

/-!
# Tension supporting a hinged current-carrying rod

A thin uniform rod is hinged at its lower end `P` and held by a horizontal
string attached at its upper end.  The rod makes an angle of `53 degrees`
above the horizontal.  It carries current toward `P` while a uniform magnetic
field points into the page.

The primary image confirms that the marked angle is measured from the
horizontal, despite the auxiliary caption's reference to a vertical line.  By
the right-hand rule the magnetic force points down and right, perpendicular to
the rod.  Thus gravity and magnetic force exert clockwise moments about `P`,
while the leftward string tension exerts a counterclockwise moment.

Physical magnitudes are unit-independent Physlib `Dimensionful` quantities.
Real numbers occur only as coherent-SI readouts, dimensionless angle readouts,
figure labels, and displayed answer values.

Assumption/target split:

* governing laws: a uniform applied field, `F_B = I L B`, the right-hand-rule
  direction, `W = m g`, the three moment-arm formulae about `P`, zero hinge
  moment, and static rotational equilibrium;
* previous-part results: none;
* figure/data readouts: hinge label `P`, a thin uniform `0.0840 kg`, `18.0 cm`
  rod at `53 degrees`, a horizontal string, an into-page `0.120 T` field, and
  a `12.0 A` current directed toward `P`;
* current target conclusions: the general tension formula and the fact that
  its value rounds to `0.472 N`, the displayed answer B.

Neither target conclusion occurs in a setup field or premise structure.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- Electric current has dimension `C T⁻¹`. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Magnetic flux density (tesla) has dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Acceleration has dimension `L T⁻²`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Force (newton) has dimension `M L T⁻²`. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Torque (newton metre) has dimension `M L² T⁻²`. -/
def torqueDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent current magnitude. -/
abbrev ElectricCurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationMagnitude : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative, unit-independent force magnitude. -/
abbrev ForceMagnitude : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A nonnegative, unit-independent moment magnitude about the hinge. -/
abbrev TorqueMagnitude : Type :=
  Dimensionful (WithDim torqueDimension NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI base units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Read a length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Read a length in centimetres. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Read a current magnitude in amperes. -/
def currentInAmperes (current : ElectricCurrentMagnitude) : ℝ :=
  nonnegativeSIReadout current

/-- Read a magnetic flux density in teslas. -/
def magneticFluxDensityInTeslas
    (field : MagneticFluxDensityMagnitude) : ℝ :=
  nonnegativeSIReadout field

/-- Read an acceleration magnitude in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitude) : ℝ :=
  nonnegativeSIReadout acceleration

/-- Read a force magnitude in newtons. -/
def forceInNewtons (force : ForceMagnitude) : ℝ :=
  nonnegativeSIReadout force

/-- Read a moment magnitude in newton metres. -/
def torqueInNewtonMeters (torque : TorqueMagnitude) : ℝ :=
  nonnegativeSIReadout torque

/-- Convert a degree readout to Mathlib's quotient type of real angles. -/
def degreesToAngle (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-! ## Spatial geometry and primary-image vocabulary -/

/-- A coherent-SI direction vector in physical three-space. -/
abbrev SpatialVector : Type :=
  EuclideanSpace ℝ (Fin 3)

/-- Rightward unit vector in the plane of the supplied image. -/
def rightwardUnitVector : SpatialVector :=
  EuclideanSpace.single (0 : Fin 3) 1

/-- Upward unit vector in the plane of the supplied image. -/
def upwardUnitVector : SpatialVector :=
  EuclideanSpace.single (1 : Fin 3) 1

/-- Unit vector into the page, represented by the field-cross convention. -/
def intoPageUnitVector : SpatialVector :=
  -EuclideanSpace.single (2 : Fin 3) 1

/-- The ordinary right-handed cross product on Euclidean three-vectors. -/
def spatialCross (left right : SpatialVector) : SpatialVector :=
  WithLp.toLp 2 (crossProduct left.ofLp right.ofLp)

/-- Unit direction of a rod inclined by `angle` above the horizontal. -/
def rodDirectionAboveHorizontal (angle : Real.Angle) : SpatialVector :=
  Real.Angle.cos angle • rightwardUnitVector +
    Real.Angle.sin angle • upwardUnitVector

/-- Idealized distribution of mass along the rod. -/
inductive RodMassModel where
  | thinUniform
  | other
  deriving DecidableEq, Repr

/-- Mechanical model of the attachment at the lower endpoint. -/
inductive HingeModel where
  | frictionlessPointHinge
  | fixedClamp
  deriving DecidableEq, Repr

/-- Orientation class of the string shown at the rod's upper endpoint. -/
inductive StringOrientation where
  | horizontal
  | vertical
  | oblique
  deriving DecidableEq, Repr

/-- Point of the rod at which the supporting string is attached. -/
inductive StringAttachment where
  | upperEndpoint
  | midpoint
  deriving DecidableEq, Repr

/-- Surface carrying the hinge at `P`. -/
inductive HingeSupportSurface where
  | floor
  | wall
  deriving DecidableEq, Repr

/-- Coarse directions sufficient to transcribe the supplied raster. -/
inductive DiagramDirection where
  | leftward
  | rightward
  | upward
  | downward
  | upAndRight
  | downAndLeft
  | downAndRight
  | intoPage
  | outOfPage
  deriving DecidableEq, Repr

/-- Literal labels and qualitative geometry visible in image `953.png`. -/
structure HingedRodFigure where
  rodShown : Bool
  hingeShown : Bool
  hingeLabel : String
  horizontalReferenceShown : Bool
  rodDirectionFromHinge : DiagramDirection
  stringShown : Bool
  stringDirectionFromRod : DiagramDirection
  currentArrowShown : Bool
  currentLabel : String
  currentArrowDirection : DiagramDirection
  fieldCrossesShown : Bool
  magneticFieldVectorLabel : String
  magneticFieldDirection : DiagramDirection
  angleArcShown : Bool
  angleLabel : String

/-!
Independent observables for the supported rod.  In particular, the tension
and the four moment magnitudes are stored independently and are constrained
only by the governing laws below.
-/
structure HingedCurrentRodSetup where
  rodMassModel : RodMassModel
  hingeModel : HingeModel
  hingeSupportSurface : HingeSupportSurface
  stringOrientation : StringOrientation
  stringAttachment : StringAttachment
  rodMass : MassQuantity
  rodLength : LengthQuantity
  rodAngleAboveHorizontal : Real.Angle
  currentMagnitude : ElectricCurrentMagnitude
  magneticFieldMagnitude : MagneticFluxDensityMagnitude
  gravitationalAcceleration : AccelerationMagnitude
  stringTensionMagnitude : ForceMagnitude
  weightMagnitude : ForceMagnitude
  magneticForceMagnitude : ForceMagnitude
  stringMomentAboutP : TorqueMagnitude
  weightMomentAboutP : TorqueMagnitude
  magneticMomentAboutP : TorqueMagnitude
  hingeMomentAboutP : TorqueMagnitude
  observationTime : Time
  rodSpatialSupportAtObservation : Set (Space 3)
  uniformFieldRegion : Set (Time × Space 3)
  magneticField : Electromagnetism.MagneticField 3
  rodAxisFromP : SpatialVector
  currentDirection : SpatialVector
  fieldDirection : SpatialVector
  tensionDirection : SpatialVector
  weightDirection : SpatialVector
  magneticForceDirection : SpatialVector
  figure : HingedRodFigure

/-! ## Scenario, figure evidence, and numerical data -/

/-- The idealizations stated in the written physical scenario. -/
structure MatchesWrittenHingedRodScenario
    (setup : HingedCurrentRodSetup) : Prop where
  rodIsThinAndUniform : setup.rodMassModel = .thinUniform
  lowerAttachmentIsFrictionlessHinge :
    setup.hingeModel = .frictionlessPointHinge
  hingeIsAttachedToFloor :
    setup.hingeSupportSurface = .floor
  supportingStringIsHorizontal :
    setup.stringOrientation = .horizontal
  stringIsAttachedAtRodTop :
    setup.stringAttachment = .upperEndpoint

/-!
Primary-raster evidence.  The image shows the angle arc between the rod and
the horizontal baseline at `P`, a downward current arrow along the rod, field
crosses, and a horizontal string extending left from the upper endpoint.
-/
structure MatchesPrimaryHingedRodFigure
    (setup : HingedCurrentRodSetup) : Prop where
  rodIsShown : setup.figure.rodShown = true
  hingeIsShown : setup.figure.hingeShown = true
  hingeIsLabeledP : setup.figure.hingeLabel = "P"
  horizontalReferenceIsShown :
    setup.figure.horizontalReferenceShown = true
  rodRunsUpAndRightFromP :
    setup.figure.rodDirectionFromHinge = .upAndRight
  horizontalStringIsShown : setup.figure.stringShown = true
  stringRunsLeftFromRod :
    setup.figure.stringDirectionFromRod = .leftward
  currentArrowIsShown : setup.figure.currentArrowShown = true
  currentIsLabeledI : setup.figure.currentLabel = "I"
  currentArrowRunsDownTowardP :
    setup.figure.currentArrowDirection = .downAndLeft
  uniformFieldCrossesAreShown :
    setup.figure.fieldCrossesShown = true
  fieldIsLabeledB :
    setup.figure.magneticFieldVectorLabel = "B"
  crossesMeanFieldIntoPage :
    setup.figure.magneticFieldDirection = .intoPage
  angleArcIsShown : setup.figure.angleArcShown = true
  angleIsLabeledTheta : setup.figure.angleLabel = "theta"

/-- Exact stated measurements, expressed in their named units. -/
structure MatchesHingedRodProblemData
    (setup : HingedCurrentRodSetup) : Prop where
  massIsPointZeroEightFourKilograms :
    massInKilograms setup.rodMass = (21 : ℝ) / 250
  lengthIsEighteenCentimeters :
    lengthInCentimeters setup.rodLength = 18
  fieldIsPointOneTwoZeroTeslas :
    magneticFluxDensityInTeslas setup.magneticFieldMagnitude =
      (3 : ℝ) / 25
  currentIsTwelveAmperes :
    currentInAmperes setup.currentMagnitude = 12
  rodAngleIsFiftyThreeDegrees :
    setup.rodAngleAboveHorizontal = degreesToAngle 53

/-- Rounded gravitational acceleration convention used by the answer choices. -/
structure UsesSchoolGravityCalibration
    (setup : HingedCurrentRodSetup) : Prop where
  gravitationalAccelerationIsNinePointEight :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = (49 : ℝ) / 5

/-- Positivity and nondegeneracy conditions for the physical branch. -/
structure HasPhysicalHingedRodParameters
    (setup : HingedCurrentRodSetup) : Prop where
  massPositive : 0 < massInKilograms setup.rodMass
  lengthPositive : 0 < lengthInMeters setup.rodLength
  currentPositive : 0 < currentInAmperes setup.currentMagnitude
  fieldMagnitudePositive :
    0 < magneticFluxDensityInTeslas setup.magneticFieldMagnitude
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  tensionPositive :
    0 < forceInNewtons setup.stringTensionMagnitude
  sineOfRodAnglePositive :
    0 < Real.Angle.sin setup.rodAngleAboveHorizontal
  rodSpatialSupportNonempty :
    setup.rodSpatialSupportAtObservation.Nonempty
  fieldRegionNonempty : setup.uniformFieldRegion.Nonempty

/-!
The physical direction vectors encode the geometry described by the prose and
confirmed by the raster.  Current is opposite the rod axis because it flows
toward `P`; tension points toward the wall.
-/
structure HasHingedRodGeometry
    (setup : HingedCurrentRodSetup) : Prop where
  rodAxisMatchesAngle :
    setup.rodAxisFromP =
      rodDirectionAboveHorizontal setup.rodAngleAboveHorizontal
  currentFlowsTowardP :
    setup.currentDirection = -setup.rodAxisFromP
  magneticFieldPointsIntoPage :
    setup.fieldDirection = intoPageUnitVector
  tensionPullsHorizontallyLeft :
    setup.tensionDirection = -rightwardUnitVector
  weightPointsDownward :
    setup.weightDirection = -upwardUnitVector

/-! ## Uniform field and governing force and moment laws -/

/-!
The Physlib magnetic field has the stated direction and coherent-SI magnitude
throughout the modeled uniform-field region at the observation time.
-/
structure HasUniformAppliedMagneticField
    (setup : HingedCurrentRodSetup) : Prop where
  fieldDirectionIsUnit : ‖setup.fieldDirection‖ = 1
  entireRodLiesInUniformFieldRegion : ∀ position,
    position ∈ setup.rodSpatialSupportAtObservation →
      (setup.observationTime, position) ∈ setup.uniformFieldRegion
  uniformVectorAtObservation : ∀ position,
    (setup.observationTime, position) ∈ setup.uniformFieldRegion →
      setup.magneticField setup.observationTime position =
        magneticFluxDensityInTeslas setup.magneticFieldMagnitude •
          setup.fieldDirection

/-!
For a straight rod perpendicular to a uniform field, the magnetic resultant
has magnitude `I L B`; its direction is the right-handed cross product of the
current direction with the field direction.
-/
structure SatisfiesMagneticForceLaw
    (setup : HingedCurrentRodSetup) : Prop where
  magneticForceMagnitudeLaw :
    forceInNewtons setup.magneticForceMagnitude =
      currentInAmperes setup.currentMagnitude *
        lengthInMeters setup.rodLength *
          magneticFluxDensityInTeslas setup.magneticFieldMagnitude
  magneticForceDirectionLaw :
    setup.magneticForceDirection =
      spatialCross setup.currentDirection setup.fieldDirection

/-!
Weight, geometric moment arms, the frictionless-hinge condition, and static
rotational equilibrium about `P`.  Uniform gravity and magnetic loading place
their resultants at the rod midpoint.  These are general balance laws and do
not state the requested tension formula or numerical answer.
-/
structure SatisfiesHingedRodStaticLaws
    (setup : HingedCurrentRodSetup) : Prop where
  weightLaw :
    forceInNewtons setup.weightMagnitude =
      massInKilograms setup.rodMass *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration
  stringMomentLaw :
    torqueInNewtonMeters setup.stringMomentAboutP =
      forceInNewtons setup.stringTensionMagnitude *
        lengthInMeters setup.rodLength *
          Real.Angle.sin setup.rodAngleAboveHorizontal
  weightMomentLaw :
    torqueInNewtonMeters setup.weightMomentAboutP =
      forceInNewtons setup.weightMagnitude *
        (lengthInMeters setup.rodLength / 2) *
          Real.Angle.cos setup.rodAngleAboveHorizontal
  magneticMomentLaw :
    torqueInNewtonMeters setup.magneticMomentAboutP =
      forceInNewtons setup.magneticForceMagnitude *
        (lengthInMeters setup.rodLength / 2)
  frictionlessHingeMomentLaw :
    torqueInNewtonMeters setup.hingeMomentAboutP = 0
  staticTorqueBalanceAboutP :
    torqueInNewtonMeters setup.stringMomentAboutP +
        torqueInNewtonMeters setup.hingeMomentAboutP =
      torqueInNewtonMeters setup.weightMomentAboutP +
        torqueInNewtonMeters setup.magneticMomentAboutP

/-! ## Derived tension relation and displayed-answer target -/

/-!
Eliminating the separately modeled forces and moments gives the general
tension formula for this geometry.  This is a derived conclusion, not a law
field.
-/
lemma tension_formula
    (setup : HingedCurrentRodSetup)
    (_physical : HasPhysicalHingedRodParameters setup)
    (_magneticForce : SatisfiesMagneticForceLaw setup)
    (_statics : SatisfiesHingedRodStaticLaws setup) :
    forceInNewtons setup.stringTensionMagnitude =
      (massInKilograms setup.rodMass *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
            Real.Angle.cos setup.rodAngleAboveHorizontal +
          currentInAmperes setup.currentMagnitude *
            lengthInMeters setup.rodLength *
              magneticFluxDensityInTeslas
                setup.magneticFieldMagnitude) /
        (2 * Real.Angle.sin setup.rodAngleAboveHorizontal) := by
  have h := _statics.staticTorqueBalanceAboutP
  rw [_statics.stringMomentLaw, _statics.frictionlessHingeMomentLaw,
    _statics.weightMomentLaw, _statics.magneticMomentLaw,
    _statics.weightLaw, _magneticForce.magneticForceMagnitudeLaw] at h
  apply (eq_div_iff
    (mul_ne_zero (by norm_num) _physical.sineOfRodAnglePositive.ne')).2
  nlinarith [h, _physical.lengthPositive]

/-- The four tension choices printed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Tension in newtons printed beside each answer label. -/
def AnswerChoice.tensionInNewtons : AnswerChoice → ℝ
  | .A => 394 / 1000
  | .B => 472 / 1000
  | .C => 528 / 1000
  | .D => 708 / 1000

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- The actual tension rounds to a displayed value at the nearest `0.001 N`. -/
def RoundsToNearestMilliNewton (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 1 / 2000

/-- A displayed choice is strictly nearer than every alternative choice. -/
def IsUniqueNearestDisplayedTension
    (actual : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |actual - choice.tensionInNewtons| <
      |actual - other.tensionInNewtons|

/-!
Using `g = 9.8 m/s²`, the force and moment laws give approximately
`0.47244 N`.  It rounds to `0.472 N` and is uniquely nearest to answer B.

Blueprint: `thm:physics:phyx_mini_0953:target`.
-/
theorem string_tension_is_answer_B
    (setup : HingedCurrentRodSetup)
    (_scenario : MatchesWrittenHingedRodScenario setup)
    (_figure : MatchesPrimaryHingedRodFigure setup)
    (_data : MatchesHingedRodProblemData setup)
    (_gravity : UsesSchoolGravityCalibration setup)
    (_physical : HasPhysicalHingedRodParameters setup)
    (_geometry : HasHingedRodGeometry setup)
    (_uniformField : HasUniformAppliedMagneticField setup)
    (_magneticForce : SatisfiesMagneticForceLaw setup)
    (_statics : SatisfiesHingedRodStaticLaws setup) :
    RoundsToNearestMilliNewton
        (forceInNewtons setup.stringTensionMagnitude)
        AnswerChoice.B.tensionInNewtons ∧
      IsUniqueNearestDisplayedTension
        (forceInNewtons setup.stringTensionMagnitude)
        recordedDatasetAnswer := by
  have hLength :
      lengthInMeters setup.rodLength = (9 : ℝ) / 50 := by
    have h := _data.lengthIsEighteenCentimeters
    unfold lengthInCentimeters at h
    linarith

  -- Use `53° = 60° - 7°`; the library's elementary Taylor bound is
  -- particularly sharp at the resulting small angle.
  let x : ℝ := 7 * Real.pi / 180
  have hxLower : (12217 : ℝ) / 100000 < x := by
    dsimp [x]
    linarith only [Real.pi_gt_d6]
  have hxUpper : x < (6109 : ℝ) / 50000 := by
    dsimp [x]
    linarith only [Real.pi_lt_d6]
  have hDistance :
      |x - (4887 : ℝ) / 40000| ≤ (1 : ℝ) / 200000 := by
    rw [abs_le]
    constructor <;> linarith only [hxLower, hxUpper]

  have hSinCenter := abs_le.mp (Real.sin_bound
    (x := (4887 / 40000 : ℝ)) (by norm_num [abs_of_nonneg]))
  have hCosCenter := abs_le.mp (Real.cos_bound
    (x := (4887 / 40000 : ℝ)) (by norm_num [abs_of_nonneg]))
  norm_num [abs_of_nonneg] at hSinCenter hCosCenter
  have hSinLipschitz := abs_le.mp
    ((Real.abs_sin_sub_sin_le x (4887 / 40000 : ℝ)).trans hDistance)
  have hCosLipschitz := abs_le.mp
    ((Real.abs_cos_sub_cos_le x (4887 / 40000 : ℝ)).trans hDistance)
  have hSinXLower : (12185 : ℝ) / 100000 < Real.sin x := by
    linarith only [hSinCenter.1, hSinLipschitz.1]
  have hSinXUpper : Real.sin x < (12189 : ℝ) / 100000 := by
    linarith only [hSinCenter.2, hSinLipschitz.2]
  have hCosXLower : (99251 : ℝ) / 100000 < Real.cos x := by
    linarith only [hCosCenter.1, hCosLipschitz.1]
  have hCosXUpper : Real.cos x < (12407 : ℝ) / 12500 := by
    linarith only [hCosCenter.2, hCosLipschitz.2]

  have hSqrtThreeLower :
      (173205 : ℝ) / 100000 < Real.sqrt 3 :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hSqrtThreeUpper :
      Real.sqrt 3 < (86603 : ℝ) / 50000 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

  have hAngle :
      (53 * Real.pi / 180 : ℝ) = Real.pi / 3 - x := by
    dsimp [x]
    ring
  have hSinAngle :
      Real.sin (53 * Real.pi / 180) =
        Real.sqrt 3 / 2 * Real.cos x - (1 / 2 : ℝ) * Real.sin x := by
    rw [hAngle, Real.sin_sub, Real.sin_pi_div_three,
      Real.cos_pi_div_three]
  have hCosAngle :
      Real.cos (53 * Real.pi / 180) =
        (1 / 2 : ℝ) * Real.cos x + Real.sqrt 3 / 2 * Real.sin x := by
    rw [hAngle, Real.cos_sub, Real.cos_pi_div_three,
      Real.sin_pi_div_three]

  have hSqrtCosLower :
      (173205 : ℝ) / 100000 * ((99251 : ℝ) / 100000) <
        Real.sqrt 3 * Real.cos x :=
    mul_lt_mul hSqrtThreeLower hCosXLower.le (by norm_num)
      (Real.sqrt_nonneg 3)
  have hSqrtCosUpper :
      Real.sqrt 3 * Real.cos x <
        (86603 : ℝ) / 50000 * ((12407 : ℝ) / 12500) :=
    mul_lt_mul hSqrtThreeUpper hCosXUpper.le
      (by linarith only [hCosXLower]) (by norm_num)
  have hSqrtSinLower :
      (173205 : ℝ) / 100000 * ((12185 : ℝ) / 100000) <
        Real.sqrt 3 * Real.sin x :=
    mul_lt_mul hSqrtThreeLower hSinXLower.le (by norm_num)
      (Real.sqrt_nonneg 3)
  have hSqrtSinUpper :
      Real.sqrt 3 * Real.sin x <
        (86603 : ℝ) / 50000 * ((12189 : ℝ) / 100000) :=
    mul_lt_mul hSqrtThreeUpper hSinXUpper.le
      (by linarith only [hSinXLower]) (by norm_num)

  have hSinAngleLower :
      (79859 : ℝ) / 100000 < Real.sin (53 * Real.pi / 180) := by
    linarith only [hSinAngle, hSqrtCosLower, hSinXUpper]
  have hSinAngleUpper :
      Real.sin (53 * Real.pi / 180) < (7987 : ℝ) / 10000 := by
    linarith only [hSinAngle, hSqrtCosUpper, hSinXLower]
  have hCosAngleLower :
      (15043 : ℝ) / 25000 < Real.cos (53 * Real.pi / 180) := by
    linarith only [hCosAngle, hCosXLower, hSqrtSinLower]
  have hCosAngleUpper :
      Real.cos (53 * Real.pi / 180) < (30093 : ℝ) / 50000 := by
    linarith only [hCosAngle, hCosXUpper, hSqrtSinUpper]

  have hT := tension_formula setup _physical _magneticForce _statics
  rw [_data.massIsPointZeroEightFourKilograms,
    _gravity.gravitationalAccelerationIsNinePointEight,
    hLength, _data.currentIsTwelveAmperes,
    _data.fieldIsPointOneTwoZeroTeslas,
    _data.rodAngleIsFiftyThreeDegrees] at hT
  simp only [degreesToAngle, Real.Angle.sin_coe,
    Real.Angle.cos_coe] at hT

  have hSinAnglePositive :
      0 < Real.sin (53 * Real.pi / 180) := by
    linarith only [hSinAngleLower]
  have hDenominatorPositive :
      0 < 2 * Real.sin (53 * Real.pi / 180) := by
    positivity
  have hTensionLower :
      (943 : ℝ) / 2000 <
        forceInNewtons setup.stringTensionMagnitude := by
    rw [hT]
    apply (lt_div_iff₀ hDenominatorPositive).2
    nlinarith only [hSinAngleUpper, hCosAngleLower]
  have hTensionUpper :
      forceInNewtons setup.stringTensionMagnitude <
        (189 : ℝ) / 400 := by
    rw [hT]
    apply (div_lt_iff₀ hDenominatorPositive).2
    nlinarith only [hSinAngleLower, hCosAngleUpper]

  have hClose :
      |forceInNewtons setup.stringTensionMagnitude -
          AnswerChoice.B.tensionInNewtons| < (1 : ℝ) / 2000 := by
    simp only [AnswerChoice.tensionInNewtons]
    rw [abs_lt]
    constructor <;>
      linarith only [hTensionLower, hTensionUpper]
  constructor
  · exact hClose
  · unfold IsUniqueNearestDisplayedTension recordedDatasetAnswer
    have hCloseNumeric :
        |forceInNewtons setup.stringTensionMagnitude -
            (472 : ℝ) / 1000| < (1 : ℝ) / 2000 := by
      simpa only [AnswerChoice.tensionInNewtons] using hClose
    intro other hOther
    fin_cases other
    · simp only [AnswerChoice.tensionInNewtons]
      rw [abs_of_pos (by
        linarith only [hTensionLower] :
          0 < forceInNewtons setup.stringTensionMagnitude -
            (394 : ℝ) / 1000)]
      linarith only [hCloseNumeric, hTensionLower]
    · exact (hOther rfl).elim
    · simp only [AnswerChoice.tensionInNewtons]
      rw [abs_of_neg (by
        linarith only [hTensionUpper] :
          forceInNewtons setup.stringTensionMagnitude -
            (528 : ℝ) / 1000 < 0)]
      linarith only [hCloseNumeric, hTensionUpper]
    · simp only [AnswerChoice.tensionInNewtons]
      rw [abs_of_neg (by
        linarith only [hTensionUpper] :
          forceInNewtons setup.stringTensionMagnitude -
            (708 : ℝ) / 1000 < 0)]
      linarith only [hCloseNumeric, hTensionUpper]

end PhyXMiniProblems.ProblemPhyXMini0953
