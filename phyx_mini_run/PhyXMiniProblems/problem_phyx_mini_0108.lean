import Mathlib
import Physlib.Units.WithDim.Basic

/-!
# Angular magnification of a reflecting telescope

A concave spherical primary mirror has radius of curvature `1.30 m`, and the
converging eyepiece has focal length `1.10 cm`. The telescope is adjusted so
that its final image is at infinity. Physical lengths are represented by
Physlib dimensionful quantities; angular magnification is a dimensionless real
magnitude.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0108

open Dimension

/-- A real-valued physical length, independent of the chosen unit readout. -/
abbrev OpticalLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Unit choices in which length readouts are measured in centimetres. -/
def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- Read a physical length as a real number of metres. -/
def lengthInMeters (length : OpticalLength) : ℝ :=
  (length UnitChoices.SI).val

/-- Read a physical length as a real number of centimetres. -/
def lengthInCentimeters (length : OpticalLength) : ℝ :=
  (length centimeterUnitChoices).val

/-- Optical elements and focal landmark visible in the source figure. -/
inductive FigureLandmark where
  | observerEye
  | eyepiece
  | primaryFocus
  | primaryMirror
  deriving DecidableEq, Repr

/-- The optical form of the primary mirror. -/
inductive PrimaryMirrorGeometry where
  | concaveSpherical
  | other
  deriving DecidableEq, Repr

/-- The optical action of the eyepiece. -/
inductive EyepieceKind where
  | converging
  | other
  deriving DecidableEq, Repr

/-- Successive regions of the ray path shown in the telescope diagram. -/
inductive TelescopeRayStage where
  | incomingToPrimaryMirror
  | primaryMirrorToFocus
  | primaryFocusToEyepiece
  | eyepieceToObserver
  deriving DecidableEq, Repr

/-- Qualitative paraxial-ray patterns used to encode the diagram. -/
inductive ParaxialRayPattern where
  | parallelToOpticalAxis
  | convergingTowardPrimaryFocus
  | divergingFromPrimaryFocus
  deriving DecidableEq, Repr

/-- Whether the final image is finite or at optical infinity. -/
inductive FinalImageLocation where
  | finite
  | infinity
  deriving DecidableEq, Repr

/--
The physical quantities and qualitative optical data of the reflecting
telescope. The requested angular magnification is stored as an unknown
nonnegative magnitude, not as an answer value.
-/
structure ReflectingTelescopeSetup where
  primaryMirrorGeometry : PrimaryMirrorGeometry
  eyepieceKind : EyepieceKind
  primaryMirrorRadiusOfCurvature : OpticalLength
  primaryMirrorFocalLength : OpticalLength
  eyepieceFocalLength : OpticalLength
  rayPattern : TelescopeRayStage → ParaxialRayPattern
  finalImageLocation : FinalImageLocation
  angularMagnificationMagnitude : ℝ

/--
Problem-text and primary-figure readouts. The mirror is concave and spherical;
the eyepiece is converging; incident light and light delivered to the eye are
parallel, with reflection through the primary focus between them.
-/
structure MatchesProblemAndFigure (setup : ReflectingTelescopeSetup) : Prop where
  mirrorGeometry :
    setup.primaryMirrorGeometry = .concaveSpherical
  eyepieceIsConverging :
    setup.eyepieceKind = .converging
  mirrorRadiusMeters :
    lengthInMeters setup.primaryMirrorRadiusOfCurvature = 13 / 10
  eyepieceFocalLengthCentimeters :
    lengthInCentimeters setup.eyepieceFocalLength = 11 / 10
  finalImageAtInfinity :
    setup.finalImageLocation = .infinity
  incomingRaysParallel :
    setup.rayPattern .incomingToPrimaryMirror = .parallelToOpticalAxis
  reflectedRaysConverge :
    setup.rayPattern .primaryMirrorToFocus = .convergingTowardPrimaryFocus
  raysFromFocusDiverge :
    setup.rayPattern .primaryFocusToEyepiece = .divergingFromPrimaryFocus
  emergentRaysParallel :
    setup.rayPattern .eyepieceToObserver = .parallelToOpticalAxis

/-- Positivity conditions for the telescope's physical parameters. -/
structure HasPhysicalParameters (setup : ReflectingTelescopeSetup) : Prop where
  mirrorRadiusPositive :
    0 < lengthInMeters setup.primaryMirrorRadiusOfCurvature
  mirrorFocalLengthPositive :
    0 < lengthInMeters setup.primaryMirrorFocalLength
  eyepieceFocalLengthPositive :
    0 < lengthInMeters setup.eyepieceFocalLength
  angularMagnificationNonnegative :
    0 ≤ setup.angularMagnificationMagnitude

/--
Governing paraxial-optics laws.

For a spherical mirror, the radius of curvature is twice its focal length. At
normal adjustment (final image at infinity), the magnitude of a telescope's
angular magnification is the primary-to-eyepiece focal-length ratio. These
relations contain no numerical magnification or answer-choice conclusion.
-/
structure SatisfiesParaxialTelescopeLaws
    (setup : ReflectingTelescopeSetup) : Prop where
  sphericalMirrorFocalRelation :
    ∀ units : UnitChoices,
      2 * (setup.primaryMirrorFocalLength units).val =
        (setup.primaryMirrorRadiusOfCurvature units).val
  normalAdjustmentMagnification :
    setup.finalImageLocation = .infinity →
      ∀ units : UnitChoices,
        setup.angularMagnificationMagnitude *
            (setup.eyepieceFocalLength units).val =
          (setup.primaryMirrorFocalLength units).val

/-- Labels of the displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Dimensionless angular-magnification magnitude printed beside each choice. -/
def AnswerChoice.angularMagnificationReadout : AnswerChoice → ℝ
  | .A => 591 / 10
  | .B => 117 / 2
  | .C => 579 / 10
  | .D => 567 / 10

/-- Agreement with a value displayed to the nearest tenth. -/
def RoundsToNearestTenth (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 1 / 20

/-- A displayed choice is strictly closest to the physical magnification. -/
def IsClosestAnswerChoice
    (actual : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |actual - choice.angularMagnificationReadout| <
      |actual - other.angularMagnificationReadout|

/--
The `1.30 m` spherical mirror has paraxial focal length `0.65 m`.
-/
lemma primaryMirrorFocalLengthInMeters
    (setup : ReflectingTelescopeSetup)
    (_physical : HasPhysicalParameters setup)
    (_figure : MatchesProblemAndFigure setup)
    (_laws : SatisfiesParaxialTelescopeLaws setup) :
    lengthInMeters setup.primaryMirrorFocalLength = 13 / 20 := by
  have h_focal := _laws.sphericalMirrorFocalRelation UnitChoices.SI
  change
    2 * lengthInMeters setup.primaryMirrorFocalLength =
      lengthInMeters setup.primaryMirrorRadiusOfCurvature at h_focal
  rw [_figure.mirrorRadiusMeters] at h_focal
  norm_num at h_focal ⊢
  linarith

/--
The normal-adjustment focal-length ratio is exactly `650 / 11`, approximately
`59.1`; hence the recorded answer is choice A.

Blueprint label: `thm:physics:phyx_mini_0108:target`.
-/
theorem angularMagnification_is_answer_A
    (setup : ReflectingTelescopeSetup)
    (_physical : HasPhysicalParameters setup)
    (_figure : MatchesProblemAndFigure setup)
    (_laws : SatisfiesParaxialTelescopeLaws setup) :
    setup.angularMagnificationMagnitude = 650 / 11 ∧
      RoundsToNearestTenth setup.angularMagnificationMagnitude
        AnswerChoice.A.angularMagnificationReadout ∧
      IsClosestAnswerChoice setup.angularMagnificationMagnitude .A := by
  have length_centimeters_eq (length : OpticalLength) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    change
      (length centimeterUnitChoices).val =
        100 * (length UnitChoices.SI).val
    rw [length.2 UnitChoices.SI centimeterUnitChoices]
    have h_scale :
        UnitChoices.dimScale UnitChoices.SI centimeterUnitChoices
          (dim (WithDim L𝓭 ℝ)) = 100 := by
      apply NNReal.eq
      norm_num [centimeterUnitChoices, UnitChoices.dimScale,
        LengthUnit.centimeters, LengthUnit.meters, LengthUnit.scale,
        LengthUnit.div_eq_val]
      rfl
    rw [h_scale]
    norm_num [WithDim.smul_val, NNReal.smul_def, smul_eq_mul]
  have h_eyepiece_meters :
      lengthInMeters setup.eyepieceFocalLength = 11 / 1000 := by
    have h_eyepiece_centimeters :=
      _figure.eyepieceFocalLengthCentimeters
    rw [length_centimeters_eq] at h_eyepiece_centimeters
    norm_num at h_eyepiece_centimeters ⊢
    linarith
  have h_primary_meters :=
    primaryMirrorFocalLengthInMeters setup _physical _figure _laws
  have h_magnification := _laws.normalAdjustmentMagnification
    _figure.finalImageAtInfinity UnitChoices.SI
  change
    setup.angularMagnificationMagnitude *
        lengthInMeters setup.eyepieceFocalLength =
      lengthInMeters setup.primaryMirrorFocalLength at h_magnification
  rw [h_eyepiece_meters, h_primary_meters] at h_magnification
  have h_exact :
      setup.angularMagnificationMagnitude = 650 / 11 := by
    norm_num at h_magnification ⊢
    linarith
  refine ⟨h_exact, ?_, ?_⟩
  · rw [h_exact]
    norm_num [RoundsToNearestTenth,
      AnswerChoice.angularMagnificationReadout, abs_lt]
  · rw [h_exact]
    intro other h_other
    cases other with
    | A => exact (h_other rfl).elim
    | B =>
      norm_num [AnswerChoice.angularMagnificationReadout,
        abs_of_nonneg, abs_of_nonpos]
    | C =>
      norm_num [AnswerChoice.angularMagnificationReadout,
        abs_of_nonneg, abs_of_nonpos]
    | D =>
      norm_num [AnswerChoice.angularMagnificationReadout,
        abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0108
