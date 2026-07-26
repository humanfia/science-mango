import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0111

/-!
# Eyepiece focal length of a Galilean telescope

The primary figure shows a converging objective followed by a diverging
eyepiece on a horizontal principal axis.  The objective would form the
intermediate image `I` at its back focus `F₁'`; this same axial point is the
object-side focus `F₂` of the eyepiece, so `I` is a virtual object for the
eyepiece.  The incident and emergent parallel ray directions are labelled
`u` and `u'`, and the other eyepiece focus is labelled `F₂'`.

Focal lengths and axial positions below are genuine signed physical lengths.
Real numbers are used only for dimensionless angular magnification, angular
readouts in radians, and numerical length readouts in an explicitly selected
unit.

Assumption/target split:

* governing laws: the signed focal-length magnification law, the afocal lens
  separation law, and the incident/emergent paraxial-angle relation;
* previous-part results: none;
* figure/data readouts: a converging objective, a diverging eyepiece, object
  and final image at infinity, a virtual erect final image, the coincident
  point `F₁' = F₂ = I`, and angular magnification `-6.33`;
* current target conclusion: in every length unit, the eyepiece focal length
  is `-100/633` times the objective focal length.

The source and raster provide no absolute length scale.  Consequently the
recorded `-15.0 cm` choice is represented only as dataset metadata and as a
separate conditional consequence of an explicitly additional `95 cm`
objective calibration; that calibration is not a premise of the main theorem.
-/

/-- A signed physical quantity carrying the dimension of length. -/
abbrev OpticalLength : Type := Dimensionful (WithDim Dimension.L𝓭 ℝ)

/-- The scalar readout of a physical length in a chosen length unit. -/
def lengthReadout (unit : LengthUnit) (length : OpticalLength) : ℝ :=
  (length { UnitChoices.SI with length := unit }).val

/-- The scalar readout of a physical length in centimeters. -/
def centimetersValue (length : OpticalLength) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Roles of the two lenses along the telescope's direction of propagation. -/
inductive LensRole where
  | objective
  | eyepiece
  deriving DecidableEq, Repr

/-- Paraxial lens kind, including the sign information of its optical power. -/
inductive ThinLensKind where
  | converging
  | diverging
  deriving DecidableEq, Repr

/-- A thin lens with a signed physical focal length. -/
structure ThinLens where
  kind : ThinLensKind
  signedFocalLength : OpticalLength

/-- Whether an object or image conjugate is at a finite axial point or infinity. -/
inductive ConjugateLocation where
  | finite
  | atInfinity
  deriving DecidableEq, Repr

/-- Whether rays physically meet at an image or only appear to originate there. -/
inductive ImageNature where
  | real
  | virtual
  deriving DecidableEq, Repr

/-- Transverse image orientation relative to the observed object. -/
inductive ImageOrientation where
  | erect
  | inverted
  deriving DecidableEq, Repr

/-- Axial points explicitly displayed in the Galilean-telescope figure. -/
inductive AxialFigurePoint where
  | objectiveCenter
  | eyepieceCenter
  | objectiveBackFocusF1Prime
  | eyepieceObjectFocusF2
  | eyepieceOtherFocusF2Prime
  | intermediateImageI
  deriving DecidableEq, Repr

/-- Labels of the incident and emergent ray directions shown in the figure. -/
inductive RayDirectionLabel where
  | u
  | uPrime
  deriving DecidableEq, Repr

/--
Physical lenses, figure-derived axial locations, ray-angle readouts, and image
classification for the telescope.  The eyepiece focal length remains an
unknown field; no requested numerical value is built into this structure.
-/
structure GalileanTelescopeSetup where
  lens : LensRole → ThinLens
  axialPosition : AxialFigurePoint → OpticalLength
  rayAngleRadians : RayDirectionLabel → ℝ
  objectLocation : ConjugateLocation
  finalImageLocation : ConjugateLocation
  finalImageNature : ImageNature
  finalImageOrientation : ImageOrientation
  angularMagnification : ℝ

/--
Qualitative and incidence data supplied by the problem and primary figure.
The coincident point `F₁' = F₂ = I` records that `I` is the objective's
would-be image and a virtual object for the diverging eyepiece.  The requested
eyepiece focal-length readout does not occur here.
-/
def MatchesGalileanTelescopeFigure (setup : GalileanTelescopeSetup) : Prop :=
  (setup.lens .objective).kind = .converging ∧
    (setup.lens .eyepiece).kind = .diverging ∧
    setup.objectLocation = .atInfinity ∧
    setup.finalImageLocation = .atInfinity ∧
    setup.finalImageNature = .virtual ∧
    setup.finalImageOrientation = .erect ∧
    setup.axialPosition .objectiveBackFocusF1Prime =
      setup.axialPosition .eyepieceObjectFocusF2 ∧
    setup.axialPosition .eyepieceObjectFocusF2 =
      setup.axialPosition .intermediateImageI ∧
    centimetersValue (setup.axialPosition .objectiveCenter) <
      centimetersValue (setup.axialPosition .eyepieceCenter)

/-- The stated dimensionless angular-magnification readout `-6.33`. -/
def MatchesAngularMagnificationReadout (setup : GalileanTelescopeSetup) : Prop :=
  setup.angularMagnification = (-633 : ℝ) / 100

/--
Physical sign and nondegeneracy conditions for the depicted Galilean branch:
the objective focal length is positive, the eyepiece focal length is negative,
and the incident ray direction has a nonzero small-angle readout.
-/
def HasPhysicalGalileanParameters (setup : GalileanTelescopeSetup) : Prop :=
  0 < centimetersValue (setup.lens .objective).signedFocalLength ∧
    centimetersValue (setup.lens .eyepiece).signedFocalLength < 0 ∧
    setup.rayAngleRadians .u ≠ 0

/--
Paraxial governing laws for an afocal Galilean telescope, stated in every
choice of length unit.  With signed focal lengths, the convention used by the
recorded negative magnification is `m = f₁ / f₂`, written without division as
`m * f₂ = f₁`.  The lens separation is `f₁ + f₂`, and the angular readouts
satisfy `u' = m * u`.
-/
structure SatisfiesAfocalGalileanLaws (setup : GalileanTelescopeSetup) : Prop where
  focal_length_magnification :
    ∀ unit : LengthUnit,
      setup.angularMagnification *
          lengthReadout unit (setup.lens .eyepiece).signedFocalLength =
        lengthReadout unit (setup.lens .objective).signedFocalLength
  afocal_lens_separation :
    ∀ unit : LengthUnit,
      lengthReadout unit (setup.axialPosition .eyepieceCenter) -
          lengthReadout unit (setup.axialPosition .objectiveCenter) =
        lengthReadout unit (setup.lens .objective).signedFocalLength +
          lengthReadout unit (setup.lens .eyepiece).signedFocalLength
  angular_readout_relation :
    setup.rayAngleRadians .uPrime =
      setup.angularMagnification * setup.rayAngleRadians .u

/--
Independent objective calibration needed to recover the recorded answer.

The source prose and primary figure do not print this `95 cm` value.  It is
therefore isolated from the actual figure predicate as an explicit additional
calibration (for example, a result supplied by omitted surrounding context),
rather than being silently attributed to the diagram.
-/
def HasObjectiveFocalLengthCalibration (setup : GalileanTelescopeSetup) : Prop :=
  centimetersValue (setup.lens .objective).signedFocalLength = 95

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Eyepiece focal-length readout printed beside each choice, in centimeters. -/
def answerEyepieceFocalLengthCentimeters : AnswerChoice → ℝ
  | .A => -15
  | .B => -14
  | .C => -13
  | .D => -12

/--
`reported` is a nearest-tenth decimal readout of `exact`: it is an integral
number of tenths and differs from the exact value by at most half a tenth.
-/
def IsNearestTenthReadout (exact reported : ℝ) : Prop :=
  (∃ tenths : ℤ, reported = (tenths : ℝ) / 10) ∧
    |exact - reported| ≤ 1 / 20

/--
If the missing absolute scale is supplied independently as an objective focal
length of `95 cm`, then the recorded choice A is the nearest-tenth readout.
This conditional lemma is not the source-supported main target below.
-/
lemma recorded_choice_A_from_objective_calibration
    (setup : GalileanTelescopeSetup)
    (h_magnification : MatchesAngularMagnificationReadout setup)
    (h_calibration : HasObjectiveFocalLengthCalibration setup)
    (h_laws : SatisfiesAfocalGalileanLaws setup) :
    centimetersValue (setup.lens .eyepiece).signedFocalLength =
        (-9500 : ℝ) / 633 ∧
      IsNearestTenthReadout
        (centimetersValue (setup.lens .eyepiece).signedFocalLength)
        (answerEyepieceFocalLengthCentimeters .A) := by
  have h_focal :=
    h_laws.focal_length_magnification LengthUnit.centimeters
  have h_focal_cm :
      setup.angularMagnification *
          centimetersValue (setup.lens .eyepiece).signedFocalLength =
        centimetersValue (setup.lens .objective).signedFocalLength := by
    simpa [centimetersValue] using h_focal
  unfold MatchesAngularMagnificationReadout at h_magnification
  unfold HasObjectiveFocalLengthCalibration at h_calibration
  have h_eyepiece :
      centimetersValue (setup.lens .eyepiece).signedFocalLength =
        (-9500 : ℝ) / 633 := by
    rw [h_magnification, h_calibration] at h_focal_cm
    linarith
  constructor
  · exact h_eyepiece
  · rw [h_eyepiece]
    constructor
    · refine ⟨-150, ?_⟩
      norm_num [answerEyepieceFocalLengthCentimeters]
    · norm_num [answerEyepieceFocalLengthCentimeters, abs_of_nonpos]

/--
The stated angular magnification determines the eyepiece focal length only
relative to the objective focal length: `f₂ = -(100/633) f₁`.  This is the
strongest scale-independent conclusion supported by the supplied problem and
primary figure.

This formalizes blueprint label `thm:physics:phyx_mini_0111:target`.
-/
theorem problem_phyx_mini_0111
    (setup : GalileanTelescopeSetup)
    (h_figure : MatchesGalileanTelescopeFigure setup)
    (h_magnification : MatchesAngularMagnificationReadout setup)
    (h_physical : HasPhysicalGalileanParameters setup)
    (h_laws : SatisfiesAfocalGalileanLaws setup) :
    ∀ unit : LengthUnit,
      lengthReadout unit (setup.lens .eyepiece).signedFocalLength =
        ((-100 : ℝ) / 633) *
          lengthReadout unit (setup.lens .objective).signedFocalLength := by
  intro unit
  have h_focal := h_laws.focal_length_magnification unit
  unfold MatchesAngularMagnificationReadout at h_magnification
  rw [h_magnification] at h_focal
  linarith

end PhyXMiniProblems.ProblemPhyXMini0111
