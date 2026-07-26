import Mathlib
import Physlib.Units.WithDim.Basic
import Physlib.SpaceAndTime.Space.LengthUnit

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0038

/-!
# Focal length of a concave spherical mirror

The figure places a headlamp filament and a wall-mounted screen in front of a
concave mirror, on the same horizontal principal axis. The mirror produces a
real, inverted image on the screen. All object, image, focal, height, and
radius quantities below are genuine physical lengths; scalar values appear
only as explicitly unit-indexed readouts.
-/

/-- A signed physical length whose numerical value changes coherently with unit choice. -/
abbrev OpticalLength : Type := Dimensionful (WithDim Dimension.L𝓭 ℝ)

/-- Unit choices obtained from SI by changing only the length unit. -/
def choicesWithLengthUnit (unit : LengthUnit) : UnitChoices :=
  { UnitChoices.SI with length := unit }

/-- The scalar readout of a physical length in the specified length unit. -/
def lengthReadout (unit : LengthUnit) (length : OpticalLength) : ℝ :=
  (length (choicesWithLengthUnit unit)).val

/-- The scalar SI readout of a physical length, in metres. -/
def metersValue (length : OpticalLength) : ℝ :=
  (length UnitChoices.SI).val

/-- The scalar readout of a physical length in centimetres. -/
def centimetersValue (length : OpticalLength) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- The scalar readout of a physical length in millimetres. -/
def millimetersValue (length : OpticalLength) : ℝ :=
  lengthReadout LengthUnit.millimeters length

/-- Spherical-mirror kind as viewed from the incident-light side. -/
inductive SphericalMirrorKind where
  | concave
  | convex
  deriving DecidableEq, Repr

/-- Whether the reflected rays physically meet or only appear to meet. -/
inductive MirrorImageNature where
  | real
  | virtual
  deriving DecidableEq, Repr

/-- The surface on which the image is received in the physical scenario. -/
inductive ImageReceiver where
  | wallScreen
  deriving DecidableEq, Repr

/-- Transverse orientation of the image relative to the object. -/
inductive ImageOrientation where
  | upright
  | inverted
  deriving DecidableEq, Repr

/-- Orientation of the principal optical axis displayed in the figure. -/
inductive PrincipalAxisOrientation where
  | horizontal
  deriving DecidableEq, Repr

/--
The physical quantities and qualitative labels in the ray diagram.

`radiusOfCurvature` is the axial distance from the mirror vertex to the point
labelled `C`; `objectHeight` is the displayed `h`, and `imageHeight` is the
unknown displayed `h'`. Object and image distances are positive distances in
front of the mirror under the real-is-positive convention.
-/
structure ConcaveMirrorImagingSetup where
  mirrorKind : SphericalMirrorKind
  imageNature : MirrorImageNature
  imageReceiver : ImageReceiver
  imageOrientation : ImageOrientation
  principalAxisOrientation : PrincipalAxisOrientation
  objectDistance : OpticalLength
  imageDistance : OpticalLength
  objectHeight : OpticalLength
  imageHeight : OpticalLength
  focalLength : OpticalLength
  radiusOfCurvature : OpticalLength

/--
Readouts and qualitative facts supplied by the problem and its figure: a
concave mirror, a real inverted image on the wall/screen, `s = 10.0 cm`,
`s' = 3.00 m`, and object height `h = 5.00 mm` on a horizontal optic axis.
The unknown `h'`, `R`, and focal length are deliberately not fixed here.
-/
def MatchesFigureReadouts (setup : ConcaveMirrorImagingSetup) : Prop :=
  setup.mirrorKind = .concave ∧
    setup.imageNature = .real ∧
    setup.imageReceiver = .wallScreen ∧
    setup.imageOrientation = .inverted ∧
    setup.principalAxisOrientation = .horizontal ∧
    centimetersValue setup.objectDistance = 10 ∧
    metersValue setup.imageDistance = 3 ∧
    millimetersValue setup.objectHeight = 5

/-- Positivity conditions for the length magnitudes in the depicted real-image configuration. -/
def HasPhysicalLengthSigns (setup : ConcaveMirrorImagingSetup) : Prop :=
  0 < metersValue setup.objectDistance ∧
    0 < metersValue setup.imageDistance ∧
    0 < metersValue setup.objectHeight ∧
    0 < metersValue setup.imageHeight ∧
    0 < metersValue setup.focalLength ∧
    0 < metersValue setup.radiusOfCurvature

/--
The paraxial spherical-mirror equation `1/f = 1/s + 1/s'`, expressed in the
division-free, dimensionally homogeneous form `f * (s + s') = s * s'` in
every unit system.
-/
def ObeysSphericalMirrorEquation (setup : ConcaveMirrorImagingSetup) : Prop :=
  ∀ units : UnitChoices,
    setup.focalLength units *
        (setup.objectDistance units + setup.imageDistance units) =
      setup.objectDistance units * setup.imageDistance units

/-- For a paraxial spherical mirror, the radius of curvature is twice its focal length. -/
def ObeysRadiusFocalLengthLaw (setup : ConcaveMirrorImagingSetup) : Prop :=
  ∀ units : UnitChoices,
    (setup.radiusOfCurvature units).val = 2 * (setup.focalLength units).val

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The focal-length readout printed beside each answer choice, in centimetres. -/
def AnswerChoice.focalLengthCentimeters : AnswerChoice → ℝ
  | .A => 868 / 100
  | .B => 968 / 100
  | .C => 966 / 100
  | .D => 905 / 100

/--
`reported` is a nearest-hundredth decimal readout of `exact`: it is an integer
number of hundredths and differs from the exact value by at most half a
hundredth.
-/
def IsNearestHundredthReadout (exact reported : ℝ) : Prop :=
  (∃ hundredths : ℤ, reported = (hundredths : ℝ) / 100) ∧
    |exact - reported| ≤ 1 / 200

/--
The mirror equation and the two stated axial distances determine the exact
focal length as `300/31 cm`.
-/
lemma focalLengthCentimeters_eq_threeHundred_div_thirtyOne
    (setup : ConcaveMirrorImagingSetup)
    (h_figure : MatchesFigureReadouts setup)
    (h_mirror : ObeysSphericalMirrorEquation setup) :
    centimetersValue setup.focalLength = 300 / 31 := by
  rcases h_figure with
    ⟨_, _, _, _, _, h_object_centimeters, h_image_meters, _⟩
  let centimeterUnits := choicesWithLengthUnit LengthUnit.centimeters
  have h_centimeter_scale :
      ((UnitChoices.SI.dimScale centimeterUnits Dimension.L𝓭 : NNReal) : ℝ) =
        100 := by
    norm_num [centimeterUnits, choicesWithLengthUnit, UnitChoices.dimScale,
      LengthUnit.centimeters]
    rfl
  have h_image_centimeters :
      centimetersValue setup.imageDistance = 300 := by
    have h_conversion := congrArg (fun value ↦ value.val)
      (setup.imageDistance.property UnitChoices.SI centimeterUnits)
    change
      (setup.imageDistance centimeterUnits).val =
        (UnitChoices.SI.dimScale centimeterUnits Dimension.L𝓭 : NNReal) •
          (setup.imageDistance UnitChoices.SI).val at h_conversion
    rw [NNReal.smul_def, h_centimeter_scale] at h_conversion
    simp only [smul_eq_mul] at h_conversion
    change (setup.imageDistance UnitChoices.SI).val = 3 at h_image_meters
    change (setup.imageDistance centimeterUnits).val = 300
    linarith
  have h_mirror_centimeters :=
    congrArg (fun value ↦ value.val) (h_mirror centimeterUnits)
  change
    centimetersValue setup.focalLength *
        (centimetersValue setup.objectDistance +
          centimetersValue setup.imageDistance) =
      centimetersValue setup.objectDistance *
        centimetersValue setup.imageDistance at h_mirror_centimeters
  rw [h_object_centimeters, h_image_centimeters] at h_mirror_centimeters
  norm_num at h_mirror_centimeters ⊢
  linarith

/--
The exact focal length is `300/31 cm`, whose nearest-hundredth readout is
`9.68 cm`, answer choice B.

This formalizes `thm:physics:phyx_mini_0038:target`.
-/
theorem problem_phyx_mini_0038
    (setup : ConcaveMirrorImagingSetup)
    (h_figure : MatchesFigureReadouts setup)
    (h_signs : HasPhysicalLengthSigns setup)
    (h_mirror : ObeysSphericalMirrorEquation setup)
    (h_radius : ObeysRadiusFocalLengthLaw setup) :
    centimetersValue setup.focalLength = 300 / 31 ∧
      IsNearestHundredthReadout
        (centimetersValue setup.focalLength)
        AnswerChoice.B.focalLengthCentimeters := by
  have h_exact :=
    focalLengthCentimeters_eq_threeHundred_div_thirtyOne setup h_figure h_mirror
  constructor
  · exact h_exact
  · rw [h_exact]
    constructor
    · refine ⟨968, ?_⟩
      norm_num [AnswerChoice.focalLengthCentimeters]
    · norm_num [AnswerChoice.focalLengthCentimeters, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0038
