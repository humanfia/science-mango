import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0153

open Dimension

/-!
# Camera focal length from the apparent diameter of the Sun

The camera is at the NIST Laboratory in Boulder and the foreground hiker is
`2.0 km` away.  The solar disk has physical diameter `1.4 * 10^6 km`, its
center is `1.5 * 10^8 km` from the camera, and its image on the photographic
film is `15 mm` across.

All distances and diameters below are genuine Physlib dimensionful lengths.
Real numbers are used only for unit readouts, the dimensionless angular
diameter in radians, and multiple-choice values.  The hiker distance and the
other visible silhouettes are retained as figure context, although they do
not enter the solar angular-size calculation.
-/

/-! ## Dimensionful quantities and figure labels -/

/-- A signed physical length represented independently of a choice of units. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Read a physical length as a real scalar in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- The metre readout used for the governing geometrical-optics equations. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- The kilometre readout used for the astronomical and foreground data. -/
def lengthInKilometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.kilometers length

/-- The millimetre readout used for the solar image on the film. -/
def lengthInMillimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.millimeters length

/-- The location from which the problem's photograph was taken. -/
inductive ObservationSite where
  | nistLaboratoryBoulder
  deriving DecidableEq, Repr

/-- Objects explicitly visible in the supplied photograph. -/
inductive FigureSubject where
  | sun
  | hiker
  | rockFormation
  | tree
  deriving DecidableEq, Repr

/-- The two visually relevant rendering styles in the source image. -/
inductive FigureAppearance where
  | orangeRedDisk
  | blackSilhouette
  deriving DecidableEq, Repr

/-- The shape assigned to the image of the solar disk on the film. -/
inductive ImageShape where
  | circular
  deriving DecidableEq, Repr

/-- The physical medium on which the source says the solar image was measured. -/
inductive ImageMedium where
  | photographicFilm
  deriving DecidableEq, Repr

/-- The geometrical-optics regime used to estimate the camera focal length. -/
inductive OpticalRegime where
  | thinLensDistantObject
  deriving DecidableEq, Repr

/-!
The physical setup and figure-derived quantities.

`sunAngularDiameterRadians` is dimensionless.  No field assigns a numerical
value to `cameraLensFocalLength`; its value is the current target.
-/
structure SolarCameraSetup where
  observationSite : ObservationSite
  imageMedium : ImageMedium
  opticalRegime : OpticalRegime
  hikerDistanceFromCamera : LengthQuantity
  sunPhysicalDiameter : LengthQuantity
  sunCenterDistanceFromCamera : LengthQuantity
  sunImageDiameterOnFilm : LengthQuantity
  cameraLensFocalLength : LengthQuantity
  sunAngularDiameterRadians : ℝ
  visibleInFigure : FigureSubject → Prop
  appearanceInFigure : FigureSubject → FigureAppearance
  sunImageShape : ImageShape

/-! ## Stated data, figure evidence, and physical admissibility -/

/-!
The numerical readouts printed in the problem.  They constrain the foreground
distance, solar diameter and distance, and film-image diameter, but do not
constrain the unknown focal length.
-/
structure MatchesStatedMeasurements (setup : SolarCameraSetup) : Prop where
  hikerDistanceKilometers :
    lengthInKilometers setup.hikerDistanceFromCamera = 2
  sunDiameterKilometers :
    lengthInKilometers setup.sunPhysicalDiameter = 14 * 10 ^ 5
  sunDistanceKilometers :
    lengthInKilometers setup.sunCenterDistanceFromCamera = 15 * 10 ^ 7
  sunImageDiameterMillimeters :
    lengthInMillimeters setup.sunImageDiameterOnFilm = 15

/-!
Primary-image metadata: the photograph was taken at NIST, the Sun is a
circular orange-red background disk, and the hiker, rocks, and tree are dark
silhouettes.  These facts preserve the figure labels without supplying an
optical answer.
-/
structure MatchesPrimaryFigure (setup : SolarCameraSetup) : Prop where
  siteIsNistBoulder :
    setup.observationSite = .nistLaboratoryBoulder
  mediumIsPhotographicFilm :
    setup.imageMedium = .photographicFilm
  sunIsVisible : setup.visibleInFigure .sun
  hikerIsVisible : setup.visibleInFigure .hiker
  rockFormationIsVisible : setup.visibleInFigure .rockFormation
  treeIsVisible : setup.visibleInFigure .tree
  sunAppearance : setup.appearanceInFigure .sun = .orangeRedDisk
  hikerAppearance : setup.appearanceInFigure .hiker = .blackSilhouette
  rockAppearance : setup.appearanceInFigure .rockFormation = .blackSilhouette
  treeAppearance : setup.appearanceInFigure .tree = .blackSilhouette
  solarImageIsCircular : setup.sunImageShape = .circular

/-!
Positivity and principal-angle conditions for the physical configuration.
They restrict the admissible model without fixing the requested focal length.
-/
structure HasPhysicalSolarCameraParameters (setup : SolarCameraSetup) : Prop where
  hikerDistancePositive :
    0 < lengthInMeters setup.hikerDistanceFromCamera
  sunDiameterPositive :
    0 < lengthInMeters setup.sunPhysicalDiameter
  sunDistancePositive :
    0 < lengthInMeters setup.sunCenterDistanceFromCamera
  filmImageDiameterPositive :
    0 < lengthInMeters setup.sunImageDiameterOnFilm
  focalLengthPositive :
    0 < lengthInMeters setup.cameraLensFocalLength
  angularDiameterOnPrincipalBranch :
    0 < setup.sunAngularDiameterRadians ∧
      setup.sunAngularDiameterRadians < Real.pi

/-! ## Governing geometrical-optics laws -/

/-!
Angular-radius geometry for a circular object viewed along the line to its
center:

`tan (theta / 2) = (solar radius) / (distance to the solar center)`.

This is a general geometric relation and contains no numerical focal-length
answer.
-/
def SatisfiesSolarAngularDiameterGeometry (setup : SolarCameraSetup) : Prop :=
  Real.tan (setup.sunAngularDiameterRadians / 2) =
    lengthInMeters setup.sunPhysicalDiameter /
      (2 * lengthInMeters setup.sunCenterDistanceFromCamera)

/-!
Central projection by a thin camera lens focused on a distant object:

`film-image radius = focal length * tan (angular radius)`.

This is the governing imaging law.  It relates the unknown focal length to
independently supplied physical quantities but does not state its requested
numeric value.
-/
def SatisfiesDistantObjectProjectionLaw (setup : SolarCameraSetup) : Prop :=
  setup.opticalRegime = .thinLensDistantObject ∧
    lengthInMeters setup.sunImageDiameterOnFilm / 2 =
      lengthInMeters setup.cameraLensFocalLength *
        Real.tan (setup.sunAngularDiameterRadians / 2)

/-! ## Derived relation and multiple-choice target -/

/-- The labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The focal-length estimate in metres printed beside each answer choice. -/
def AnswerChoice.focalLengthMeters : AnswerChoice → ℝ
  | .A => 2
  | .B => 9 / 5
  | .C => 8 / 5
  | .D => 7 / 5

/-- Dataset metadata: the recorded answer is C, never used as a premise. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Agreement with a focal length displayed to the nearest tenth of a metre. -/
def MatchesAnswerToNearestTenth
    (focalLength : LengthQuantity) (choice : AnswerChoice) : Prop :=
  |lengthInMeters focalLength - choice.focalLengthMeters| < 1 / 20

/-- A displayed choice is uniquely closest to the derived focal length. -/
def IsClosestAnswerChoice
    (focalLength : LengthQuantity) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |lengthInMeters focalLength - choice.focalLengthMeters| <
      |lengthInMeters focalLength - other.focalLengthMeters|

/-!
Combining angular-diameter geometry with central projection gives the usual
similar-triangles formula `f = imageDiameter * distance / objectDiameter`.
This symbolic conclusion remains independent of all numerical readouts.
-/
lemma focalLength_eq_imageDiameter_mul_distance_div_sunDiameter
    (setup : SolarCameraSetup)
    (hPhysical : HasPhysicalSolarCameraParameters setup)
    (hAngularGeometry : SatisfiesSolarAngularDiameterGeometry setup)
    (hProjection : SatisfiesDistantObjectProjectionLaw setup) :
    lengthInMeters setup.cameraLensFocalLength =
      lengthInMeters setup.sunImageDiameterOnFilm *
        lengthInMeters setup.sunCenterDistanceFromCamera /
          lengthInMeters setup.sunPhysicalDiameter := by
  unfold SatisfiesSolarAngularDiameterGeometry at hAngularGeometry
  rcases hProjection with ⟨_, hProjection⟩
  rw [hAngularGeometry] at hProjection
  have hSunDiameter :
      0 < lengthInMeters setup.sunPhysicalDiameter :=
    hPhysical.sunDiameterPositive
  have hSunDistance :
      0 < lengthInMeters setup.sunCenterDistanceFromCamera :=
    hPhysical.sunDistancePositive
  field_simp at hProjection ⊢
  nlinarith

/-!
The stated `15 mm`, `1.4 * 10^6 km`, and `1.5 * 10^8 km` data give the exact
model readout `45/28 m`, approximately `1.607 m`.  Its nearest-tenth estimate
is `1.6 m`, uniquely selecting answer choice C.

Blueprint label: `thm:physics:phyx_mini_0153:target`.
-/
theorem problem_phyx_mini_0153
    (setup : SolarCameraSetup)
    (hMeasurements : MatchesStatedMeasurements setup)
    (hFigure : MatchesPrimaryFigure setup)
    (hPhysical : HasPhysicalSolarCameraParameters setup)
    (hAngularGeometry : SatisfiesSolarAngularDiameterGeometry setup)
    (hProjection : SatisfiesDistantObjectProjectionLaw setup) :
    lengthInMeters setup.cameraLensFocalLength = 45 / 28 ∧
      MatchesAnswerToNearestTenth setup.cameraLensFocalLength .C ∧
      IsClosestAnswerChoice setup.cameraLensFocalLength .C := by
  have lengthInKilometers_eq (length : LengthQuantity) :
      lengthInMeters length = 1000 * lengthInKilometers length := by
    have h := congrArg WithDim.val
      (length.2
        ({ UnitChoices.SI with length := LengthUnit.kilometers } : UnitChoices)
        ({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices))
    change lengthInMeters length =
      _ * lengthInKilometers length at h
    norm_num [lengthInKilometers, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.kilometers, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, WithDim.smul_val,
      NNReal.smul_def, NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_div,
      NNReal.coe_ofNat, NNReal.coe_mk] at h ⊢
    exact h
  have lengthInMillimeters_eq (length : LengthQuantity) :
      lengthInMillimeters length = 1000 * lengthInMeters length := by
    have h := congrArg WithDim.val
      (length.2
        ({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices)
        ({ UnitChoices.SI with length := LengthUnit.millimeters } : UnitChoices))
    change lengthInMillimeters length =
      _ * lengthInMeters length at h
    norm_num [lengthInMillimeters, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.millimeters, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, WithDim.smul_val,
      NNReal.smul_def, NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_div,
      NNReal.coe_ofNat, NNReal.coe_mk] at h ⊢
    exact h
  have hSunDiameterMeters :
      lengthInMeters setup.sunPhysicalDiameter = 1400000000 := by
    rw [lengthInKilometers_eq, hMeasurements.sunDiameterKilometers]
    norm_num
  have hSunDistanceMeters :
      lengthInMeters setup.sunCenterDistanceFromCamera = 150000000000 := by
    rw [lengthInKilometers_eq, hMeasurements.sunDistanceKilometers]
    norm_num
  have hImageDiameterMeters :
      lengthInMeters setup.sunImageDiameterOnFilm = 3 / 200 := by
    have h := hMeasurements.sunImageDiameterMillimeters
    rw [lengthInMillimeters_eq] at h
    norm_num at h ⊢
    linarith
  have hFocalFormula :=
    focalLength_eq_imageDiameter_mul_distance_div_sunDiameter
      setup hPhysical hAngularGeometry hProjection
  have hFocal :
      lengthInMeters setup.cameraLensFocalLength = 45 / 28 := by
    rw [hFocalFormula, hImageDiameterMeters, hSunDistanceMeters,
      hSunDiameterMeters]
    norm_num
  refine ⟨hFocal, ?_, ?_⟩
  · rw [MatchesAnswerToNearestTenth, hFocal]
    norm_num [AnswerChoice.focalLengthMeters, abs_of_nonneg, abs_of_nonpos]
  · unfold IsClosestAnswerChoice
    intro other hOther
    cases other with
    | A =>
        norm_num [hFocal, AnswerChoice.focalLengthMeters,
          abs_of_nonneg, abs_of_nonpos]
    | B =>
        norm_num [hFocal, AnswerChoice.focalLengthMeters,
          abs_of_nonneg, abs_of_nonpos]
    | C => exact (hOther rfl).elim
    | D =>
        norm_num [hFocal, AnswerChoice.focalLengthMeters,
          abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0153
