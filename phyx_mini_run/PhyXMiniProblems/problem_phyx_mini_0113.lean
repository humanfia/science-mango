import Mathlib
import Physlib.Optics.Basic
import Physlib.Units.WithDim.Basic

/-!
# A concave-mirror image calibrated by a magnification plot

Physical lengths are represented by Physlib dimension-carrying quantities.
The real numbers appearing below are explicitly named numerical readouts in
centimetres, millimetres, or dimensionless lateral magnification.
-/

namespace PhyXMiniProblems.ProblemPhyXMini0113

noncomputable section

open CarriesDimension Dimension UnitChoices

/-- A physical quantity carrying the dimension of length. -/
abbrev LengthQuantity := Dimensionful (WithDim L𝓭 ℝ)

/-- Construct a physical length from its SI-metre readout. -/
noncomputable def metres (value : ℝ) : LengthQuantity :=
  toDimensionful SI ⟨value⟩

/-- Construct a physical length from its centimetre readout. -/
noncomputable def centimetres (value : ℝ) : LengthQuantity :=
  metres (value / 100)

/-- Construct a physical length from its millimetre readout. -/
noncomputable def millimetres (value : ℝ) : LengthQuantity :=
  metres (value / 1000)

/-- The SI-metre scalar readout of a physical length. -/
noncomputable def metreReadout (length : LengthQuantity) : ℝ :=
  (length SI).val

/-- The centimetre scalar readout of a physical length. -/
noncomputable def centimetreReadout (length : LengthQuantity) : ℝ :=
  100 * metreReadout length

/-- The millimetre scalar readout of a physical length. -/
noncomputable def millimetreReadout (length : LengthQuantity) : ℝ :=
  1000 * metreReadout length

/-- The two sides of the mirror vertex along its oriented optic axis. -/
inductive SideOfVertex where
  | left
  | right
  deriving DecidableEq, Repr

/--
A location constrained to the mirror's optic axis.  Its distance is a
dimensionful, strictly positive distance from the vertex; `side` retains the
orientation information that an unsigned distance alone would discard.
-/
structure AxialLocation where
  side : SideOfVertex
  distanceFromVertex : LengthQuantity
  distance_positive : 0 < metreReadout distanceFromVertex

/--
The concave spherical mirror used by the experiment.  The radius and focal
length are physical lengths, and the last field records the paraxial focal
relation for a spherical mirror.
-/
structure ConcaveSphericalMirror where
  radiusOfCurvature : LengthQuantity
  focalLength : LengthQuantity
  radius_positive : 0 < metreReadout radiusOfCurvature
  focalLength_positive : 0 < metreReadout focalLength
  spherical_focal_relation :
    metreReadout radiusOfCurvature = 2 * metreReadout focalLength

/-- Whether an optical object is real or virtual. -/
inductive ObjectNature where
  | real
  | virtual
  deriving DecidableEq, Repr

/-- The firefly regarded as an axial optical object. -/
structure AxialObject where
  location : AxialLocation
  height : LengthQuantity
  height_positive : 0 < metreReadout height
  nature : ObjectNature

/-- Whether the image is formed by actual rays or only by backward extensions. -/
inductive ImageNature where
  | real
  | virtual
  deriving DecidableEq, Repr

/-- Orientation of an image relative to the upright object. -/
inductive ImageOrientation where
  | upright
  | inverted
  deriving DecidableEq, Repr

/-- A sharply observed axial mirror image and its physical height magnitude. -/
structure AxialImage where
  location : AxialLocation
  heightMagnitude : LengthQuantity
  height_positive : 0 < metreReadout heightMagnitude
  nature : ImageNature
  orientation : ImageOrientation

/-- The white cardboard screen used to locate a real, sharply focused image. -/
structure CardboardScreen where
  location : AxialLocation

/--
One trial of the mirror experiment.  This stores the physical objects and the
dimensionless measured lateral magnification, but no optical law and no answer
to the current question.
-/
structure MirrorTrial where
  mirror : ConcaveSphericalMirror
  object : AxialObject
  image : AxialImage
  screen : CardboardScreen
  lateralMagnification : ℝ
  image_focused_on_screen : image.location = screen.location
  screen_farther_right_than_object :
    metreReadout object.location.distanceFromVertex <
      metreReadout screen.location.distanceFromVertex

/-- The sign attached to an image height by its orientation. -/
def orientationSign : ImageOrientation → ℝ
  | .upright => 1
  | .inverted => -1

/-- The signed millimetre height used in the lateral-magnification law. -/
noncomputable def signedImageHeightMillimetres (image : AxialImage) : ℝ :=
  orientationSign image.orientation * millimetreReadout image.heightMagnitude

/--
The paraxial spherical-mirror equation, expressed using consistent centimetre
readouts for object distance `s`, image distance `s'`, and focal length `f`.
-/
def SatisfiesSphericalMirrorEquation (trial : MirrorTrial) : Prop :=
  1 / centimetreReadout trial.object.location.distanceFromVertex +
      1 / centimetreReadout trial.image.location.distanceFromVertex =
    1 / centimetreReadout trial.mirror.focalLength

/--
Both standard meanings of the dimensionless lateral magnification:
`m = hᵢ/hₒ` with an orientation sign, and `m = -s'/s` for a mirror.
-/
def SatisfiesLateralMagnificationLaw (trial : MirrorTrial) : Prop :=
  trial.lateralMagnification =
      signedImageHeightMillimetres trial.image /
        millimetreReadout trial.object.height ∧
    trial.lateralMagnification =
      -(centimetreReadout trial.image.location.distanceFromVertex /
        centimetreReadout trial.object.location.distanceFromVertex)

/--
The five measured plot points and the magenta best-fit line.  Horizontal
coordinates are dimensionless `1/m`; vertical coordinates and line
coefficients are numerical centimetre readouts.
-/
structure CalibrationPlot where
  reciprocalMagnification : Fin 5 → ℝ
  objectDistanceCentimetres : Fin 5 → ℝ
  xAxisMinimum : ℝ
  xAxisMaximum : ℝ
  xGridStep : ℝ
  yAxisMinimumCentimetres : ℝ
  yAxisMaximumCentimetres : ℝ
  yGridStepCentimetres : ℝ
  fitInterceptCentimetres : ℝ
  fitSlopeCentimetresPerReciprocal : ℝ

/--
Primary-image readout for Figure 113: the five black points, displayed axis
ranges and grid spacings, and the magenta line read from the graph.
-/
def IsFigure113Calibration (plot : CalibrationPlot) : Prop :=
  plot.reciprocalMagnification =
      ![(-9 / 5 : ℝ), (-7 / 5 : ℝ), (-1 : ℝ), (-3 / 5 : ℝ), (-1 / 5 : ℝ)] ∧
    plot.objectDistanceCentimetres = ![(70 : ℝ), 60, 50, 40, 30] ∧
    plot.xAxisMinimum = -2 ∧
    plot.xAxisMaximum = 0 ∧
    plot.xGridStep = 1 / 2 ∧
    plot.yAxisMinimumCentimetres = 0 ∧
    plot.yAxisMaximumCentimetres = 80 ∧
    plot.yGridStepCentimetres = 20 ∧
    plot.fitInterceptCentimetres = 25 ∧
    plot.fitSlopeCentimetresPerReciprocal = -25

/--
Physical interpretation of the `s` versus `1/m` calibration line.  From the
mirror and magnification equations, the intercept is `f` and the slope is
`-f`; this predicate connects those generic coefficients to the actual mirror.
-/
def CalibrationLineRepresentsMirror
    (plot : CalibrationPlot) (mirror : ConcaveSphericalMirror) : Prop :=
  plot.fitInterceptCentimetres = centimetreReadout mirror.focalLength ∧
    plot.fitSlopeCentimetresPerReciprocal =
      -centimetreReadout mirror.focalLength

/-- Labels of the four printed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Centimetre readouts printed for the four answer choices. -/
def answerDistanceCentimetres : AnswerChoice → ℝ
  | .A => 37.5
  | .B => 38.6
  | .C => 36.4
  | .D => 35.8

/-- A physical object distance has the numerical centimetre readout of a choice. -/
def MatchesAnswerChoice (distance : LengthQuantity) (choice : AnswerChoice) : Prop :=
  centimetreReadout distance = answerDistanceCentimetres choice

/--
For a real `4.00 mm` firefly and a real, inverted `8.00 mm` image, the
dimensionless magnification is `-2`.  Combining this with the calibrated
spherical-mirror laws makes the required object distance match choice A,
`37.5 cm`.

Blueprint: `thm:physics:phyx_mini_0113:target`.
-/
theorem object_distance_matches_choice_A
    (plot : CalibrationPlot)
    (trial : MirrorTrial)
    (h_figure : IsFigure113Calibration plot)
    (h_calibration : CalibrationLineRepresentsMirror plot trial.mirror)
    (h_object_right : trial.object.location.side = .right)
    (h_image_right : trial.image.location.side = .right)
    (h_screen_right : trial.screen.location.side = .right)
    (h_real_object : trial.object.nature = .real)
    (h_object_height : trial.object.height = millimetres 4.00)
    (h_real_image : trial.image.nature = .real)
    (h_image_height : trial.image.heightMagnitude = millimetres 8.00)
    (h_inverted : trial.image.orientation = .inverted)
    (h_mirror_equation : SatisfiesSphericalMirrorEquation trial)
    (h_magnification : SatisfiesLateralMagnificationLaw trial) :
    MatchesAnswerChoice trial.object.location.distanceFromVertex .A := by
  rcases h_figure with ⟨_, _, _, _, _, _, _, _, h_fit, _⟩
  rcases h_magnification with ⟨h_mag_height, h_mag_distance⟩
  have h_object_readout : millimetreReadout trial.object.height = 4 := by
    rw [h_object_height]
    norm_num [millimetreReadout, metreReadout, millimetres, metres,
      CarriesDimension.toDimensionful_apply_apply]
  have h_image_readout : millimetreReadout trial.image.heightMagnitude = 8 := by
    rw [h_image_height]
    norm_num [millimetreReadout, metreReadout, millimetres, metres,
      CarriesDimension.toDimensionful_apply_apply]
  have h_mag : trial.lateralMagnification = -2 := by
    rw [h_mag_height]
    rw [signedImageHeightMillimetres, h_inverted, orientationSign,
      h_image_readout, h_object_readout]
    norm_num
  have h_focal : centimetreReadout trial.mirror.focalLength = 25 := by
    linarith [h_calibration.1, h_fit]
  have h_object_distance_positive :
      0 < centimetreReadout trial.object.location.distanceFromVertex := by
    rw [centimetreReadout]
    exact mul_pos (by norm_num) trial.object.location.distance_positive
  have h_ratio :
      centimetreReadout trial.image.location.distanceFromVertex /
        centimetreReadout trial.object.location.distanceFromVertex = 2 := by
    rw [h_mag] at h_mag_distance
    linarith
  have h_image_distance :
      centimetreReadout trial.image.location.distanceFromVertex =
        2 * centimetreReadout trial.object.location.distanceFromVertex := by
    exact (div_eq_iff (ne_of_gt h_object_distance_positive)).mp h_ratio
  rw [SatisfiesSphericalMirrorEquation] at h_mirror_equation
  rw [h_image_distance, h_focal] at h_mirror_equation
  field_simp [ne_of_gt h_object_distance_positive] at h_mirror_equation
  norm_num [MatchesAnswerChoice, answerDistanceCentimetres]
  linarith

end

end PhyXMiniProblems.ProblemPhyXMini0113
