import Mathlib
import Physlib.Units.WithDim.Basic
import Physlib.SpaceAndTime.Space.LengthUnit

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0160

open Dimension

/-!
# Magnification of an object on the axis of a spherical mirror

Signed axial distances are positive for a real object or real image.  Thus a
concave mirror has positive focal length, while a virtual image has negative
signed image distance.  The lateral magnification is dimensionless.

The source text and auxiliary caption describe a magnification-versus-distance
graph for a spherical mirror.  The supplied raster `160.png` instead shows an
unrelated thin-lens ray diagram labelled `s` and `s'`.  The declarations below
therefore follow the stated mirror problem; no measurement from that mismatched
raster is used, and the intended graph's focal calibration is exposed as a
separate hypothesis.
-/

/-- A signed physical length represented coherently in every choice of units. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Scalar readout of a signed physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- The centimeter readout used by the graph and the question. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- The two spherical-mirror orientations distinguished by their focal signs. -/
inductive SphericalMirrorKind where
  | concave
  | convex
  deriving DecidableEq, Repr

/-- Physical quantities plotted on the two axes of the supplied graph. -/
inductive GraphVariable where
  | objectDistanceCentimeters
  | lateralMagnification
  deriving DecidableEq, Repr

/-!
The mirror, its signed paraxial image-distance response, and the measured
magnification curve.  The three named object distances are the graph endpoints
`p_a`, `p_b`, and the requested distance `p = 14 cm`.

No field fixes the magnification at the requested distance.
-/
structure SphericalMirrorMagnificationSetup where
  mirrorKind : SphericalMirrorKind
  focalLength : LengthQuantity
  signedImageDistanceAt : LengthQuantity → LengthQuantity
  lateralMagnificationAt : LengthQuantity → ℝ
  graphLowerObjectDistancePA : LengthQuantity
  graphUpperObjectDistancePB : LengthQuantity
  requestedObjectDistance : LengthQuantity
  horizontalAxis : GraphVariable
  verticalAxis : GraphVariable

/-!
The explicit problem and intended-graph readouts.  Besides the axis labels and
the object-distance range, the source caption records a positive, increasing
branch of the magnification curve on `[p_a,p_b]`.
-/
structure MatchesProblemAndGraph
    (setup : SphericalMirrorMagnificationSetup) : Prop where
  mirror_is_concave : setup.mirrorKind = .concave
  horizontal_axis_is_p_cm :
    setup.horizontalAxis = .objectDistanceCentimeters
  vertical_axis_is_m : setup.verticalAxis = .lateralMagnification
  lower_endpoint_centimeters :
    lengthInCentimeters setup.graphLowerObjectDistancePA = 2
  upper_endpoint_centimeters :
    lengthInCentimeters setup.graphUpperObjectDistancePB = 8
  requested_distance_centimeters :
    lengthInCentimeters setup.requestedObjectDistance = 14
  curve_positive_on_displayed_range :
    ∀ p : LengthQuantity,
      lengthInCentimeters setup.graphLowerObjectDistancePA ≤
          lengthInCentimeters p →
      lengthInCentimeters p ≤
          lengthInCentimeters setup.graphUpperObjectDistancePB →
      0 < setup.lateralMagnificationAt p
  curve_strictly_increases_on_displayed_range :
    ∀ p₁ p₂ : LengthQuantity,
      lengthInCentimeters setup.graphLowerObjectDistancePA ≤
          lengthInCentimeters p₁ →
      lengthInCentimeters p₂ ≤
          lengthInCentimeters setup.graphUpperObjectDistancePB →
      lengthInCentimeters p₁ < lengthInCentimeters p₂ →
      setup.lateralMagnificationAt p₁ < setup.lateralMagnificationAt p₂

/-!
The intended magnification curve's spherical-mirror calibration is a focal
length of `10 cm`.  It is kept as a separate intermediate graph/model input,
not as the requested magnification at `14 cm`.
-/
structure HasFigureDerivedFocalCalibration
    (setup : SphericalMirrorMagnificationSetup) : Prop where
  focal_length_centimeters : lengthInCentimeters setup.focalLength = 10

/-- Positivity and finite-distance conditions for the stated configuration. -/
structure HasPhysicalParameters
    (setup : SphericalMirrorMagnificationSetup) : Prop where
  focal_length_positive : 0 < lengthInCentimeters setup.focalLength
  graph_lower_distance_positive :
    0 < lengthInCentimeters setup.graphLowerObjectDistancePA
  requested_distance_positive :
    0 < lengthInCentimeters setup.requestedObjectDistance
  requested_distance_not_focal :
    lengthInCentimeters setup.requestedObjectDistance ≠
      lengthInCentimeters setup.focalLength

/-- A positive object distance at which the paraxial image is finite. -/
def IsFiniteObjectConfiguration
    (setup : SphericalMirrorMagnificationSetup)
    (objectDistance : LengthQuantity) : Prop :=
  0 < lengthInCentimeters objectDistance ∧
    lengthInCentimeters objectDistance ≠
      lengthInCentimeters setup.focalLength

/-!
The paraxial spherical-mirror equation
`1/p + 1/q = 1/f` and the signed lateral-magnification law `m = -q/p`.
Both laws are stated in every length unit, so the physical content is not tied
to the centimeter readouts used by the graph.
-/
structure SatisfiesParaxialSphericalMirrorLaws
    (setup : SphericalMirrorMagnificationSetup) : Prop where
  mirror_equation :
    ∀ (unit : LengthUnit) (objectDistance : LengthQuantity),
      IsFiniteObjectConfiguration setup objectDistance →
      1 / lengthReadout unit objectDistance +
          1 / lengthReadout unit
            (setup.signedImageDistanceAt objectDistance) =
        1 / lengthReadout unit setup.focalLength
  lateral_magnification_law :
    ∀ (unit : LengthUnit) (objectDistance : LengthQuantity),
      IsFiniteObjectConfiguration setup objectDistance →
      setup.lateralMagnificationAt objectDistance =
        -(lengthReadout unit
            (setup.signedImageDistanceAt objectDistance)) /
          lengthReadout unit objectDistance

/-- Labels of the four answer choices printed in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Dimensionless magnification displayed beside each answer choice. -/
def AnswerChoice.displayedMagnification : AnswerChoice → ℝ
  | .A => -4
  | .B => -(7 / 2)
  | .C => -3
  | .D => -(5 / 2)

/-- The answer label recorded in the supplied dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A choice agrees exactly with the requested dimensionless magnification. -/
def MatchesDisplayedAnswer
    (setup : SphericalMirrorMagnificationSetup)
    (choice : AnswerChoice) : Prop :=
  setup.lateralMagnificationAt setup.requestedObjectDistance =
    choice.displayedMagnification

/-!
At `p = 14 cm` and `f = 10 cm`, the mirror equation gives the intermediate
signed image distance `q = 35 cm`.
-/
lemma requestedSignedImageDistanceCentimeters_eq_thirty_five
    (setup : SphericalMirrorMagnificationSetup)
    (_figure : MatchesProblemAndGraph setup)
    (_calibration : HasFigureDerivedFocalCalibration setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesParaxialSphericalMirrorLaws setup) :
    lengthInCentimeters
        (setup.signedImageDistanceAt setup.requestedObjectDistance) = 35 := by
  have hfinite :
      IsFiniteObjectConfiguration setup setup.requestedObjectDistance :=
    ⟨_physical.requested_distance_positive,
      _physical.requested_distance_not_focal⟩
  have hmirror :=
    _laws.mirror_equation LengthUnit.centimeters
      setup.requestedObjectDistance hfinite
  change
    1 / lengthInCentimeters setup.requestedObjectDistance +
        1 / lengthInCentimeters
          (setup.signedImageDistanceAt setup.requestedObjectDistance) =
      1 / lengthInCentimeters setup.focalLength at hmirror
  rw [_figure.requested_distance_centimeters,
    _calibration.focal_length_centimeters] at hmirror
  have himage_ne :
      lengthInCentimeters
          (setup.signedImageDistanceAt setup.requestedObjectDistance) ≠ 0 := by
    intro himage_zero
    rw [himage_zero] at hmirror
    norm_num at hmirror
  field_simp [himage_ne] at hmirror
  linarith

/-!
For the object at `p = 14 cm`, the signed magnification is
`m = -q/p = -35/14 = -5/2 = -2.5`, which is answer choice D.

This formalizes `thm:physics:phyx_mini_0160:target`.
-/
theorem problem_phyx_mini_0160
    (setup : SphericalMirrorMagnificationSetup)
    (_figure : MatchesProblemAndGraph setup)
    (_calibration : HasFigureDerivedFocalCalibration setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesParaxialSphericalMirrorLaws setup) :
    setup.lateralMagnificationAt setup.requestedObjectDistance =
        (-5 : ℝ) / 2 ∧
      MatchesDisplayedAnswer setup recordedDatasetAnswer := by
  have hfinite :
      IsFiniteObjectConfiguration setup setup.requestedObjectDistance :=
    ⟨_physical.requested_distance_positive,
      _physical.requested_distance_not_focal⟩
  have himage :=
    requestedSignedImageDistanceCentimeters_eq_thirty_five setup _figure
      _calibration _physical _laws
  have hmagnification :=
    _laws.lateral_magnification_law LengthUnit.centimeters
      setup.requestedObjectDistance hfinite
  change
    setup.lateralMagnificationAt setup.requestedObjectDistance =
      -(lengthInCentimeters
          (setup.signedImageDistanceAt setup.requestedObjectDistance)) /
        lengthInCentimeters setup.requestedObjectDistance at hmagnification
  rw [himage, _figure.requested_distance_centimeters] at hmagnification
  constructor
  · calc
      setup.lateralMagnificationAt setup.requestedObjectDistance =
          -35 / 14 := hmagnification
      _ = (-5 : ℝ) / 2 := by norm_num
  · change
      setup.lateralMagnificationAt setup.requestedObjectDistance =
        -(5 / 2 : ℝ)
    calc
      setup.lateralMagnificationAt setup.requestedObjectDistance =
          -35 / 14 := hmagnification
      _ = -(5 / 2 : ℝ) := by norm_num

end PhyXMiniProblems.ProblemPhyXMini0160
