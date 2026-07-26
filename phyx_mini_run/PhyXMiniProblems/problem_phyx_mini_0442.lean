import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0442

open Dimension

/-!
# Image distance inferred from a spherical-mirror graph

An object starts against the vertex of a spherical mirror and is moved along
the horizontal principal axis.  The intended source graph plots signed image
distance `i` against object distance `p`, with horizontal scale mark
`p_s = 40 cm`.  The supplied PNG does not depict this graph.  Consequently,
the half-scale vertical-asymptote calibration needed to recover the recorded
answer is exposed below as a conditional intended-graph hypothesis; it is not
claimed to have been read from the mismatched raster image.

All optical distances are genuine Physlib dimension-carrying quantities.
Real numbers occur only as scalar readouts in a named unit.
-/

/-- A signed physical optical length, independent of the unit used to read it. -/
abbrev OpticalLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- SI base units with centimeters selected as the length unit. -/
noncomputable def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The signed scalar readout of an optical length in centimeters. -/
def lengthInCentimeters (length : OpticalLength) : ℝ :=
  (length centimeterUnitChoices).val

/-- The optical type of a spherical mirror, viewed from the incident-light side. -/
inductive SphericalMirrorKind where
  | concave
  | convex
  deriving DecidableEq, Repr

/-- Orientation of the central optical axis in the intended graph and experiment. -/
inductive PrincipalAxisOrientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- The two coordinate axes of the mirror-distance graph. -/
inductive GraphAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical quantities attached to the graph labels `p` and `i`. -/
inductive DistanceGraphQuantity where
  | objectDistanceP
  | imageDistanceI
  deriving DecidableEq, Repr

/-!
The intended `i`-versus-`p` graph.  `pSubS` is the dimensionful quantity
printed as `p_s`; `verticalAsymptoteObjectDistance` records the object-distance
coordinate at which the plotted curve diverges.  The image-distance response
is stored as a physical length for every object distance, including distances
beyond the displayed range.
-/
structure MirrorDistanceGraph where
  axisQuantity : GraphAxis → DistanceGraphQuantity
  axisLengthUnit : GraphAxis → LengthUnit
  originLabelVisible : GraphAxis → Bool
  pSubSLabelVisible : Bool
  hasRectangularGrid : Bool
  pSubS : OpticalLength
  verticalAsymptoteObjectDistance : OpticalLength
  imageDistanceAt : OpticalLength → OpticalLength

/-!
The spherical mirror, its intended graph, and the two axial positions needed
by the question.  `axialDisplacement` is the object's physical motion from its
initial position; `requestedObjectDistance` is the resulting value of `p`.
No value is assigned here to the requested image distance.
-/
structure SphericalMirrorExperiment where
  mirrorKind : SphericalMirrorKind
  principalAxisOrientation : PrincipalAxisOrientation
  focalLength : OpticalLength
  initialObjectDistance : OpticalLength
  axialDisplacement : OpticalLength
  requestedObjectDistance : OpticalLength
  graph : MirrorDistanceGraph

/-!
Problem-statement data and the explicit intended-graph calibration.  The object
begins at `p = 0`, moves `70 cm`, and the graph's horizontal scale mark is
`p_s = 40 cm`.  Because the supplied raster is unrelated, the condition that
the vertical asymptote bisects the displayed scale is a transparent conditional
input for the intended graph, not a claimed raster readout.  No value of `i` at
`p = 70 cm` occurs here.
-/
structure MatchesProblemAndIntendedGraph
    (setup : SphericalMirrorExperiment) : Prop where
  mirror_is_concave : setup.mirrorKind = .concave
  principal_axis_is_horizontal :
    setup.principalAxisOrientation = .horizontal
  horizontal_axis_is_p :
    setup.graph.axisQuantity .horizontal = .objectDistanceP
  vertical_axis_is_i :
    setup.graph.axisQuantity .vertical = .imageDistanceI
  horizontal_axis_uses_centimeters :
    setup.graph.axisLengthUnit .horizontal = LengthUnit.centimeters
  vertical_axis_uses_centimeters :
    setup.graph.axisLengthUnit .vertical = LengthUnit.centimeters
  horizontal_origin_label_visible :
    setup.graph.originLabelVisible .horizontal = true
  vertical_origin_label_visible :
    setup.graph.originLabelVisible .vertical = true
  p_sub_s_label_visible : setup.graph.pSubSLabelVisible = true
  rectangular_grid_visible : setup.graph.hasRectangularGrid = true
  object_starts_against_mirror_center :
    lengthInCentimeters setup.initialObjectDistance = 0
  displacement_is_seventy_centimeters :
    lengthInCentimeters setup.axialDisplacement = 70
  requested_distance_is_initial_plus_displacement :
    lengthInCentimeters setup.requestedObjectDistance =
      lengthInCentimeters setup.initialObjectDistance +
        lengthInCentimeters setup.axialDisplacement
  p_sub_s_is_forty_centimeters :
    lengthInCentimeters setup.graph.pSubS = 40
  asymptote_bisects_horizontal_scale :
    2 * lengthInCentimeters setup.graph.verticalAsymptoteObjectDistance =
      lengthInCentimeters setup.graph.pSubS

/-- Positivity conditions selecting the physical concave-mirror branch. -/
structure HasPhysicalMirrorDistances
    (setup : SphericalMirrorExperiment) : Prop where
  focal_length_positive : 0 < lengthInCentimeters setup.focalLength
  displacement_positive : 0 < lengthInCentimeters setup.axialDisplacement
  requested_object_distance_positive :
    0 < lengthInCentimeters setup.requestedObjectDistance
  graph_scale_positive : 0 < lengthInCentimeters setup.graph.pSubS
  asymptote_distance_positive :
    0 < lengthInCentimeters setup.graph.verticalAsymptoteObjectDistance

/-!
For an ideal paraxial spherical mirror, the vertical asymptote of the
`i`-versus-`p` graph occurs at `p = f`.  This connects a generic graph feature
to the mirror's unknown focal length and contains no requested image distance.
-/
def GraphAsymptoteRepresentsFocalDistance
    (setup : SphericalMirrorExperiment) : Prop :=
  setup.graph.verticalAsymptoteObjectDistance = setup.focalLength

/-!
The signed Gaussian spherical-mirror equation

`1 / f = 1 / p + 1 / i`

is written, away from `p = f`, in the division-free homogeneous form
`f * (p + i) = p * i`.  Requiring it for every unit choice makes the relation
independent of the centimeter readouts used by the graph.
-/
def SatisfiesGaussianSphericalMirrorEquation
    (setup : SphericalMirrorExperiment) : Prop :=
  ∀ objectDistance : OpticalLength,
    objectDistance ≠ setup.focalLength →
      ∀ units : UnitChoices,
        (setup.focalLength units).val *
              ((objectDistance units).val +
                (setup.graph.imageDistanceAt objectDistance units).val) =
          (objectDistance units).val *
            (setup.graph.imageDistanceAt objectDistance units).val

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The image-distance readout printed beside each answer label, in centimeters. -/
def AnswerChoice.imageDistanceInCentimeters : AnswerChoice → ℝ
  | .A => 22
  | .B => 24
  | .C => 26
  | .D => 28

/-- Exact agreement of a physical image distance with a displayed choice. -/
def MatchesAnswerChoice
    (imageDistance : OpticalLength) (choice : AnswerChoice) : Prop :=
  lengthInCentimeters imageDistance = choice.imageDistanceInCentimeters

/-!
Under the explicit intended-graph calibration, `p_s = 40 cm` and the focal
asymptote lies at half that scale, so the mirror has focal length `20 cm`.
-/
lemma focalLengthInCentimeters_eq_twenty
    (setup : SphericalMirrorExperiment)
    (_figure : MatchesProblemAndIntendedGraph setup)
    (_physical : HasPhysicalMirrorDistances setup)
    (_asymptote : GraphAsymptoteRepresentsFocalDistance setup) :
    lengthInCentimeters setup.focalLength = 20 := by
  unfold GraphAsymptoteRepresentsFocalDistance at _asymptote
  rw [← _asymptote]
  linarith [_figure.asymptote_bisects_horizontal_scale,
    _figure.p_sub_s_is_forty_centimeters]

/-!
At the requested object distance `p = 70 cm`, the calibrated value `f = 20 cm`
and the Gaussian mirror equation give `i = 28 cm`, which is answer choice D.

This formalizes blueprint label `thm:physics:phyx_mini_0442:target`.
-/
theorem problem_phyx_mini_0442
    (setup : SphericalMirrorExperiment)
    (_figure : MatchesProblemAndIntendedGraph setup)
    (_physical : HasPhysicalMirrorDistances setup)
    (_asymptote : GraphAsymptoteRepresentsFocalDistance setup)
    (_mirrorEquation : SatisfiesGaussianSphericalMirrorEquation setup) :
    lengthInCentimeters
        (setup.graph.imageDistanceAt setup.requestedObjectDistance) = 28 ∧
      MatchesAnswerChoice
        (setup.graph.imageDistanceAt setup.requestedObjectDistance) .D := by
  have hf : lengthInCentimeters setup.focalLength = 20 :=
    focalLengthInCentimeters_eq_twenty setup _figure _physical _asymptote
  have hp : lengthInCentimeters setup.requestedObjectDistance = 70 := by
    linarith [_figure.object_starts_against_mirror_center,
      _figure.displacement_is_seventy_centimeters,
      _figure.requested_distance_is_initial_plus_displacement]
  have hp_ne : setup.requestedObjectDistance ≠ setup.focalLength := by
    intro h
    rw [h] at hp
    linarith
  have heq :=
    _mirrorEquation setup.requestedObjectDistance hp_ne centimeterUnitChoices
  change lengthInCentimeters setup.focalLength *
      (lengthInCentimeters setup.requestedObjectDistance +
        lengthInCentimeters
          (setup.graph.imageDistanceAt setup.requestedObjectDistance)) =
    lengthInCentimeters setup.requestedObjectDistance *
      lengthInCentimeters
        (setup.graph.imageDistanceAt setup.requestedObjectDistance) at heq
  have hi : lengthInCentimeters
      (setup.graph.imageDistanceAt setup.requestedObjectDistance) = 28 := by
    nlinarith
  refine ⟨hi, ?_⟩
  simpa [MatchesAnswerChoice, AnswerChoice.imageDistanceInCentimeters] using hi

end PhyXMiniProblems.ProblemPhyXMini0442
