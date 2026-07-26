import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0066

open Dimension

/-!
# Focal length of the depicted concave glass lens

The figure shows a biconcave glass lens centered on a horizontal principal
axis.  The two black axial markers are interpreted as the two principal focal
points, and each marker is labelled as being `40 cm` from the optical center.

Physical focal lengths and axial positions are represented by Physlib
dimensionful length quantities.  Real numbers occur only as signed centimeter
readouts and as dimensionless refractive indices.
-/

/-- A signed physical length whose value transforms coherently with the unit choice. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- SI units with centimeters selected for length readouts. -/
def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The signed scalar readout of a physical length in centimeters. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  (length centimeterUnitChoices).val

/-- The optical media needed to classify a glass lens surrounded by air. -/
inductive OpticalMedium where
  | air
  | glass
  deriving DecidableEq, Repr

/-- The material from which the depicted thin lens is made. -/
inductive LensMaterial where
  | glass
  | other
  deriving DecidableEq, Repr

/-- Axial cross-section profiles relevant to the depicted lens. -/
inductive LensProfile where
  | biconcave
  | other
  deriving DecidableEq, Repr

/-- The two paraxial optical classes of a thin lens. -/
inductive ThinLensKind where
  | converging
  | diverging
  deriving DecidableEq, Repr

/-- The three concrete axial locations visible in the figure. -/
inductive AxialLocation where
  | leftBlackMarker
  | opticalCenter
  | rightBlackMarker
  deriving DecidableEq, Repr

/-- The two principal focal-point roles of a thin lens. -/
inductive PrincipalFocusSide where
  | left
  | right
  deriving DecidableEq, Repr

/--
The physical lens and the labelled one-dimensional geometry of its figure.

`principalFocusMarker` records the optical interpretation of the two black
dots without identifying their distance with the unknown focal length in the
data structure itself.
-/
structure ConcaveLensSetup where
  material : LensMaterial
  profile : LensProfile
  kind : ThinLensKind
  refractiveIndex : OpticalMedium → ℝ
  focalLength : LengthQuantity
  axisPosition : AxialLocation → LengthQuantity
  principalFocusMarker : PrincipalFocusSide → AxialLocation

/-- The unsigned separation of two labelled axis locations, in centimeters. -/
def axialSeparationInCentimeters
    (setup : ConcaveLensSetup) (first second : AxialLocation) : ℝ :=
  |lengthInCentimeters (setup.axisPosition second) -
    lengthInCentimeters (setup.axisPosition first)|

/-!
The qualitative labels and quantitative arrows read from the primary figure.
The two `40 cm` relations are retained independently, even though either one
is sufficient to determine the focal-length magnitude.
-/
structure MatchesConcaveLensFigure (setup : ConcaveLensSetup) : Prop where
  lens_is_glass : setup.material = .glass
  profile_is_biconcave : setup.profile = .biconcave
  left_marker_is_principal_focus :
    setup.principalFocusMarker .left = .leftBlackMarker
  right_marker_is_principal_focus :
    setup.principalFocusMarker .right = .rightBlackMarker
  axial_order :
    lengthInCentimeters (setup.axisPosition .leftBlackMarker) <
        lengthInCentimeters (setup.axisPosition .opticalCenter) ∧
      lengthInCentimeters (setup.axisPosition .opticalCenter) <
        lengthInCentimeters (setup.axisPosition .rightBlackMarker)
  left_distance_label :
    axialSeparationInCentimeters setup .leftBlackMarker .opticalCenter = 40
  right_distance_label :
    axialSeparationInCentimeters setup .opticalCenter .rightBlackMarker = 40

/-- The physical refractive-index branch for ordinary glass surrounded by air. -/
structure HasOrdinaryGlassOpticalParameters (setup : ConcaveLensSetup) : Prop where
  air_index_positive : 0 < setup.refractiveIndex .air
  glass_index_exceeds_air :
    setup.refractiveIndex .air < setup.refractiveIndex .glass

/-!
The standard paraxial classification of a biconcave glass lens in a
lower-index ambient medium.  This law determines only that the lens is
diverging; it does not specify its focal-length magnitude.
-/
def SatisfiesBiconcaveLensClassification (setup : ConcaveLensSetup) : Prop :=
  setup.material = .glass →
    setup.profile = .biconcave →
      setup.refractiveIndex .air < setup.refractiveIndex .glass →
        setup.kind = .diverging

/-!
The governing relation between the two principal focal points and signed
focal length.  Each principal-focus separation is the magnitude `|f|`, while
the Cartesian sign convention assigns a negative focal length to a diverging
lens.  No numerical focal length is assumed here.
-/
structure SatisfiesPrincipalFocusLaw (setup : ConcaveLensSetup) : Prop where
  left_focus_distance :
    axialSeparationInCentimeters setup
        (setup.principalFocusMarker .left) .opticalCenter =
      |lengthInCentimeters setup.focalLength|
  right_focus_distance :
    axialSeparationInCentimeters setup .opticalCenter
        (setup.principalFocusMarker .right) =
      |lengthInCentimeters setup.focalLength|
  diverging_focal_length_negative :
    setup.kind = .diverging → lengthInCentimeters setup.focalLength < 0

/-- Labels of the four multiple-choice answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The signed focal-length readout printed for each answer, in centimeters. -/
def answerFocalLengthInCentimeters : AnswerChoice → ℝ
  | .A => -24
  | .B => -56
  | .C => -40
  | .D => -68

/-- Exact agreement with one of the displayed whole-centimeter answers. -/
def MatchesAnswerExactly
    (focalLength : LengthQuantity) (choice : AnswerChoice) : Prop :=
  lengthInCentimeters focalLength = answerFocalLengthInCentimeters choice

/-!
Either focal-point arrow in the figure, together with the principal-focus
law, determines the magnitude of the focal length as `40 cm`.
-/
lemma focalLengthMagnitude_eq_forty
    (setup : ConcaveLensSetup)
    (_figure : MatchesConcaveLensFigure setup)
    (_focusLaw : SatisfiesPrincipalFocusLaw setup) :
    |lengthInCentimeters setup.focalLength| = 40 := by
  calc
    |lengthInCentimeters setup.focalLength| =
        axialSeparationInCentimeters setup .leftBlackMarker .opticalCenter := by
          rw [← _figure.left_marker_is_principal_focus]
          exact _focusLaw.left_focus_distance.symm
    _ = 40 := _figure.left_distance_label

/-!
The biconcave glass lens is diverging, so the `40 cm` focal-point distance has
negative signed focal length.  Thus its focal length is `-40 cm`, answer C.

This formalizes blueprint label `thm:physics:phyx_mini_0066:target`.
-/
theorem problem_phyx_mini_0066
    (setup : ConcaveLensSetup)
    (_figure : MatchesConcaveLensFigure setup)
    (_physical : HasOrdinaryGlassOpticalParameters setup)
    (_classification : SatisfiesBiconcaveLensClassification setup)
    (_focusLaw : SatisfiesPrincipalFocusLaw setup) :
    lengthInCentimeters setup.focalLength = -40 ∧
      MatchesAnswerExactly setup.focalLength .C := by
  have hdiverging : setup.kind = .diverging :=
    _classification _figure.lens_is_glass _figure.profile_is_biconcave
      _physical.glass_index_exceeds_air
  have hnegative : lengthInCentimeters setup.focalLength < 0 :=
    _focusLaw.diverging_focal_length_negative hdiverging
  have hmagnitude :
      |lengthInCentimeters setup.focalLength| = 40 :=
    focalLengthMagnitude_eq_forty setup _figure _focusLaw
  rw [abs_of_neg hnegative] at hmagnitude
  have hfocal : lengthInCentimeters setup.focalLength = -40 := by
    linarith
  exact ⟨hfocal, hfocal⟩

end PhyXMiniProblems.ProblemPhyXMini0066
