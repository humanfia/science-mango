import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0149

open Dimension

/-!
# Estimating a converging lens's focal length from image orientation

The source photograph has two panels.  A converging magnifying lens is held
`5 cm` above a sheet of paper in panel (a) and `15 cm` above it in panel (b).
The central copy of the letter A is upright through the lens in (a) and
inverted in (b), while the three letters printed on the paper have equal
physical size.

For a real object and a converging lens, the upright observation places the
object inside the focal plane and the inverted observation places it beyond
the focal plane.  The uncovered equal-sized letters provide a scale from
which the two central images have approximately equal magnification magnitude.
Together with the thin-lens transverse-magnification law, these observations
estimate the focal length.  All physical lengths are unit-independent Physlib
quantities; real numbers occur only as scalar centimeter readouts or as the
dimensionless signed magnification.
-/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- The scalar readout of a physical length in centimeters. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  ((length { UnitChoices.SI with length := LengthUnit.centimeters }).val : ℝ)

/-- Labels (a) and (b) of the two source-image panels. -/
inductive FigurePanel where
  | a
  | b
  deriving DecidableEq, Repr

/-- Horizontal positions of the three equal-sized printed letters. -/
inductive LetterPosition where
  | left
  | center
  | right
  deriving DecidableEq, Repr

/-- Physical elements present in each panel of the photograph. -/
inductive FigureElement where
  | lens
  | paper
  | letter (position : LetterPosition)
  deriving DecidableEq, Repr

/-- The printed glyph used at all three positions. -/
inductive PrintedGlyph where
  | capitalA
  deriving DecidableEq, Repr

/-- Optical kind of a paraxial thin lens. -/
inductive LensKind where
  | converging
  | diverging
  deriving DecidableEq, Repr

/-- Orientation of the central letter as viewed through the lens. -/
inductive ImageOrientation where
  | upright
  | inverted
  deriving DecidableEq, Repr

/-- Apparent size of the central image relative to the uncovered letters. -/
inductive ApparentSizeRelation where
  | reduced
  | sameSize
  | magnified
  deriving DecidableEq, Repr

/-- A thin lens with its genuine, as-yet unknown physical focal length. -/
structure ThinLens where
  kind : LensKind
  focalLength : LengthQuantity

/-!
The physical setup and all panel-indexed measurements.  The actual focal
length remains an unknown physical length; no numerical answer is assigned to
it here.  Signed transverse magnification is positive for an upright image and
negative for an inverted image.
-/
structure FocalLengthEstimateSetup where
  lens : ThinLens
  figureShows : FigurePanel → FigureElement → Prop
  glyphAt : LetterPosition → PrintedGlyph
  physicalLetterHeight : LetterPosition → LengthQuantity
  lensDistanceFromPaper : FigurePanel → LengthQuantity
  observedCentralOrientation : FigurePanel → ImageOrientation
  observedCentralSize : FigurePanel → ApparentSizeRelation
  observedSignedTransverseMagnification : FigurePanel → ℝ

/-!
Primary-figure and problem-statement readouts: both panels contain the lens,
paper, and three copies of A; the printed copies have equal physical height;
the lens-paper separations are `5 cm` and `15 cm`; and the viewed central A is
upright in (a) and inverted in (b).  Both central images are magnified by
approximately the same factor relative to the uncovered equal-sized letters;
that visual estimate is idealized as equality of magnification magnitudes.
No focal-length value or answer choice occurs in this predicate.
-/
def MatchesProblemAndPrimaryFigure (setup : FocalLengthEstimateSetup) : Prop :=
  setup.lens.kind = .converging ∧
    (∀ panel, setup.figureShows panel .lens) ∧
    (∀ panel, setup.figureShows panel .paper) ∧
    (∀ panel position, setup.figureShows panel (.letter position)) ∧
    (∀ position, setup.glyphAt position = .capitalA) ∧
    (∀ position,
      lengthInCentimeters (setup.physicalLetterHeight position) =
        lengthInCentimeters (setup.physicalLetterHeight .center)) ∧
    lengthInCentimeters (setup.lensDistanceFromPaper .a) = 5 ∧
    lengthInCentimeters (setup.lensDistanceFromPaper .b) = 15 ∧
    setup.observedCentralOrientation .a = .upright ∧
    setup.observedCentralSize .a = .magnified ∧
    setup.observedCentralOrientation .b = .inverted ∧
    setup.observedCentralSize .b = .magnified ∧
    |setup.observedSignedTransverseMagnification .a| =
      |setup.observedSignedTransverseMagnification .b|

/-- Positivity conditions for every physical length used in the model. -/
def HasPositivePhysicalLengths (setup : FocalLengthEstimateSetup) : Prop :=
  0 < lengthInCentimeters setup.lens.focalLength ∧
    (∀ panel, 0 < lengthInCentimeters (setup.lensDistanceFromPaper panel)) ∧
    ∀ position, 0 < lengthInCentimeters (setup.physicalLetterHeight position)

/-!
The paraxial laws used in this problem.  For a converging lens and a real
object on the paper, an upright view means that the object is inside the focal
plane and has positive signed magnification, whereas an inverted view means
that it is beyond the focal plane and has negative signed magnification.

The transverse-magnification equation is written without division as
`m * (f - u) = f`, where all length readouts use centimeters.  It is the
standard relation `m = f / (f - u)` obtained from the Gaussian thin-lens and
magnification equations.  These are general governing laws and contain no
problem-specific focal-length answer.
-/
structure SatisfiesParaxialConvergingLensModel
    (setup : FocalLengthEstimateSetup) : Prop where
  upright_image_inside_focal_plane :
    ∀ panel,
      setup.lens.kind = .converging →
        setup.observedCentralOrientation panel = .upright →
          lengthInCentimeters (setup.lensDistanceFromPaper panel) <
            lengthInCentimeters setup.lens.focalLength
  inverted_image_beyond_focal_plane :
    ∀ panel,
      setup.lens.kind = .converging →
        setup.observedCentralOrientation panel = .inverted →
          lengthInCentimeters setup.lens.focalLength <
            lengthInCentimeters (setup.lensDistanceFromPaper panel)
  upright_image_has_positive_magnification :
    ∀ panel,
      setup.observedCentralOrientation panel = .upright →
        0 < setup.observedSignedTransverseMagnification panel
  inverted_image_has_negative_magnification :
    ∀ panel,
      setup.observedCentralOrientation panel = .inverted →
        setup.observedSignedTransverseMagnification panel < 0
  transverse_magnification_law :
    ∀ panel,
      setup.observedSignedTransverseMagnification panel *
          (lengthInCentimeters setup.lens.focalLength -
            lengthInCentimeters (setup.lensDistanceFromPaper panel)) =
        lengthInCentimeters setup.lens.focalLength

/-- Labels of the four focal-length choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The focal-length readout printed beside each answer label, in centimeters. -/
def displayedFocalLengthInCentimeters : AnswerChoice → ℝ
  | .A => 8
  | .B => 12
  | .C => 10
  | .D => 14

/-- Exact agreement between the inferred physical focal length and a choice. -/
def MatchesAnswerChoice
    (setup : FocalLengthEstimateSetup) (choice : AnswerChoice) : Prop :=
  lengthInCentimeters setup.lens.focalLength =
    displayedFocalLengthInCentimeters choice

/-- The selected choice is the unique displayed value equal to the estimate. -/
def IsUniqueMatchingAnswerChoice
    (setup : FocalLengthEstimateSetup) (choice : AnswerChoice) : Prop :=
  MatchesAnswerChoice setup choice ∧
    ∀ other : AnswerChoice, MatchesAnswerChoice setup other → other = choice

/-- The upright and inverted observations bracket the true focal length. -/
lemma actualFocalLength_is_bracketed
    (setup : FocalLengthEstimateSetup)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_optics : SatisfiesParaxialConvergingLensModel setup) :
    lengthInCentimeters (setup.lensDistanceFromPaper .a) <
        lengthInCentimeters setup.lens.focalLength ∧
      lengthInCentimeters setup.lens.focalLength <
        lengthInCentimeters (setup.lensDistanceFromPaper .b) := by
  rcases h_figure with
    ⟨h_kind, _, _, _, _, _, _, _, h_orientation_a, _,
      h_orientation_b, _, _⟩
  exact
    ⟨h_optics.upright_image_inside_focal_plane
        .a h_kind h_orientation_a,
      h_optics.inverted_image_beyond_focal_plane
        .b h_kind h_orientation_b⟩

/-!
The actual focal length lies strictly between `5 cm` and `15 cm`.  The equal
magnification magnitudes and the transverse-magnification law sharpen this
bracket to the figure-based estimate `10 cm`, uniquely selecting answer C.

This formalizes `thm:physics:phyx_mini_0149:target`.  Neither `10 cm` nor
choice C occurs in a premise, setup field, or governing-law field.
-/
theorem problem_phyx_mini_0149
    (setup : FocalLengthEstimateSetup)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_physical : HasPositivePhysicalLengths setup)
    (h_optics : SatisfiesParaxialConvergingLensModel setup) :
    (5 < lengthInCentimeters setup.lens.focalLength ∧
      lengthInCentimeters setup.lens.focalLength < 15) ∧
      lengthInCentimeters setup.lens.focalLength = 10 ∧
      IsUniqueMatchingAnswerChoice setup .C := by
  have h_bracket :=
    actualFocalLength_is_bracketed setup h_figure h_optics
  rcases h_figure with
    ⟨_, _, _, _, _, _, h_distance_a, h_distance_b,
      h_orientation_a, _, h_orientation_b, _, h_equal_magnitudes⟩
  have h_magnification_a_positive :=
    h_optics.upright_image_has_positive_magnification
      .a h_orientation_a
  have h_magnification_b_negative :=
    h_optics.inverted_image_has_negative_magnification
      .b h_orientation_b
  have h_opposite_magnifications :
      setup.observedSignedTransverseMagnification .a =
        -setup.observedSignedTransverseMagnification .b := by
    simpa [abs_of_pos h_magnification_a_positive,
      abs_of_neg h_magnification_b_negative] using h_equal_magnitudes
  have h_lens_law_a := h_optics.transverse_magnification_law .a
  have h_lens_law_b := h_optics.transverse_magnification_law .b
  rw [h_distance_a] at h_lens_law_a
  rw [h_distance_b] at h_lens_law_b
  have h_focal_length :
      lengthInCentimeters setup.lens.focalLength = 10 := by
    nlinarith
  constructor
  · simpa [h_distance_a, h_distance_b] using h_bracket
  constructor
  · exact h_focal_length
  · constructor
    · simpa [MatchesAnswerChoice,
        displayedFocalLengthInCentimeters] using h_focal_length
    · intro other h_other
      cases other <;>
        simp_all [MatchesAnswerChoice, displayedFocalLengthInCentimeters]

end PhyXMiniProblems.ProblemPhyXMini0149
