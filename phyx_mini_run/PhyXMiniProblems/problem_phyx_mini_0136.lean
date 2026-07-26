import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0136

open Dimension

/-!
# Width of a film-projector image

A `105 mm` converging thin lens projects a real image of a `24 mm`-wide
film frame onto a screen `25.5 m` from the lens.  The source figure orders
the film, lens, and screen from left to right and shows representative light
rays travelling from the film, through the lens, and converging at the screen.

Every distance and width below is a Physlib dimensionful length.  Real numbers
occur only as readouts in an explicitly selected length unit.  The unknown
film-to-lens distance is determined by the thin-lens equation; the unknown
picture width is then determined by paraxial transverse magnification.
-/

/-- A signed physical length whose numerical value changes coherently with unit choice. -/
abbrev OpticalLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Unit choices obtained from SI by changing only the length unit. -/
def choicesWithLengthUnit (unit : LengthUnit) : UnitChoices :=
  { UnitChoices.SI with length := unit }

/-- Scalar readout of a physical length in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : OpticalLength) : ℝ :=
  (length (choicesWithLengthUnit unit)).val

/-- Scalar readout of a physical length in metres. -/
def metersValue (length : OpticalLength) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Scalar readout of a physical length in millimetres. -/
def millimetersValue (length : OpticalLength) : ℝ :=
  lengthReadout LengthUnit.millimeters length

/-- The optical type of the lens drawn in the projector figure. -/
inductive ThinLensKind where
  | converging
  | diverging
  deriving DecidableEq, Repr

/-- Whether the transmitted rays physically meet at the image. -/
inductive ImageNature where
  | real
  | virtual
  deriving DecidableEq, Repr

/-- The three labeled components ordered along the principal optical axis. -/
inductive ProjectorElement where
  | film
  | lens
  | screen
  deriving DecidableEq, Repr

/-- The three representative magenta ray paths visible in the source figure. -/
inductive FigureRay where
  | upper
  | central
  | lower
  deriving DecidableEq, Repr

/-- Orientation of the principal optical axis shown in the figure. -/
inductive PrincipalAxisOrientation where
  | horizontal
  deriving DecidableEq, Repr

/-- Direction in which light propagates through the projector. -/
inductive PropagationDirection where
  | filmToScreen
  | screenToFilm
  deriving DecidableEq, Repr

/-- A thin lens together with its physical focal length and qualitative kind. -/
structure ThinLens where
  kind : ThinLensKind
  focalLength : OpticalLength

/-
The physical quantities and labeled geometry in the film-projector setup.

`objectDistance` is the positive film-to-lens distance and `imageDistance` is
the positive lens-to-screen distance.  `filmWidth` and `pictureWidth` are
transverse length magnitudes represented in the same dimensionful length
type.  The three ray maps retain the qualitative path drawn in the figure.
-/
structure FilmProjectorSetup where
  lens : ThinLens
  imageNature : ImageNature
  principalAxisOrientation : PrincipalAxisOrientation
  propagationDirection : PropagationDirection
  axialPosition : ProjectorElement → OpticalLength
  raySource : FigureRay → ProjectorElement
  rayPassesThrough : FigureRay → ProjectorElement
  rayConvergesAt : FigureRay → ProjectorElement
  objectDistance : OpticalLength
  imageDistance : OpticalLength
  filmWidth : OpticalLength
  pictureWidth : OpticalLength

/-
Numerical readouts stated in the problem.  In particular, no readout of the
unknown object distance or projected picture width occurs in this predicate.
-/
structure HasStatedProjectorReadouts (setup : FilmProjectorSetup) : Prop where
  focal_length_millimeters :
    millimetersValue setup.lens.focalLength = 105
  screen_distance_meters :
    metersValue setup.imageDistance = 255 / 10
  film_width_millimeters :
    millimetersValue setup.filmWidth = 24

/-
Qualitative geometry read from the source image: the convex lens is between
the film and screen, and every displayed light ray goes from film through lens
to the common real image on the screen.  The distance equalities merely relate
the physical distance fields to axial figure positions.
-/
structure MatchesProjectorFigure (setup : FilmProjectorSetup) : Prop where
  converging_lens : setup.lens.kind = .converging
  real_screen_image : setup.imageNature = .real
  horizontal_axis : setup.principalAxisOrientation = .horizontal
  light_travels_film_to_screen :
    setup.propagationDirection = .filmToScreen
  film_left_of_lens :
    metersValue (setup.axialPosition .film) <
      metersValue (setup.axialPosition .lens)
  lens_left_of_screen :
    metersValue (setup.axialPosition .lens) <
      metersValue (setup.axialPosition .screen)
  object_distance_geometry :
    ∀ units : UnitChoices,
      setup.objectDistance units =
        setup.axialPosition .lens units - setup.axialPosition .film units
  image_distance_geometry :
    ∀ units : UnitChoices,
      setup.imageDistance units =
        setup.axialPosition .screen units - setup.axialPosition .lens units
  ray_sources : ∀ ray : FigureRay, setup.raySource ray = .film
  rays_pass_through_lens :
    ∀ ray : FigureRay, setup.rayPassesThrough ray = .lens
  ray_convergence_targets :
    ∀ ray : FigureRay, setup.rayConvergesAt ray = .screen

/-- Positivity conditions appropriate to physical distance and width magnitudes. -/
structure HasPhysicalProjectorLengths (setup : FilmProjectorSetup) : Prop where
  focal_length_positive : 0 < metersValue setup.lens.focalLength
  object_distance_positive : 0 < metersValue setup.objectDistance
  image_distance_positive : 0 < metersValue setup.imageDistance
  film_width_positive : 0 < metersValue setup.filmWidth
  picture_width_positive : 0 < metersValue setup.pictureWidth

/-
The Gaussian thin-lens equation `1/f = 1/d_o + 1/d_i`, written in the
division-free, dimensionally homogeneous form
`f * (d_o + d_i) = d_o * d_i` for every length unit.
-/
def ObeysThinLensEquation (setup : FilmProjectorSetup) : Prop :=
  ∀ unit : LengthUnit,
    lengthReadout unit setup.lens.focalLength *
        (lengthReadout unit setup.objectDistance +
          lengthReadout unit setup.imageDistance) =
      lengthReadout unit setup.objectDistance *
        lengthReadout unit setup.imageDistance

/-
The paraxial transverse-width law
`pictureWidth / filmWidth = imageDistance / objectDistance`, written without
division as a dimensionally homogeneous relation in every length unit.  This
is a general governing law and contains no numerical picture-width answer.
-/
def ObeysParaxialWidthMagnificationLaw (setup : FilmProjectorSetup) : Prop :=
  ∀ unit : LengthUnit,
    lengthReadout unit setup.pictureWidth *
        lengthReadout unit setup.objectDistance =
      lengthReadout unit setup.filmWidth *
        lengthReadout unit setup.imageDistance

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Picture-width readout in metres printed beside an answer choice. -/
def AnswerChoice.pictureWidthMeters : AnswerChoice → ℝ
  | .A => 38 / 10
  | .B => 48 / 10
  | .C => 58 / 10
  | .D => 68 / 10

/-
`reported` is a nearest-tenth decimal readout of `exact`: it is an integer
number of tenths and differs from the exact value by at most half a tenth.
-/
def IsNearestTenthReadout (exact reported : ℝ) : Prop :=
  (∃ tenths : ℤ, reported = (tenths : ℝ) / 10) ∧
    |exact - reported| ≤ 1 / 20

/-- A choice agrees to the nearest tenth with the physical picture width. -/
def AnswerChoiceMatchesPicture
    (setup : FilmProjectorSetup) (choice : AnswerChoice) : Prop :=
  IsNearestTenthReadout
    (metersValue setup.pictureWidth) choice.pictureWidthMeters

/-
The stated focal length and screen distance determine the film-to-lens object
distance as `357/3386 m`.  This is a derived result, not a setup assumption.
-/
lemma objectDistanceInMeters_eq_three_fifty_seven_over_three_three_eight_six
    (setup : FilmProjectorSetup)
    (h_data : HasStatedProjectorReadouts setup)
    (h_lens : ObeysThinLensEquation setup) :
    metersValue setup.objectDistance = 357 / 3386 := by
  have millimeters_eq (length : OpticalLength) :
      millimetersValue length = 1000 * metersValue length := by
    have h := congrArg WithDim.val
      (length.2 (choicesWithLengthUnit LengthUnit.meters)
        (choicesWithLengthUnit LengthUnit.millimeters))
    change millimetersValue length = _ * metersValue length at h
    norm_num [choicesWithLengthUnit, UnitChoices.dimScale,
      LengthUnit.millimeters, LengthUnit.scale, LengthUnit.div_eq_val,
      LengthUnit.meters, NNReal.smul_def] at h ⊢
    exact h
  have h_focal_meters :
      metersValue setup.lens.focalLength = 105 / 1000 := by
    nlinarith only
      [h_data.focal_length_millimeters,
        millimeters_eq setup.lens.focalLength]
  have h_equation := h_lens LengthUnit.meters
  change
    metersValue setup.lens.focalLength *
        (metersValue setup.objectDistance +
          metersValue setup.imageDistance) =
      metersValue setup.objectDistance *
        metersValue setup.imageDistance at h_equation
  rw [h_focal_meters, h_data.screen_distance_meters] at h_equation
  norm_num at h_equation ⊢
  linarith

/-
The thin-lens and transverse-width laws determine the exact projected width as
`5079/875 m`, approximately `5.80457 m`.
-/
lemma pictureWidthInMeters_eq_five_zero_seven_nine_over_eight_seven_five
    (setup : FilmProjectorSetup)
    (h_data : HasStatedProjectorReadouts setup)
    (h_physical : HasPhysicalProjectorLengths setup)
    (h_lens : ObeysThinLensEquation setup)
    (h_magnification : ObeysParaxialWidthMagnificationLaw setup) :
    metersValue setup.pictureWidth = 5079 / 875 := by
  have millimeters_eq (length : OpticalLength) :
      millimetersValue length = 1000 * metersValue length := by
    have h := congrArg WithDim.val
      (length.2 (choicesWithLengthUnit LengthUnit.meters)
        (choicesWithLengthUnit LengthUnit.millimeters))
    change millimetersValue length = _ * metersValue length at h
    norm_num [choicesWithLengthUnit, UnitChoices.dimScale,
      LengthUnit.millimeters, LengthUnit.scale, LengthUnit.div_eq_val,
      LengthUnit.meters, NNReal.smul_def] at h ⊢
    exact h
  have h_film_width_meters :
      metersValue setup.filmWidth = 24 / 1000 := by
    nlinarith only
      [h_data.film_width_millimeters, millimeters_eq setup.filmWidth]
  have h_object_distance :=
    objectDistanceInMeters_eq_three_fifty_seven_over_three_three_eight_six
      setup h_data h_lens
  have h_equation := h_magnification LengthUnit.meters
  change
    metersValue setup.pictureWidth * metersValue setup.objectDistance =
      metersValue setup.filmWidth * metersValue setup.imageDistance at h_equation
  rw [h_object_distance, h_film_width_meters,
    h_data.screen_distance_meters] at h_equation
  norm_num at h_equation ⊢
  linarith

/-
A `105 mm` lens projecting a `24 mm` film frame onto a screen `25.5 m` away
therefore produces an exact picture width of `5079/875 m`.  Its nearest-tenth
readout is `5.8 m`, answer choice C.

This formalizes `thm:physics:phyx_mini_0136:target`.
-/
theorem problem_phyx_mini_0136
    (setup : FilmProjectorSetup)
    (h_data : HasStatedProjectorReadouts setup)
    (h_figure : MatchesProjectorFigure setup)
    (h_physical : HasPhysicalProjectorLengths setup)
    (h_lens : ObeysThinLensEquation setup)
    (h_magnification : ObeysParaxialWidthMagnificationLaw setup) :
    metersValue setup.pictureWidth = 5079 / 875 ∧
      AnswerChoiceMatchesPicture setup .C := by
  have h_width :=
    pictureWidthInMeters_eq_five_zero_seven_nine_over_eight_seven_five
      setup h_data h_physical h_lens h_magnification
  refine ⟨h_width, ?_⟩
  rw [AnswerChoiceMatchesPicture, IsNearestTenthReadout,
    AnswerChoice.pictureWidthMeters, h_width]
  constructor
  · exact ⟨58, by norm_num⟩
  · norm_num [abs_of_nonneg]

end PhyXMiniProblems.ProblemPhyXMini0136
