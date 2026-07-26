import Mathlib.Data.Real.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0132

open Dimension

/-!
# Angular resolution of the Arecibo radio telescope

The Arecibo reflector is modeled as a circular aperture of diameter `300 m`
and radius of curvature `300 m`. Its shortest stated operating wavelength is
`4 cm`. Rayleigh's circular-aperture criterion determines the theoretical
minimum angular separation of two just-resolved stars.

The three lengths below are unit-independent Physlib quantities. Real numbers
are used only for named scalar readouts, dimensionless radian angles, and the
displayed answer-choice values.
-/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- Scalar readout of a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length { UnitChoices.SI with length := unit }).val : ℝ)

/-- Meter readout used for the dish geometry stated in the problem. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimeter readout used for the shortest operating wavelength. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- The named instrument in the physical scenario. -/
inductive RadioTelescopeLabel where
  | arecibo
  deriving DecidableEq, Repr

/-- The two astronomical sources whose resolution is considered. -/
inductive StarLabel where
  | first
  | second
  deriving DecidableEq, Repr

/-- Physical class of each member of the source pair. -/
inductive AstronomicalSourceKind where
  | star
  deriving DecidableEq, Repr

/-- Shape of the effective collecting aperture. -/
inductive ApertureShape where
  | circular
  deriving DecidableEq, Repr

/-- Geometry of the Arecibo reflector visible in the supplied photograph. -/
inductive ReflectorGeometry where
  | fixedSphericalDish
  deriving DecidableEq, Repr

/-- Optical idealization used to define the theoretical resolution limit. -/
inductive ResolutionRegime where
  | circularApertureRayleigh
  deriving DecidableEq, Repr

/-- Distinct qualitative features visible in the primary figure. -/
inductive FigureFeature where
  | groundEmbeddedDish
  | suspendedReceiverPlatform
  | cableSupportTowers
  deriving DecidableEq, Repr

/-!
All physical quantities and figure labels in the problem.

`minimumAngularSeparationRad` is the unknown theoretical resolution limit.
Neither it nor `observedPairSeparationRad` is assigned a numerical answer in
this structure.
-/
structure AreciboResolutionSetup where
  telescope : RadioTelescopeLabel
  sourceKind : StarLabel → AstronomicalSourceKind
  apertureShape : ApertureShape
  reflectorGeometry : ReflectorGeometry
  resolutionRegime : ResolutionRegime
  figureShows : FigureFeature → Prop
  dishDiameter : LengthQuantity
  dishRadiusOfCurvature : LengthQuantity
  shortestOperatingWavelength : LengthQuantity
  observedPairSeparationRad : ℝ
  minimumAngularSeparationRad : ℝ

/-!
Qualitative scenario and primary-image readouts. The photograph shows the
large ground-embedded dish, its suspended receiver platform, and the support
towers and cables. It supplies no angular measurement.

The final equality says only that the two stars are *just resolved*: their
unknown separation is the unknown resolution limit. It does not assign the
requested numerical value.
-/
def MatchesScenarioAndFigure (setup : AreciboResolutionSetup) : Prop :=
  setup.telescope = .arecibo ∧
    (∀ star, setup.sourceKind star = .star) ∧
    setup.apertureShape = .circular ∧
    setup.reflectorGeometry = .fixedSphericalDish ∧
    setup.resolutionRegime = .circularApertureRayleigh ∧
    setup.figureShows .groundEmbeddedDish ∧
    setup.figureShows .suspendedReceiverPlatform ∧
    setup.figureShows .cableSupportTowers ∧
    setup.observedPairSeparationRad = setup.minimumAngularSeparationRad

/-!
Numerical data explicitly stated in the problem: dish diameter `300 m`, dish
radius of curvature `300 m`, and shortest operating wavelength `4 cm`.
-/
def MatchesProblemReadouts (setup : AreciboResolutionSetup) : Prop :=
  lengthInMeters setup.dishDiameter = 300 ∧
    lengthInMeters setup.dishRadiusOfCurvature = 300 ∧
    lengthInCentimeters setup.shortestOperatingWavelength = 4

/-- Positivity and angular-range conditions for the physical configuration. -/
def HasPhysicalParameters (setup : AreciboResolutionSetup) : Prop :=
  0 < lengthInMeters setup.dishDiameter ∧
    0 < lengthInMeters setup.dishRadiusOfCurvature ∧
    0 < lengthInCentimeters setup.shortestOperatingWavelength ∧
    0 < setup.minimumAngularSeparationRad ∧
    setup.minimumAngularSeparationRad < 1 ∧
    0 < setup.observedPairSeparationRad

/-!
Rayleigh's criterion for a circular aperture,

`theta_min = 1.22 * lambda / D`.

The radian angle is dimensionless. The factor `1.22` is represented exactly
as `61 / 50`, and the relation is required in every common length unit. This
is a governing optical law, not the requested numerical answer.
-/
structure SatisfiesCircularApertureRayleighCriterion
    (setup : AreciboResolutionSetup) : Prop where
  angularResolutionLaw :
    ∀ unit : LengthUnit,
      setup.minimumAngularSeparationRad =
        (61 / 50 : ℝ) *
          lengthReadout unit setup.shortestOperatingWavelength /
            lengthReadout unit setup.dishDiameter

/-- Labels of the four angular-separation choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Radian value printed beside each answer label. -/
def displayedAngularSeparationRad : AnswerChoice → ℝ
  | .A => 16 / 10 ^ 6
  | .B => 16 / 10 ^ 4
  | .C => 16 / 10 ^ 5
  | .D => 17 / 10 ^ 5

/-- Place value of the last displayed significant digit, in radians. -/
def displayedPrecisionRad : AnswerChoice → ℝ
  | .A => 1 / 10 ^ 6
  | .B => 1 / 10 ^ 4
  | .C => 1 / 10 ^ 5
  | .D => 1 / 10 ^ 5

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Agreement with a displayed answer after rounding to its shown precision. -/
def MatchesDisplayedAngularSeparation
    (setup : AreciboResolutionSetup) (choice : AnswerChoice) : Prop :=
  |setup.minimumAngularSeparationRad -
      displayedAngularSeparationRad choice| ≤
    displayedPrecisionRad choice / 2

/-- The selected choice is the unique displayed value matching the limit. -/
def IsUniqueMatchingAngularSeparation
    (setup : AreciboResolutionSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedAngularSeparation setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedAngularSeparation setup other → other = choice

/-!
For `lambda = 4 cm` and `D = 300 m`, Rayleigh's criterion gives the
unrounded theoretical limit

`theta_min = 61 / 375000 rad = 1.6266... * 10^(-4) rad`.

At the precision displayed by the options this uniquely selects
`1.6 * 10^(-4) rad`, answer C. The radius of curvature is retained as stated
setup data but does not enter the circular-aperture resolution law.

This formalizes `thm:physics:phyx_mini_0132:target`.
-/
theorem problem_phyx_mini_0132
    (setup : AreciboResolutionSetup)
    (h_scenario : MatchesScenarioAndFigure setup)
    (h_data : MatchesProblemReadouts setup)
    (h_physical : HasPhysicalParameters setup)
    (h_rayleigh : SatisfiesCircularApertureRayleighCriterion setup) :
    setup.minimumAngularSeparationRad = (61 / 375000 : ℝ) ∧
      IsUniqueMatchingAngularSeparation setup .C := by
  rcases h_data with ⟨h_diameter, h_radius, h_wavelength⟩
  have readout_centimeters_eq (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have h_units := length.2
      ({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices)
      ({ UnitChoices.SI with length := LengthUnit.centimeters } : UnitChoices)
    have h_units_real := congrArg
      (fun reading : WithDim L𝓭 NNReal => (reading.val : ℝ)) h_units
    norm_num [lengthInCentimeters, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.centimeters, LengthUnit.meters, LengthUnit.scale,
      LengthUnit.div_eq_val] at h_units_real ⊢
    exact h_units_real
  have h_diameter_cm :
      lengthInCentimeters setup.dishDiameter = 30000 := by
    rw [readout_centimeters_eq, h_diameter]
    norm_num
  have h_limit :
      setup.minimumAngularSeparationRad =
        (61 / 50 : ℝ) *
          lengthInCentimeters setup.shortestOperatingWavelength /
            lengthInCentimeters setup.dishDiameter := by
    simpa [lengthInCentimeters] using
      h_rayleigh.angularResolutionLaw LengthUnit.centimeters
  rw [h_wavelength, h_diameter_cm] at h_limit
  norm_num at h_limit
  refine ⟨h_limit, ?_⟩
  constructor
  · norm_num [MatchesDisplayedAngularSeparation,
      displayedAngularSeparationRad, displayedPrecisionRad, h_limit, abs_of_nonneg]
  · intro other h_other
    cases other with
    | A =>
        norm_num [MatchesDisplayedAngularSeparation,
          displayedAngularSeparationRad, displayedPrecisionRad, h_limit,
          abs_of_nonneg, abs_of_nonpos] at h_other
    | B =>
        norm_num [MatchesDisplayedAngularSeparation,
          displayedAngularSeparationRad, displayedPrecisionRad, h_limit,
          abs_of_nonneg, abs_of_nonpos] at h_other
    | C => rfl
    | D =>
        norm_num [MatchesDisplayedAngularSeparation,
          displayedAngularSeparationRad, displayedPrecisionRad, h_limit,
          abs_of_nonneg, abs_of_nonpos] at h_other

end PhyXMiniProblems.ProblemPhyXMini0132
