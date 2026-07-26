import Mathlib.Data.Real.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0151

open Dimension

/-!
# Thickness at point B of an oil film on water

The supplied cross section shows a varying oil film between air and water.
White light is incident from above.  Moving from point `A` toward point `B`,
the reflected appearance is dark, then blue--yellow--red, then blue--yellow;
`B` is aligned with the second yellow band.

Lengths are genuine dimensionful Physlib quantities.  Real numbers below are
used only for dimensionless refractive indices, angles, and scalar readouts in
a named length unit.
-/

/-- A physical length represented coherently in every choice of units. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Read a physical length as a scalar in the selected length unit. -/
def lengthValueIn (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- The nanometre readout used for the stated wavelength and answer choices. -/
def nanometersValue (length : LengthQuantity) : ℝ :=
  lengthValueIn LengthUnit.nanometers length

/-- Optical media in top-to-bottom order in the supplied cross section. -/
inductive OpticalMedium where
  | air
  | oil
  | water
  deriving DecidableEq, Repr

/-- The two interfaces which produce the reflected rays that interfere. -/
inductive FilmInterface where
  | airOil
  | oilWater
  deriving DecidableEq, Repr

/-- The medium from which the incident ray reaches each interface. -/
def FilmInterface.incidentMedium : FilmInterface → OpticalMedium
  | .airOil => .air
  | .oilWater => .oil

/-- The medium on the transmitted side of each interface. -/
def FilmInterface.transmittedMedium : FilmInterface → OpticalMedium
  | .airOil => .oil
  | .oilWater => .water

/-- Named locations encountered from the dark region near `A` to point `B`. -/
inductive FilmLocation where
  | pointA
  | firstBlueBand
  | firstYellowBand
  | firstRedBand
  | secondBlueBand
  | pointB
  deriving DecidableEq, Repr

/-- Qualitative reflected-light labels printed in the figure. -/
inductive ReflectedAppearance where
  | dark
  | blue
  | yellow
  | red
  deriving DecidableEq, Repr

/-- The broadband illumination specified by the problem. -/
inductive IlluminationKind where
  | whiteLight
  deriving DecidableEq, Repr

/-- Vertical directions singled out by illumination and observation from above. -/
inductive VerticalDirection where
  | downward
  | upward
  deriving DecidableEq, Repr

/-!
The physical quantities, optical data, and figure-labelled observations.

`reflectionPhaseHalfTurns` records an interface reflection phase in integral
multiples of `π`.  `roundTripOpticalPathAt` is the optical path accumulated by
the ray which traverses the oil inward and outward.  The predicate
`constructiveReflectionAt location wavelength order` records that the named
location is a constructive reflected band of that incident wavelength and
order.  None of these fields fixes the requested thickness at `B`.
-/
structure OilFilmSetup where
  refractiveIndex : OpticalMedium → ℝ
  yellowWavelengthInAir : LengthQuantity
  filmThicknessAt : FilmLocation → LengthQuantity
  distanceFromA : FilmLocation → LengthQuantity
  reflectedAppearanceAt : FilmLocation → ReflectedAppearance
  constructiveReflectionAt : FilmLocation → LengthQuantity → ℕ → Prop
  roundTripOpticalPathAt : FilmLocation → LengthQuantity
  reflectionPhaseHalfTurns : FilmInterface → ℤ
  illuminationKind : IlluminationKind
  illuminationDirection : VerticalDirection
  viewingDirection : VerticalDirection
  incidenceAngleFromNormalRadians : ℝ
  viewingAngleFromNormalRadians : ℝ

/-!
Numerical and directional data stated or implicit in the normal-incidence
problem setup.  Refractive indices are dimensionless, while `580` is a
nanometre readout of the yellow wavelength in air.  No thickness readout
occurs here.
-/
structure HasProblemReadouts (setup : OilFilmSetup) : Prop where
  air_refractive_index : setup.refractiveIndex .air = 1
  oil_refractive_index : setup.refractiveIndex .oil = (3 : ℝ) / 2
  water_refractive_index : setup.refractiveIndex .water = (133 : ℝ) / 100
  yellow_wavelength_in_air_nanometers :
    nanometersValue setup.yellowWavelengthInAir = 580
  source_is_white_light : setup.illuminationKind = .whiteLight
  illumination_is_downward : setup.illuminationDirection = .downward
  viewing_is_upward : setup.viewingDirection = .upward
  normal_incidence : setup.incidenceAngleFromNormalRadians = 0
  normal_viewing : setup.viewingAngleFromNormalRadians = 0

/-!
Data read from the supplied figure.  The inequalities retain the increasing
position and thickness branch of the curved oil surface.  On that branch the
pictured first and second yellow bands are interpreted as the first two
constructive yellow fringes, of orders zero and one.  This ordinal fringe
identification does not assign any numerical value to the thickness at `B`.
-/
structure MatchesOilFilmFigure (setup : OilFilmSetup) : Prop where
  pointA_distance_is_zero :
    nanometersValue (setup.distanceFromA .pointA) = 0
  pointA_is_dark : setup.reflectedAppearanceAt .pointA = .dark
  first_band_is_blue : setup.reflectedAppearanceAt .firstBlueBand = .blue
  first_yellow_band_is_yellow :
    setup.reflectedAppearanceAt .firstYellowBand = .yellow
  first_red_band_is_red : setup.reflectedAppearanceAt .firstRedBand = .red
  second_blue_band_is_blue : setup.reflectedAppearanceAt .secondBlueBand = .blue
  pointB_is_second_yellow_band : setup.reflectedAppearanceAt .pointB = .yellow
  first_yellow_is_order_zero :
    setup.constructiveReflectionAt
      .firstYellowBand setup.yellowWavelengthInAir 0
  pointB_yellow_is_order_one :
    setup.constructiveReflectionAt .pointB setup.yellowWavelengthInAir 1
  pointA_precedes_first_blue :
    nanometersValue (setup.distanceFromA .pointA) <
      nanometersValue (setup.distanceFromA .firstBlueBand)
  first_blue_precedes_first_yellow :
    nanometersValue (setup.distanceFromA .firstBlueBand) <
      nanometersValue (setup.distanceFromA .firstYellowBand)
  first_yellow_precedes_first_red :
    nanometersValue (setup.distanceFromA .firstYellowBand) <
      nanometersValue (setup.distanceFromA .firstRedBand)
  first_red_precedes_second_blue :
    nanometersValue (setup.distanceFromA .firstRedBand) <
      nanometersValue (setup.distanceFromA .secondBlueBand)
  second_blue_precedes_pointB :
    nanometersValue (setup.distanceFromA .secondBlueBand) <
      nanometersValue (setup.distanceFromA .pointB)
  thickness_increases_A_to_first_blue :
    nanometersValue (setup.filmThicknessAt .pointA) <
      nanometersValue (setup.filmThicknessAt .firstBlueBand)
  thickness_increases_first_blue_to_first_yellow :
    nanometersValue (setup.filmThicknessAt .firstBlueBand) <
      nanometersValue (setup.filmThicknessAt .firstYellowBand)
  thickness_increases_first_yellow_to_first_red :
    nanometersValue (setup.filmThicknessAt .firstYellowBand) <
      nanometersValue (setup.filmThicknessAt .firstRedBand)
  thickness_increases_first_red_to_second_blue :
    nanometersValue (setup.filmThicknessAt .firstRedBand) <
      nanometersValue (setup.filmThicknessAt .secondBlueBand)
  thickness_increases_second_blue_to_B :
    nanometersValue (setup.filmThicknessAt .secondBlueBand) <
      nanometersValue (setup.filmThicknessAt .pointB)

/-- Positivity conditions selecting the physical branch of the model. -/
structure HasPhysicalOpticalParameters (setup : OilFilmSetup) : Prop where
  refractive_indices_positive : ∀ medium, 0 < setup.refractiveIndex medium
  wavelength_positive :
    ∀ units : UnitChoices, 0 < (setup.yellowWavelengthInAir units).val
  thickness_nonnegative :
    ∀ (units : UnitChoices) (location : FilmLocation),
      0 ≤ (setup.filmThicknessAt location units).val

/-!
Governing laws for normal-incidence reflected thin-film interference.

Reflection toward a larger refractive index contributes one half-turn (`π`).
The round-trip optical path at a location is `2 n_o t`.  In half-turn units,
constructive reflected order `m` obeys

`2 * opticalPath + (lowerPhase - upperPhase) * wavelength
    = 2 * m * wavelength`.

For the air--oil--water indices here, only the upper reflection reverses phase,
so this general law yields `4 n_o t = (2m+1) λ`.  The law contains neither the
requested numerical thickness nor an answer-choice label.
-/
structure SatisfiesReflectedThinFilmInterference
    (setup : OilFilmSetup) : Prop where
  reflection_phase_reversal_law :
    ∀ interface : FilmInterface,
      setup.reflectionPhaseHalfTurns interface =
        if setup.refractiveIndex interface.incidentMedium <
            setup.refractiveIndex interface.transmittedMedium then
          1
        else
          0
  round_trip_optical_path_law :
    ∀ (units : UnitChoices) (location : FilmLocation),
      (setup.roundTripOpticalPathAt location units).val =
        2 * setup.refractiveIndex .oil *
          (setup.filmThicknessAt location units).val
  constructive_reflection_law :
    ∀ (units : UnitChoices) (location : FilmLocation)
        (wavelength : LengthQuantity) (order : ℕ),
      setup.constructiveReflectionAt location wavelength order →
        2 * (setup.roundTripOpticalPathAt location units).val +
            ((setup.reflectionPhaseHalfTurns .oilWater -
                setup.reflectionPhaseHalfTurns .airOil : ℤ) : ℝ) *
              (wavelength units).val =
          2 * (order : ℝ) * (wavelength units).val

/-- Labels of the four thickness choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Thickness in nanometres displayed beside each answer label. -/
def displayedThicknessNanometers : AnswerChoice → ℝ
  | .A => 270
  | .B => 280
  | .C => 290
  | .D => 300

/-- A displayed choice agrees with the derived nanometre thickness at `B`. -/
def MatchesDisplayedThickness
    (setup : OilFilmSetup) (choice : AnswerChoice) : Prop :=
  nanometersValue (setup.filmThicknessAt .pointB) =
    displayedThicknessNanometers choice

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/--
The index ordering makes the air--oil reflection acquire a half-turn while the
oil--water reflection does not, so the lower-minus-upper phase contribution is
`-1` half-turn.
-/
lemma reflectedInterfacePhaseDifference_eq_neg_one
    (setup : OilFilmSetup)
    (_data : HasProblemReadouts setup)
    (_laws : SatisfiesReflectedThinFilmInterference setup) :
    setup.reflectionPhaseHalfTurns .oilWater -
        setup.reflectionPhaseHalfTurns .airOil = -1 := by
  rw [_laws.reflection_phase_reversal_law,
    _laws.reflection_phase_reversal_law]
  norm_num [FilmInterface.incidentMedium, FilmInterface.transmittedMedium,
    _data.air_refractive_index, _data.oil_refractive_index,
    _data.water_refractive_index]

/--
At point `B`, the figure selects the second yellow band, constructive order
`m = 1`.  Thus `4 n_o t_B = 3 λ_yellow`.
-/
lemma pointB_secondYellow_constructive_condition
    (setup : OilFilmSetup)
    (_data : HasProblemReadouts setup)
    (_figure : MatchesOilFilmFigure setup)
    (_laws : SatisfiesReflectedThinFilmInterference setup) :
    4 * setup.refractiveIndex .oil *
        nanometersValue (setup.filmThicknessAt .pointB) =
      3 * nanometersValue setup.yellowWavelengthInAir := by
  have hPhase :
      setup.reflectionPhaseHalfTurns .oilWater -
          setup.reflectionPhaseHalfTurns .airOil = -1 :=
    reflectedInterfacePhaseDifference_eq_neg_one setup _data _laws
  have hPath := _laws.round_trip_optical_path_law
    ({ UnitChoices.SI with length := LengthUnit.nanometers } : UnitChoices)
    FilmLocation.pointB
  have hConstructive := _laws.constructive_reflection_law
    ({ UnitChoices.SI with length := LengthUnit.nanometers } : UnitChoices)
    FilmLocation.pointB setup.yellowWavelengthInAir 1
    _figure.pointB_yellow_is_order_one
  rw [hPath, hPhase] at hConstructive
  change
    4 * setup.refractiveIndex .oil *
        (setup.filmThicknessAt .pointB
          ({ UnitChoices.SI with length := LengthUnit.nanometers } :
            UnitChoices)).val =
      3 * (setup.yellowWavelengthInAir
        ({ UnitChoices.SI with length := LengthUnit.nanometers } :
          UnitChoices)).val
  norm_num at hConstructive ⊢
  linarith

/--
The second yellow band has
`t_B = 3 * 580 nm / (4 * 1.50) = 290 nm`, which is answer choice C.

This formalizes `thm:physics:phyx_mini_0151:target`.
-/
theorem oilThicknessAtPointB_eq_290nm
    (setup : OilFilmSetup)
    (_data : HasProblemReadouts setup)
    (_figure : MatchesOilFilmFigure setup)
    (_physical : HasPhysicalOpticalParameters setup)
    (_laws : SatisfiesReflectedThinFilmInterference setup) :
    nanometersValue (setup.filmThicknessAt .pointB) = 290 ∧
      MatchesDisplayedThickness setup recordedDatasetAnswer := by
  have hCondition :=
    pointB_secondYellow_constructive_condition setup _data _figure _laws
  rw [_data.oil_refractive_index,
    _data.yellow_wavelength_in_air_nanometers] at hCondition
  have hThickness :
      nanometersValue (setup.filmThicknessAt .pointB) = 290 := by
    norm_num at hCondition ⊢
    linarith
  refine ⟨hThickness, ?_⟩
  simpa [MatchesDisplayedThickness, recordedDatasetAnswer,
    displayedThicknessNanometers] using hThickness

end PhyXMiniProblems.ProblemPhyXMini0151
