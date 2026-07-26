import Mathlib.Algebra.Order.Round
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0084

open Dimension

/-!
# Thickness at the third blue band of an oil film on water

The oil drop is treated as a thin film between air and water.  Sunlight is
incident vertically downward and the reflected light is viewed vertically
upward, so this is the normal-incidence branch of reflected thin-film
interference.

Physical lengths are represented dimensionfully.  Real numbers are used only
for dimensionless refractive indices, angles in radians, and scalar readouts in
a specified unit.  In particular, the film thickness and blue wavelength are
not replaced by bare real scalars.
-/

/-- A physical length represented coherently in every choice of units. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Read a physical length as a real scalar in a chosen length unit. -/
def lengthValueIn (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- The nanometre readout used for the wavelength and answer choices. -/
def nanometersValue (length : LengthQuantity) : ℝ :=
  lengthValueIn LengthUnit.nanometers length

/-- The optical media in top-to-bottom order in the oil-drop cross section. -/
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

/-- Medium from which the downward-travelling ray reaches an interface. -/
def FilmInterface.incidentMedium : FilmInterface → OpticalMedium
  | .airOil => .air
  | .oilWater => .oil

/-- Medium below an interface in the depicted air--oil--water stack. -/
def FilmInterface.transmittedMedium : FilmInterface → OpticalMedium
  | .airOil => .oil
  | .oilWater => .water

/-- Propagation directions singled out by the overhead-viewing geometry. -/
inductive VerticalDirection where
  | downward
  | upward
  deriving DecidableEq, Repr

/-- The broadband source and the spectral component selected for observation. -/
inductive IlluminationKind where
  | sunlight
  | other
  deriving DecidableEq, Repr

/-- Visible-color label used when identifying the interference bands. -/
inductive SpectralColor where
  | blue
  | other
  deriving DecidableEq, Repr

/--
Locations encountered while moving inward from one rim of the oil drop.
The rim itself has zero film thickness; the next three constructors name the
successive blue reflected-light bands asked for in the problem.
-/
inductive BandLocation where
  | rim
  | firstBlueBand
  | secondBlueBand
  | thirdBlueBand
  deriving DecidableEq, Repr

/--
The dimensionful quantities, material data, and labeled geometry of the oil
film observation.

`reflectionPhaseHalfTurns` records the phase change of a ray reflected at an
interface in integral multiples of `π`.  `roundTripOpticalPath` is the optical
path difference accumulated by the ray which traverses the oil twice.
-/
structure OilDropThinFilmSetup where
  refractiveIndex : OpticalMedium → ℝ
  blueVacuumWavelength : LengthQuantity
  filmThicknessAt : BandLocation → LengthQuantity
  inwardDistanceFromRim : BandLocation → LengthQuantity
  interferenceOrderAt : BandLocation → ℕ
  roundTripOpticalPath : BandLocation → LengthQuantity
  reflectionPhaseHalfTurns : FilmInterface → ℤ
  illuminationKind : IlluminationKind
  observedColor : SpectralColor
  illuminationDirection : VerticalDirection
  viewingDirection : VerticalDirection
  incidenceAngleFromNormalRadians : ℝ
  viewingAngleFromNormalRadians : ℝ

/--
Numerical and directional data stated in the problem.  Refractive indices are
dimensionless, and `475` is explicitly a nanometre readout.  The air value is
the standard idealization implicit in illumination through ambient air.

No film-thickness value occurs in these readouts.
-/
structure HasProblemReadouts (setup : OilDropThinFilmSetup) : Prop where
  air_refractive_index : setup.refractiveIndex .air = 1
  oil_refractive_index : setup.refractiveIndex .oil = 1.20
  water_refractive_index : setup.refractiveIndex .water = 1.33
  blue_wavelength_nanometers : nanometersValue setup.blueVacuumWavelength = 475
  source_is_sunlight : setup.illuminationKind = .sunlight
  selected_color_is_blue : setup.observedColor = .blue
  illumination_is_downward : setup.illuminationDirection = .downward
  viewing_is_upward : setup.viewingDirection = .upward
  normal_incidence : setup.incidenceAngleFromNormalRadians = 0
  normal_viewing : setup.viewingAngleFromNormalRadians = 0

/--
Geometric and counting information supplied by the cross-sectional figure and
the instruction to move inward from the rim to the third band.

The inequalities express the locally increasing-thickness branch on one side
of the curved drop.  Only the band orders, not their requested thicknesses,
are assigned numerical values.
-/
structure MatchesOilDropFigure (setup : OilDropThinFilmSetup) : Prop where
  rim_inward_distance : nanometersValue (setup.inwardDistanceFromRim .rim) = 0
  inward_order_first :
    nanometersValue (setup.inwardDistanceFromRim .rim) <
      nanometersValue (setup.inwardDistanceFromRim .firstBlueBand)
  inward_order_second :
    nanometersValue (setup.inwardDistanceFromRim .firstBlueBand) <
      nanometersValue (setup.inwardDistanceFromRim .secondBlueBand)
  inward_order_third :
    nanometersValue (setup.inwardDistanceFromRim .secondBlueBand) <
      nanometersValue (setup.inwardDistanceFromRim .thirdBlueBand)
  rim_has_zero_thickness : nanometersValue (setup.filmThicknessAt .rim) = 0
  thickness_increases_to_first :
    nanometersValue (setup.filmThicknessAt .rim) <
      nanometersValue (setup.filmThicknessAt .firstBlueBand)
  thickness_increases_to_second :
    nanometersValue (setup.filmThicknessAt .firstBlueBand) <
      nanometersValue (setup.filmThicknessAt .secondBlueBand)
  thickness_increases_to_third :
    nanometersValue (setup.filmThicknessAt .secondBlueBand) <
      nanometersValue (setup.filmThicknessAt .thirdBlueBand)
  rim_order : setup.interferenceOrderAt .rim = 0
  first_blue_order : setup.interferenceOrderAt .firstBlueBand = 1
  second_blue_order : setup.interferenceOrderAt .secondBlueBand = 2
  third_blue_order : setup.interferenceOrderAt .thirdBlueBand = 3

/-- Positivity conditions for the idealized physical branch of the setup. -/
structure HasPhysicalOpticalParameters (setup : OilDropThinFilmSetup) : Prop where
  refractive_indices_positive : ∀ medium, 0 < setup.refractiveIndex medium
  wavelength_positive :
    ∀ units : UnitChoices, 0 < (setup.blueVacuumWavelength units).val
  thickness_nonnegative :
    ∀ (units : UnitChoices) (location : BandLocation),
      0 ≤ (setup.filmThicknessAt location units).val

/--
The governing laws of normal-incidence reflected thin-film interference.

At a boundary where the transmitted medium has larger refractive index, the
reflected ray acquires one half-turn (`π`) of phase.  The round-trip optical
path in the oil is `2 n_oil t`.  Constructive reflection requires the total
relative phase, including the difference of the two interface phase shifts,
to be an integral number of turns.  The denominator-free last equation says

`2 * opticalPath + (lowerHalfTurns - upperHalfTurns) * wavelength
    = 2 * order * wavelength`.

These are general physical relations in every unit choice.  They contain no
numerical value for the requested third-band thickness or answer choice.
-/
structure SatisfiesReflectedThinFilmInterference
    (setup : OilDropThinFilmSetup) : Prop where
  reflection_phase_reversal_law :
    ∀ interface : FilmInterface,
      setup.reflectionPhaseHalfTurns interface =
        if setup.refractiveIndex interface.incidentMedium <
            setup.refractiveIndex interface.transmittedMedium then
          1
        else
          0
  round_trip_optical_path_law :
    ∀ (units : UnitChoices) (location : BandLocation),
      (setup.roundTripOpticalPath location units).val =
        2 * setup.refractiveIndex .oil *
          (setup.filmThicknessAt location units).val
  constructive_reflection_law :
    ∀ (units : UnitChoices) (location : BandLocation),
      2 * (setup.roundTripOpticalPath location units).val +
          ((setup.reflectionPhaseHalfTurns .oilWater -
              setup.reflectionPhaseHalfTurns .airOil : ℤ) : ℝ) *
            (setup.blueVacuumWavelength units).val =
        2 * (setup.interferenceOrderAt location : ℝ) *
          (setup.blueVacuumWavelength units).val

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The whole-nanometre thickness printed beside each answer choice. -/
def answerThicknessNanometers : AnswerChoice → ℤ
  | .A => 356
  | .B => 712
  | .C => 594
  | .D => 475

/-- Agreement with a displayed answer after rounding to the nearest nanometre. -/
def MatchesAnswerToNearestNanometer
    (thickness : LengthQuantity) (choice : AnswerChoice) : Prop :=
  round (nanometersValue thickness) = answerThicknessNanometers choice

/-- The answer label recorded in the supplied dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/--
Both reflected rays acquire one half-turn at their respective interfaces, so
there is no relative interface phase reversal.
-/
lemma reflectedInterfacePhaseDifference_eq_zero
    (setup : OilDropThinFilmSetup)
    (_data : HasProblemReadouts setup)
    (_laws : SatisfiesReflectedThinFilmInterference setup) :
    setup.reflectionPhaseHalfTurns .oilWater -
        setup.reflectionPhaseHalfTurns .airOil = 0 := by
  rw [_laws.reflection_phase_reversal_law .oilWater,
    _laws.reflection_phase_reversal_law .airOil]
  norm_num [FilmInterface.incidentMedium, FilmInterface.transmittedMedium,
    _data.air_refractive_index, _data.oil_refractive_index,
    _data.water_refractive_index]

/--
For interference order three, the normal-incidence law gives
`t = 3 * 475 / (2 * 1.20) = 2375/4 nm`.
-/
lemma thirdBlueBandThickness_exact
    (setup : OilDropThinFilmSetup)
    (_data : HasProblemReadouts setup)
    (_figure : MatchesOilDropFigure setup)
    (_physical : HasPhysicalOpticalParameters setup)
    (_laws : SatisfiesReflectedThinFilmInterference setup) :
    nanometersValue (setup.filmThicknessAt .thirdBlueBand) = 2375 / 4 := by
  let nmUnits : UnitChoices :=
    { UnitChoices.SI with length := LengthUnit.nanometers }
  change (setup.filmThicknessAt .thirdBlueBand nmUnits).val = 2375 / 4
  have hphase := reflectedInterfacePhaseDifference_eq_zero setup _data _laws
  have hpath :=
    _laws.round_trip_optical_path_law nmUnits .thirdBlueBand
  have hinterference :=
    _laws.constructive_reflection_law nmUnits .thirdBlueBand
  have hwavelength : (setup.blueVacuumWavelength nmUnits).val = 475 := by
    exact _data.blue_wavelength_nanometers
  rw [hphase, hwavelength, _figure.third_blue_order] at hinterference
  rw [_data.oil_refractive_index] at hpath
  norm_num at hpath hinterference ⊢
  linarith [hpath, hinterference]

/--
The third blue band has exact thickness `593.75 nm`, which rounds to the
displayed `594 nm` and hence is recorded answer choice C.

This formalizes `thm:physics:phyx_mini_0084:target`.
-/
theorem problem_phyx_mini_0084
    (setup : OilDropThinFilmSetup)
    (_data : HasProblemReadouts setup)
    (_figure : MatchesOilDropFigure setup)
    (_physical : HasPhysicalOpticalParameters setup)
    (_laws : SatisfiesReflectedThinFilmInterference setup) :
    nanometersValue (setup.filmThicknessAt .thirdBlueBand) = 2375 / 4 ∧
      MatchesAnswerToNearestNanometer
        (setup.filmThicknessAt .thirdBlueBand) .C := by
  constructor
  · exact thirdBlueBandThickness_exact setup _data _figure _physical _laws
  · unfold MatchesAnswerToNearestNanometer answerThicknessNanometers
    rw [thirdBlueBandThickness_exact setup _data _figure _physical _laws]
    norm_num

end PhyXMiniProblems.ProblemPhyXMini0084
