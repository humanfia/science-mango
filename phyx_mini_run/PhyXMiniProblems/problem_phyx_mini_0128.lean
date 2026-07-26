import Mathlib.Algebra.Order.Round
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0128

open Dimension

/-!
# Quarter-wave magnesium-fluoride antireflection coating

The source figure shows light incident from air on a magnesium-fluoride
coating deposited on glass.  Reflected ray 1 comes from the air--coating
interface, reflected ray 2 comes from the coating--glass interface after a
round trip through the film, and the transmitted ray continues into the
glass.

Wavelength and coating thickness are genuine dimensionful Physlib lengths.
Real numbers below are used only for dimensionless refractive indices, angles
in radians, normalized amplitude magnitudes, and scalar readouts in a named
length unit.
-/

/-- A physical length represented coherently in every choice of units. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Read a physical length as a scalar in the selected length unit. -/
def lengthValueIn (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- The nanometre readout used for the design wavelength and answer choices. -/
def nanometersValue (length : LengthQuantity) : ℝ :=
  lengthValueIn LengthUnit.nanometers length

/-- Optical media in their top-to-bottom order in the coating stack. -/
inductive OpticalMedium where
  | air
  | magnesiumFluorideCoating
  | glass
  deriving DecidableEq, Repr

/-- The two boundaries at which the displayed reflected rays originate. -/
inductive FilmInterface where
  | airCoating
  | coatingGlass
  deriving DecidableEq, Repr

/-- The medium from which light reaches each interface. -/
def FilmInterface.incidentMedium : FilmInterface → OpticalMedium
  | .airCoating => .air
  | .coatingGlass => .magnesiumFluorideCoating

/-- The medium on the transmitted side of each interface. -/
def FilmInterface.transmittedMedium : FilmInterface → OpticalMedium
  | .airCoating => .magnesiumFluorideCoating
  | .coatingGlass => .glass

/-- Labels `1` and `2` printed beside the two reflected rays in the figure. -/
inductive ReflectedRay where
  | one
  | two
  deriving DecidableEq, Repr

/-- All ray labels visible in the supplied diagram. -/
inductive FigureRay where
  | incident
  | reflectedOne
  | reflectedTwo
  | transmitted
  deriving DecidableEq, Repr

/-!
The dimensionful quantities, material data, and labeled ray geometry of the
coating design.  `reflectionPhaseHalfTurns` measures an interface reflection
phase in integral multiples of `π`.  `roundTripOpticalPath` is the optical
path accumulated by ray 2 in traversing the coating inward and outward.

`coatingThickness` is an unknown physical length: no field fixes its requested
numerical value or selects an answer choice.
-/
structure AntireflectionCoatingSetup where
  refractiveIndex : OpticalMedium → ℝ
  designWavelengthInAir : LengthQuantity
  coatingThickness : LengthQuantity
  incidenceAngleFromNormalRadians : ℝ
  figureRayMedium : FigureRay → OpticalMedium
  reflectionInterface : ReflectedRay → FilmInterface
  reflectionPhaseHalfTurns : FilmInterface → ℤ
  roundTripOpticalPath : LengthQuantity
  destructiveInterferenceOrder : ℕ
  relativeReflectedAmplitudeMagnitude : ReflectedRay → ℝ

/-!
Numerical data stated in the problem.  Refractive indices and the incidence
angle are dimensionless; `550` is explicitly a nanometre readout.  The ideal
air index is the standard approximation implicit in the scenario.

No coating-thickness value occurs in these readouts.
-/
structure HasProblemReadouts (setup : AntireflectionCoatingSetup) : Prop where
  air_refractive_index : setup.refractiveIndex .air = 1
  magnesium_fluoride_refractive_index :
    setup.refractiveIndex .magnesiumFluorideCoating = (69 : ℝ) / 50
  glass_refractive_index : setup.refractiveIndex .glass = (3 : ℝ) / 2
  wavelength_in_air_nanometers :
    nanometersValue setup.designWavelengthInAir = 550
  normal_incidence : setup.incidenceAngleFromNormalRadians = 0

/-!
Ray and medium labels read from the supplied air--coating--glass diagram.
Ray 1 is the surface-reflected ray and ray 2 is the ray reflected from the
coating--glass boundary; both emerge into air.  The transmitted ray continues
into glass.
-/
structure MatchesCoatingFigure (setup : AntireflectionCoatingSetup) : Prop where
  incident_ray_in_air : setup.figureRayMedium .incident = .air
  transmitted_ray_in_glass : setup.figureRayMedium .transmitted = .glass
  reflected_ray_one_in_air : setup.figureRayMedium .reflectedOne = .air
  reflected_ray_two_in_air : setup.figureRayMedium .reflectedTwo = .air
  ray_one_reflects_at_air_coating :
    setup.reflectionInterface .one = .airCoating
  ray_two_reflects_at_coating_glass :
    setup.reflectionInterface .two = .coatingGlass

/-- Positivity conditions for the physical branch of the coating model. -/
structure HasPhysicalOpticalParameters
    (setup : AntireflectionCoatingSetup) : Prop where
  refractive_indices_positive : ∀ medium, 0 < setup.refractiveIndex medium
  wavelength_positive :
    ∀ units : UnitChoices, 0 < (setup.designWavelengthInAir units).val
  coating_thickness_positive :
    ∀ units : UnitChoices, 0 < (setup.coatingThickness units).val
  reflected_amplitudes_positive :
    ∀ ray, 0 < setup.relativeReflectedAmplitudeMagnitude ray

/-!
The conventional thinnest antireflection design uses the first destructive
order.  This fixes an interference-order label, not the requested thickness.
-/
def UsesThinnestAntireflectionOrder
    (setup : AntireflectionCoatingSetup) : Prop :=
  setup.destructiveInterferenceOrder = 0

/-!
Governing laws for normal-incidence reflected thin-film interference.

Reflection from a lower-index to a higher-index medium contributes one
half-turn (`π`).  Ray 2 accumulates round-trip optical path `2 n t` in the
film.  In half-turn units, destructive interference of order `m` is

`2 * opticalPath + (lowerPhase - upperPhase) * wavelength
    = (2 * m + 1) * wavelength`.

The final field records the equal normalized reflected-amplitude condition
needed for complete cancellation.  These are general physical relations and
contain neither the requested numerical thickness nor an answer label.
-/
structure SatisfiesAntireflectionThinFilmLaws
    (setup : AntireflectionCoatingSetup) : Prop where
  reflection_phase_reversal_law :
    ∀ interface : FilmInterface,
      setup.reflectionPhaseHalfTurns interface =
        if setup.refractiveIndex interface.incidentMedium <
            setup.refractiveIndex interface.transmittedMedium then
          1
        else
          0
  round_trip_optical_path_law :
    ∀ units : UnitChoices,
      (setup.roundTripOpticalPath units).val =
        2 * setup.refractiveIndex .magnesiumFluorideCoating *
          (setup.coatingThickness units).val
  destructive_reflection_law :
    ∀ units : UnitChoices,
      2 * (setup.roundTripOpticalPath units).val +
          ((setup.reflectionPhaseHalfTurns .coatingGlass -
              setup.reflectionPhaseHalfTurns .airCoating : ℤ) : ℝ) *
            (setup.designWavelengthInAir units).val =
        (2 * (setup.destructiveInterferenceOrder : ℝ) + 1) *
          (setup.designWavelengthInAir units).val
  equal_reflected_amplitude_magnitudes :
    setup.relativeReflectedAmplitudeMagnitude .one =
      setup.relativeReflectedAmplitudeMagnitude .two

/-- Labels of the four thickness choices printed in the dataset item. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Thickness in nanometres displayed beside each answer label. -/
def displayedThicknessNanometers : AnswerChoice → ℝ
  | .A => 77.8
  | .B => 88.9
  | .C => 99.6
  | .D => 66.7

/-- Agreement with a displayed answer after rounding to `0.1 nm`. -/
def MatchesAnswerToNearestTenthNanometer
    (thickness : LengthQuantity) (choice : AnswerChoice) : Prop :=
  round (10 * nanometersValue thickness) =
    round (10 * displayedThicknessNanometers choice)

/-- The answer label recorded in the supplied dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/--
Both reflected rays undergo a half-turn phase reversal because each reflection
is from a lower-index medium toward a higher-index medium.  Their interface
phase contributions therefore have zero relative difference.
-/
lemma reflectedInterfacePhaseDifference_eq_zero
    (setup : AntireflectionCoatingSetup)
    (_data : HasProblemReadouts setup)
    (_laws : SatisfiesAntireflectionThinFilmLaws setup) :
    setup.reflectionPhaseHalfTurns .coatingGlass -
        setup.reflectionPhaseHalfTurns .airCoating = 0 := by
  have h_air_coating :=
    _laws.reflection_phase_reversal_law FilmInterface.airCoating
  have h_coating_glass :=
    _laws.reflection_phase_reversal_law FilmInterface.coatingGlass
  simp only [FilmInterface.incidentMedium, FilmInterface.transmittedMedium,
    _data.air_refractive_index,
    _data.magnesium_fluoride_refractive_index,
    _data.glass_refractive_index] at h_air_coating h_coating_glass
  norm_num at h_air_coating h_coating_glass
  omega

/--
For the first destructive order, the phase and optical-path laws give the
quarter-wave condition `4 n t = λ`.  With `λ = 550 nm` and `n = 1.38`, the
exact coating thickness is `6875 / 69 nm`.
-/
lemma coatingThickness_exact
    (setup : AntireflectionCoatingSetup)
    (_data : HasProblemReadouts setup)
    (_physical : HasPhysicalOpticalParameters setup)
    (_order : UsesThinnestAntireflectionOrder setup)
    (_laws : SatisfiesAntireflectionThinFilmLaws setup) :
    nanometersValue setup.coatingThickness = (6875 : ℝ) / 69 := by
  let nmUnits : UnitChoices :=
    { UnitChoices.SI with length := LengthUnit.nanometers }
  have h_wavelength :
      (setup.designWavelengthInAir nmUnits).val = 550 := by
    simpa [nanometersValue, lengthValueIn, nmUnits] using
      _data.wavelength_in_air_nanometers
  have h_phase :=
    reflectedInterfacePhaseDifference_eq_zero setup _data _laws
  have h_optical := _laws.round_trip_optical_path_law nmUnits
  have h_interference := _laws.destructive_reflection_law nmUnits
  rw [_data.magnesium_fluoride_refractive_index] at h_optical
  rw [h_phase, _order, h_wavelength] at h_interference
  change (setup.coatingThickness nmUnits).val = (6875 : ℝ) / 69
  norm_num at h_optical h_interference ⊢
  linarith

/--
The exact quarter-wave thickness is approximately `99.6377 nm`, which rounds
to `99.6 nm`, displayed as answer choice C.

This formalizes `thm:physics:phyx_mini_0128:target`.
-/
theorem problem_phyx_mini_0128
    (setup : AntireflectionCoatingSetup)
    (_data : HasProblemReadouts setup)
    (_figure : MatchesCoatingFigure setup)
    (_physical : HasPhysicalOpticalParameters setup)
    (_order : UsesThinnestAntireflectionOrder setup)
    (_laws : SatisfiesAntireflectionThinFilmLaws setup) :
    nanometersValue setup.coatingThickness = (6875 : ℝ) / 69 ∧
      MatchesAnswerToNearestTenthNanometer
        setup.coatingThickness recordedDatasetAnswer := by
  have h_thickness :=
    coatingThickness_exact setup _data _physical _order _laws
  refine ⟨h_thickness, ?_⟩
  rw [MatchesAnswerToNearestTenthNanometer, h_thickness]
  norm_num [recordedDatasetAnswer, displayedThicknessNanometers, round_eq_iff]

end PhyXMiniProblems.ProblemPhyXMini0128
