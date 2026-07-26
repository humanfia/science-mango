import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.SpaceAndTime.Space.Basic
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0117

open Dimension

/-!
# Destructive interference from two in-phase radio antennas

The primary figure places antennas `A` and `B` on a vertical line, with `A`
200 metres above `B`.  The receiver moves from `B` along the horizontal ray
`BC`, perpendicular to `AB`.  Both antennas emit in phase at `5.80 MHz`.

Lengths, frequency, and propagation speed are Physlib dimensionful
quantities.  The coordinates of `Space 2` are explicitly metre readouts.
Destructive interference is kept as an observable predicate and is related to
the ray-path difference only by the general odd-half-wavelength law below.
-/

/-- A physical quantity carrying the dimension of length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical frequency, carrying the inverse-time dimension. -/
abbrev FrequencyQuantity : Type := Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- A physical propagation speed. -/
abbrev SpeedQuantity : Type := Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- The scalar readout of a physical length in metres. -/
def metersValue (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- The scalar readout of a physical frequency in hertz. -/
def hertzValue (frequency : FrequencyQuantity) : ℝ :=
  (frequency UnitChoices.SI).val

/-- The scalar readout of a physical frequency in megahertz. -/
def megahertzValue (frequency : FrequencyQuantity) : ℝ :=
  (frequency
    ({ UnitChoices.SI with time := TimeUnit.microseconds } : UnitChoices)).val

/-- The scalar readout of a physical speed in metres per second. -/
def metersPerSecondValue (speed : SpeedQuantity) : ℝ :=
  (speed UnitChoices.SI).val

/-- The three point labels printed in the primary figure. -/
inductive FigurePoint where
  | A
  | B
  | C
  deriving DecidableEq, Repr

/-- The two radiating antennas. -/
inductive AntennaLabel where
  | A
  | B
  deriving DecidableEq, Repr

/-- The figure point occupied by each antenna. -/
def AntennaLabel.figurePoint : AntennaLabel → FigurePoint
  | .A => .A
  | .B => .B

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The metre readout printed beside each answer label. -/
def displayedDistanceMeters : AnswerChoice → ℝ
  | .A => 200
  | .B => 250
  | .C => 275
  | .D => 225

/-- One monochromatic radio antenna at the common reference time. -/
structure RadioAntenna where
  /-- Frequency of the emitted radio wave. -/
  frequency : FrequencyQuantity
  /-- Emission phase, regarded modulo a full turn. -/
  emissionPhase : Real.Angle

/-!
The physical apparatus and its figure-derived quantities.  The receiver
position and both ray lengths are parameterized by the physical distance
travelled from `B`.  `destructiveInterferenceAt` records the observable to be
predicted; it is not defined to make any displayed answer true.
-/
structure TwoAntennaInterferenceSetup where
  antenna : AntennaLabel → RadioAntenna
  radioFrequency : FrequencyQuantity
  wavelength : LengthQuantity
  propagationSpeed : SpeedQuantity
  antennaSeparation : LengthQuantity
  figurePosition : FigurePoint → Space 2
  receiverPositionAt : LengthQuantity → Space 2
  rayPathLength : AntennaLabel → LengthQuantity → LengthQuantity
  displayedDistance : AnswerChoice → LengthQuantity
  destructiveInterferenceAt : LengthQuantity → Prop

/-- The two antennas emit in phase and at the common stated frequency. -/
def RadiatesInPhaseAtCommonFrequency
    (setup : TwoAntennaInterferenceSetup) : Prop :=
  (setup.antenna .A).frequency = setup.radioFrequency ∧
    (setup.antenna .B).frequency = setup.radioFrequency ∧
    (setup.antenna .A).emissionPhase = (setup.antenna .B).emissionPhase

/-!
The categorical and coordinate layout read from the primary image.  The
coordinate chart is measured in metres: `B` is the origin, `A` lies on the
positive vertical axis, and `C` lies on the positive horizontal axis.  A
receiver at nonnegative physical distance `x` from `B` has coordinates
`(x, 0)`.  Thus the receiver ray `BC` is perpendicular to `AB`.
-/
def HasDepictedGeometry (setup : TwoAntennaInterferenceSetup) : Prop :=
  setup.figurePosition .B 0 = 0 ∧
    setup.figurePosition .B 1 = 0 ∧
    setup.figurePosition .A 0 = 0 ∧
    setup.figurePosition .A 1 = metersValue setup.antennaSeparation ∧
    setup.figurePosition .C 1 = 0 ∧
    0 < setup.figurePosition .C 0 ∧
    dist (setup.figurePosition .A) (setup.figurePosition .B) =
      metersValue setup.antennaSeparation ∧
    ∀ distance : LengthQuantity,
      0 ≤ metersValue distance →
        setup.receiverPositionAt distance 0 = metersValue distance ∧
        setup.receiverPositionAt distance 1 = 0

/-!
The numerical text and answer-table readouts.  The wave frequency is
`5.80 MHz`, the antenna separation is `200 m`, and radio propagation is
modeled at Physlib's dimensionful speed of light.  No interference behavior
at any displayed distance occurs in this predicate.
-/
def HasStatedReadouts (setup : TwoAntennaInterferenceSetup) : Prop :=
  metersValue setup.antennaSeparation = 200 ∧
    megahertzValue setup.radioFrequency = 5.80 ∧
    setup.propagationSpeed = DimSpeed.speedOfLight ∧
    ∀ choice : AnswerChoice,
      metersValue (setup.displayedDistance choice) =
        displayedDistanceMeters choice

/-- Positivity and nonnegativity conditions for the physical quantities. -/
def HasPhysicalParameters (setup : TwoAntennaInterferenceSetup) : Prop :=
  0 < metersValue setup.antennaSeparation ∧
    0 < hertzValue setup.radioFrequency ∧
    0 < metersValue setup.wavelength ∧
    0 < metersPerSecondValue setup.propagationSpeed ∧
    (∀ choice : AnswerChoice,
      0 ≤ metersValue (setup.displayedDistance choice)) ∧
    ∀ (antenna : AntennaLabel) (distance : LengthQuantity),
      0 ≤ metersValue distance →
        0 ≤ metersValue (setup.rayPathLength antenna distance)

/-- The absolute geometric ray-path difference, read in metres. -/
def pathDifferenceMeters
    (setup : TwoAntennaInterferenceSetup)
    (distance : LengthQuantity) : ℝ :=
  |metersValue (setup.rayPathLength .A distance) -
    metersValue (setup.rayPathLength .B distance)|

/-!
The governing physical laws, stated without any answer-choice value:

* the vacuum dispersion relation is `c = f * wavelength` in SI readouts;
* each ray length is the Euclidean source-to-receiver distance;
* for in-phase sources, a nonnegative receiver distance is destructive iff
  its path difference is an odd multiple of one half-wavelength.

The last clause is uniform over every nonnegative physical distance and does
not assert that any of the four displayed candidates is destructive.
-/
def SatisfiesFreeSpaceTwoSourceLaws
    (setup : TwoAntennaInterferenceSetup) : Prop :=
  metersPerSecondValue setup.propagationSpeed =
      hertzValue setup.radioFrequency * metersValue setup.wavelength ∧
    (∀ (antenna : AntennaLabel) (distance : LengthQuantity),
      0 ≤ metersValue distance →
        metersValue (setup.rayPathLength antenna distance) =
          dist (setup.figurePosition antenna.figurePoint)
            (setup.receiverPositionAt distance)) ∧
    (RadiatesInPhaseAtCommonFrequency setup →
      ∀ distance : LengthQuantity,
        0 ≤ metersValue distance →
          (setup.destructiveInterferenceAt distance ↔
            ∃ order : ℕ,
              2 * pathDifferenceMeters setup distance =
                (2 * (order : ℝ) + 1) * metersValue setup.wavelength))

/-!
The vacuum dispersion law determines the wavelength from the stated
frequency.  This is a derived physical intermediate, not the requested
receiver distance.
-/
lemma wavelength_meters_eq_speed_div_frequency
    (setup : TwoAntennaInterferenceSetup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : SatisfiesFreeSpaceTwoSourceLaws setup) :
    metersValue setup.wavelength =
      metersPerSecondValue setup.propagationSpeed /
        hertzValue setup.radioFrequency := by
  sorry

/-!
For a receiver `x` metres from `B`, the upper path has length
`sqrt(200^2 + x^2)` while the lower path has length `x`.  The statement is
kept in terms of the physical separation so it follows from the depicted
geometry before the `200 m` readout is substituted.
-/
lemma pathDifferenceMeters_eq
    (setup : TwoAntennaInterferenceSetup)
    (distance : LengthQuantity)
    (h_distance : 0 ≤ metersValue distance)
    (h_geometry : HasDepictedGeometry setup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : SatisfiesFreeSpaceTwoSourceLaws setup) :
    pathDifferenceMeters setup distance =
      Real.sqrt
          (metersValue setup.antennaSeparation ^ 2 +
            metersValue distance ^ 2) -
        metersValue distance := by
  sorry

/-!
The dataset records answer A (`200 m`), but that exact answer is inconsistent
with the stated frequency and the free-space path-difference law.  It is kept
only as source metadata in this comment and in the answer-table readout above.

This formalizes blueprint label `thm:physics:phyx_mini_0117:target` as the
strongest source-supported symbolic answer: it characterizes every
nonnegative receiver distance at which destructive interference occurs.  The
conclusion combines the depicted right-triangle geometry, the vacuum
dispersion relation, and the odd-half-wavelength law; this combined relation
does not occur in any hypothesis.
-/
theorem problem_phyx_mini_0117
    (setup : TwoAntennaInterferenceSetup)
    (h_emission : RadiatesInPhaseAtCommonFrequency setup)
    (h_geometry : HasDepictedGeometry setup)
    (h_readouts : HasStatedReadouts setup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : SatisfiesFreeSpaceTwoSourceLaws setup) :
    ∀ distance : LengthQuantity,
      0 ≤ metersValue distance →
        (setup.destructiveInterferenceAt distance ↔
          ∃ order : ℕ,
            2 *
                (Real.sqrt
                    (metersValue setup.antennaSeparation ^ 2 +
                      metersValue distance ^ 2) -
                  metersValue distance) =
              (2 * (order : ℝ) + 1) *
                (metersPerSecondValue setup.propagationSpeed /
                  hertzValue setup.radioFrequency)) := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0117
