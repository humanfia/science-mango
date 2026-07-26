import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Speed

/-!
# Position of a Mach 2 jet when its sonic boom reaches an observer

This file models the two panels of problem `phyx_mini_0221`. In panel `(a)`
the jet passes directly above the ground observer at altitude `9500 m`. In
panel `(b)` the jet has continued horizontally to the right, and the trailing
shock line has just reached the observer. The angle `theta` is the acute Mach
angle from the horizontal flight path to that shock line.

Lengths and speeds are unit-independent Physlib quantities. Real numbers are
used only for named-unit readouts, the dimensionless Mach number, the angle in
radians, and displayed answer values. In particular, the horizontal distance
at boom reception is an independent physical quantity constrained by the
Mach-cone and right-triangle laws; it is not defined to be the recorded answer.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0221

open Dimension

/-! ## Dimensionful quantities and unit readouts -/

/-- A nonnegative physical length, independent of the chosen unit readout. -/
abbrev AcousticLength : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : AcousticLength) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical speed in selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) (speed : DimSpeed) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Metre readout used by the altitude label and the exact displacement. -/
def lengthInMeters (length : AcousticLength) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Kilometre readout used by the four displayed answer choices. -/
def lengthInKilometers (length : AcousticLength) : ℝ :=
  lengthReadout LengthUnit.kilometers length

/-- Metres-per-second readout used to state positivity of the two speeds. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-! ## Physical objects and primary-figure labels -/

/-- The jet aircraft drawn at the vertex of the blue Mach cone. -/
inductive AircraftLabel where
  | jet
  deriving DecidableEq, Repr

/-- The person standing on the ground in both panels. -/
inductive ObserverLabel where
  | groundObserver
  deriving DecidableEq, Repr

/-- The blue trailing shock line responsible for the sonic boom. -/
inductive WavefrontLabel where
  | shockWave
  deriving DecidableEq, Repr

/-- The two explicitly labeled panels in the source figure. -/
inductive FigurePanel where
  | a
  | b
  deriving DecidableEq, Repr

/-- Physical moments depicted by the two figure panels. -/
inductive FigureMoment where
  | overheadPassage
  | boomReception
  deriving DecidableEq, Repr

/-- Orientations along the horizontal flight axis of the figure. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- Direction of the dashed sound-direction arrow in panel `(b)`. -/
inductive SoundDirection where
  | fromJetToObserver
  | fromObserverToJet
  deriving DecidableEq, Repr

/-!
Independent physical quantities and qualitative figure data. The horizontal
distance and shock-path length at boom reception are not assigned numerical
values here.
-/
structure SonicBoomSetup where
  aircraft : AircraftLabel
  observer : ObserverLabel
  shockFront : WavefrontLabel
  panelMoment : FigurePanel → FigureMoment
  flightDirection : HorizontalDirection
  soundDirectionAtReception : SoundDirection
  flightPathIsHorizontal : Bool
  /-- Ground object directly below the jet during panel `(a)`. -/
  overheadGroundObject : ObserverLabel
  altitude : AcousticLength
  soundSpeed : DimSpeed
  jetSpeed : DimSpeed
  /-- Dimensionless ratio of jet speed to sound speed. -/
  machNumber : ℝ
  /-- Figure angle `theta`, in radians, from horizontal to the shock line. -/
  machConeAngleRadians : ℝ
  /-- Horizontal distance to the right of the observer in panel `(b)`. -/
  horizontalDistanceAtBoom : AcousticLength
  /-- Slanted distance from the observer to the jet along the shock line. -/
  shockWavePathLength : AcousticLength
  /-- Whether the trailing shock front has reached the observer in a panel. -/
  shockFrontAtObserver : FigurePanel → Bool

/-!
Problem-text and primary-figure readouts. These state Mach `2`, altitude
`9500 m`, the direct overflight, the panel roles, and the drawn directions.
They do not state a horizontal distance or select an answer choice.
-/
structure MatchesProblemAndFigure (setup : SonicBoomSetup) : Prop where
  aircraft_is_jet : setup.aircraft = .jet
  observer_is_ground_observer : setup.observer = .groundObserver
  wavefront_is_shock_wave : setup.shockFront = .shockWave
  panel_a_is_overhead_passage : setup.panelMoment .a = .overheadPassage
  panel_b_is_boom_reception : setup.panelMoment .b = .boomReception
  airplane_moves_right : setup.flightDirection = .right
  sound_points_from_jet_to_observer :
    setup.soundDirectionAtReception = .fromJetToObserver
  horizontal_flight_path : setup.flightPathIsHorizontal = true
  airplane_passes_directly_over_observer :
    setup.overheadGroundObject = .groundObserver
  shock_not_yet_at_observer_in_panel_a : setup.shockFrontAtObserver .a = false
  shock_reaches_observer_in_panel_b : setup.shockFrontAtObserver .b = true
  altitude_meters : lengthInMeters setup.altitude = 9500
  mach_number : setup.machNumber = 2

/-!
Positivity, supersonic motion, and the acute physical branch of the Mach cone.
These conditions rule out degenerate geometry without fixing the requested
horizontal distance.
-/
structure HasPhysicalSonicBoomParameters (setup : SonicBoomSetup) : Prop where
  altitude_positive : 0 < lengthInMeters setup.altitude
  sound_speed_positive : 0 < speedInMetersPerSecond setup.soundSpeed
  jet_speed_positive : 0 < speedInMetersPerSecond setup.jetSpeed
  supersonic : 1 < setup.machNumber
  mach_angle_acute : setup.machConeAngleRadians ∈ Set.Ioo 0 (Real.pi / 2)
  horizontal_distance_positive :
    0 < lengthInMeters setup.horizontalDistanceAtBoom
  shock_path_positive : 0 < lengthInMeters setup.shockWavePathLength

/-!
Governing relations for steady horizontal flight and the Mach-cone triangle.

* `v_jet = M c` is the definition of Mach number.
* `sin theta = c / v_jet` is the Mach-cone law.
* `tan theta = h / x` expresses the right triangle in panel `(b)`.
* the Pythagorean relation identifies the slanted blue shock path.

The laws are unit-compatible and contain no numerical horizontal distance.
-/
structure SatisfiesMachConeGeometry (setup : SonicBoomSetup) : Prop where
  jet_speed_from_mach : ∀ lengthUnit timeUnit,
    speedReadout lengthUnit timeUnit setup.jetSpeed =
      setup.machNumber * speedReadout lengthUnit timeUnit setup.soundSpeed
  mach_cone_relation : ∀ lengthUnit timeUnit,
    Real.sin setup.machConeAngleRadians =
      speedReadout lengthUnit timeUnit setup.soundSpeed /
        speedReadout lengthUnit timeUnit setup.jetSpeed
  observer_on_shock_front_tangent : ∀ lengthUnit,
    Real.tan setup.machConeAngleRadians =
      lengthReadout lengthUnit setup.altitude /
        lengthReadout lengthUnit setup.horizontalDistanceAtBoom
  shock_path_pythagorean : ∀ lengthUnit,
    (lengthReadout lengthUnit setup.shockWavePathLength) ^ 2 =
      (lengthReadout lengthUnit setup.altitude) ^ 2 +
        (lengthReadout lengthUnit setup.horizontalDistanceAtBoom) ^ 2

/-! ## Derived displacement and displayed answers -/

/-- General conversion between the two distance readouts used here. -/
lemma lengthInKilometers_eq_lengthInMeters_div_thousand
    (distance : AcousticLength) :
    lengthInKilometers distance = lengthInMeters distance / 1000 := by
  have h := congrArg (fun x : NNReal => (x : ℝ)) <|
    congrArg WithDim.val <|
      distance.2
        ({UnitChoices.SI with length := LengthUnit.meters} : UnitChoices)
        ({UnitChoices.SI with length := LengthUnit.kilometers} : UnitChoices)
  change lengthInKilometers distance = _ * lengthInMeters distance at h
  norm_num [lengthInKilometers, lengthInMeters, lengthReadout,
    UnitChoices.dimScale, LengthUnit.kilometers, LengthUnit.meters,
    LengthUnit.scale, LengthUnit.div_eq_val, NNReal.smul_def,
    NNReal.coe_inv] at h ⊢
  convert h using 1
  change _ / 1000 = (1 / 1000 : ℝ) * _
  ring

/-!
The general horizontal displacement formula derived from the Mach-cone law
and the right triangle. It remains parameterized by the independent altitude
and Mach number, so it does not encode this problem's numerical answer.
-/
lemma horizontalDistance_formula
    (setup : SonicBoomSetup)
    (_physical : HasPhysicalSonicBoomParameters setup)
    (_laws : SatisfiesMachConeGeometry setup) :
    lengthInMeters setup.horizontalDistanceAtBoom =
      lengthInMeters setup.altitude *
        Real.sqrt (setup.machNumber ^ 2 - 1) := by
  have h_sound_pos :
      0 < speedReadout LengthUnit.meters TimeUnit.seconds setup.soundSpeed :=
    _physical.sound_speed_positive
  have h_jet_pos :
      0 < speedReadout LengthUnit.meters TimeUnit.seconds setup.jetSpeed :=
    _physical.jet_speed_positive
  have h_mach_pos : 0 < setup.machNumber := lt_trans (by norm_num) _physical.supersonic
  have h_distance_pos :
      0 < lengthInMeters setup.horizontalDistanceAtBoom :=
    _physical.horizontal_distance_positive
  have h_altitude_pos : 0 < lengthInMeters setup.altitude :=
    _physical.altitude_positive
  have h_angle := _physical.mach_angle_acute
  have h_cos_pos : 0 < Real.cos setup.machConeAngleRadians := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · exact lt_trans
        (neg_lt_zero.mpr (div_pos Real.pi_pos (by norm_num)))
        h_angle.1
    · exact h_angle.2
  have h_speed :=
    _laws.jet_speed_from_mach LengthUnit.meters TimeUnit.seconds
  have h_sin :=
    _laws.mach_cone_relation LengthUnit.meters TimeUnit.seconds
  have h_sin_mach :
      Real.sin setup.machConeAngleRadians * setup.machNumber = 1 := by
    rw [h_speed] at h_sin
    field_simp [ne_of_gt h_sound_pos, ne_of_gt h_mach_pos] at h_sin
    nlinarith
  have h_tan := _laws.observer_on_shock_front_tangent LengthUnit.meters
  change
    Real.tan setup.machConeAngleRadians =
      lengthInMeters setup.altitude /
        lengthInMeters setup.horizontalDistanceAtBoom at h_tan
  rw [Real.tan_eq_sin_div_cos] at h_tan
  have h_cross :
      Real.sin setup.machConeAngleRadians *
          lengthInMeters setup.horizontalDistanceAtBoom =
        Real.cos setup.machConeAngleRadians *
          lengthInMeters setup.altitude := by
    field_simp [ne_of_gt h_cos_pos, ne_of_gt h_distance_pos] at h_tan
    nlinarith
  have h_cross_sq :
      Real.sin setup.machConeAngleRadians ^ 2 *
          lengthInMeters setup.horizontalDistanceAtBoom ^ 2 =
        Real.cos setup.machConeAngleRadians ^ 2 *
          lengthInMeters setup.altitude ^ 2 := by
    calc
      Real.sin setup.machConeAngleRadians ^ 2 *
            lengthInMeters setup.horizontalDistanceAtBoom ^ 2 =
          (Real.sin setup.machConeAngleRadians *
            lengthInMeters setup.horizontalDistanceAtBoom) ^ 2 := by ring
      _ = (Real.cos setup.machConeAngleRadians *
            lengthInMeters setup.altitude) ^ 2 := by rw [h_cross]
      _ = Real.cos setup.machConeAngleRadians ^ 2 *
            lengthInMeters setup.altitude ^ 2 := by ring
  have h_mach_sin_sq :
      setup.machNumber ^ 2 * Real.sin setup.machConeAngleRadians ^ 2 = 1 := by
    calc
      setup.machNumber ^ 2 * Real.sin setup.machConeAngleRadians ^ 2 =
          (Real.sin setup.machConeAngleRadians * setup.machNumber) ^ 2 := by
            ring
      _ = 1 := by rw [h_sin_mach]; norm_num
  have h_trig := Real.sin_sq_add_cos_sq setup.machConeAngleRadians
  have h_cos_sq :
      setup.machNumber ^ 2 * Real.cos setup.machConeAngleRadians ^ 2 =
        setup.machNumber ^ 2 - 1 := by
    have h_cos_from_sin :
        Real.cos setup.machConeAngleRadians ^ 2 =
          1 - Real.sin setup.machConeAngleRadians ^ 2 := by
      nlinarith
    rw [h_cos_from_sin]
    calc
      setup.machNumber ^ 2 *
            (1 - Real.sin setup.machConeAngleRadians ^ 2) =
          setup.machNumber ^ 2 -
            setup.machNumber ^ 2 *
              Real.sin setup.machConeAngleRadians ^ 2 := by ring
      _ = setup.machNumber ^ 2 - 1 := by rw [h_mach_sin_sq]
  have h_distance_sq :
      lengthInMeters setup.horizontalDistanceAtBoom ^ 2 =
        lengthInMeters setup.altitude ^ 2 *
          (setup.machNumber ^ 2 - 1) := by
    calc
      lengthInMeters setup.horizontalDistanceAtBoom ^ 2 =
          (setup.machNumber ^ 2 *
              Real.sin setup.machConeAngleRadians ^ 2) *
            lengthInMeters setup.horizontalDistanceAtBoom ^ 2 := by
              rw [h_mach_sin_sq]
              norm_num
      _ = setup.machNumber ^ 2 *
            (Real.sin setup.machConeAngleRadians ^ 2 *
              lengthInMeters setup.horizontalDistanceAtBoom ^ 2) := by ring
      _ = setup.machNumber ^ 2 *
            (Real.cos setup.machConeAngleRadians ^ 2 *
              lengthInMeters setup.altitude ^ 2) := by rw [h_cross_sq]
      _ = lengthInMeters setup.altitude ^ 2 *
            (setup.machNumber ^ 2 *
              Real.cos setup.machConeAngleRadians ^ 2) := by ring
      _ = lengthInMeters setup.altitude ^ 2 *
            (setup.machNumber ^ 2 - 1) := by rw [h_cos_sq]
  have h_radicand_nonneg : 0 ≤ setup.machNumber ^ 2 - 1 := by
    nlinarith [sq_nonneg (setup.machNumber - 1)]
  have h_target_sq :
      lengthInMeters setup.horizontalDistanceAtBoom ^ 2 =
        (lengthInMeters setup.altitude *
          Real.sqrt (setup.machNumber ^ 2 - 1)) ^ 2 := by
    rw [h_distance_sq]
    calc
      lengthInMeters setup.altitude ^ 2 *
            (setup.machNumber ^ 2 - 1) =
          lengthInMeters setup.altitude ^ 2 *
            Real.sqrt (setup.machNumber ^ 2 - 1) ^ 2 := by
              rw [Real.sq_sqrt h_radicand_nonneg]
      _ = (lengthInMeters setup.altitude *
            Real.sqrt (setup.machNumber ^ 2 - 1)) ^ 2 := by ring
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp h_target_sq) with h | h
  · exact h
  · have h_rhs_nonneg :
        0 ≤ lengthInMeters setup.altitude *
          Real.sqrt (setup.machNumber ^ 2 - 1) :=
      mul_nonneg h_altitude_pos.le (Real.sqrt_nonneg _)
    nlinarith

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Integer-kilometre distances printed beside the four answer labels. -/
def AnswerChoice.distanceInKilometers : AnswerChoice → ℝ
  | .A => 28
  | .B => 24
  | .C => 20
  | .D => 16

/-!
A physical distance rounds to a displayed integer-kilometre answer. The
half-kilometre tolerance is half of the choices' displayed `1 km` precision.
-/
def MatchesAnswerChoice
    (distance : AcousticLength) (choice : AnswerChoice) : Prop :=
  |lengthInKilometers distance - choice.distanceInKilometers| ≤ 1 / 2

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
At the instant the trailing shock front reaches the observer, the jet is
exactly `9500 * sqrt 3` metres horizontally to the right. This is about
`16.45 km`, hence it rounds to displayed answer D, `16 km`.

This formalizes blueprint label `thm:physics:phyx_mini_0221:target`.
-/
theorem jetPositionWhenBoomHeard_matches_recordedAnswerD
    (setup : SonicBoomSetup)
    (_problem : MatchesProblemAndFigure setup)
    (_physical : HasPhysicalSonicBoomParameters setup)
    (_laws : SatisfiesMachConeGeometry setup) :
    lengthInMeters setup.horizontalDistanceAtBoom =
        9500 * Real.sqrt 3 ∧
      MatchesAnswerChoice setup.horizontalDistanceAtBoom recordedAnswerChoice := by
  have h_distance :=
    horizontalDistance_formula setup _physical _laws
  rw [_problem.altitude_meters, _problem.mach_number] at h_distance
  norm_num at h_distance
  constructor
  · exact h_distance
  · change
      |lengthInKilometers setup.horizontalDistanceAtBoom - 16| ≤ 1 / 2
    rw [lengthInKilometers_eq_lengthInMeters_div_thousand, h_distance]
    have h_sqrt_lower : (31 / 19 : ℝ) ≤ Real.sqrt 3 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    have h_sqrt_upper : Real.sqrt 3 ≤ (33 / 19 : ℝ) := by
      rw [Real.sqrt_le_iff]
      constructor <;> norm_num
    rw [abs_le]
    constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0221
