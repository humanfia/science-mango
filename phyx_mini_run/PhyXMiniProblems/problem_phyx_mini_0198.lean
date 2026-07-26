import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Speed

/-!
# Sonic-boom delay for a Mach 1.75 airplane

This file models problem `phyx_mini_0198`.  An airplane passes directly above
listener `L` at altitude `8000 m` and continues horizontally at Mach `1.75` in
air whose sound speed is `320 m/s`.  The primary figure labels the Mach-cone
angle `alpha`, the shock-wave slant path, and the horizontal distance `v_s t`.

The recorded answer and the figure interpret the requested time as the delay
from the overhead passage until the trailing shock front reaches the listener.
It is not the microscopic duration of the pressure pulse.  Lengths, durations,
and speeds are unit-independent Physlib quantities; real numbers are used only
for named unit readouts, the dimensionless Mach number and angle, and displayed
answer values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0198

open Dimension

/-! ## Dimensionful quantities and unit readouts -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev AcousticLength : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical elapsed time. -/
abbrev AcousticDuration : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : AcousticLength) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical elapsed time in a selected time unit. -/
def durationReadout (unit : TimeUnit) (duration : AcousticDuration) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a physical speed in selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) (speed : DimSpeed) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Metre readout used for the numerical and geometric data. -/
def lengthInMeters (length : AcousticLength) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Second readout used by the requested time and answer choices. -/
def durationInSeconds (duration : AcousticDuration) : ℝ :=
  durationReadout TimeUnit.seconds duration

/-- Metres-per-second readout used for the stated sound speed. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-! ## Physical objects and primary-figure labels -/

/-- The aircraft depicted at the vertex of the Mach cone. -/
inductive AircraftLabel where
  | airplane
  deriving DecidableEq, Repr

/-- The listener label printed as `L` in the primary figure. -/
inductive ListenerLabel where
  | L
  deriving DecidableEq, Repr

/-- The blue slanted wavefront labeled `Shock wave` in the primary figure. -/
inductive WavefrontLabel where
  | shockWave
  deriving DecidableEq, Repr

/-- Orientations along the horizontal flight axis. -/
inductive AxialDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-!
The independent physical quantities and named objects in the sonic-boom
experiment.  `boomDelay` is the unknown elapsed time from the overhead passage
until the shock front reaches `listener`; it is not assigned a numerical value
by this structure.
-/
structure SonicBoomSetup where
  aircraft : AircraftLabel
  listener : ListenerLabel
  shockFront : WavefrontLabel
  flightDirection : AxialDirection
  /-- The ground point directly below the airplane at its overhead passage. -/
  overheadGroundPoint : ListenerLabel
  altitude : AcousticLength
  soundSpeed : DimSpeed
  airplaneSpeed : DimSpeed
  machNumber : ℝ
  /-- Figure angle `alpha`, measured in radians from the horizontal. -/
  machConeAngleRadians : ℝ
  /-- Figure leg from `L` to the airplane's current ground projection. -/
  listenerToAircraftGroundProjection : AcousticLength
  /-- Figure hypotenuse running from the shock front at `L` to the airplane. -/
  shockWavePathLength : AcousticLength
  boomDelay : AcousticDuration

/-!
The numerical and qualitative data stated in the problem and read from the
primary figure.  The airplane passes directly over `L`, moves right at Mach
`1.75`, has altitude `8000 m`, and flies in air with sound speed `320 m/s`.
No readout of `boomDelay` occurs here.
-/
structure MatchesProblemAndFigure (setup : SonicBoomSetup) : Prop where
  aircraft_is_airplane : setup.aircraft = .airplane
  listener_is_L : setup.listener = .L
  wavefront_is_shock_wave : setup.shockFront = .shockWave
  airplane_moves_right : setup.flightDirection = .right
  airplane_passes_directly_over_listener : setup.overheadGroundPoint = .L
  altitude_meters : lengthInMeters setup.altitude = 8000
  sound_speed_meters_per_second :
    speedInMetersPerSecond setup.soundSpeed = 320
  mach_number : setup.machNumber = 7 / 4

/-!
Positivity, supersonic motion, and the acute physical branch of the Mach cone.
These conditions rule out degenerate geometry and the nonphysical
trigonometric branches without fixing the requested delay.
-/
structure HasPhysicalSonicBoomParameters (setup : SonicBoomSetup) : Prop where
  altitude_positive : 0 < lengthInMeters setup.altitude
  sound_speed_positive : 0 < speedInMetersPerSecond setup.soundSpeed
  airplane_speed_positive : 0 < speedInMetersPerSecond setup.airplaneSpeed
  supersonic : 1 < setup.machNumber
  mach_angle_acute : setup.machConeAngleRadians ∈ Set.Ioo 0 (Real.pi / 2)
  horizontal_distance_positive :
    0 < lengthInMeters setup.listenerToAircraftGroundProjection
  shock_path_positive : 0 < lengthInMeters setup.shockWavePathLength
  boom_delay_positive : 0 < durationInSeconds setup.boomDelay

/-!
The governing relations for a steady airplane and its Mach cone.

* `v_s = M c` defines the Mach-number speed relation.
* `sin alpha = c / v_s` is the Mach-cone law.
* the horizontal figure leg is `v_s t`.
* `tan alpha = h / (v_s t)` and the Pythagorean relation describe the
  right triangle whose hypotenuse is the labeled shock wave.

The quantified readout laws use compatible units on both sides.  They express
general physics and geometry and contain no numerical answer choice.
-/
structure SatisfiesMachConeAndFlightLaws (setup : SonicBoomSetup) : Prop where
  airplane_speed_from_mach : ∀ lengthUnit timeUnit,
    speedReadout lengthUnit timeUnit setup.airplaneSpeed =
      setup.machNumber * speedReadout lengthUnit timeUnit setup.soundSpeed
  mach_cone_relation : ∀ lengthUnit timeUnit,
    Real.sin setup.machConeAngleRadians =
      speedReadout lengthUnit timeUnit setup.soundSpeed /
        speedReadout lengthUnit timeUnit setup.airplaneSpeed
  horizontal_distance_is_vs_mul_t : ∀ lengthUnit timeUnit,
    lengthReadout lengthUnit setup.listenerToAircraftGroundProjection =
      speedReadout lengthUnit timeUnit setup.airplaneSpeed *
        durationReadout timeUnit setup.boomDelay
  right_triangle_tangent : ∀ lengthUnit,
    Real.tan setup.machConeAngleRadians =
      lengthReadout lengthUnit setup.altitude /
        lengthReadout lengthUnit setup.listenerToAircraftGroundProjection
  shock_path_pythagorean : ∀ lengthUnit,
    (lengthReadout lengthUnit setup.shockWavePathLength) ^ 2 =
      (lengthReadout lengthUnit setup.altitude) ^ 2 +
        (lengthReadout lengthUnit
          setup.listenerToAircraftGroundProjection) ^ 2

/-! ## Derived delay and displayed answers -/

/-!
The general delay formula obtained from the Mach-cone and right-triangle laws.
It still depends on the setup's independent altitude, Mach number, and sound
speed, so it does not encode the numerical answer to this instance.
-/
lemma boomDelay_formula
    (setup : SonicBoomSetup)
    (_physical : HasPhysicalSonicBoomParameters setup)
    (_laws : SatisfiesMachConeAndFlightLaws setup) :
    durationInSeconds setup.boomDelay =
      lengthInMeters setup.altitude *
          Real.sqrt (setup.machNumber ^ 2 - 1) /
        (setup.machNumber * speedInMetersPerSecond setup.soundSpeed) := by
  have hMachPos : 0 < setup.machNumber := by
    linarith [_physical.supersonic]
  have hRadicand : 0 ≤ setup.machNumber ^ 2 - 1 := by
    nlinarith [_physical.supersonic]
  have hCosPos : 0 < Real.cos setup.machConeAngleRadians :=
    Real.cos_pos_of_mem_Ioo
      ⟨by
        nlinarith
          [_physical.mach_angle_acute.1, Real.pi_pos],
        _physical.mach_angle_acute.2⟩
  have hSpeed :
      speedInMetersPerSecond setup.airplaneSpeed =
        setup.machNumber * speedInMetersPerSecond setup.soundSpeed := by
    exact
      _laws.airplane_speed_from_mach
        LengthUnit.meters TimeUnit.seconds
  have hSin :
      Real.sin setup.machConeAngleRadians =
        speedInMetersPerSecond setup.soundSpeed /
          speedInMetersPerSecond setup.airplaneSpeed := by
    exact
      _laws.mach_cone_relation
        LengthUnit.meters TimeUnit.seconds
  have hHorizontal :
      lengthInMeters setup.listenerToAircraftGroundProjection =
        speedInMetersPerSecond setup.airplaneSpeed *
          durationInSeconds setup.boomDelay := by
    exact
      _laws.horizontal_distance_is_vs_mul_t
        LengthUnit.meters TimeUnit.seconds
  have hTangent :
      Real.tan setup.machConeAngleRadians =
        lengthInMeters setup.altitude /
          lengthInMeters setup.listenerToAircraftGroundProjection := by
    exact _laws.right_triangle_tangent LengthUnit.meters
  have hSinMach :
      Real.sin setup.machConeAngleRadians = 1 / setup.machNumber := by
    rw [hSin, hSpeed]
    field_simp
      [_physical.sound_speed_positive.ne', hMachPos.ne']
  have hTrig :=
    Real.tan_sq_div_one_add_tan_sq hCosPos.ne'
  rw [hSinMach] at hTrig
  have hTanPolynomial :
      Real.tan setup.machConeAngleRadians ^ 2 *
          (setup.machNumber ^ 2 - 1) =
        1 := by
    field_simp [hMachPos.ne'] at hTrig
    nlinarith [hTrig]
  have hTangent' :
      Real.tan setup.machConeAngleRadians =
        lengthInMeters setup.altitude /
          (speedInMetersPerSecond setup.airplaneSpeed *
            durationInSeconds setup.boomDelay) := by
    calc
      Real.tan setup.machConeAngleRadians =
          lengthInMeters setup.altitude /
            lengthInMeters setup.listenerToAircraftGroundProjection :=
        hTangent
      _ =
          lengthInMeters setup.altitude /
            (speedInMetersPerSecond setup.airplaneSpeed *
              durationInSeconds setup.boomDelay) := by
        rw [hHorizontal]
  have hSpeedTimePos :
      0 <
        speedInMetersPerSecond setup.airplaneSpeed *
          durationInSeconds setup.boomDelay :=
    mul_pos
      _physical.airplane_speed_positive
      _physical.boom_delay_positive
  have hSquare :
      (speedInMetersPerSecond setup.airplaneSpeed *
          durationInSeconds setup.boomDelay) ^ 2 =
        lengthInMeters setup.altitude ^ 2 *
          (setup.machNumber ^ 2 - 1) := by
    rw [hTangent'] at hTanPolynomial
    field_simp
      [hSpeedTimePos.ne',
        _physical.airplane_speed_positive.ne',
        _physical.boom_delay_positive.ne']
      at hTanPolynomial
    nlinarith [hTanPolynomial]
  apply
    (sq_eq_sq₀ _physical.boom_delay_positive.le
      (div_nonneg
        (mul_nonneg
          _physical.altitude_positive.le
          (Real.sqrt_nonneg _))
        (mul_nonneg
          hMachPos.le
          _physical.sound_speed_positive.le) :
        0 ≤
          lengthInMeters setup.altitude *
              Real.sqrt (setup.machNumber ^ 2 - 1) /
            (setup.machNumber *
              speedInMetersPerSecond setup.soundSpeed))).mp
  rw [div_pow, mul_pow, Real.sq_sqrt hRadicand]
  field_simp
    [hMachPos.ne', _physical.sound_speed_positive.ne']
  rw [hSpeed] at hSquare
  nlinarith [hSquare]

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Seconds printed beside each displayed answer label. -/
def AnswerChoice.seconds : AnswerChoice → ℝ
  | .A => 231 / 10
  | .B => 205 / 10
  | .C => 192 / 10
  | .D => 189 / 10

/-!
A physical delay agrees with a displayed tenth-second answer.  The tolerance
`0.05 s` is half of the displayed `0.1 s` increment.
-/
def MatchesAnswerChoice
    (duration : AcousticDuration) (choice : AnswerChoice) : Prop :=
  |durationInSeconds duration - choice.seconds| ≤ 1 / 20

/-- The answer label recorded by the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .B

/-!
The Mach-cone model gives the exact delay `25 * sqrt 33 / 7` seconds, which is
approximately `20.5 s` and therefore agrees with recorded answer B.

This formalizes blueprint label `thm:physics:phyx_mini_0198:target`.
-/
theorem boomDelay_matches_recordedAnswerB
    (setup : SonicBoomSetup)
    (_problem : MatchesProblemAndFigure setup)
    (_physical : HasPhysicalSonicBoomParameters setup)
    (_laws : SatisfiesMachConeAndFlightLaws setup) :
    durationInSeconds setup.boomDelay = 25 * Real.sqrt 33 / 7 ∧
      MatchesAnswerChoice setup.boomDelay recordedAnswerChoice := by
  have hDelay :
      durationInSeconds setup.boomDelay = 25 * Real.sqrt 33 / 7 := by
    calc
      durationInSeconds setup.boomDelay =
          lengthInMeters setup.altitude *
              Real.sqrt (setup.machNumber ^ 2 - 1) /
            (setup.machNumber *
              speedInMetersPerSecond setup.soundSpeed) :=
        boomDelay_formula setup _physical _laws
      _ = 25 * Real.sqrt 33 / 7 := by
        rw
          [_problem.altitude_meters, _problem.mach_number,
            _problem.sound_speed_meters_per_second]
        have hSqrtSixteen : Real.sqrt (16 : ℝ) = 4 := by
          rw
            [show (16 : ℝ) = 4 ^ 2 by norm_num,
              Real.sqrt_sq_eq_abs]
          norm_num
        norm_num [Real.sqrt_div, hSqrtSixteen]
        ring
  constructor
  · exact hDelay
  · change
      |durationInSeconds setup.boomDelay - (205 : ℝ) / 10| ≤
        1 / 20
    rw [hDelay]
    have hLower : (2863 : ℝ) / 500 ≤ Real.sqrt 33 :=
      (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
    have hUpper : Real.sqrt 33 ≤ (2877 : ℝ) / 500 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    rw [abs_le]
    constructor
    · linarith [hLower]
    · linarith [hUpper]

end PhyXMiniProblems.ProblemPhyXMini0198
