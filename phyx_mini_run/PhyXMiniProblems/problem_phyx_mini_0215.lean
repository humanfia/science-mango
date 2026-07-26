import Mathlib
import Physlib.Units.Examples

/-!
# PhyX mini problem 0215: hearing a backfire across the water

The primary figure shows the fishermen's boat `(b)` and a second, background
boat separated by `1.55 km`.  The fishermen's boat is immediately above the
tuna school `(a)`.  A backfire at the background boat propagates through the
foggy air to the fishermen.

Lengths, durations, and speeds are represented by Physlib's unit-independent
`Dimensionful` quantities.  Real numbers occur only as readouts in explicitly
named units and as the dimensionless labels of the multiple-choice answers.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0215

open Dimension

/-! ## Dimensioned quantities and figure labels -/

/-- A real-valued physical length, independent of the chosen unit readout. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A real-valued physical duration, independent of the chosen unit readout. -/
abbrev DurationQuantity : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- A real-valued physical speed, carrying length-per-time dimension. -/
abbrev SpeedQuantity : Type := Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a physical length as a real number in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length { UnitChoices.SI with length := unit }).val

/-- Read a physical duration as a real number in the selected time unit. -/
def durationReadout (unit : TimeUnit) (duration : DurationQuantity) : ℝ :=
  (duration { UnitChoices.SI with time := unit }).val

/-- Read a physical speed in metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  (speed UnitChoices.SI).val

/-- Kilometre readout used by the `1.55 km` figure annotation. -/
def lengthInKilometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.kilometers length

/-- Metre readout used with the standard sound speed. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Second readout used by the displayed answer choices. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  durationReadout TimeUnit.seconds duration

/-- Objects whose labels or physical roles are visible in the primary figure. -/
inductive SceneObject where
  /-- The tuna school marked `(a)`. -/
  | tunaSchoolA
  /-- The orange-and-white fishermen's boat marked `(b)`. -/
  | fishermenBoatB
  /-- The green-and-white background boat where the backfire occurs. -/
  | backgroundBackfireBoat
  deriving DecidableEq, Repr

/-- Atmospheric condition explicitly stated in the scenario. -/
inductive AtmosphericCondition where
  | foggy
  deriving DecidableEq, Repr

/-! ## Physical setup, source data, and governing law -/

/--
Physical quantities in the boat-to-boat sound-propagation experiment.

The `directlyAbove` relation is an abstract geometric readout from the scene;
it records the otherwise calculation-irrelevant placement of boat `(b)` above
tuna school `(a)` without inventing coordinates not supplied by the image.
-/
structure BoatBackfireSetup where
  soundSource : SceneObject
  listener : SceneObject
  boatSeparation : LengthQuantity
  soundSpeedInAir : SpeedQuantity
  elapsedTime : DurationQuantity
  atmosphere : AtmosphericCondition
  directlyAbove : SceneObject → SceneObject → Prop

/--
Problem-text and primary-figure readouts.  This contains the `1.55 km`
annotation and the identities of `(a)`, `(b)`, source, and receiver, but no
requested elapsed-time value.
-/
structure MatchesProblemAndFigure (setup : BoatBackfireSetup) : Prop where
  sourceIsBackgroundBoat : setup.soundSource = .backgroundBackfireBoat
  listenerIsBoatB : setup.listener = .fishermenBoatB
  boatBAboveTunaSchool : setup.directlyAbove .fishermenBoatB .tunaSchoolA
  atmosphereIsFoggy : setup.atmosphere = .foggy
  separationKilometers : lengthInKilometers setup.boatSeparation = 31 / 20

/-- Positivity conditions selecting a physical sound-propagation situation. -/
structure HasPhysicalParameters (setup : BoatBackfireSetup) : Prop where
  separationPositive : 0 < lengthInMeters setup.boatSeparation
  soundSpeedPositive : 0 < speedInMetersPerSecond setup.soundSpeedInAir
  elapsedTimeNonnegative : 0 ≤ durationInSeconds setup.elapsedTime

/--
The standard textbook model input that sound in the ambient air travels at
`343 m/s`.  It is kept separate from both the figure data and the target time.
-/
structure UsesStandardAirSoundSpeed (setup : BoatBackfireSetup) : Prop where
  speedMetersPerSecond : speedInMetersPerSecond setup.soundSpeedInAir = 343

/--
Governing constant-speed propagation law, stated in every unit system through
Physlib's dimensionally correct `UnitExamples.SpeedEq`: `v = d / t`.
-/
structure ObeysConstantSpeedSoundPropagation
    (setup : BoatBackfireSetup) : Prop where
  speedDistanceTime : ∀ units : UnitChoices,
    UnitExamples.SpeedEq
      (setup.soundSpeedInAir units)
      (setup.boatSeparation units)
      (setup.elapsedTime units)

/-! ## Answer readouts and target -/

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Number of seconds printed beside each answer label. -/
def AnswerChoice.displayedSeconds : AnswerChoice → ℝ
  | .A => 88 / 25
  | .B => 163 / 25
  | .C => 138 / 25
  | .D => 113 / 25

/-- Agreement with a time displayed to the nearest hundredth of a second. -/
def MatchesAnswerChoice (actualSeconds : ℝ) (choice : AnswerChoice) : Prop :=
  |actualSeconds - choice.displayedSeconds| ≤ 1 / 200

/--
Constant-speed propagation determines elapsed time as distance divided by
speed when both are read in SI units.  This is a derived relation, not a field
of the propagation-law interface.
-/
lemma elapsedTime_eq_distance_div_speed
    (setup : BoatBackfireSetup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : ObeysConstantSpeedSoundPropagation setup) :
    durationInSeconds setup.elapsedTime =
      lengthInMeters setup.boatSeparation /
        speedInMetersPerSecond setup.soundSpeedInAir := by
  have h :=
    congrArg WithDim.val
      (h_laws.speedDistanceTime UnitChoices.SI)
  have h_speed :
      speedInMetersPerSecond setup.soundSpeedInAir =
        lengthInMeters setup.boatSeparation /
          durationInSeconds setup.elapsedTime := by
    simpa [durationInSeconds, durationReadout, lengthInMeters, lengthReadout,
      speedInMetersPerSecond, UnitExamples.SpeedEq, UnitChoices.SI] using h
  have h_time_ne : durationInSeconds setup.elapsedTime ≠ 0 := by
    intro h_time
    rw [h_time] at h_speed
    simp only [div_zero] at h_speed
    linarith [h_physical.soundSpeedPositive]
  apply (eq_div_iff h_physical.soundSpeedPositive.ne').2
  have h_distance :=
    (div_eq_iff h_time_ne).1 h_speed.symm
  simpa [mul_comm] using h_distance.symm

/-!
The `1.55 km` separation and `343 m/s` sound speed give the exact ideal-model
time `1550 / 343` seconds.  This is within half a hundredth of `4.52 s`, so it
agrees with displayed answer D.

This formalizes `thm:physics:phyx_mini_0215:target`.
-/
theorem backfire_is_heard_after_answer_D
    (setup : BoatBackfireSetup)
    (h_physical : HasPhysicalParameters setup)
    (h_figure : MatchesProblemAndFigure setup)
    (h_soundSpeed : UsesStandardAirSoundSpeed setup)
    (h_laws : ObeysConstantSpeedSoundPropagation setup) :
    durationInSeconds setup.elapsedTime = 1550 / 343 ∧
      MatchesAnswerChoice (durationInSeconds setup.elapsedTime) .D := by
  have length_kilometers_eq (length : LengthQuantity) :
      lengthInKilometers length = lengthInMeters length / 1000 := by
    have h := congrArg WithDim.val <|
      length.2
        ({UnitChoices.SI with length := LengthUnit.meters} : UnitChoices)
        ({UnitChoices.SI with length := LengthUnit.kilometers} : UnitChoices)
    change lengthInKilometers length = _ * lengthInMeters length at h
    norm_num [lengthInKilometers, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.kilometers, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.smul_def,
      NNReal.coe_inv] at h ⊢
    convert h using 1
    change _ / 1000 = (1 / 1000 : ℝ) * _
    ring
  have h_distance : lengthInMeters setup.boatSeparation = 1550 := by
    have h_units := length_kilometers_eq setup.boatSeparation
    rw [h_figure.separationKilometers] at h_units
    norm_num at h_units ⊢
    linarith
  have h_time := elapsedTime_eq_distance_div_speed setup h_physical h_laws
  rw [h_distance, h_soundSpeed.speedMetersPerSecond] at h_time
  refine ⟨h_time, ?_⟩
  rw [MatchesAnswerChoice, h_time]
  norm_num [AnswerChoice.displayedSeconds, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0215
