import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0124

open Dimension

/-!
# Slit-array interference from two oppositely sliding membranes

An opaque barrier consists of an inner and an outer membrane.  Each membrane
has a periodic array of parallel slits of width `a` and repeat pitch `d`.
The outer membrane moves upward and the inner one downward with the same speed
`v`.  The figure points `P` and `Q` are adjacent at the initially closed
aperture, and the aperture closes again after `3 s`.

The incident beam is a green `532 nm` laser arriving from the left.  The two
named first-order spots are observed on a circular-arc screen centered at the
fixed midpoint of the slits.  The screen spans `60 degrees` in total.

Lengths, times, and speed use Physlib's unit-independent dimensionful types.
Signed transverse positions also retain their length dimension.  Optical
angles use Mathlib's `Real.Angle`; numerical degree values are only readouts.
-/

/-! ## Dimensionful quantities and scalar readouts -/

/-- A nonnegative unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed transverse coordinate with the physical dimension of length. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative unit-independent physical time. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- The nonnegative physical speed type supplied by Physlib. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a nonnegative physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length { UnitChoices.SI with length := unit }).val : ℝ)

/-- Read a signed physical position in a selected length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (position : SignedLengthQuantity) : ℝ :=
  (position { UnitChoices.SI with length := unit }).val

/-- Read a physical time in a selected time unit. -/
def timeReadout (unit : TimeUnit) (time : TimeQuantity) : ℝ :=
  ((time { UnitChoices.SI with time := unit }).val : ℝ)

/-- Read a physical speed in selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed { UnitChoices.SI with
    length := lengthUnit, time := timeUnit }).val : ℝ)

/-- The nanometer readout used for the laser wavelength. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-- The meter readout used by the kinematic and interference laws. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- The second readout used for the closure cycle. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.seconds time

/-- The SI speed readout in meters per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-! ## Figure labels and experimental objects -/

/-- The two independently moving layers of the opaque barrier. -/
inductive MembraneLabel where
  | outer
  | inner
  deriving DecidableEq, Repr

/-- The two opposite transverse directions shown by the green arrows. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- The two moving edge points labelled in the primary figure. -/
inductive FigurePointLabel where
  | P
  | Q
  deriving DecidableEq, Repr

/-- Qualitative material character stated for the barrier. -/
inductive BarrierKind where
  | opaque
  deriving DecidableEq, Repr

/-- The actuator named in the problem statement. -/
inductive DriveKind where
  | nanomotor
  deriving DecidableEq, Repr

/-- The side from which the beam reaches the membrane stack. -/
inductive IncidentSide where
  | left
  deriving DecidableEq, Repr

/-- The visible color stated for the `532 nm` laser. -/
inductive LightColor where
  | green
  deriving DecidableEq, Repr

/-- The coherent monochromatic beam character implicit in an ideal laser. -/
inductive BeamKind where
  | monochromaticCoherent
  deriving DecidableEq, Repr

/-- The screen shape visible in the figure. -/
inductive ScreenShape where
  | circularArc
  deriving DecidableEq, Repr

/-- The fixed point about which screen angles are measured. -/
inductive ScreenCenter where
  | fixedMidpointBetweenSlits
  deriving DecidableEq, Repr

/-- The ideal optical regime in which the stated interference law applies. -/
inductive OpticalRegime where
  | normalIncidenceFarField
  deriving DecidableEq, Repr

/-- The two symmetric spots whose angular positions are requested. -/
inductive SpotLabel where
  | aboveAxis
  | belowAxis
  deriving DecidableEq, Repr

/-- The signed diffraction/interference order assigned to each named spot. -/
def spotOrder : SpotLabel → ℤ
  | .aboveAxis => 1
  | .belowAxis => -1

/-- All physical quantities and figure-indexed observations in the setup. -/
structure SlidingMembraneInterferenceSetup where
  barrierKind : BarrierKind
  membraneDrive : MembraneLabel → DriveKind
  membraneDirection : MembraneLabel → VerticalDirection
  slitOrientation : MembraneLabel → Real.Angle
  pointCarrier : FigurePointLabel → MembraneLabel
  pointVerticalPosition : FigurePointLabel → TimeQuantity → SignedLengthQuantity
  slitWidthA : LengthQuantity
  slitRepeatPitchD : LengthQuantity
  membraneSpeedMagnitudeV : SpeedQuantity
  initialTime : TimeQuantity
  reclosureTime : TimeQuantity
  effectiveApertureWidth : TimeQuantity → LengthQuantity
  laserColor : LightColor
  laserKind : BeamKind
  laserIncidentSide : IncidentSide
  laserWavelength : LengthQuantity
  screenShape : ScreenShape
  screenCenter : ScreenCenter
  screenRadius : LengthQuantity
  screenSubtendedAngleRadians : ℝ
  opticalRegime : OpticalRegime
  visibleInterferenceOrder : ℤ → Prop
  interferenceAngle : ℤ → Real.Angle

/-- The angular position of either named first-order spot. -/
def spotAngle
    (setup : SlidingMembraneInterferenceSetup) (spot : SpotLabel) : Real.Angle :=
  setup.interferenceAngle (spotOrder spot)

/-- The effective overlap aperture is fully closed at a given instant. -/
def FullyClosedAt
    (setup : SlidingMembraneInterferenceSetup) (time : TimeQuantity) : Prop :=
  lengthInMeters (setup.effectiveApertureWidth time) = 0

/-- A time belongs to the first closure-to-closure cycle. -/
def WithinFirstApertureCycle
    (setup : SlidingMembraneInterferenceSetup) (time : TimeQuantity) : Prop :=
  timeInSeconds setup.initialTime ≤ timeInSeconds time ∧
    timeInSeconds time ≤ timeInSeconds setup.reclosureTime

/-! ## Figure/data readouts, physical conditions, and governing laws -/

/--
Qualitative geometry read from the primary image.  In particular, the angle
signs and screen bounds select the principal representatives of the two
first-order spots without assigning either spot a numerical answer value.
-/
structure MatchesFigureGeometry
    (setup : SlidingMembraneInterferenceSetup) : Prop where
  barrierIsOpaque : setup.barrierKind = .opaque
  pointPOnOuterMembrane : setup.pointCarrier .P = .outer
  pointQOnInnerMembrane : setup.pointCarrier .Q = .inner
  outerMovesUpward : setup.membraneDirection .outer = .upward
  innerMovesDownward : setup.membraneDirection .inner = .downward
  bothDrivenByNanomotors : ∀ membrane, setup.membraneDrive membrane = .nanomotor
  membraneSlitsParallel :
    setup.slitOrientation .outer = setup.slitOrientation .inner
  pointsInitiallyAdjacent :
    setup.pointVerticalPosition .P setup.initialTime =
      setup.pointVerticalPosition .Q setup.initialTime
  screenIsCircularArc : setup.screenShape = .circularArc
  screenHasFixedSlitMidpointCenter :
    setup.screenCenter = .fixedMidpointBetweenSlits
  normalIncidenceFarFieldRegime :
    setup.opticalRegime = .normalIncidenceFarField
  upperFirstOrderVisible : setup.visibleInterferenceOrder (spotOrder .aboveAxis)
  lowerFirstOrderVisible : setup.visibleInterferenceOrder (spotOrder .belowAxis)
  upperSpotAboveAxis : 0 < (spotAngle setup .aboveAxis).toReal
  lowerSpotBelowAxis : (spotAngle setup .belowAxis).toReal < 0
  upperSpotOnScreen :
    |(spotAngle setup .aboveAxis).toReal| ≤
      setup.screenSubtendedAngleRadians / 2
  lowerSpotOnScreen :
    |(spotAngle setup .belowAxis).toReal| ≤
      setup.screenSubtendedAngleRadians / 2

/--
Numerical and endpoint readouts explicitly supplied by the problem.  This
contains `532 nm`, `0 s`, `3 s`, and the `60 degree` screen span, but no spot
angle or answer choice.
-/
structure MatchesProblemReadouts
    (setup : SlidingMembraneInterferenceSetup) : Prop where
  laserIsGreen : setup.laserColor = .green
  laserIsMonochromaticCoherent : setup.laserKind = .monochromaticCoherent
  laserArrivesFromLeft : setup.laserIncidentSide = .left
  wavelengthNanometers : lengthInNanometers setup.laserWavelength = 532
  initialTimeSeconds : timeInSeconds setup.initialTime = 0
  reclosureTimeSeconds : timeInSeconds setup.reclosureTime = 3
  screenSpanRadians : setup.screenSubtendedAngleRadians = Real.pi / 3
  initiallyClosed : FullyClosedAt setup setup.initialTime
  closedAgain : FullyClosedAt setup setup.reclosureTime

/--
Positivity and nondegeneracy of the experiment.  The existence of an open
intermediate aperture rules out a barrier which remains closed throughout.
-/
structure HasPhysicalParameters
    (setup : SlidingMembraneInterferenceSetup) : Prop where
  slitWidthPositive : 0 < lengthInMeters setup.slitWidthA
  slitRepeatPitchPositive : 0 < lengthInMeters setup.slitRepeatPitchD
  slitWidthLessThanRepeatPitch :
    lengthInMeters setup.slitWidthA < lengthInMeters setup.slitRepeatPitchD
  membraneSpeedPositive :
    0 < speedInMetersPerSecond setup.membraneSpeedMagnitudeV
  wavelengthPositive : 0 < lengthInMeters setup.laserWavelength
  screenRadiusPositive : 0 < lengthInMeters setup.screenRadius
  screenSpanPositive : 0 < setup.screenSubtendedAngleRadians
  closureTimesOrdered :
    timeInSeconds setup.initialTime < timeInSeconds setup.reclosureTime
  apertureNeverWiderThanSlit :
    ∀ time, WithinFirstApertureCycle setup time →
      lengthInMeters (setup.effectiveApertureWidth time) ≤
        lengthInMeters setup.slitWidthA
  apertureOpensBetweenClosures :
    ∃ time, WithinFirstApertureCycle setup time ∧
      timeInSeconds setup.initialTime < timeInSeconds time ∧
      timeInSeconds time < timeInSeconds setup.reclosureTime ∧
      0 < lengthInMeters (setup.effectiveApertureWidth time)

/--
Uniform opposite membrane motion and periodic reclosure.  Between successive
closures the relative displacement is one repeat pitch `d`, hence
`d = 2 v Δt`.  This general kinematic law contains no optical answer.
-/
structure SatisfiesSlidingMembraneKinematics
    (setup : SlidingMembraneInterferenceSetup) : Prop where
  outerPointUniformMotion :
    ∀ time, WithinFirstApertureCycle setup time → ∀ unit : LengthUnit,
      signedLengthReadout unit (setup.pointVerticalPosition .P time) -
          signedLengthReadout unit
            (setup.pointVerticalPosition .P setup.initialTime) =
        speedReadout unit TimeUnit.seconds setup.membraneSpeedMagnitudeV *
          (timeInSeconds time - timeInSeconds setup.initialTime)
  innerPointUniformMotion :
    ∀ time, WithinFirstApertureCycle setup time → ∀ unit : LengthUnit,
      signedLengthReadout unit (setup.pointVerticalPosition .Q time) -
          signedLengthReadout unit
            (setup.pointVerticalPosition .Q setup.initialTime) =
        -(speedReadout unit TimeUnit.seconds setup.membraneSpeedMagnitudeV *
          (timeInSeconds time - timeInSeconds setup.initialTime))
  oneRepeatPitchBetweenClosures :
    ∀ unit : LengthUnit,
      lengthReadout unit setup.slitRepeatPitchD =
        2 * speedReadout unit TimeUnit.seconds setup.membraneSpeedMagnitudeV *
          (timeInSeconds setup.reclosureTime -
            timeInSeconds setup.initialTime)

/--
Far-field slit-array interference for every visible signed order:
`d sin(θₘ) = m λ`.  Visibility is explicit because orders outside the
screen or diffraction envelope need not produce observed spots.
-/
structure SatisfiesSlitArrayInterferenceLaw
    (setup : SlidingMembraneInterferenceSetup) : Prop where
  constructiveInterference :
    ∀ order : ℤ, setup.visibleInterferenceOrder order →
      lengthInMeters setup.slitRepeatPitchD *
          Real.Angle.sin (setup.interferenceAngle order) =
        (order : ℝ) * lengthInMeters setup.laserWavelength

/-! ## Recorded multiple-choice metadata and the supported target -/

/-- The four answer labels printed with the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The positive angular magnitude in degrees displayed beside each choice. -/
def AnswerChoice.displayedMagnitudeDegrees : AnswerChoice → ℝ
  | .A => 72 / 25
  | .B => 62 / 25
  | .C => 129 / 50
  | .D => 67 / 25

/-- The dataset records choice A; this is metadata, not a physics premise. -/
def recordedAnswerChoice : AnswerChoice := .A

/--
The physically supported angular-position result.  The `3 s` cycle gives
`d = 6v`, while the two visible first-order spots have principal signed
positions `+arcsin(λ/d)` and `-arcsin(λ/d)`.

Blueprint: `thm:physics:phyx_mini_0124:target`.

The source omits a numerical value for `v` (equivalently for the repeat pitch
`d`), so it does not determine the recorded `2.88°` magnitude.  The missing
readout is intentionally not fabricated as a premise.  Here `d` is modeled as
the repeat pitch, rather than the opaque gap between neighboring slits, because
successive closures occur after one period of relative membrane displacement.
-/
theorem problem_phyx_mini_0124
    (setup : SlidingMembraneInterferenceSetup)
    (physical : HasPhysicalParameters setup)
    (figure : MatchesFigureGeometry setup)
    (readouts : MatchesProblemReadouts setup)
    (kinematics : SatisfiesSlidingMembraneKinematics setup)
    (interference : SatisfiesSlitArrayInterferenceLaw setup) :
    lengthInMeters setup.slitRepeatPitchD =
        6 * speedInMetersPerSecond setup.membraneSpeedMagnitudeV ∧
      (spotAngle setup .aboveAxis).toReal =
        Real.arcsin
          (lengthInMeters setup.laserWavelength /
            lengthInMeters setup.slitRepeatPitchD) ∧
      (spotAngle setup .belowAxis).toReal =
        -Real.arcsin
          (lengthInMeters setup.laserWavelength /
            lengthInMeters setup.slitRepeatPitchD) := by
  have hd :
      lengthInMeters setup.slitRepeatPitchD =
        6 * speedInMetersPerSecond setup.membraneSpeedMagnitudeV := by
    have hkin :=
      kinematics.oneRepeatPitchBetweenClosures LengthUnit.meters
    rw [readouts.reclosureTimeSeconds, readouts.initialTimeSeconds] at hkin
    dsimp [lengthInMeters, speedInMetersPerSecond] at hkin ⊢
    nlinarith [hkin]
  have hd_ne : lengthInMeters setup.slitRepeatPitchD ≠ 0 :=
    ne_of_gt physical.slitRepeatPitchPositive
  have hupper_law :=
    interference.constructiveInterference
      (spotOrder .aboveAxis) figure.upperFirstOrderVisible
  have hupper_sin :
      Real.sin (spotAngle setup .aboveAxis).toReal =
        lengthInMeters setup.laserWavelength /
          lengthInMeters setup.slitRepeatPitchD := by
    apply (eq_div_iff hd_ne).2
    rw [Real.Angle.sin_toReal]
    simpa [spotAngle, spotOrder, mul_comm] using hupper_law
  have hlower_law :=
    interference.constructiveInterference
      (spotOrder .belowAxis) figure.lowerFirstOrderVisible
  have hlower_sin :
      Real.sin (spotAngle setup .belowAxis).toReal =
        -(lengthInMeters setup.laserWavelength /
          lengthInMeters setup.slitRepeatPitchD) := by
    rw [← neg_div]
    apply (eq_div_iff hd_ne).2
    rw [Real.Angle.sin_toReal]
    simpa [spotAngle, spotOrder, mul_comm] using hlower_law
  have hupper_screen := figure.upperSpotOnScreen
  have hlower_screen := figure.lowerSpotOnScreen
  rw [readouts.screenSpanRadians] at hupper_screen hlower_screen
  have hupper_lower_bound :
      -(Real.pi / 2) ≤ (spotAngle setup .aboveAxis).toReal := by
    have h := neg_le_of_abs_le hupper_screen
    nlinarith [Real.pi_pos]
  have hupper_upper_bound :
      (spotAngle setup .aboveAxis).toReal ≤ Real.pi / 2 := by
    have h := le_of_abs_le hupper_screen
    nlinarith [Real.pi_pos]
  have hlower_lower_bound :
      -(Real.pi / 2) ≤ (spotAngle setup .belowAxis).toReal := by
    have h := neg_le_of_abs_le hlower_screen
    nlinarith [Real.pi_pos]
  have hlower_upper_bound :
      (spotAngle setup .belowAxis).toReal ≤ Real.pi / 2 := by
    have h := le_of_abs_le hlower_screen
    nlinarith [Real.pi_pos]
  refine ⟨hd, ?_, ?_⟩
  · calc
      (spotAngle setup .aboveAxis).toReal =
          Real.arcsin (Real.sin (spotAngle setup .aboveAxis).toReal) :=
        (Real.arcsin_sin hupper_lower_bound hupper_upper_bound).symm
      _ = Real.arcsin
          (lengthInMeters setup.laserWavelength /
            lengthInMeters setup.slitRepeatPitchD) := by
        rw [hupper_sin]
  · calc
      (spotAngle setup .belowAxis).toReal =
          Real.arcsin (Real.sin (spotAngle setup .belowAxis).toReal) :=
        (Real.arcsin_sin hlower_lower_bound hlower_upper_bound).symm
      _ = Real.arcsin
          (-(lengthInMeters setup.laserWavelength /
            lengthInMeters setup.slitRepeatPitchD)) := by
        rw [hlower_sin]
      _ = -Real.arcsin
          (lengthInMeters setup.laserWavelength /
            lengthInMeters setup.slitRepeatPitchD) :=
        Real.arcsin_neg _

end PhyXMiniProblems.ProblemPhyXMini0124
