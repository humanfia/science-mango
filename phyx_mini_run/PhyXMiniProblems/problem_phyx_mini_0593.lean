import Mathlib.Analysis.Real.Sqrt
import Physlib.Relativity.LorentzGroup.Boosts.Basic
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0593

open Dimension

/-!
# Arrival interval of radar pulses from a receding relativistic source

A receiver `R` is fixed in inertial frame `S`.  A transmitter `T` and its
mechanical timer are fixed in frame `S'`, which moves to the right relative to
`S`.  The timer has proper period `τ₀` and triggers two radar pulses travelling
left at the vacuum speed of light.  Because the source recedes between
emissions, the receiver interval `τ_R` includes both time dilation and the
extra light-travel time.

Durations, lengths, and speeds are unit-independent Physlib quantities.  Real
numbers occur only at named-unit readout boundaries, in dimensionless ratios,
and in the formulas printed in the multiple-choice list.

Assumption/target split:

* `MatchesRadarPulseScenario` records apparatus, frame, trigger, and direction
  roles from the prose;
* `MatchesSuppliedRadarFigure` records the literal labels and geometry in the
  primary image, including the otherwise unused baseline label `A`;
* `HasPhysicalRadarParameters` supplies positivity and subluminality;
* `SatisfiesRelativisticEmissionClockLaw` states only the generic time-dilation
  relation between the proper timer period and the `S`-frame emission period;
* `SatisfiesRecedingRadarPulseKinematics` states independent source-separation,
  light-flight, and arrival-time accounting equations for two pulses; and
* the strict distinction between `τ₀`, `τ`, and `τ_R`, together with the
  square-root Doppler factor, occurs only in the theorem conclusion.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative, unit-independent physical duration. -/
abbrev DurationQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical duration in a selected time unit. -/
def durationReadout
    (unit : TimeUnit) (duration : DurationQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a physical length in a selected length unit. -/
def lengthReadout
    (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical speed in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read Physlib's exact vacuum speed of light in coherent selected units. -/
def vacuumLightSpeedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) : ℝ :=
  (DimSpeed.speedOfLight {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-! ## Frames, apparatus, directions, and primary-image vocabulary -/

/-- The stationary receiver frame `S` and receding transmitter frame `S'`. -/
inductive InertialFrameLabel where
  | S
  | SPrime
  deriving DecidableEq, Fintype, Repr

/-- Physical apparatus present in the radar timing experiment. -/
inductive RadarApparatus where
  | receiverR
  | transmitterT
  | mechanicalTimer
  deriving DecidableEq, Fintype, Repr

/-- The electromagnetic signal emitted by the transmitter. -/
inductive SignalKind where
  | radarPulse
  deriving DecidableEq, Repr

/-- Horizontal directions in the orientation of the supplied figure. -/
inductive AxialDirection where
  | positiveX
  | negativeX
  deriving DecidableEq, Repr

/-- Literal text labels visible in the supplied radar schematic. -/
inductive FigureLabel where
  | frameS
  | frameSPrime
  | receiverR
  | transmitterT
  | properPeriodTau0
  | baselineA
  | velocityV
  deriving DecidableEq, Fintype, Repr

/-!
Typed transcription of the primary raster.  The figure gives qualitative
placement and direction, but no numerical speed, distance, or time readout.
-/
structure RadarPulseFigure where
  labelShown : FigureLabel → Bool
  leftFrameLabel : InertialFrameLabel
  rightFrameLabel : InertialFrameLabel
  leftApparatus : RadarApparatus
  rightApparatus : RadarApparatus
  timerConnectedTo : RadarApparatus
  timerBoxLabel : FigureLabel
  horizontalBaselineLabel : FigureLabel
  signalEmitter : RadarApparatus
  signalReceiver : RadarApparatus
  movingFrameVelocityArrowAttachedTo : InertialFrameLabel
  movingFrameVelocityDirection : AxialDirection
  wavefrontPropagationDirection : AxialDirection
  wavefrontsShown : Bool

/-! ## Independent physical setup -/

/-!
Independent frame assignments and physical observables for two consecutive
pulses.  In particular, `receiverArrivalIntervalTauR` is not defined from a
Doppler formula or answer choice.  The two source--receiver separations and
two flight durations retain the light-propagation route by which the initial
separation cancels from the requested interval.
-/
structure RadarPulseTimingSetup where
  figure : RadarPulseFigure
  referenceFrame : InertialFrameLabel
  movingFrame : InertialFrameLabel
  receiver : RadarApparatus
  transmitter : RadarApparatus
  pulseTrigger : RadarApparatus
  pulseEmitter : RadarApparatus
  pulseDetector : RadarApparatus
  apparatusFrame : RadarApparatus → InertialFrameLabel
  signalKind : SignalKind
  movingFrameDirectionInS : AxialDirection
  pulsePropagationDirectionInS : AxialDirection
  movingFrameSpeedRelativeToS : SpeedQuantity
  properTimerPeriodTau0 : DurationQuantity
  referenceFrameEmissionIntervalTau : DurationQuantity
  receiverArrivalIntervalTauR : DurationQuantity
  separationAtFirstEmission : LengthQuantity
  separationAtSecondEmission : LengthQuantity
  firstPulseFlightDuration : DurationQuantity
  secondPulseFlightDuration : DurationQuantity

/-- The dimensionless relative speed `β = v/c`, evaluated in SI units. -/
def speedFractionOfLight (setup : RadarPulseTimingSetup) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds
      setup.movingFrameSpeedRelativeToS /
    vacuumLightSpeedReadout LengthUnit.meters TimeUnit.seconds

/-- Physlib's Lorentz factor for the frame speed `v/c`. -/
def movingFrameLorentzFactor (setup : RadarPulseTimingSetup) : ℝ :=
  LorentzGroup.γ (speedFractionOfLight setup)

/-! ## Scenario and figure readouts -/

/-- Apparatus, frame, triggering, and travel roles stated in the problem. -/
structure MatchesRadarPulseScenario
    (setup : RadarPulseTimingSetup) : Prop where
  stationaryFrameIsS : setup.referenceFrame = .S
  movingFrameIsSPrime : setup.movingFrame = .SPrime
  namedReceiverIsR : setup.receiver = .receiverR
  namedTransmitterIsT : setup.transmitter = .transmitterT
  mechanicalTimerTriggersPulses : setup.pulseTrigger = .mechanicalTimer
  transmitterEmitsPulses : setup.pulseEmitter = .transmitterT
  receiverDetectsPulses : setup.pulseDetector = .receiverR
  receiverFixedInS : setup.apparatusFrame .receiverR = .S
  transmitterFixedInSPrime : setup.apparatusFrame .transmitterT = .SPrime
  timerFixedInSPrime : setup.apparatusFrame .mechanicalTimer = .SPrime
  signalIsRadarPulse : setup.signalKind = .radarPulse
  movingFrameRecedesRightward :
    setup.movingFrameDirectionInS = .positiveX
  pulsesTravelLeftTowardReceiver :
    setup.pulsePropagationDirectionInS = .negativeX

/-!
Primary-image evidence: `S` and `R` are on the left; `S'`, `T`, and the timer
box labelled `τ₀` are on the right; the frame arrow points right while the
drawn wavefronts propagate left.  The literal baseline label `A` is recorded
without assigning it an unsupported physical interpretation.
-/
structure MatchesSuppliedRadarFigure
    (figure : RadarPulseFigure) : Prop where
  everyLiteralLabelShown : ∀ label, figure.labelShown label = true
  leftFrameIsS : figure.leftFrameLabel = .S
  rightFrameIsSPrime : figure.rightFrameLabel = .SPrime
  receiverAppearsOnLeft : figure.leftApparatus = .receiverR
  transmitterAppearsOnRight : figure.rightApparatus = .transmitterT
  timerIsConnectedToTransmitter :
    figure.timerConnectedTo = .transmitterT
  timerBoxCarriesTau0 : figure.timerBoxLabel = .properPeriodTau0
  baselineCarriesA : figure.horizontalBaselineLabel = .baselineA
  drawnSignalLeavesTransmitter : figure.signalEmitter = .transmitterT
  drawnSignalArrivesAtReceiver : figure.signalReceiver = .receiverR
  velocityArrowAttachedToSPrime :
    figure.movingFrameVelocityArrowAttachedTo = .SPrime
  velocityArrowPointsRight :
    figure.movingFrameVelocityDirection = .positiveX
  drawnWavefrontsTravelLeft :
    figure.wavefrontPropagationDirection = .negativeX
  wavefrontsAreShown : figure.wavefrontsShown = true

/-! ## Physical-domain conditions and governing laws -/

/-!
Positivity and the ordinary receding, subluminal branch.  The strict positive
speed is what makes the three intervals distinct; no Doppler factor is stated
here.
-/
structure HasPhysicalRadarParameters
    (setup : RadarPulseTimingSetup) : Prop where
  movingSpeedPositive : ∀ lengthUnit timeUnit,
    0 < speedReadout lengthUnit timeUnit
      setup.movingFrameSpeedRelativeToS
  movingSpeedSubluminal : ∀ lengthUnit timeUnit,
    speedReadout lengthUnit timeUnit setup.movingFrameSpeedRelativeToS <
      vacuumLightSpeedReadout lengthUnit timeUnit
  vacuumLightSpeedPositive : ∀ lengthUnit timeUnit,
    0 < vacuumLightSpeedReadout lengthUnit timeUnit
  properTimerPeriodPositive : ∀ timeUnit,
    0 < durationReadout timeUnit setup.properTimerPeriodTau0
  referenceEmissionIntervalPositive : ∀ timeUnit,
    0 < durationReadout timeUnit setup.referenceFrameEmissionIntervalTau
  receiverArrivalIntervalPositive : ∀ timeUnit,
    0 < durationReadout timeUnit setup.receiverArrivalIntervalTauR
  firstSeparationPositive : ∀ lengthUnit,
    0 < lengthReadout lengthUnit setup.separationAtFirstEmission
  secondSeparationPositive : ∀ lengthUnit,
    0 < lengthReadout lengthUnit setup.separationAtSecondEmission
  firstFlightDurationPositive : ∀ timeUnit,
    0 < durationReadout timeUnit setup.firstPulseFlightDuration
  secondFlightDurationPositive : ∀ timeUnit,
    0 < durationReadout timeUnit setup.secondPulseFlightDuration

/-!
Special-relativistic time dilation between successive ticks of the co-moving
timer and their emission events in `S`.  This generic law identifies the
intermediate interval `τ`; it does not state the receiver's interval.
-/
structure SatisfiesRelativisticEmissionClockLaw
    (setup : RadarPulseTimingSetup) : Prop where
  emissionIntervalTimeDilation : ∀ timeUnit,
    durationReadout timeUnit setup.referenceFrameEmissionIntervalTau =
      movingFrameLorentzFactor setup *
        durationReadout timeUnit setup.properTimerPeriodTau0

/-!
Two-pulse kinematics in the stationary receiver frame.  Between emissions the
source--receiver separation grows by `v τ`; each pulse flight obeys distance
equals `c` times flight time; and `τ_R` is the second arrival time minus the
first.  These are governing relations involving independent observables, not
the requested square-root Doppler formula.
-/
structure SatisfiesRecedingRadarPulseKinematics
    (setup : RadarPulseTimingSetup) : Prop where
  sourceRecedesBetweenEmissions : ∀ lengthUnit timeUnit,
    lengthReadout lengthUnit setup.separationAtSecondEmission =
      lengthReadout lengthUnit setup.separationAtFirstEmission +
        speedReadout lengthUnit timeUnit
            setup.movingFrameSpeedRelativeToS *
          durationReadout timeUnit setup.referenceFrameEmissionIntervalTau
  firstPulseTravelsAtLightSpeed : ∀ lengthUnit timeUnit,
    vacuumLightSpeedReadout lengthUnit timeUnit *
        durationReadout timeUnit setup.firstPulseFlightDuration =
      lengthReadout lengthUnit setup.separationAtFirstEmission
  secondPulseTravelsAtLightSpeed : ∀ lengthUnit timeUnit,
    vacuumLightSpeedReadout lengthUnit timeUnit *
        durationReadout timeUnit setup.secondPulseFlightDuration =
      lengthReadout lengthUnit setup.separationAtSecondEmission
  receiverArrivalIntervalAccounting : ∀ timeUnit,
    durationReadout timeUnit setup.receiverArrivalIntervalTauR =
      durationReadout timeUnit setup.referenceFrameEmissionIntervalTau +
        durationReadout timeUnit setup.secondPulseFlightDuration -
          durationReadout timeUnit setup.firstPulseFlightDuration

/-! ## Printed choices -/

/-- Labels of the four interval formulas printed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
The dimensionless factor printed beside each answer label.  These definitions
record the multiple-choice data; none is assumed to equal the physical arrival
interval.
-/
def displayedArrivalIntervalFactor
    (setup : RadarPulseTimingSetup) (choice : AnswerChoice)
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) : ℝ :=
  let c := vacuumLightSpeedReadout lengthUnit timeUnit
  let v := speedReadout lengthUnit timeUnit
    setup.movingFrameSpeedRelativeToS
  match choice with
  | .A => Real.sqrt ((c - v) / (c - v))
  | .B => (c + v) / (c + v)
  | .C => Real.sqrt ((c + v) / (c - v))
  | .D => 1 / Real.sqrt (1 - (v / c) ^ 2)

/-- The interval readout represented by a displayed answer choice. -/
def displayedArrivalIntervalReadout
    (setup : RadarPulseTimingSetup) (choice : AnswerChoice)
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) : ℝ :=
  durationReadout timeUnit setup.properTimerPeriodTau0 *
    displayedArrivalIntervalFactor setup choice lengthUnit timeUnit

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-! ## Derived receiver interval and final target -/

/-!
The independent two-pulse flight equations first give the receding-source
arrival relation `τ_R = τ (c + v) / c`.  This helper is a consequence of the
governing kinematics and contains no proper-time Doppler factor.
-/
lemma receiverArrivalInterval_from_kinematics
    (setup : RadarPulseTimingSetup)
    (hPhysical : HasPhysicalRadarParameters setup)
    (hKinematics : SatisfiesRecedingRadarPulseKinematics setup) :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      durationReadout timeUnit setup.receiverArrivalIntervalTauR =
      durationReadout timeUnit setup.referenceFrameEmissionIntervalTau *
          (vacuumLightSpeedReadout lengthUnit timeUnit +
            speedReadout lengthUnit timeUnit
              setup.movingFrameSpeedRelativeToS) /
          vacuumLightSpeedReadout lengthUnit timeUnit := by
  intro lengthUnit timeUnit
  have hc := hPhysical.vacuumLightSpeedPositive lengthUnit timeUnit
  field_simp [ne_of_gt hc]
  nlinarith
    [hKinematics.sourceRecedesBetweenEmissions lengthUnit timeUnit,
      hKinematics.firstPulseTravelsAtLightSpeed lengthUnit timeUnit,
      hKinematics.secondPulseTravelsAtLightSpeed lengthUnit timeUnit,
      hKinematics.receiverArrivalIntervalAccounting timeUnit]

/-!
Combining `τ = γ τ₀` with the extra propagation interval and
`γ = 1 / sqrt (1 - (v/c)^2)` gives

`τ_R = τ₀ sqrt ((c + v) / (c - v))`.

For strictly positive receding speed, both effects are strict, so the receiver
interval is neither the proper period `τ₀` nor the intermediate `S`-frame
emission interval `τ`.  This formalizes
`thm:physics:phyx_mini_0593:target`.
-/
theorem problem_phyx_mini_0593
    (setup : RadarPulseTimingSetup)
    (hScenario : MatchesRadarPulseScenario setup)
    (hFigure : MatchesSuppliedRadarFigure setup.figure)
    (hPhysical : HasPhysicalRadarParameters setup)
    (hClock : SatisfiesRelativisticEmissionClockLaw setup)
    (hKinematics : SatisfiesRecedingRadarPulseKinematics setup) :
    (∀ timeUnit : TimeUnit,
      durationReadout timeUnit setup.properTimerPeriodTau0 <
        durationReadout timeUnit setup.referenceFrameEmissionIntervalTau) ∧
    (∀ timeUnit : TimeUnit,
      durationReadout timeUnit setup.referenceFrameEmissionIntervalTau <
        durationReadout timeUnit setup.receiverArrivalIntervalTauR) ∧
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      durationReadout timeUnit setup.receiverArrivalIntervalTauR =
        durationReadout timeUnit setup.properTimerPeriodTau0 *
          Real.sqrt
            ((vacuumLightSpeedReadout lengthUnit timeUnit +
                speedReadout lengthUnit timeUnit
                  setup.movingFrameSpeedRelativeToS) /
              (vacuumLightSpeedReadout lengthUnit timeUnit -
                speedReadout lengthUnit timeUnit
                  setup.movingFrameSpeedRelativeToS)) := by
  have hβpos : 0 < speedFractionOfLight setup := by
    exact div_pos
      (hPhysical.movingSpeedPositive LengthUnit.meters TimeUnit.seconds)
      (hPhysical.vacuumLightSpeedPositive LengthUnit.meters TimeUnit.seconds)
  have hβlt : speedFractionOfLight setup < 1 := by
    exact (div_lt_one
      (hPhysical.vacuumLightSpeedPositive
        LengthUnit.meters TimeUnit.seconds)).2
      (hPhysical.movingSpeedSubluminal
        LengthUnit.meters TimeUnit.seconds)
  have hradpos : 0 < 1 - speedFractionOfLight setup ^ 2 := by
    nlinarith
  have hsqrtpos :
      0 < Real.sqrt (1 - speedFractionOfLight setup ^ 2) :=
    Real.sqrt_pos.2 hradpos
  have hsqrtlt :
      Real.sqrt (1 - speedFractionOfLight setup ^ 2) < 1 := by
    apply (Real.sqrt_lt' zero_lt_one).2
    nlinarith [sq_pos_of_pos hβpos]
  have hγgt : 1 < movingFrameLorentzFactor setup := by
    rw [movingFrameLorentzFactor, LorentzGroup.γ]
    exact one_lt_one_div hsqrtpos hsqrtlt
  constructor
  · intro timeUnit
    rw [hClock.emissionIntervalTimeDilation timeUnit]
    have hτ₀ := hPhysical.properTimerPeriodPositive timeUnit
    nlinarith [mul_pos hτ₀ (sub_pos.mpr hγgt)]
  constructor
  · intro timeUnit
    rw [receiverArrivalInterval_from_kinematics
      setup hPhysical hKinematics LengthUnit.meters timeUnit]
    have hc :=
      hPhysical.vacuumLightSpeedPositive LengthUnit.meters timeUnit
    have hv :=
      hPhysical.movingSpeedPositive LengthUnit.meters timeUnit
    have hτ :=
      hPhysical.referenceEmissionIntervalPositive timeUnit
    have hfactor :
        1 <
          (vacuumLightSpeedReadout LengthUnit.meters timeUnit +
            speedReadout LengthUnit.meters timeUnit
              setup.movingFrameSpeedRelativeToS) /
            vacuumLightSpeedReadout LengthUnit.meters timeUnit := by
      apply (one_lt_div hc).2
      linarith
    have h := mul_lt_mul_of_pos_left hfactor hτ
    ring_nf at h ⊢
    assumption
  · intro lengthUnit timeUnit
    rw [receiverArrivalInterval_from_kinematics
      setup hPhysical hKinematics lengthUnit timeUnit,
      hClock.emissionIntervalTimeDilation timeUnit]
    set c : ℝ := vacuumLightSpeedReadout lengthUnit timeUnit with hc_def
    set v : ℝ :=
      speedReadout lengthUnit timeUnit
        setup.movingFrameSpeedRelativeToS with hv_def
    have hc : 0 < c := by
      rw [hc_def]
      exact hPhysical.vacuumLightSpeedPositive lengthUnit timeUnit
    have hv : 0 < v := by
      rw [hv_def]
      exact hPhysical.movingSpeedPositive lengthUnit timeUnit
    have hvc : v < c := by
      rw [hv_def, hc_def]
      exact hPhysical.movingSpeedSubluminal lengthUnit timeUnit
    have hRatio : v / c = speedFractionOfLight setup := by
      rw [hv_def, hc_def]
      let units : UnitChoices := {UnitChoices.SI with
        length := lengthUnit, time := timeUnit}
      change
        ((setup.movingFrameSpeedRelativeToS units).val : ℝ) /
            (DimSpeed.speedOfLight units).val =
          ((setup.movingFrameSpeedRelativeToS UnitChoices.SI).val : ℝ) /
            (DimSpeed.speedOfLight UnitChoices.SI).val
      rw [setup.movingFrameSpeedRelativeToS.2 UnitChoices.SI units,
        DimSpeed.speedOfLight.2 UnitChoices.SI units]
      simp only [WithDim.dim_apply, WithDim.smul_val, NNReal.smul_def,
        smul_eq_mul, NNReal.coe_mul]
      field_simp [UnitChoices.dimScale_ne_zero]
    have hfactor :
        LorentzGroup.γ (v / c) * (c + v) / c =
          Real.sqrt ((c + v) / (c - v)) := by
      have hβpos' : 0 < v / c := div_pos hv hc
      have hβlt' : v / c < 1 := (div_lt_one hc).2 hvc
      have hradpos' : 0 < 1 - (v / c) ^ 2 := by
        nlinarith
      rw [LorentzGroup.γ]
      set s : ℝ := Real.sqrt (1 - (v / c) ^ 2) with hs_def
      set r : ℝ := Real.sqrt ((c + v) / (c - v)) with hr_def
      have hspos : 0 < s := by
        rw [hs_def]
        exact Real.sqrt_pos.2 hradpos'
      have hquotpos : 0 < (c + v) / (c - v) :=
        div_pos (by linarith) (sub_pos.mpr hvc)
      have hrpos : 0 < r := by
        rw [hr_def]
        exact Real.sqrt_pos.2 hquotpos
      have hs_sq : s ^ 2 = 1 - (v / c) ^ 2 := by
        rw [hs_def]
        exact Real.sq_sqrt (le_of_lt hradpos')
      have hr_sq : r ^ 2 = (c + v) / (c - v) := by
        rw [hr_def]
        exact Real.sq_sqrt (le_of_lt hquotpos)
      have hcne : c ≠ 0 := ne_of_gt hc
      have hcvne : c - v ≠ 0 := ne_of_gt (sub_pos.mpr hvc)
      have hsne : s ≠ 0 := ne_of_gt hspos
      have hs_sq_scaled : c ^ 2 * s ^ 2 = c ^ 2 - v ^ 2 := by
        field_simp [hcne] at hs_sq
        nlinarith
      have hsq : (1 / s * (c + v) / c) ^ 2 = r ^ 2 := by
        rw [hr_sq]
        field_simp [hcne, hcvne, hsne]
        nlinarith
      have hlpos : 0 < 1 / s * (c + v) / c :=
        div_pos (mul_pos (div_pos zero_lt_one hspos) (by linarith)) hc
      nlinarith
    rw [movingFrameLorentzFactor, ← hRatio, ← hfactor]
    ring

end PhyXMiniProblems.ProblemPhyXMini0593
