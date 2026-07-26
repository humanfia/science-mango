import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0294

open Dimension

/-!
# Phase difference of two traveling string waves

Two sinusoidal transverse waves have the same `9.00 mm` amplitude and the
same wavelength. Their resultant is drawn at two times. The valley labeled
`A` moves `56.0 cm` toward negative `x` in `8.0 ms`. In the figure, the
vertical arrow `H = 8.0 mm` runs from crest to trough, and adjacent horizontal
ticks are `10 cm` apart.

The dimensional quantities below are unit-independent Physlib objects.
Coordinates and displacements occurring in wave equations are scalar
readouts in explicitly selected units. Phase angles are dimensionless real
numbers measured in radians.
-/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical coordinate along the string. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative wave number with inverse-length dimension. -/
abbrev WaveNumberQuantity : Type := Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-- A nonnegative angular frequency with inverse-time dimension. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- The physical propagation speed of a feature of the resultant. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a nonnegative physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed string coordinate in a selected length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (coordinate : SignedLengthQuantity) : ℝ :=
  (coordinate {UnitChoices.SI with length := unit}).val

/-- Read a physical duration in a selected time unit. -/
def timeReadout (unit : TimeUnit) (duration : TimeQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a wave number in inverse units of the selected length unit. -/
def waveNumberReadout
    (unit : LengthUnit) (waveNumber : WaveNumberQuantity) : ℝ :=
  ((waveNumber {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read angular frequency in radians per selected time unit. -/
def angularFrequencyReadout
    (unit : TimeUnit) (frequency : AngularFrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read speed in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- The two equal-amplitude component waves named in the question. -/
inductive ComponentWave where
  | first
  | second
  deriving DecidableEq, Repr

/-- The two drawings of the same traveling resultant. -/
inductive WaveSnapshot where
  | atLabeledA
  | afterNegativeTravel
  deriving DecidableEq, Repr

/-- Line styles distinguishing the two snapshots in the figure. -/
inductive CurveStyle where
  | solid
  | dashed
  deriving DecidableEq, Repr

/-- Coordinate-axis labels printed on the figure. -/
inductive FigureAxis where
  | x
  | y
  deriving DecidableEq, Repr

/-- The two directions along the string's horizontal `x`-axis. -/
inductive HorizontalDirection where
  | positiveX
  | negativeX
  deriving DecidableEq, Repr

/--
The sign multiplying `omega * t` in `sin (k*x + sign*omega*t + phi)`.
A wave traveling toward positive `x` has the minus sign; a wave traveling
toward negative `x` has the plus sign.
-/
def temporalPhaseSign : HorizontalDirection → ℝ
  | .positiveX => -1
  | .negativeX => 1

/--
Typed contents of the supplied graph. `peakToTroughHeightH` is the full
arrow labeled `H`, rather than a wave amplitude. `valleyAXPosition` stores
the signed `x`-coordinate of the same labeled valley at both snapshots.
-/
structure ResultantWaveFigure where
  horizontalAxisLabel : FigureAxis
  verticalAxisLabel : FigureAxis
  curveStyle : WaveSnapshot → CurveStyle
  valleyALabeledSnapshot : WaveSnapshot
  travelArrowDirection : HorizontalDirection
  valleyAXPosition : WaveSnapshot → SignedLengthQuantity
  travelDistanceD : LengthQuantity
  peakToTroughHeightH : LengthQuantity
  horizontalTickSpacing : LengthQuantity

/--
Physical parameters and observable scalar readouts for the two component
waves and their resultant. The common fields express the statement that the
components have the same amplitude, wavelength, angular frequency, and
direction. The unknown second phase remains an unconstrained field here.
-/
structure StringWaveInterferenceSetup where
  componentAmplitudeYm : LengthQuantity
  commonWavelength : LengthQuantity
  waveNumber : WaveNumberQuantity
  angularFrequency : AngularFrequencyQuantity
  propagationSpeed : SpeedQuantity
  elapsedTravelTime : TimeQuantity
  resultantAmplitude : LengthQuantity
  phaseRadians : ComponentWave → ℝ
  propagationDirection : HorizontalDirection
  componentDisplacementReadout :
    ComponentWave → LengthUnit → TimeUnit → ℝ → ℝ → ℝ
  resultantDisplacementReadout : LengthUnit → TimeUnit → ℝ → ℝ → ℝ
  snapshotTime : WaveSnapshot → TimeQuantity
  figure : ResultantWaveFigure

/-- The marked point in a snapshot is a global valley of the resultant. -/
def IsResultantValleyAt
    (setup : StringWaveInterferenceSetup) (snapshot : WaveSnapshot) : Prop :=
  ∀ xMeters : ℝ,
    setup.resultantDisplacementReadout
        LengthUnit.meters TimeUnit.seconds
        (signedLengthReadout LengthUnit.meters
          (setup.figure.valleyAXPosition snapshot))
        (timeReadout TimeUnit.seconds (setup.snapshotTime snapshot)) ≤
      setup.resultantDisplacementReadout
        LengthUnit.meters TimeUnit.seconds xMeters
        (timeReadout TimeUnit.seconds (setup.snapshotTime snapshot))

/-!
Problem-statement and primary-image readouts. The solid curve carries label
`A`; the dashed curve is the later snapshot after that valley has shifted
left by `d`. Four `10 cm` tick intervals make one wavelength in the solid
curve. No field assigns a numerical value to the unknown second phase.
-/
structure MatchesProblemAndFigureReadouts
    (setup : StringWaveInterferenceSetup) : Prop where
  componentAmplitudeMillimeters :
    lengthReadout LengthUnit.millimeters setup.componentAmplitudeYm = 9
  firstPhaseIsZero : setup.phaseRadians .first = 0
  horizontalAxisIsX : setup.figure.horizontalAxisLabel = .x
  verticalAxisIsY : setup.figure.verticalAxisLabel = .y
  labeledCurveIsSolid : setup.figure.curveStyle .atLabeledA = .solid
  shiftedCurveIsDashed :
    setup.figure.curveStyle .afterNegativeTravel = .dashed
  labelAIsOnSolidSnapshot :
    setup.figure.valleyALabeledSnapshot = .atLabeledA
  arrowPointsTowardNegativeX :
    setup.figure.travelArrowDirection = .negativeX
  propagationIsTowardNegativeX : setup.propagationDirection = .negativeX
  travelDistanceCentimeters :
    lengthReadout LengthUnit.centimeters setup.figure.travelDistanceD = 56
  elapsedTimeMilliseconds :
    timeReadout TimeUnit.milliseconds setup.elapsedTravelTime = 8
  heightMillimeters :
    lengthReadout LengthUnit.millimeters setup.figure.peakToTroughHeightH = 8
  tickSpacingCentimeters :
    lengthReadout LengthUnit.centimeters setup.figure.horizontalTickSpacing = 10
  wavelengthSpansFourTicks :
    ∀ unit : LengthUnit,
      lengthReadout unit setup.commonWavelength =
        4 * lengthReadout unit setup.figure.horizontalTickSpacing
  snapshotTimeDifference :
    ∀ unit : TimeUnit,
      timeReadout unit (setup.snapshotTime .afterNegativeTravel) =
        timeReadout unit (setup.snapshotTime .atLabeledA) +
          timeReadout unit setup.elapsedTravelTime
  valleyShiftIsNegativeD :
    ∀ unit : LengthUnit,
      signedLengthReadout unit
          (setup.figure.valleyAXPosition .afterNegativeTravel) =
        signedLengthReadout unit
            (setup.figure.valleyAXPosition .atLabeledA) -
          lengthReadout unit setup.figure.travelDistanceD
  markedPositionsAreValleys :
    ∀ snapshot, IsResultantValleyAt setup snapshot
  heightIsPeakToTrough :
    ∀ unit : LengthUnit,
      lengthReadout unit setup.figure.peakToTroughHeightH =
        2 * lengthReadout unit setup.resultantAmplitude

/-- Positivity, nondegeneracy, and the principal phase convention. -/
structure HasPhysicalWaveParameters
    (setup : StringWaveInterferenceSetup) : Prop where
  componentAmplitudePositive :
    ∀ unit, 0 < lengthReadout unit setup.componentAmplitudeYm
  wavelengthPositive :
    ∀ unit, 0 < lengthReadout unit setup.commonWavelength
  waveNumberPositive :
    ∀ unit, 0 < waveNumberReadout unit setup.waveNumber
  angularFrequencyPositive :
    ∀ unit, 0 < angularFrequencyReadout unit setup.angularFrequency
  propagationSpeedPositive :
    ∀ lengthUnit timeUnit,
      0 < speedReadout lengthUnit timeUnit setup.propagationSpeed
  elapsedTimePositive :
    ∀ unit, 0 < timeReadout unit setup.elapsedTravelTime
  resultantAmplitudePositive :
    ∀ unit, 0 < lengthReadout unit setup.resultantAmplitude
  secondPhaseIsPrincipal :
    setup.phaseRadians .second ∈ Set.Icc 0 Real.pi

/-!
General wave kinematics: `k*lambda = 2*pi`, the observed feature obeys
`d = v*Delta t`, and `omega = k*v`. These laws keep the wavelength, travel
distance, elapsed time, and frequency roles explicit even though the phase
calculation ultimately uses the amplitude data.
-/
structure SatisfiesWaveKinematics
    (setup : StringWaveInterferenceSetup) : Prop where
  waveNumberWavelengthRelation :
    ∀ lengthUnit,
      waveNumberReadout lengthUnit setup.waveNumber *
          lengthReadout lengthUnit setup.commonWavelength =
        2 * Real.pi
  travelDistanceRelation :
    ∀ lengthUnit timeUnit,
      speedReadout lengthUnit timeUnit setup.propagationSpeed *
          timeReadout timeUnit setup.elapsedTravelTime =
        lengthReadout lengthUnit setup.figure.travelDistanceD
  angularFrequencyRelation :
    ∀ lengthUnit timeUnit,
      angularFrequencyReadout timeUnit setup.angularFrequency =
        waveNumberReadout lengthUnit setup.waveNumber *
          speedReadout lengthUnit timeUnit setup.propagationSpeed

/-- Each component obeys the dimensionally coherent traveling-sine law. -/
structure SatisfiesSinusoidalTravelingWaveLaw
    (setup : StringWaveInterferenceSetup) : Prop where
  componentWaveEquation :
    ∀ wave lengthUnit timeUnit x t,
      setup.componentDisplacementReadout wave lengthUnit timeUnit x t =
        lengthReadout lengthUnit setup.componentAmplitudeYm *
          Real.sin
            (waveNumberReadout lengthUnit setup.waveNumber * x +
              temporalPhaseSign setup.propagationDirection *
                angularFrequencyReadout timeUnit setup.angularFrequency * t +
              setup.phaseRadians wave)

/-- The string displacement is the linear sum of both component waves. -/
structure SatisfiesLinearSuperposition
    (setup : StringWaveInterferenceSetup) : Prop where
  resultantIsSum :
    ∀ lengthUnit timeUnit x t,
      setup.resultantDisplacementReadout lengthUnit timeUnit x t =
        setup.componentDisplacementReadout
            .first lengthUnit timeUnit x t +
          setup.componentDisplacementReadout
            .second lengthUnit timeUnit x t

/-!
The resultant amplitude is identified by writing the resultant with the
common carrier and mean phase. This is the general equal-amplitude
interference convention; it neither assigns the amplitude readout nor fixes
the unknown phase to a problem-specific answer.
-/
structure IdentifiesResultantAmplitude
    (setup : StringWaveInterferenceSetup) : Prop where
  resultantWaveEquation :
    ∀ lengthUnit timeUnit x t,
      setup.resultantDisplacementReadout lengthUnit timeUnit x t =
        lengthReadout lengthUnit setup.resultantAmplitude *
          Real.sin
            (waveNumberReadout lengthUnit setup.waveNumber * x +
              temporalPhaseSign setup.propagationDirection *
                angularFrequencyReadout timeUnit setup.angularFrequency * t +
              (setup.phaseRadians .first + setup.phaseRadians .second) / 2)

/-- The four phase-angle answer choices, in radians. -/
inductive PhaseAnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Numerical phase readout printed beside each answer choice. -/
def displayedPhaseRadians : PhaseAnswerChoice → ℝ
  | .A => 2.48
  | .B => 2.55
  | .C => 2.62
  | .D => 2.69

/-- Agreement with a phase displayed to the nearest hundredth of a radian. -/
def RoundsToDisplayedPhase
    (setup : StringWaveInterferenceSetup)
    (choice : PhaseAnswerChoice) : Prop :=
  |setup.phaseRadians .second - displayedPhaseRadians choice| < 1 / 200

/-- The sum-to-product identity used for equal-amplitude interference. -/
lemma equalAmplitudeSineSuperposition
    (amplitude carrier phase₁ phase₂ : ℝ) :
    amplitude * Real.sin (carrier + phase₁) +
        amplitude * Real.sin (carrier + phase₂) =
      2 * amplitude * Real.cos ((phase₁ - phase₂) / 2) *
        Real.sin (carrier + (phase₁ + phase₂) / 2) := by
  rw [← mul_add, Real.sin_add_sin]
  ring_nf

/-- The general resultant-amplitude relation, before using numeric data. -/
lemma resultantAmplitudeReadout_eq
    (setup : StringWaveInterferenceSetup)
    (h_physical : HasPhysicalWaveParameters setup)
    (h_wave : SatisfiesSinusoidalTravelingWaveLaw setup)
    (h_superposition : SatisfiesLinearSuperposition setup)
    (h_resultant : IdentifiesResultantAmplitude setup) :
    ∀ unit : LengthUnit,
      lengthReadout unit setup.resultantAmplitude =
        2 * lengthReadout unit setup.componentAmplitudeYm *
          Real.cos
            ((setup.phaseRadians .first - setup.phaseRadians .second) / 2) := by
  intro unit
  let k := waveNumberReadout unit setup.waveNumber
  let meanPhase :=
    (setup.phaseRadians .first + setup.phaseRadians .second) / 2
  let x := (Real.pi / 2 - meanPhase) / k
  have hk_pos : 0 < k := h_physical.waveNumberPositive unit
  have hk_ne : k ≠ 0 := ne_of_gt hk_pos
  have hcarrier :
      k * x + temporalPhaseSign setup.propagationDirection *
          angularFrequencyReadout TimeUnit.seconds setup.angularFrequency * 0 =
        Real.pi / 2 - meanPhase := by
    simp only [mul_zero, add_zero, x]
    field_simp
  have hsum :=
    equalAmplitudeSineSuperposition
      (lengthReadout unit setup.componentAmplitudeYm)
      (k * x + temporalPhaseSign setup.propagationDirection *
        angularFrequencyReadout TimeUnit.seconds setup.angularFrequency * 0)
      (setup.phaseRadians .first) (setup.phaseRadians .second)
  have hresultant :=
    h_resultant.resultantWaveEquation unit TimeUnit.seconds x 0
  rw [h_superposition.resultantIsSum,
    h_wave.componentWaveEquation, h_wave.componentWaveEquation] at hresultant
  change
    lengthReadout unit setup.componentAmplitudeYm *
          Real.sin
            (k * x + temporalPhaseSign setup.propagationDirection *
              angularFrequencyReadout TimeUnit.seconds setup.angularFrequency * 0 +
              setup.phaseRadians .first) +
        lengthReadout unit setup.componentAmplitudeYm *
          Real.sin
            (k * x + temporalPhaseSign setup.propagationDirection *
              angularFrequencyReadout TimeUnit.seconds setup.angularFrequency * 0 +
              setup.phaseRadians .second) =
      2 * lengthReadout unit setup.componentAmplitudeYm *
          Real.cos
            ((setup.phaseRadians .first - setup.phaseRadians .second) / 2) *
        Real.sin
          (k * x + temporalPhaseSign setup.propagationDirection *
            angularFrequencyReadout TimeUnit.seconds setup.angularFrequency * 0 +
            meanPhase) at hsum
  rw [hsum] at hresultant
  rw [hcarrier, sub_add_cancel, Real.sin_pi_div_two] at hresultant
  linarith

/-- Four horizontal `10 cm` intervals give a wavelength of `40 cm`. -/
lemma wavelengthInCentimeters_eq_forty
    (setup : StringWaveInterferenceSetup)
    (h_readouts : MatchesProblemAndFigureReadouts setup) :
    lengthReadout LengthUnit.centimeters setup.commonWavelength = 40 := by
  rw [h_readouts.wavelengthSpansFourTicks,
    h_readouts.tickSpacingCentimeters]
  norm_num

/-- The observed travel gives a feature speed of `7 cm/ms`. -/
lemma waveSpeedInCentimetersPerMillisecond_eq_seven
    (setup : StringWaveInterferenceSetup)
    (h_readouts : MatchesProblemAndFigureReadouts setup)
    (h_kinematics : SatisfiesWaveKinematics setup) :
    speedReadout LengthUnit.centimeters TimeUnit.milliseconds
      setup.propagationSpeed = 7 := by
  have htravel :=
    h_kinematics.travelDistanceRelation
      LengthUnit.centimeters TimeUnit.milliseconds
  rw [h_readouts.elapsedTimeMilliseconds,
    h_readouts.travelDistanceCentimeters] at htravel
  linarith

/-- Leftward travel selects the plus sign in front of `omega*t`. -/
lemma temporalPhaseSign_eq_one
    (setup : StringWaveInterferenceSetup)
    (h_readouts : MatchesProblemAndFigureReadouts setup) :
    temporalPhaseSign setup.propagationDirection = 1 := by
  rw [h_readouts.propagationIsTowardNegativeX]
  rfl

/-- Since `H = 8 mm` is crest-to-trough, the resultant amplitude is `4 mm`. -/
lemma resultantAmplitudeInMillimeters_eq_four
    (setup : StringWaveInterferenceSetup)
    (h_readouts : MatchesProblemAndFigureReadouts setup) :
    lengthReadout LengthUnit.millimeters setup.resultantAmplitude = 4 := by
  have hheight :=
    h_readouts.heightIsPeakToTrough LengthUnit.millimeters
  rw [h_readouts.heightMillimeters] at hheight
  linarith

/-!
The `4 mm` resultant amplitude and two `9 mm` component amplitudes give
`cos (phi₂/2) = 2/9`. The principal-phase convention then determines the
exact phase as `2 * arccos (2/9)`.
-/
lemma secondPhaseRadians_eq
    (setup : StringWaveInterferenceSetup)
    (h_readouts : MatchesProblemAndFigureReadouts setup)
    (h_physical : HasPhysicalWaveParameters setup)
    (h_wave : SatisfiesSinusoidalTravelingWaveLaw setup)
    (h_superposition : SatisfiesLinearSuperposition setup)
    (h_resultant : IdentifiesResultantAmplitude setup) :
    setup.phaseRadians .second = 2 * Real.arccos (2 / 9) := by
  have hamplitude :=
    resultantAmplitudeReadout_eq setup h_physical h_wave h_superposition
      h_resultant LengthUnit.millimeters
  rw [resultantAmplitudeInMillimeters_eq_four setup h_readouts,
    h_readouts.componentAmplitudeMillimeters,
    h_readouts.firstPhaseIsZero] at hamplitude
  have hcos :
      Real.cos (setup.phaseRadians .second / 2) = 2 / 9 := by
    rw [show (0 - setup.phaseRadians .second) / 2 =
      -(setup.phaseRadians .second / 2) by ring, Real.cos_neg] at hamplitude
    nlinarith
  have hphase := h_physical.secondPhaseIsPrincipal
  have harccos :
      Real.arccos (Real.cos (setup.phaseRadians .second / 2)) =
        setup.phaseRadians .second / 2 :=
    Real.arccos_cos (by linarith [hphase.1])
      (by nlinarith only [hphase.2, Real.pi_pos])
  calc
    setup.phaseRadians .second =
        2 * (setup.phaseRadians .second / 2) := by ring
    _ = 2 * Real.arccos
        (Real.cos (setup.phaseRadians .second / 2)) := by rw [harccos]
    _ = 2 * Real.arccos (2 / 9) := by rw [hcos]

/-- The exact principal phase rounds to the displayed value `2.69 rad`. -/
lemma secondPhaseRoundsToChoiceD
    (setup : StringWaveInterferenceSetup)
    (h_readouts : MatchesProblemAndFigureReadouts setup)
    (h_physical : HasPhysicalWaveParameters setup)
    (h_wave : SatisfiesSinusoidalTravelingWaveLaw setup)
    (h_superposition : SatisfiesLinearSuperposition setup)
    (h_resultant : IdentifiesResultantAmplitude setup) :
    RoundsToDisplayedPhase setup .D := by
  let xLower : ℝ := 537 / 6400
  have hxLowerAbs : |xLower| ≤ 1 := by
    norm_num [xLower, abs_of_nonneg]
  have hTaylorLower := abs_le.mp (Real.cos_bound hxLowerAbs)
  rw [abs_of_nonneg (by norm_num [xLower])] at hTaylorLower
  have hCosXLower :
      (0.99647 : ℝ) ≤ Real.cos xLower := by
    norm_num [xLower] at hTaylorLower ⊢
    nlinarith only [hTaylorLower.1]
  have hCosTwoLower :
      (0.9859 : ℝ) ≤ Real.cos (2 * xLower) := by
    rw [Real.cos_two_mul]
    have hSquare :=
      mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 0.99647)
        hCosXLower
    nlinarith only [hSquare]
  have hCosFourLower :
      (0.9439 : ℝ) ≤ Real.cos (4 * xLower) := by
    rw [show 4 * xLower = 2 * (2 * xLower) by ring,
      Real.cos_two_mul]
    have hSquare :=
      mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 0.9859)
        hCosTwoLower
    nlinarith only [hSquare]
  have hCosEightLower :
      (0.7818 : ℝ) ≤ Real.cos (8 * xLower) := by
    rw [show 8 * xLower = 2 * (4 * xLower) by ring,
      Real.cos_two_mul]
    have hSquare :=
      mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 0.9439)
        hCosFourLower
    nlinarith only [hSquare]
  have hCosSixteenLower :
      (2 : ℝ) / 9 < Real.cos (16 * xLower) := by
    rw [show 16 * xLower = 2 * (8 * xLower) by ring,
      Real.cos_two_mul]
    have hSquare :=
      mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 0.7818)
        hCosEightLower
    nlinarith only [hSquare]
  have hCosLowerEndpoint :
      (2 : ℝ) / 9 < Real.cos ((537 : ℝ) / 400) := by
    norm_num [xLower] at hCosSixteenLower ⊢
    exact hCosSixteenLower
  let xUpper : ℝ := 539 / 6400
  have hxUpperAbs : |xUpper| ≤ 1 := by
    norm_num [xUpper, abs_of_nonneg]
  have hTaylorUpper := abs_le.mp (Real.cos_bound hxUpperAbs)
  rw [abs_of_nonneg (by norm_num [xUpper])] at hTaylorUpper
  have hCosXUpperNonnegative :
      0 ≤ Real.cos xUpper := by
    norm_num [xUpper] at hTaylorUpper ⊢
    nlinarith only [hTaylorUpper.1]
  have hCosXUpper :
      Real.cos xUpper ≤ (0.9964563 : ℝ) := by
    norm_num [xUpper] at hTaylorUpper ⊢
    nlinarith only [hTaylorUpper.2]
  have hCosTwoUpperNonnegative :
      0 ≤ Real.cos (2 * xUpper) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by norm_num [xUpper]; linarith only [Real.one_le_pi_div_two])
      (by norm_num [xUpper]; linarith only [Real.one_le_pi_div_two])
  have hCosTwoUpper :
      Real.cos (2 * xUpper) ≤ (0.985851 : ℝ) := by
    rw [Real.cos_two_mul]
    have hSquare :=
      mul_self_le_mul_self hCosXUpperNonnegative hCosXUpper
    nlinarith only [hSquare]
  have hCosFourUpperNonnegative :
      0 ≤ Real.cos (4 * xUpper) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by norm_num [xUpper]; linarith only [Real.one_le_pi_div_two])
      (by norm_num [xUpper]; linarith only [Real.one_le_pi_div_two])
  have hCosFourUpper :
      Real.cos (4 * xUpper) ≤ (0.943805 : ℝ) := by
    rw [show 4 * xUpper = 2 * (2 * xUpper) by ring,
      Real.cos_two_mul]
    have hSquare :=
      mul_self_le_mul_self hCosTwoUpperNonnegative hCosTwoUpper
    nlinarith only [hSquare]
  have hCosEightUpperNonnegative :
      0 ≤ Real.cos (8 * xUpper) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by norm_num [xUpper]; linarith only [Real.one_le_pi_div_two])
      (by norm_num [xUpper]; linarith only [Real.one_le_pi_div_two])
  have hCosEightUpper :
      Real.cos (8 * xUpper) ≤ (0.78154 : ℝ) := by
    rw [show 8 * xUpper = 2 * (4 * xUpper) by ring,
      Real.cos_two_mul]
    have hSquare :=
      mul_self_le_mul_self hCosFourUpperNonnegative hCosFourUpper
    nlinarith only [hSquare]
  have hCosSixteenUpper :
      Real.cos (16 * xUpper) < (2 : ℝ) / 9 := by
    rw [show 16 * xUpper = 2 * (8 * xUpper) by ring,
      Real.cos_two_mul]
    have hSquare :=
      mul_self_le_mul_self hCosEightUpperNonnegative hCosEightUpper
    nlinarith only [hSquare]
  have hCosUpperEndpoint :
      Real.cos ((539 : ℝ) / 400) < (2 : ℝ) / 9 := by
    norm_num [xUpper] at hCosSixteenUpper ⊢
    exact hCosSixteenUpper
  have hAngleLower :
      (537 : ℝ) / 400 < Real.arccos (2 / 9) := by
    have hComparison :=
      Real.arccos_lt_arccos (x := (2 : ℝ) / 9)
        (y := Real.cos ((537 : ℝ) / 400))
        (by norm_num) hCosLowerEndpoint (Real.cos_le_one _)
    rw [Real.arccos_cos (by norm_num)
      (by nlinarith only [Real.two_le_pi])] at hComparison
    exact hComparison
  have hAngleUpper :
      Real.arccos (2 / 9) < (539 : ℝ) / 400 := by
    have hComparison :=
      Real.arccos_lt_arccos
        (x := Real.cos ((539 : ℝ) / 400))
        (y := (2 : ℝ) / 9)
        (Real.neg_one_le_cos _) hCosUpperEndpoint (by norm_num)
    rw [Real.arccos_cos (by norm_num)
      (by nlinarith only [Real.two_le_pi])] at hComparison
    exact hComparison
  unfold RoundsToDisplayedPhase
  rw [secondPhaseRadians_eq setup h_readouts h_physical h_wave
    h_superposition h_resultant]
  change |2 * Real.arccos (2 / 9) - 2.69| < 1 / 200
  rw [abs_lt]
  constructor <;> norm_num at hAngleLower hAngleUpper ⊢ <;> linarith

/-!
For the depicted equal-amplitude waves, negative-`x` travel selects
`sin (k*x + omega*t + phi)`. The second phase is exactly
`2 * arccos (2/9)` in the principal convention and rounds to `2.69 rad`,
answer choice D.

This is the Lean declaration corresponding to
`thm:physics:phyx_mini_0294:target`.
-/
theorem problem_phyx_mini_0294
    (setup : StringWaveInterferenceSetup)
    (h_readouts : MatchesProblemAndFigureReadouts setup)
    (h_physical : HasPhysicalWaveParameters setup)
    (h_kinematics : SatisfiesWaveKinematics setup)
    (h_wave : SatisfiesSinusoidalTravelingWaveLaw setup)
    (h_superposition : SatisfiesLinearSuperposition setup)
    (h_resultant : IdentifiesResultantAmplitude setup) :
    temporalPhaseSign setup.propagationDirection = 1 ∧
      setup.phaseRadians .second = 2 * Real.arccos (2 / 9) ∧
      RoundsToDisplayedPhase setup .D := by
  exact ⟨temporalPhaseSign_eq_one setup h_readouts,
    secondPhaseRadians_eq setup h_readouts h_physical h_wave
      h_superposition h_resultant,
    secondPhaseRoundsToChoiceD setup h_readouts h_physical h_wave
      h_superposition h_resultant⟩

end PhyXMiniProblems.ProblemPhyXMini0294
