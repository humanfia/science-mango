import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0241

open Dimension

/-!
# Wave speed on a string tensioned by a hanging mass

The primary figure shows a string fixed to a wall on the left, running
horizontally across a table to a pulley at the table edge, and then vertically
down to a square load labelled `m`.  A `3.00 kg` calibration load produces the
observed transverse-wave speed `24.0 m/s`; the question replaces that load by
`2.00 kg` and asks for the new speed.

Mass, acceleration, tension, linear mass density, and wave speed remain
unit-independent Physlib quantities.  Real numbers are used only for named SI
readouts and for the displayed multiple-choice values.
-/

/-! ## Dimensionful physical quantities and coherent SI readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative force, used here for string tension. -/
abbrev TensionQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative mass per unit length of string. -/
abbrev LinearMassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹) NNReal)

/-- A unit-independent propagation speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a nonnegative dimensionful quantity in a coherent unit system. -/
def quantityReadout {d : Dimension}
    (units : UnitChoices) (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  quantityReadout UnitChoices.SI mass

/-- Metres-per-second-squared readout of an acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  quantityReadout UnitChoices.SI acceleration

/-- Newton readout of a string tension. -/
def tensionInNewtons (tension : TensionQuantity) : ℝ :=
  quantityReadout UnitChoices.SI tension

/-- Kilograms-per-metre readout of a string's linear mass density. -/
def linearMassDensityInKilogramsPerMeter
    (density : LinearMassDensityQuantity) : ℝ :=
  quantityReadout UnitChoices.SI density

/-- Metres-per-second readout of a wave speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  quantityReadout UnitChoices.SI speed

/-! ## Trials and primary-figure labels -/

/-- The measured calibration state and the state asked about in the problem. -/
inductive Trial where
  | calibration
  | requested
  deriving DecidableEq, Repr

/-- Individually identifiable components in the supplied figure. -/
inductive FigureComponent where
  | fixedWall
  | table
  | horizontalString
  | tableEdgePulley
  | verticalString
  | hangingMassM
  deriving DecidableEq, Repr

/-- The route followed by the string in the primary figure. -/
inductive StringRoute where
  | fixedAtWallAcrossTableOverPulleyThenVerticallyDown
  deriving DecidableEq, Repr

/-- The two ends of the pictured string and their attachments. -/
inductive StringEndpoint where
  | fixedEnd
  | loadEnd
  deriving DecidableEq, Repr

/-- Objects attached to the two ends of the string. -/
inductive EndpointAttachment where
  | wall
  | hangingMass
  deriving DecidableEq, Repr

/-!
Independent physical quantities and categorical figure data for the two
trials.  The single `stringLinearMassDensity` and `gravitationalAcceleration`
fields express that the same string and location are used in both trials.
Neither requested-speed value is assigned in this structure.
-/
structure StringPulleySetup where
  figureShows : FigureComponent → Prop
  stringRoute : StringRoute
  endpointAttachment : StringEndpoint → EndpointAttachment
  stringIsTaut : Trial → Prop
  hangingLoadInStaticEquilibrium : Trial → Prop
  hangingMass : Trial → MassQuantity
  transverseWaveSpeed : Trial → SpeedQuantity
  horizontalTension : Trial → TensionQuantity
  verticalTension : Trial → TensionQuantity
  stringLinearMassDensity : LinearMassDensityQuantity
  gravitationalAcceleration : AccelerationQuantity

/-!
The categorical information read from the primary figure and the numerical
data stated in the problem: `3.00 kg` with measured speed `24.0 m/s`, followed
by a `2.00 kg` load.  In particular, the requested trial's speed is absent.
-/
structure MatchesProblemAndPrimaryFigure (setup : StringPulleySetup) : Prop where
  showsFixedWall : setup.figureShows .fixedWall
  showsTable : setup.figureShows .table
  showsHorizontalString : setup.figureShows .horizontalString
  showsTableEdgePulley : setup.figureShows .tableEdgePulley
  showsVerticalString : setup.figureShows .verticalString
  showsHangingMassM : setup.figureShows .hangingMassM
  routeReadout :
    setup.stringRoute =
      .fixedAtWallAcrossTableOverPulleyThenVerticallyDown
  fixedEndAtWall : setup.endpointAttachment .fixedEnd = .wall
  loadEndAtHangingMass :
    setup.endpointAttachment .loadEnd = .hangingMass
  stringTautInBothTrials : ∀ trial, setup.stringIsTaut trial
  hangingLoadStaticInBothTrials :
    ∀ trial, setup.hangingLoadInStaticEquilibrium trial
  calibrationMassKilograms :
    massInKilograms (setup.hangingMass .calibration) = 3
  observedCalibrationSpeedMetersPerSecond :
    speedInMetersPerSecond (setup.transverseWaveSpeed .calibration) = 24
  requestedMassKilograms :
    massInKilograms (setup.hangingMass .requested) = 2

/-- Positivity and nondegeneracy conditions for the taut-string model. -/
structure HasPositivePhysicalParameters (setup : StringPulleySetup) : Prop where
  massesPositive :
    ∀ trial, 0 < massInKilograms (setup.hangingMass trial)
  speedsPositive :
    ∀ trial, 0 < speedInMetersPerSecond (setup.transverseWaveSpeed trial)
  horizontalTensionsPositive :
    ∀ trial, 0 < tensionInNewtons (setup.horizontalTension trial)
  verticalTensionsPositive :
    ∀ trial, 0 < tensionInNewtons (setup.verticalTension trial)
  linearMassDensityPositive :
    0 < linearMassDensityInKilogramsPerMeter setup.stringLinearMassDensity
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration

/-! ## Governing string and pulley laws -/

/-!
The standard idealizations used for each trial:

* a frictionless, massless pulley transmits the same tension to both segments;
* static balance makes the vertical tension equal to the hanging weight;
* a uniform taut string obeys `μ v² = T`.

These are general laws relating independent quantities.  They contain neither
the requested exact speed nor the displayed answer `19.6 m/s`.
-/
structure SatisfiesTautStringAndIdealPulleyLaws
    (setup : StringPulleySetup) : Prop where
  pulleyTransmitsTension :
    ∀ trial,
      tensionInNewtons (setup.horizontalTension trial) =
        tensionInNewtons (setup.verticalTension trial)
  staticHangingMassBalance :
    ∀ trial,
      setup.hangingLoadInStaticEquilibrium trial →
        tensionInNewtons (setup.verticalTension trial) =
          massInKilograms (setup.hangingMass trial) *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration
  transverseWaveSpeedLaw :
    ∀ trial,
      setup.stringIsTaut trial →
        speedInMetersPerSecond (setup.transverseWaveSpeed trial) ^ 2 *
            linearMassDensityInKilogramsPerMeter
              setup.stringLinearMassDensity =
          tensionInNewtons (setup.horizontalTension trial)

/-! ## Derived exact speed and displayed answer -/

/-!
Because the two trials use the same string and gravitational field, the laws
give `v_requested / v_calibration = sqrt (2 / 3)`.  With the measured
calibration speed, the requested unrounded value is
`24 * sqrt (2 / 3) m/s`.
-/
lemma requestedWaveSpeed_exact
    (setup : StringPulleySetup)
    (h_problem : MatchesProblemAndPrimaryFigure setup)
    (h_positive : HasPositivePhysicalParameters setup)
    (h_laws : SatisfiesTautStringAndIdealPulleyLaws setup) :
    speedInMetersPerSecond (setup.transverseWaveSpeed .requested) =
      24 * Real.sqrt ((2 : ℝ) / 3) := by
  have h_calibration_relation :
      (24 : ℝ) ^ 2 *
          linearMassDensityInKilogramsPerMeter setup.stringLinearMassDensity =
        3 * accelerationInMetersPerSecondSquared setup.gravitationalAcceleration := by
    rw [← h_problem.observedCalibrationSpeedMetersPerSecond,
      h_laws.transverseWaveSpeedLaw .calibration
        (h_problem.stringTautInBothTrials .calibration),
      h_laws.pulleyTransmitsTension .calibration,
      h_laws.staticHangingMassBalance .calibration
        (h_problem.hangingLoadStaticInBothTrials .calibration),
      h_problem.calibrationMassKilograms]
  have h_requested_relation :
      speedInMetersPerSecond (setup.transverseWaveSpeed .requested) ^ 2 *
          linearMassDensityInKilogramsPerMeter setup.stringLinearMassDensity =
        2 * accelerationInMetersPerSecondSquared setup.gravitationalAcceleration := by
    rw [h_laws.transverseWaveSpeedLaw .requested
        (h_problem.stringTautInBothTrials .requested),
      h_laws.pulleyTransmitsTension .requested,
      h_laws.staticHangingMassBalance .requested
        (h_problem.hangingLoadStaticInBothTrials .requested),
      h_problem.requestedMassKilograms]
  have h_factor :
      (speedInMetersPerSecond (setup.transverseWaveSpeed .requested) ^ 2 - 384) *
          linearMassDensityInKilogramsPerMeter setup.stringLinearMassDensity = 0 := by
    calc
      _ = speedInMetersPerSecond (setup.transverseWaveSpeed .requested) ^ 2 *
            linearMassDensityInKilogramsPerMeter setup.stringLinearMassDensity -
          384 * linearMassDensityInKilogramsPerMeter setup.stringLinearMassDensity := by
            ring
      _ = 0 := by
        rw [h_requested_relation]
        nlinarith [h_calibration_relation]
  have h_density_ne :
      linearMassDensityInKilogramsPerMeter setup.stringLinearMassDensity ≠ 0 :=
    ne_of_gt h_positive.linearMassDensityPositive
  have h_vsq :
      speedInMetersPerSecond (setup.transverseWaveSpeed .requested) ^ 2 = 384 := by
    rcases mul_eq_zero.mp h_factor with h | h
    · nlinarith
    · exact (h_density_ne h).elim
  have h_sqrt_sq : Real.sqrt ((2 : ℝ) / 3) ^ 2 = 2 / 3 :=
    Real.sq_sqrt (by norm_num)
  have h_sqrt_pos : 0 < Real.sqrt ((2 : ℝ) / 3) :=
    Real.sqrt_pos.2 (by norm_num)
  have h_speed_pos := h_positive.speedsPositive .requested
  nlinarith [h_sqrt_sq]

/-- Labels of the four answers printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Wave speed printed beside each answer label, in metres per second. -/
def AnswerChoice.speedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 113 / 5
  | .B => 108 / 5
  | .C => 103 / 5
  | .D => 98 / 5

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
Agreement with a speed displayed to one decimal place.  The half-unit in the
last printed digit is `0.05 m/s`; using a tolerance avoids falsely asserting
that the unrounded physical speed is exactly the displayed decimal.
-/
def MatchesAnswerChoice
    (setup : StringPulleySetup) (choice : AnswerChoice) : Prop :=
  abs (speedInMetersPerSecond (setup.transverseWaveSpeed .requested) -
      choice.speedInMetersPerSecond) ≤ 1 / 20

/-!
The requested wave speed agrees with recorded choice D, `19.6 m/s`, at the
precision displayed by the answer choices.

Blueprint: `thm:physics:phyx_mini_0241:target`.
-/
theorem problem_phyx_mini_0241
    (setup : StringPulleySetup)
    (h_problem : MatchesProblemAndPrimaryFigure setup)
    (h_positive : HasPositivePhysicalParameters setup)
    (h_laws : SatisfiesTautStringAndIdealPulleyLaws setup) :
    MatchesAnswerChoice setup recordedAnswerChoice := by
  change
    |speedInMetersPerSecond (setup.transverseWaveSpeed .requested) - 98 / 5| ≤
      1 / 20
  rw [requestedWaveSpeed_exact setup h_problem h_positive h_laws]
  have h_sqrt_sq : Real.sqrt ((2 : ℝ) / 3) ^ 2 = 2 / 3 :=
    Real.sq_sqrt (by norm_num)
  have h_sqrt_nonneg : 0 ≤ Real.sqrt ((2 : ℝ) / 3) := Real.sqrt_nonneg _
  rw [abs_le]
  constructor <;> nlinarith [h_sqrt_sq]

end PhyXMiniProblems.ProblemPhyXMini0241
