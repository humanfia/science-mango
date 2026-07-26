import Mathlib
import Physlib.Units.WithDim.Energy

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0499

open Dimension

/-!
# Planck's constant from a photoelectric stopping-potential graph

The primary raster plots the stopping potential `V_stop` in volts against the
incident-light frequency `f` in units of `10^15 Hz`.  Its straight green line
passes through the two readable points `(1, 0)` and `(3, 8)`.  Consequently its
physical slope is `4 * 10^-15 V s`.

Frequency, electric potential, charge magnitude, work function, and Planck's
constant remain dimension-tagged physical quantities.  Real numbers are used
only for explicitly named SI readouts and for the displayed graph coordinates.
-/

/-! ## Dimensionful physical quantities and SI readouts -/

/-- The SI dimension of electric potential, energy per unit charge. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The SI dimension of action, equivalently joule-seconds. -/
def actionDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative physical frequency carrying inverse-time dimension. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative physical electric-potential magnitude. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension NNReal)

/-- A nonnegative physical electric-charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative physical quantity with the dimension of Planck's constant. -/
abbrev PlanckConstantQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- Hertz readout of a physical frequency in the SI unit choice. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Volt readout of a physical electric potential in the SI unit choice. -/
def electricPotentialInVolts (potential : ElectricPotentialQuantity) : ℝ :=
  ((potential UnitChoices.SI).val : ℝ)

/-- Coulomb readout of a physical charge magnitude in the SI unit choice. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge UnitChoices.SI).val : ℝ)

/-- Joule-second readout of a physical action in the SI unit choice. -/
def actionInJouleSeconds (action : PlanckConstantQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-- Joule readout of a signed dimensionful energy. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-! ## Axis labels and geometry extracted from the primary raster -/

/-- The two physical quantities assigned to the graph axes. -/
inductive GraphAxisQuantity where
  | incidentFrequency
  | stoppingPotential
  deriving DecidableEq, Repr

/-- The two unit labels printed beside the graph axes. -/
inductive GraphDisplayUnit where
  | tenToFifteenthHertz
  | volt
  deriving DecidableEq, Repr

/-- The visible color of the data line. -/
inductive GraphLineColor where
  | green
  | other
  deriving DecidableEq, Repr

/-- Qualitative direction of the displayed line as frequency increases. -/
inductive GraphLineTrend where
  | increasing
  | decreasing
  | constant
  | other
  deriving DecidableEq, Repr

/-- A point expressed in the scalar coordinates printed on the graph. -/
structure PhotoelectricPlotPoint where
  frequencyInTenToFifteenthHertz : ℝ
  stoppingPotentialInVolts : ℝ

/-!
The graph records literal display coordinates separately from the physical
observables of the experiment.  The largest labeled ticks are `3` and `8`;
the green line itself extends slightly past them in the raster.
-/
structure PhotoelectricStoppingPotentialGraph where
  horizontalAxis : GraphAxisQuantity
  verticalAxis : GraphAxisQuantity
  axisUnit : GraphAxisQuantity → GraphDisplayUnit
  horizontalAxisSmallestLabeledValue : ℝ
  horizontalAxisLargestLabeledValue : ℝ
  verticalAxisSmallestLabeledValue : ℝ
  verticalAxisLargestLabeledValue : ℝ
  linePoints : Set PhotoelectricPlotPoint
  lineColor : GraphLineColor
  lineTrend : GraphLineTrend
  straightLineShown : Bool

/-! ## Photoelectric experiment and governing law -/

/-!
The two reference frequencies name the physical measurements corresponding to
the readable graph points.  The experimental Planck constant is an unknown
physical parameter, while the electron charge magnitude and work function are
independent physical inputs to the Einstein photoelectric equation.
-/
structure PhotoelectricExperiment where
  measuredFrequencies : Set FrequencyQuantity
  stoppingPotentialAt : FrequencyQuantity → ElectricPotentialQuantity
  lowerReferenceFrequency : FrequencyQuantity
  upperReferenceFrequency : FrequencyQuantity
  electronChargeMagnitude : ChargeMagnitudeQuantity
  workFunction : DimEnergy
  experimentalPlanckConstant : PlanckConstantQuantity
  figure : PhotoelectricStoppingPotentialGraph

/-- The scalar plot coordinate associated with a measured physical frequency. -/
def plottedMeasurement
    (experiment : PhotoelectricExperiment)
    (frequency : FrequencyQuantity) : PhotoelectricPlotPoint where
  frequencyInTenToFifteenthHertz :=
    frequencyInHertz frequency / 1e15
  stoppingPotentialInVolts :=
    electricPotentialInVolts (experiment.stoppingPotentialAt frequency)

/-!
Axis assignments, labels, qualitative line geometry, and the two clear
reference points read from the primary image.  The auxiliary caption's
approximate horizontal intercept `0.6` is not used because the raster itself
clearly places the intercept at the tick labeled `1`.
-/
def MatchesPrimaryPhotoelectricGraph
    (experiment : PhotoelectricExperiment) : Prop :=
  let lowerPoint : PhotoelectricPlotPoint := ⟨1, 0⟩
  let upperPoint : PhotoelectricPlotPoint := ⟨3, 8⟩
  experiment.figure.horizontalAxis = .incidentFrequency ∧
    experiment.figure.verticalAxis = .stoppingPotential ∧
    experiment.figure.axisUnit .incidentFrequency = .tenToFifteenthHertz ∧
    experiment.figure.axisUnit .stoppingPotential = .volt ∧
    experiment.figure.horizontalAxisSmallestLabeledValue = 0 ∧
    experiment.figure.horizontalAxisLargestLabeledValue = 3 ∧
    experiment.figure.verticalAxisSmallestLabeledValue = 0 ∧
    experiment.figure.verticalAxisLargestLabeledValue = 8 ∧
    experiment.figure.lineColor = .green ∧
    experiment.figure.lineTrend = .increasing ∧
    experiment.figure.straightLineShown = true ∧
    lowerPoint ∈ experiment.figure.linePoints ∧
    upperPoint ∈ experiment.figure.linePoints ∧
    experiment.lowerReferenceFrequency ∈ experiment.measuredFrequencies ∧
    experiment.upperReferenceFrequency ∈ experiment.measuredFrequencies ∧
    frequencyInHertz experiment.lowerReferenceFrequency = 1e15 ∧
    frequencyInHertz experiment.upperReferenceFrequency = 3e15 ∧
    electricPotentialInVolts
        (experiment.stoppingPotentialAt experiment.lowerReferenceFrequency) = 0 ∧
    electricPotentialInVolts
        (experiment.stoppingPotentialAt experiment.upperReferenceFrequency) = 8 ∧
    plottedMeasurement experiment experiment.lowerReferenceFrequency = lowerPoint ∧
    plottedMeasurement experiment experiment.upperReferenceFrequency = upperPoint ∧
    (∀ frequency, frequency ∈ experiment.measuredFrequencies →
      plottedMeasurement experiment frequency ∈ experiment.figure.linePoints)

/-- Positivity conditions for the physical parameters of the experiment. -/
def HasPhysicalPhotoelectricParameters
    (experiment : PhotoelectricExperiment) : Prop :=
  0 < chargeMagnitudeInCoulombs experiment.electronChargeMagnitude ∧
    0 ≤ energyInJoules experiment.workFunction ∧
    0 < actionInJouleSeconds experiment.experimentalPlanckConstant

/-!
The Einstein photoelectric equation at every measured frequency:

`e V_stop = h f - phi`.

All terms are SI scalar readouts of dimensionally typed physical quantities,
so each side represents an energy in joules.  This governing law contains no
numerical value for the unknown experimental Planck constant.
-/
def SatisfiesEinsteinPhotoelectricEquation
    (experiment : PhotoelectricExperiment) : Prop :=
  ∀ frequency, frequency ∈ experiment.measuredFrequencies →
    chargeMagnitudeInCoulombs experiment.electronChargeMagnitude *
        electricPotentialInVolts (experiment.stoppingPotentialAt frequency) =
      actionInJouleSeconds experiment.experimentalPlanckConstant *
          frequencyInHertz frequency -
        energyInJoules experiment.workFunction

/-!
The two-significant-figure elementary-charge calibration implicit in the
recorded multiple-choice computation.  The exact SI charge would change only
digits beyond the precision supported by the plotted readouts.
-/
def UsesTextbookElementaryChargeCalibration
    (experiment : PhotoelectricExperiment) : Prop :=
  chargeMagnitudeInCoulombs experiment.electronChargeMagnitude = 1.6e-19

/-! ## Displayed answer choices -/

/-- Labels of the four answer choices in the problem statement. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Planck-constant readout printed beside each choice, in joule-seconds. -/
def answerPlanckConstantInJouleSeconds : AnswerChoice → ℝ
  | .A => 6.8e-34
  | .B => 3.2e-34
  | .C => 6.4e-34
  | .D => 7.4e-34

/-!
The two image readouts determine the stopping-potential-versus-frequency
slope `8 V / (2 * 10^15 Hz) = 4 * 10^-15 V s`.
-/
def stoppingPotentialSlopeInVoltSeconds
    (experiment : PhotoelectricExperiment) : ℝ :=
  (electricPotentialInVolts
        (experiment.stoppingPotentialAt experiment.upperReferenceFrequency) -
      electricPotentialInVolts
        (experiment.stoppingPotentialAt experiment.lowerReferenceFrequency)) /
    (frequencyInHertz experiment.upperReferenceFrequency -
      frequencyInHertz experiment.lowerReferenceFrequency)

/-- The physical slope derived solely from the two primary-image points. -/
lemma stoppingPotentialSlope_from_primary_graph
    (experiment : PhotoelectricExperiment)
    (h_figure : MatchesPrimaryPhotoelectricGraph experiment) :
    stoppingPotentialSlopeInVoltSeconds experiment = 4e-15 := by
  rcases h_figure with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h_lower_frequency,
      h_upper_frequency, h_lower_potential, h_upper_potential, _, _, _⟩
  unfold stoppingPotentialSlopeInVoltSeconds
  rw [h_lower_frequency, h_upper_frequency, h_lower_potential, h_upper_potential]
  norm_num

/-!
Subtracting the Einstein equation at the two graph points eliminates the work
function.  Multiplying the measured slope by the calibrated electron charge
gives `h = 6.4 * 10^-34 J s`, the recorded answer choice C.

This formalizes blueprint label `thm:physics:phyx_mini_0499:target`.
-/
theorem problem_phyx_mini_0499
    (experiment : PhotoelectricExperiment)
    (h_figure : MatchesPrimaryPhotoelectricGraph experiment)
    (h_physical : HasPhysicalPhotoelectricParameters experiment)
    (h_photoelectric : SatisfiesEinsteinPhotoelectricEquation experiment)
    (h_charge : UsesTextbookElementaryChargeCalibration experiment) :
    actionInJouleSeconds experiment.experimentalPlanckConstant = 6.4e-34 ∧
      actionInJouleSeconds experiment.experimentalPlanckConstant =
        answerPlanckConstantInJouleSeconds .C := by
  rcases h_figure with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h_lower_measured,
      h_upper_measured, h_lower_frequency, h_upper_frequency,
      h_lower_potential, h_upper_potential, _, _, _⟩
  have h_lower_equation :=
    h_photoelectric experiment.lowerReferenceFrequency h_lower_measured
  have h_upper_equation :=
    h_photoelectric experiment.upperReferenceFrequency h_upper_measured
  rw [h_charge, h_lower_potential, h_lower_frequency] at h_lower_equation
  rw [h_charge, h_upper_potential, h_upper_frequency] at h_upper_equation
  have h_planck :
      actionInJouleSeconds experiment.experimentalPlanckConstant = 6.4e-34 := by
    norm_num at h_lower_equation h_upper_equation ⊢
    linarith
  exact
    ⟨h_planck,
      by simpa [answerPlanckConstantInJouleSeconds] using h_planck⟩

end PhyXMiniProblems.ProblemPhyXMini0499
