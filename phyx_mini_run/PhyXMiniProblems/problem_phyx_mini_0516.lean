import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0516

open Dimension
open scoped BigOperators

/-!
# Planck's constant from a stopping-potential table

The primary figure is a two-column table of six measured wavelengths and
stopping potentials.  The requested graph uses incident-light frequency on
the horizontal axis and stopping potential on the vertical axis.  Frequencies
are obtained from `c = lambda * f`, and the slope of a least-squares line
through the plotted readouts is interpreted using Einstein's photoelectric
equation `e V_stop = h f - phi`.

The table entries have only two decimal places and are not exactly collinear.
Accordingly, the final statement says that the inferred value agrees with
`6.58 * 10^-34 J s` at the precision displayed by the answer choices; it does
not turn the rounded answer into an exact physical equality.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- The MLTQ dimension of energy. -/
def energyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Electric potential has dimension energy per charge. -/
def electricPotentialDimension : Dimension :=
  energyDimension * C𝓭⁻¹

/-- Planck's constant has the dimension of action, energy times time. -/
def actionDimension : Dimension :=
  energyDimension * T𝓭

/-- A nonnegative, unit-independent physical wavelength. -/
abbrev WavelengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical frequency. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A signed, unit-independent electric potential. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- A nonnegative physical magnitude of electric charge. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative physical energy. -/
abbrev EnergyQuantity : Type :=
  Dimensionful (WithDim energyDimension NNReal)

/-- A nonnegative physical value of Planck's constant. -/
abbrev PlanckConstantQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- Coherent-SI readout of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of a signed dimensionful quantity. -/
def signedSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Read a wavelength in a chosen length unit. -/
def wavelengthReadout
    (unit : LengthUnit) (wavelength : WavelengthQuantity) : ℝ :=
  ((wavelength {UnitChoices.SI with length := unit}).val : ℝ)

/-- Wavelength readout in metres. -/
def wavelengthInMeters (wavelength : WavelengthQuantity) : ℝ :=
  wavelengthReadout LengthUnit.meters wavelength

/-- Wavelength readout in nanometres, as printed in the table. -/
def wavelengthInNanometers (wavelength : WavelengthQuantity) : ℝ :=
  wavelengthReadout LengthUnit.nanometers wavelength

/-- Incident-light frequency readout in hertz. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  nonnegativeSIReadout frequency

/-- Stopping-potential readout in volts. -/
def stoppingPotentialInVolts
    (potential : ElectricPotentialQuantity) : ℝ :=
  signedSIReadout potential

/-- Speed readout in metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Charge-magnitude readout in coulombs. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout charge

/-- Energy readout in joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  nonnegativeSIReadout energy

/-- Planck-constant readout in joule-seconds. -/
def planckConstantInJouleSeconds
    (constant : PlanckConstantQuantity) : ℝ :=
  nonnegativeSIReadout constant

/-! ## Primary table, requested graph, and experimental roles -/

/-- The six rows shown in the supplied table, from top to bottom. -/
inductive MeasurementRow where
  | row366
  | row405
  | row436
  | row492
  | row546
  | row579
  deriving DecidableEq, Fintype, Repr

/-- The two columns visible in the primary figure. -/
inductive TableColumn where
  | wavelength
  | stoppingPotential
  deriving DecidableEq, Fintype, Repr

/-- Literal physical roles and unit annotations printed in the table header. -/
inductive TableColumnLabel where
  | wavelengthNanometers
  | stoppingPotentialVolts
  deriving DecidableEq, Repr

/-- The two axes of the graph requested in the prose. -/
inductive PlotAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical quantity assigned to each requested plot axis. -/
inductive PlotAxisRole where
  | incidentLightFrequency
  | stoppingPotential
  deriving DecidableEq, Repr

/-- Unit annotation for each requested plot axis. -/
inductive PlotAxisUnit where
  | hertz
  | volts
  deriving DecidableEq, Repr

/-- The physical process taking place at the illuminated surface. -/
inductive QuantumProcess where
  | photoelectricEmission
  | other
  deriving DecidableEq, Repr

/-- The primary two-column figure, with dimensionful quantities in each row. -/
structure StoppingPotentialTableFigure where
  columnLabel : TableColumn → TableColumnLabel
  wavelengthAt : MeasurementRow → WavelengthQuantity
  stoppingPotentialAt : MeasurementRow → ElectricPotentialQuantity

/-- The frequency-versus-stopping-potential graph requested by the problem. -/
structure FrequencyStoppingPotentialPlot where
  axisRole : PlotAxis → PlotAxisRole
  axisUnit : PlotAxis → PlotAxisUnit
  plottedFrequencyAt : MeasurementRow → FrequencyQuantity
  plottedStoppingPotentialAt : MeasurementRow → ElectricPotentialQuantity

/-!
Independent quantities in the photoelectric experiment.  The Planck constant
and work function are fields, not definitions of an answer choice.  Their
connection to the graph is imposed only by the general physical laws below.
-/
structure PhotoelectricExperiment where
  process : QuantumProcess
  table : StoppingPotentialTableFigure
  plot : FrequencyStoppingPotentialPlot
  incidentFrequencyAt : MeasurementRow → FrequencyQuantity
  vacuumLightSpeed : DimSpeed
  electronChargeMagnitude : ChargeMagnitudeQuantity
  planckConstant : PlanckConstantQuantity
  workFunction : EnergyQuantity

/-! ## Problem and figure data -/

/-- Nanometre number printed in a given table row. -/
def displayedWavelengthInNanometers : MeasurementRow → ℝ
  | .row366 => 366
  | .row405 => 405
  | .row436 => 436
  | .row492 => 492
  | .row546 => 546
  | .row579 => 579

/-- Volt number printed in a given table row. -/
def displayedStoppingPotentialInVolts : MeasurementRow → ℝ
  | .row366 => 1.48
  | .row405 => 1.15
  | .row436 => 0.93
  | .row492 => 0.62
  | .row546 => 0.36
  | .row579 => 0.24

/-- The prose identifies the experiment as photoelectric emission. -/
structure MatchesPhotoelectricScenario
    (setup : PhotoelectricExperiment) : Prop where
  processIsPhotoelectric : setup.process = .photoelectricEmission

/-!
Direct transcription of the primary bitmap.  These hypotheses give only the
two printed headers and the six measured row values; they contain no
frequency, fitted slope, Planck constant, or answer choice.
-/
structure MatchesSuppliedStoppingPotentialTable
    (table : StoppingPotentialTableFigure) : Prop where
  wavelengthColumnHeader :
    table.columnLabel .wavelength = .wavelengthNanometers
  stoppingPotentialColumnHeader :
    table.columnLabel .stoppingPotential = .stoppingPotentialVolts
  wavelengthReadout : ∀ row,
    wavelengthInNanometers (table.wavelengthAt row) =
      displayedWavelengthInNanometers row
  stoppingPotentialReadout : ∀ row,
    stoppingPotentialInVolts (table.stoppingPotentialAt row) =
      displayedStoppingPotentialInVolts row

/-!
The requested graph places the frequency derived for every table row on the
horizontal axis and that row's observed stopping potential on the vertical
axis.  This carries no numerical slope or fitted value.
-/
structure MatchesRequestedFrequencyPlot
    (setup : PhotoelectricExperiment) : Prop where
  horizontalAxisRole :
    setup.plot.axisRole .horizontal = .incidentLightFrequency
  verticalAxisRole :
    setup.plot.axisRole .vertical = .stoppingPotential
  horizontalAxisUnit : setup.plot.axisUnit .horizontal = .hertz
  verticalAxisUnit : setup.plot.axisUnit .vertical = .volts
  plottedFrequency : ∀ row,
    setup.plot.plottedFrequencyAt row = setup.incidentFrequencyAt row
  plottedStoppingPotential : ∀ row,
    setup.plot.plottedStoppingPotentialAt row =
      setup.table.stoppingPotentialAt row

/-!
The rounded reference values conventionally used in this multiple-choice
calculation.  They are independent calibrations, not the requested value of
Planck's constant.  Using Physlib's exact `299792458 m/s` and exact elementary
charge would change the last displayed digit of this dataset's estimate.
-/
structure UsesRoundedReferenceValues
    (setup : PhotoelectricExperiment) : Prop where
  vacuumLightSpeedCalibration :
    speedInMetersPerSecond setup.vacuumLightSpeed =
      (3 : ℝ) * 10 ^ (8 : ℕ)
  knownElectronChargeCalibration :
    chargeMagnitudeInCoulombs setup.electronChargeMagnitude =
      (1.6 : ℝ) * 10 ^ (-19 : ℤ)

/-- Positivity conditions selecting a physically meaningful experiment. -/
structure HasPhysicalPhotoelectricParameters
    (setup : PhotoelectricExperiment) : Prop where
  positiveWavelengths : ∀ row,
    0 < wavelengthInMeters (setup.table.wavelengthAt row)
  positiveFrequencies : ∀ row,
    0 < frequencyInHertz (setup.incidentFrequencyAt row)
  positiveLightSpeed : 0 < speedInMetersPerSecond setup.vacuumLightSpeed
  positiveElectronCharge :
    0 < chargeMagnitudeInCoulombs setup.electronChargeMagnitude
  positivePlanckConstant :
    0 < planckConstantInJouleSeconds setup.planckConstant
  nonnegativeWorkFunction : 0 ≤ energyInJoules setup.workFunction

/-! ## Least-squares graph and governing laws -/

/-- Arithmetic mean of the six plotted frequencies, in hertz. -/
def meanIncidentFrequencyInHertz (setup : PhotoelectricExperiment) : ℝ :=
  (∑ row : MeasurementRow,
      frequencyInHertz (setup.incidentFrequencyAt row)) / 6

/-- Arithmetic mean of the six measured stopping potentials, in volts. -/
def meanStoppingPotentialInVolts (setup : PhotoelectricExperiment) : ℝ :=
  (∑ row : MeasurementRow,
      stoppingPotentialInVolts (setup.table.stoppingPotentialAt row)) / 6

/-!
Least-squares slope of stopping potential against frequency.  Its scalar unit
is volts per hertz, equivalently volt-seconds.
-/
def fittedStoppingPotentialSlope (setup : PhotoelectricExperiment) : ℝ :=
  let meanFrequency := meanIncidentFrequencyInHertz setup
  let meanPotential := meanStoppingPotentialInVolts setup
  (∑ row : MeasurementRow,
      (frequencyInHertz (setup.incidentFrequencyAt row) - meanFrequency) *
        (stoppingPotentialInVolts
            (setup.table.stoppingPotentialAt row) - meanPotential)) /
    (∑ row : MeasurementRow,
      (frequencyInHertz (setup.incidentFrequencyAt row) - meanFrequency) ^ 2)

/-- The least-squares line evaluated at a frequency readout in hertz. -/
def fittedStoppingPotentialInVolts
    (setup : PhotoelectricExperiment) (frequencyHertz : ℝ) : ℝ :=
  meanStoppingPotentialInVolts setup +
    fittedStoppingPotentialSlope setup *
      (frequencyHertz - meanIncidentFrequencyInHertz setup)

/-!
The two physical laws used by the intended graph method:

* every incident wavelength and frequency obey `lambda * f = c` in vacuum;
* the least-squares trend line is interpreted by Einstein's photoelectric
  equation `e V_stop = h f - phi`.

Neither law contains a numerical slope, a numerical Planck constant, or an
answer label.
-/
structure SatisfiesPhotoelectricGraphLaws
    (setup : PhotoelectricExperiment) : Prop where
  vacuumWavelengthFrequencyLaw : ∀ row,
    wavelengthInMeters (setup.table.wavelengthAt row) *
        frequencyInHertz (setup.incidentFrequencyAt row) =
      speedInMetersPerSecond setup.vacuumLightSpeed
  einsteinEquationForFittedLine : ∀ frequencyHertz : ℝ,
    chargeMagnitudeInCoulombs setup.electronChargeMagnitude *
        fittedStoppingPotentialInVolts setup frequencyHertz =
      planckConstantInJouleSeconds setup.planckConstant * frequencyHertz -
        energyInJoules setup.workFunction

/-!
Einstein's equation identifies the voltage-frequency slope as `h / e`.
This is a general intermediate relation and does not select any displayed
number.
-/
lemma planck_constant_eq_charge_mul_fitted_slope
    (setup : PhotoelectricExperiment)
    (hphysical : HasPhysicalPhotoelectricParameters setup)
    (hlaws : SatisfiesPhotoelectricGraphLaws setup) :
    planckConstantInJouleSeconds setup.planckConstant =
      chargeMagnitudeInCoulombs setup.electronChargeMagnitude *
        fittedStoppingPotentialSlope setup := by
  have hzero := hlaws.einsteinEquationForFittedLine 0
  have hone := hlaws.einsteinEquationForFittedLine 1
  simp only [fittedStoppingPotentialInVolts] at hzero hone
  nlinarith [hphysical.positiveElectronCharge]

/-! ## Displayed answer values and current target -/

/-- Labels of the four answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Planck-constant value printed beside each choice, in joule-seconds. -/
def displayedPlanckConstantInJouleSeconds : AnswerChoice → ℝ
  | .A => (6.71 : ℝ) * 10 ^ (-34 : ℤ)
  | .B => (6.50 : ℝ) * 10 ^ (-34 : ℤ)
  | .C => (6.63 : ℝ) * 10 ^ (-34 : ℤ)
  | .D => (6.58 : ℝ) * 10 ^ (-34 : ℤ)

/-- Half of one unit in the final displayed decimal place of the choices. -/
def answerHalfUnitInJouleSeconds : ℝ :=
  (0.005 : ℝ) * 10 ^ (-34 : ℤ)

/-!
Agreement at the three-significant-figure precision used by all four choices.
-/
def AgreesAtDisplayedPrecision (value displayed : ℝ) : Prop :=
  |value - displayed| < answerHalfUnitInJouleSeconds

/-- A modeled Planck constant agrees with a displayed answer choice. -/
def MatchesAnswerChoice
    (setup : PhotoelectricExperiment) (choice : AnswerChoice) : Prop :=
  AgreesAtDisplayedPrecision
    (planckConstantInJouleSeconds setup.planckConstant)
    (displayedPlanckConstantInJouleSeconds choice)

/-- Answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
The six table rows, `c = 3.00 * 10^8 m/s`, and
`e = 1.60 * 10^-19 C` give a least-squares estimate approximately
`6.57986 * 10^-34 J s`.  Thus the value at the displayed precision is
`6.58 * 10^-34 J s`, uniquely choice D.

This formalizes `thm:physics:phyx_mini_0516:target`.
-/
theorem problem_phyx_mini_0516
    (setup : PhotoelectricExperiment)
    (hscenario : MatchesPhotoelectricScenario setup)
    (hphysical : HasPhysicalPhotoelectricParameters setup)
    (htable : MatchesSuppliedStoppingPotentialTable setup.table)
    (hplot : MatchesRequestedFrequencyPlot setup)
    (hreference : UsesRoundedReferenceValues setup)
    (hlaws : SatisfiesPhotoelectricGraphLaws setup) :
    AgreesAtDisplayedPrecision
        (planckConstantInJouleSeconds setup.planckConstant)
        ((6.58 : ℝ) * 10 ^ (-34 : ℤ)) ∧
      MatchesAnswerChoice setup recordedDatasetAnswer ∧
      (∀ choice, MatchesAnswerChoice setup choice → choice = .D) := by
  have nanometers_eq_meters (wavelength : WavelengthQuantity) :
      wavelengthInNanometers wavelength =
        1000000000 * wavelengthInMeters wavelength := by
    have h := wavelength.2
      ({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices)
      ({ UnitChoices.SI with length := LengthUnit.nanometers } : UnitChoices)
    have hv := congrArg (fun quantity => ((quantity.val : NNReal) : ℝ)) h
    norm_num [wavelengthInNanometers, wavelengthInMeters, wavelengthReadout,
      UnitChoices.dimScale, LengthUnit.nanometers, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, Dimension.L𝓭,
      NNReal.smul_def] at hv ⊢
    exact hv
  have wavelength_meters (row : MeasurementRow) :
      wavelengthInMeters (setup.table.wavelengthAt row) =
        displayedWavelengthInNanometers row / 1000000000 := by
    have hnm := htable.wavelengthReadout row
    have hconversion := nanometers_eq_meters (setup.table.wavelengthAt row)
    nlinarith
  have frequency_hertz (row : MeasurementRow) :
      frequencyInHertz (setup.incidentFrequencyAt row) =
        300000000000000000 / displayedWavelengthInNanometers row := by
    have hwavelength := wavelength_meters row
    have hlaw := hlaws.vacuumWavelengthFrequencyLaw row
    rw [hwavelength, hreference.vacuumLightSpeedCalibration] at hlaw
    cases row <;>
      norm_num [displayedWavelengthInNanometers] at hlaw ⊢ <;>
      nlinarith
  have measurement_rows :
      (Finset.univ : Finset MeasurementRow) =
        {.row366, .row405, .row436, .row492, .row546, .row579} := by
    decide
  have hslope :
      fittedStoppingPotentialSlope setup =
        278242157280470045475267 /
          67659078620283277055000000000000000000 := by
    simp [fittedStoppingPotentialSlope, meanIncidentFrequencyInHertz,
      meanStoppingPotentialInVolts, frequency_hertz,
      htable.stoppingPotentialReadout, displayedWavelengthInNanometers,
      displayedStoppingPotentialInVolts, measurement_rows]
    norm_num
  have hplanck :=
    planck_constant_eq_charge_mul_fitted_slope setup hphysical hlaws
  rw [hreference.knownElectronChargeCalibration, hslope] at hplanck
  norm_num at hplanck
  have hagreement :
      AgreesAtDisplayedPrecision
        (planckConstantInJouleSeconds setup.planckConstant)
        ((6.58 : ℝ) * 10 ^ (-34 : ℤ)) := by
    norm_num [AgreesAtDisplayedPrecision, answerHalfUnitInJouleSeconds,
      hplanck, abs_of_nonneg, abs_of_neg]
  refine ⟨hagreement, ?_, ?_⟩
  · simpa [MatchesAnswerChoice, recordedDatasetAnswer,
      displayedPlanckConstantInJouleSeconds] using hagreement
  · intro choice hchoice
    cases choice with
    | A =>
        norm_num [MatchesAnswerChoice, AgreesAtDisplayedPrecision,
          displayedPlanckConstantInJouleSeconds, answerHalfUnitInJouleSeconds,
          hplanck, abs_of_nonneg, abs_of_neg] at hchoice
    | B =>
        norm_num [MatchesAnswerChoice, AgreesAtDisplayedPrecision,
          displayedPlanckConstantInJouleSeconds, answerHalfUnitInJouleSeconds,
          hplanck, abs_of_nonneg, abs_of_neg] at hchoice
    | C =>
        norm_num [MatchesAnswerChoice, AgreesAtDisplayedPrecision,
          displayedPlanckConstantInJouleSeconds, answerHalfUnitInJouleSeconds,
          hplanck, abs_of_nonneg, abs_of_neg] at hchoice
    | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0516
