import Mathlib
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0515

open Dimension

/-!
# Photoelectric work function from a stopping-potential graph

The supplied graph plots stopping potential against the frequency of light
incident on a metal surface.  Its vertical axis is printed in volts, while the
horizontal frequency numbers are interpreted in units of `10^15 Hz`.  The
plotted line reaches zero stopping potential at approximately `1.25` on that
horizontal scale.

Frequency, potential difference, charge, action, and energy are represented by
unit-independent Physlib quantities.  Real numbers below are only calibrated
readouts, graph coordinates, and displayed multiple-choice values.  In
particular, the metal's work function is an independent physical quantity; it
is not defined to be the recorded answer.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A physical cyclic frequency, with inverse-time dimension. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- A physical electric-charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- The dimension `M L² T⁻² C⁻¹` of an electric potential difference. -/
def potentialDifferenceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A physical stopping-potential difference. -/
abbrev PotentialDifferenceQuantity : Type :=
  Dimensionful (WithDim potentialDifferenceDimension ℝ)

/-- The dimension `M L² T⁻¹` of action. -/
def actionDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A physical action, used here for the ordinary Planck constant `h`. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension ℝ)

/-- SI readout of a frequency in hertz. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  (frequency UnitChoices.SI).val

/-- SI readout of a charge magnitude in coulombs. -/
def chargeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- SI readout of a potential difference in volts. -/
def potentialDifferenceInVolts
    (potentialDifference : PotentialDifferenceQuantity) : ℝ :=
  (potentialDifference UnitChoices.SI).val

/-- SI readout of an action in joule-seconds. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  (action UnitChoices.SI).val

/-- SI readout of a Physlib energy in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-!
Read an energy in electron-volts.  Physlib's `DimEnergy.electronVolt` is the
dimensionful energy corresponding to one electron-volt, so this is a ratio of
two energy readouts rather than a scalar alias for energy.
-/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / energyInJoules DimEnergy.electronVolt

/-! ## Physical roles and graph labels -/

/-- The two axes shown in the supplied graph. -/
inductive PlotAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical meaning assigned to each graph axis. -/
inductive PlotAxisRole where
  | incidentLightFrequency
  | stoppingPotential
  deriving DecidableEq, Repr

/-!
The directly visible features of the supplied graph.  Coordinates are the
dimensionless numbers printed on the axes.  The horizontal physical scale is
connected to hertz separately in `MatchesSuppliedStoppingPotentialGraph`.
-/
structure StoppingPotentialFigure where
  axisRole : PlotAxis → PlotAxisRole
  printedAxisLabel : PlotAxis → Option String
  smallestPrintedTick : PlotAxis → ℝ
  largestPrintedTick : PlotAxis → ℝ
  printedMajorTickIncrement : PlotAxis → ℝ
  thresholdHorizontalCoordinate : ℝ
  thresholdVerticalCoordinate : ℝ
  hasRectangularGrid : Bool
  plottedTraceIsStraight : Bool
  plottedTraceRisesToRight : Bool

/-!
The physical objects and unknown quantities in the photoelectric experiment.
The work function is a field, not a definition in terms of an answer choice.
-/
structure PhotoelectricSetup where
  workFunction : DimEnergy
  ordinaryPlanckAction : ActionQuantity
  electronChargeMagnitude : ChargeMagnitudeQuantity
  thresholdFrequency : FrequencyQuantity
  stoppingPotentialAt : FrequencyQuantity → PotentialDifferenceQuantity
  figure : StoppingPotentialFigure
  targetIsMetalSurface : Bool
  incidentLightFallsOnSurface : Bool

/-! ## Scenario, figure data, standard data, and governing law -/

/-- The qualitative physical scenario stated in the problem. -/
structure MatchesPhotoelectricScenario (setup : PhotoelectricSetup) : Prop where
  metalSurface : setup.targetIsMetalSurface = true
  illuminatedSurface : setup.incidentLightFallsOnSurface = true

/-!
Axis labels, tick labels, qualitative trace shape, and the threshold intercept
read from the primary image.  The graph's prose identifies the unlabeled
horizontal axis as frequency; its numerical coordinate is calibrated in units
of `10^15 Hz`.  None of these fields states the work function or an answer
choice.
-/
structure MatchesSuppliedStoppingPotentialGraph
    (setup : PhotoelectricSetup) : Prop where
  horizontalRole :
    setup.figure.axisRole .horizontal = .incidentLightFrequency
  verticalRole : setup.figure.axisRole .vertical = .stoppingPotential
  horizontalAxisHasNoPrintedLabel :
    setup.figure.printedAxisLabel .horizontal = none
  verticalAxisPrintedLabel :
    setup.figure.printedAxisLabel .vertical = some "Stopping potential (V)"
  horizontalFirstPrintedTick :
    setup.figure.smallestPrintedTick .horizontal = 0
  horizontalLastPrintedTick :
    setup.figure.largestPrintedTick .horizontal = 3
  horizontalPrintedTickStep :
    setup.figure.printedMajorTickIncrement .horizontal = 1 / 2
  verticalFirstPrintedTick :
    setup.figure.smallestPrintedTick .vertical = 0
  verticalLastPrintedTick :
    setup.figure.largestPrintedTick .vertical = 7
  verticalPrintedTickStep :
    setup.figure.printedMajorTickIncrement .vertical = 1
  thresholdHorizontalReadout :
    setup.figure.thresholdHorizontalCoordinate = 5 / 4
  thresholdVerticalReadout :
    setup.figure.thresholdVerticalCoordinate = 0
  thresholdFrequencyCalibration :
    frequencyInHertz setup.thresholdFrequency =
      setup.figure.thresholdHorizontalCoordinate * 10 ^ 15
  plottedPotentialAtThreshold :
    potentialDifferenceInVolts
        (setup.stoppingPotentialAt setup.thresholdFrequency) =
      setup.figure.thresholdVerticalCoordinate
  rectangularGrid : setup.figure.hasRectangularGrid = true
  straightTrace : setup.figure.plottedTraceIsStraight = true
  traceRisesWithFrequency : setup.figure.plottedTraceRisesToRight = true

/-!
Standard SI calibration data.  `ordinaryPlanckAction` uses the exact SI value
of `h`, and the charge magnitude is the elementary charge.  These reference
values do not mention the unknown work function or the displayed answers.
-/
structure UsesStandardPhotoelectricReferenceData
    (setup : PhotoelectricSetup) : Prop where
  ordinaryPlanckConstantReadout :
    actionInJouleSeconds setup.ordinaryPlanckAction = 6.62607015e-34
  elementaryChargeReadout :
    chargeInCoulombs setup.electronChargeMagnitude = 1.602176634e-19

/-- Positivity conditions selecting a physically meaningful experiment. -/
structure HasPhysicalPhotoelectricParameters
    (setup : PhotoelectricSetup) : Prop where
  positiveWorkFunction : 0 < energyInJoules setup.workFunction
  positivePlanckAction :
    0 < actionInJouleSeconds setup.ordinaryPlanckAction
  positiveElectronCharge :
    0 < chargeInCoulombs setup.electronChargeMagnitude
  positiveThresholdFrequency :
    0 < frequencyInHertz setup.thresholdFrequency
  nonnegativeStoppingPotentialAboveThreshold :
    ∀ frequency,
      frequencyInHertz setup.thresholdFrequency ≤ frequencyInHertz frequency →
        0 ≤ potentialDifferenceInVolts (setup.stoppingPotentialAt frequency)

/-!
Einstein's photoelectric equation

`e V_s = h f - φ`

for frequencies at or above threshold.  It is a general governing relation
between the stopping-potential trace and the independent work-function field;
it does not supply the numerical answer requested by the problem.
-/
structure SatisfiesEinsteinPhotoelectricLaw
    (setup : PhotoelectricSetup) : Prop where
  photoelectricEquation : ∀ frequency,
    frequencyInHertz setup.thresholdFrequency ≤ frequencyInHertz frequency →
      chargeInCoulombs setup.electronChargeMagnitude *
          potentialDifferenceInVolts (setup.stoppingPotentialAt frequency) =
        actionInJouleSeconds setup.ordinaryPlanckAction *
            frequencyInHertz frequency -
          energyInJoules setup.workFunction

/-! ## Displayed choices and current target -/

/-- Labels attached to the four displayed work-function choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The energy, in electron-volts, printed beside each answer label. -/
def displayedWorkFunctionInElectronVolts : AnswerChoice → ℝ
  | .A => 5.6
  | .B => 2.9
  | .C => 3.2
  | .D => 4.8

/-!
A displayed choice is best when its printed electron-volt value is at least as
close to the inferred work function as every other displayed value.  This
encodes the resolution of the graph-based multiple-choice question without
assuming that the physical work function was defined by a choice.
-/
def IsClosestDisplayedWorkFunction
    (workFunction : DimEnergy) (choice : AnswerChoice) : Prop :=
  ∀ alternative,
    |energyInElectronVolts workFunction -
        displayedWorkFunctionInElectronVolts choice| ≤
      |energyInElectronVolts workFunction -
        displayedWorkFunctionInElectronVolts alternative|

/-!
At the threshold, the zero stopping-potential readout and Einstein equation
imply `φ = h f₀`.  This is a derived physical relation, not a premise field.
-/
lemma workFunction_eq_planckAction_mul_thresholdFrequency
    (setup : PhotoelectricSetup)
    (hGraph : MatchesSuppliedStoppingPotentialGraph setup)
    (hLaw : SatisfiesEinsteinPhotoelectricLaw setup) :
    energyInJoules setup.workFunction =
      actionInJouleSeconds setup.ordinaryPlanckAction *
        frequencyInHertz setup.thresholdFrequency := by
  have hAtThreshold :=
    hLaw.photoelectricEquation setup.thresholdFrequency (le_refl _)
  rw [hGraph.plottedPotentialAtThreshold, hGraph.thresholdVerticalReadout] at hAtThreshold
  linarith

/-!
The threshold intercept and standard constants place the inferred work
function within `0.4 eV` of the displayed `4.8 eV` and make choice D the
closest of the four choices.  The exact energy relation is included alongside
the graph-resolution conclusion.
-/
theorem photoelectric_workFunction_matches_choiceD
    (setup : PhotoelectricSetup)
    (hScenario : MatchesPhotoelectricScenario setup)
    (hGraph : MatchesSuppliedStoppingPotentialGraph setup)
    (hReference : UsesStandardPhotoelectricReferenceData setup)
    (hPhysical : HasPhysicalPhotoelectricParameters setup)
    (hLaw : SatisfiesEinsteinPhotoelectricLaw setup) :
    energyInJoules setup.workFunction =
        actionInJouleSeconds setup.ordinaryPlanckAction *
          frequencyInHertz setup.thresholdFrequency ∧
      |energyInElectronVolts setup.workFunction -
          displayedWorkFunctionInElectronVolts .D| ≤ 2 / 5 ∧
      displayedWorkFunctionInElectronVolts .D = 4.8 ∧
      IsClosestDisplayedWorkFunction setup.workFunction .D := by
  have hExact :=
    workFunction_eq_planckAction_mul_thresholdFrequency setup hGraph hLaw
  have hElectronVoltJoules :
      energyInJoules DimEnergy.electronVolt = (1.602176634e-19 : ℝ) := by
    norm_num [energyInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply]
  have hWorkJoules :
      energyInJoules setup.workFunction =
        (6.62607015e-34 : ℝ) * ((5 / 4 : ℝ) * 10 ^ 15) := by
    rw [hExact, hReference.ordinaryPlanckConstantReadout,
      hGraph.thresholdFrequencyCalibration,
      hGraph.thresholdHorizontalReadout]
  constructor
  · exact hExact
  constructor
  · rw [energyInElectronVolts, hWorkJoules, hElectronVoltJoules]
    norm_num [displayedWorkFunctionInElectronVolts, abs_of_nonneg, abs_of_nonpos]
  constructor
  · norm_num [displayedWorkFunctionInElectronVolts]
  · unfold IsClosestDisplayedWorkFunction
    intro alternative
    cases alternative <;>
      rw [energyInElectronVolts, hWorkJoules, hElectronVoltJoules] <;>
      norm_num [displayedWorkFunctionInElectronVolts, abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0515
