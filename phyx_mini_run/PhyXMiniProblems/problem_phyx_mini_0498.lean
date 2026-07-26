import Mathlib
import Physlib.Electromagnetism.Charge.ChargeUnit
import Physlib.Units.WithDim.Basic
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0498

open Dimension

/-!
# Photoelectron rate and a stopping-potential graph

The supplied raster is a graph of stopping potential against incident-light
frequency. Its green line passes through the visible points
`(1 × 10¹⁵ Hz, 0 V)`, `(2 × 10¹⁵ Hz, 4 V)`, and
`(3 × 10¹⁵ Hz, 8 V)`. It contains no current axis or photoelectron-rate
readout.

Consequently, the raster determines photoelectric energy information but not
an emission count rate. In particular, it provides no photocurrent to insert
in the charge-rate law `I = e N`. The dataset's recorded answer
`6.25 × 10¹³ s⁻¹` is therefore retained as metadata only: it is not a
conclusion of the physical statement below.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The MLTQ dimension of energy. -/
def energyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Electric potential has the dimension energy per charge. -/
def electricPotentialDimension : Dimension :=
  energyDimension * C𝓭⁻¹

/-- Electric current has the dimension charge per time. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Planck's constant has the dimension energy times time. -/
def actionDimension : Dimension :=
  energyDimension * T𝓭

/-- A nonnegative physical frequency. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A signed physical stopping potential. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- A nonnegative physical magnitude of electric charge. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative physical electric current. -/
abbrev ElectricCurrentQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative number of emitted photoelectrons per unit time. -/
abbrev PhotoelectronRateQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative physical value of Planck's constant. -/
abbrev PlanckConstantQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- A physical work function, constrained to be nonnegative by the setup premise. -/
abbrev WorkFunctionQuantity : Type :=
  DimEnergy

/-- Coherent-SI readout of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of a signed dimensionful quantity. -/
def signedSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Frequency readout in hertz. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  nonnegativeSIReadout frequency

/-- Stopping-potential readout in volts. -/
def potentialInVolts (potential : ElectricPotentialQuantity) : ℝ :=
  signedSIReadout potential

/-- Charge-magnitude readout in coulombs. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout charge

/-- Electric-current readout in amperes. -/
def currentInAmperes (current : ElectricCurrentQuantity) : ℝ :=
  nonnegativeSIReadout current

/-- Photoelectron-rate readout in electrons per second. -/
def photoelectronRatePerSecond (rate : PhotoelectronRateQuantity) : ℝ :=
  nonnegativeSIReadout rate

/-- Planck-constant readout in joule-seconds. -/
def planckConstantInJouleSeconds (constant : PlanckConstantQuantity) : ℝ :=
  nonnegativeSIReadout constant

/-- Work-function readout in joules. -/
def workFunctionInJoules (workFunction : WorkFunctionQuantity) : ℝ :=
  signedSIReadout workFunction

/-!
Physlib represents an elementary charge as a charge *unit*. This scalar is
its exact magnitude relative to the Physlib coulomb unit.
-/
def physlibElementaryChargeInCoulombs : ℝ :=
  ((ChargeUnit.elementaryCharge / ChargeUnit.coulombs : NNReal) : ℝ)

/-! ## Figure axes, labels, and marked green-line points -/

/-- The two coordinate axes shown in the supplied raster. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical role assigned to each axis. -/
inductive AxisQuantity where
  | incidentLightFrequency
  | stoppingPotential
  deriving DecidableEq, Repr

/-- Unit annotation printed beside an axis. -/
inductive AxisUnit where
  | tenPowFifteenHertz
  | volts
  deriving DecidableEq, Repr

/-- Three unambiguous grid intersections on the green line. -/
inductive GreenLinePoint where
  | threshold
  | middle
  | upper
  deriving DecidableEq, Fintype, Repr

/-!
Physical quantities represented by the plotted green-line points, together
with the visible axis metadata. The Boolean fields record the absence of the
two readouts that would be needed for the question as written.
-/
structure StoppingPotentialFrequencyFigure where
  showsAxis : FigureAxis → Bool
  axisQuantity : FigureAxis → AxisQuantity
  axisUnit : FigureAxis → AxisUnit
  frequencyTickCoordinates : List ℝ
  stoppingPotentialTickCoordinates : List ℝ
  plottedFrequency : GreenLinePoint → FrequencyQuantity
  plottedStoppingPotential : GreenLinePoint → ElectricPotentialQuantity
  showsGreenLinePoint : GreenLinePoint → Bool
  containsPhotocurrentAxis : Bool
  containsPhotoelectronRateReadout : Bool

/-! ## Experiment data independent of the requested answer -/

/-- The physical process represented by the setup. -/
inductive QuantumProcess where
  | photoelectricEmission
  | other
  deriving DecidableEq, Repr

/-- Species emitted by the illuminated surface. -/
inductive EmittedParticle where
  | electron
  | other
  deriving DecidableEq, Repr

/-!
The experiment stores energy-side observables, charge/count-side observables,
and the supplied graph. Neither the requested scalar rate nor an answer
choice is a field.
-/
structure PhotoelectricExperiment where
  process : QuantumProcess
  emittedParticle : EmittedParticle
  stoppingPotentialAt : FrequencyQuantity → ElectricPotentialQuantity
  photoelectronRateAt : FrequencyQuantity → PhotoelectronRateQuantity
  photocurrentAt : FrequencyQuantity → ElectricCurrentQuantity
  operatingFrequency : FrequencyQuantity
  electronChargeMagnitude : ChargeMagnitudeQuantity
  planckConstant : PlanckConstantQuantity
  workFunction : WorkFunctionQuantity
  figure : StoppingPotentialFrequencyFigure

/-! ## Assumptions: scenario, primary-raster evidence, and governing laws -/

/-- The prose identifies the phenomenon and the emitted particles. -/
structure MatchesPhotoelectricScenario
    (setup : PhotoelectricExperiment) : Prop where
  processIsPhotoelectric : setup.process = .photoelectricEmission
  emittedParticlesAreElectrons : setup.emittedParticle = .electron

/-!
Evidence read directly from image 498. In particular, the line begins at
frequency coordinate `1`, not at the origin as claimed by the auxiliary
caption. No current or count-rate datum occurs in this structure.
-/
structure MatchesSuppliedStoppingPotentialFigure
    (setup : PhotoelectricExperiment) : Prop where
  bothAxesShown : ∀ axis, setup.figure.showsAxis axis = true
  horizontalAxisIsFrequency :
    setup.figure.axisQuantity .horizontal = .incidentLightFrequency
  verticalAxisIsStoppingPotential :
    setup.figure.axisQuantity .vertical = .stoppingPotential
  horizontalUnit :
    setup.figure.axisUnit .horizontal = .tenPowFifteenHertz
  verticalUnit : setup.figure.axisUnit .vertical = .volts
  frequencyTicks :
    setup.figure.frequencyTickCoordinates = [0, 1, 2, 3]
  stoppingPotentialTicks :
    setup.figure.stoppingPotentialTickCoordinates = [0, 2, 4, 6, 8]
  everyMarkedPointShown :
    ∀ point, setup.figure.showsGreenLinePoint point = true
  markedPointsRepresentExperiment : ∀ point,
    setup.stoppingPotentialAt (setup.figure.plottedFrequency point) =
      setup.figure.plottedStoppingPotential point
  thresholdFrequency :
    frequencyInHertz (setup.figure.plottedFrequency .threshold) =
      (1 : ℝ) * 10 ^ (15 : ℕ)
  middleFrequency :
    frequencyInHertz (setup.figure.plottedFrequency .middle) =
      (2 : ℝ) * 10 ^ (15 : ℕ)
  upperFrequency :
    frequencyInHertz (setup.figure.plottedFrequency .upper) =
      (3 : ℝ) * 10 ^ (15 : ℕ)
  thresholdPotential :
    potentialInVolts (setup.figure.plottedStoppingPotential .threshold) = 0
  middlePotential :
    potentialInVolts (setup.figure.plottedStoppingPotential .middle) = 4
  upperPotential :
    potentialInVolts (setup.figure.plottedStoppingPotential .upper) = 8
  noPhotocurrentAxis : setup.figure.containsPhotocurrentAxis = false
  noPhotoelectronRateReadout :
    setup.figure.containsPhotoelectronRateReadout = false

/-- Positivity conditions for the physical constants and operating light. -/
structure HasPhysicalPhotoelectricParameters
    (setup : PhotoelectricExperiment) : Prop where
  operatingFrequencyPositive :
    0 < frequencyInHertz setup.operatingFrequency
  electronChargeMagnitudePositive :
    0 < chargeMagnitudeInCoulombs setup.electronChargeMagnitude
  planckConstantPositive :
    0 < planckConstantInJouleSeconds setup.planckConstant
  workFunctionNonnegative :
    0 ≤ workFunctionInJoules setup.workFunction

/-!
The two governing laws needed to distinguish the graph's energy information
from rate information:

* Einstein's stopping-potential relation `e V_stop = h f - φ`, where a
  nonnegative stopping potential is defined;
* collected conventional photocurrent equals the elementary charge magnitude
  times the emitted-electron count rate.

Both laws are uniform relations and contain no numerical answer choice.
-/
structure SatisfiesPhotoelectricLaws
    (setup : PhotoelectricExperiment) : Prop where
  einsteinStoppingPotentialLaw : ∀ frequency,
    0 ≤ potentialInVolts (setup.stoppingPotentialAt frequency) →
      chargeMagnitudeInCoulombs setup.electronChargeMagnitude *
          potentialInVolts (setup.stoppingPotentialAt frequency) =
        planckConstantInJouleSeconds setup.planckConstant *
            frequencyInHertz frequency -
          workFunctionInJoules setup.workFunction
  photocurrentChargeRateLaw : ∀ frequency,
    currentInAmperes (setup.photocurrentAt frequency) =
      chargeMagnitudeInCoulombs setup.electronChargeMagnitude *
        photoelectronRatePerSecond (setup.photoelectronRateAt frequency)

/-! The emitted particles carry the exact Physlib elementary-charge magnitude. -/
structure UsesPhyslibElementaryCharge
    (setup : PhotoelectricExperiment) : Prop where
  chargeCalibration :
    chargeMagnitudeInCoulombs setup.electronChargeMagnitude =
      physlibElementaryChargeInCoulombs

/-! ## Answer metadata and formal conclusions -/

/-- Labels printed beside the four answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Photoelectron-rate value printed beside each answer label. -/
def displayedPhotoelectronRatePerSecond : AnswerChoice → ℝ
  | .A => (6.25 : ℝ) * 10 ^ (12 : ℕ)
  | .B => (6.25 : ℝ) * 10 ^ (14 : ℕ)
  | .C => (6.25 : ℝ) * 10 ^ (13 : ℕ)
  | .D => (6.25 : ℝ) * 10 ^ (16 : ℕ)

/-- The source dataset's recorded answer, retained only as metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
A hypothetical pair of nonnegative scalar readouts obeys the standard
collected-photocurrent law. This relation does not assert that the figure
contains either readout.
-/
def CompatibleCurrentRateReadouts
    (setup : PhotoelectricExperiment)
    (candidateCurrentInAmperes candidateRatePerSecond : ℝ) : Prop :=
  0 ≤ candidateCurrentInAmperes ∧
    0 ≤ candidateRatePerSecond ∧
    candidateCurrentInAmperes =
      chargeMagnitudeInCoulombs setup.electronChargeMagnitude *
        candidateRatePerSecond

/-!
A displayed rate is compatible with the unmeasured-current law when some
nonnegative photocurrent readout could accompany it. Compatibility is not a
claim that the displayed rate is the experiment's actual rate.
-/
def DisplayedRateHasCompatibleUnmeasuredCurrent
    (setup : PhotoelectricExperiment) (choice : AnswerChoice) : Prop :=
  ∃ candidateCurrentInAmperes : ℝ,
    CompatibleCurrentRateReadouts setup candidateCurrentInAmperes
      (displayedPhotoelectronRatePerSecond choice)

/-- The supplied stopping-potential graph explicitly contains no rate datum. -/
lemma suppliedFigure_has_no_current_or_rate_readout
    (setup : PhotoelectricExperiment)
    (hFigure : MatchesSuppliedStoppingPotentialFigure setup) :
    setup.figure.containsPhotocurrentAxis = false ∧
      setup.figure.containsPhotoelectronRateReadout = false := by
  sorry

/-!
Since no photocurrent value is supplied, each printed rate can be paired with
a nonnegative current satisfying `I = e N`; that law alone selects no option.
-/
lemma everyDisplayedRate_has_compatible_unmeasuredCurrent
    (setup : PhotoelectricExperiment)
    (hPhysical : HasPhysicalPhotoelectricParameters setup)
    (hCharge : UsesPhyslibElementaryCharge setup) :
    ∀ choice : AnswerChoice,
      DisplayedRateHasCompatibleUnmeasuredCurrent setup choice := by
  sorry

/-!
The strongest count-rate conclusion supported by the source is symbolic:
`N = I / e`. The current is not shown, and every displayed rate is compatible
with some possible unmeasured current. Thus the source does not determine a
numeric choice; the recorded choice remains metadata only.
-/
theorem problem_phyx_mini_0498
    (setup : PhotoelectricExperiment)
    (hScenario : MatchesPhotoelectricScenario setup)
    (hFigure : MatchesSuppliedStoppingPotentialFigure setup)
    (hPhysical : HasPhysicalPhotoelectricParameters setup)
    (hLaws : SatisfiesPhotoelectricLaws setup)
    (hCharge : UsesPhyslibElementaryCharge setup) :
    photoelectronRatePerSecond
        (setup.photoelectronRateAt setup.operatingFrequency) =
        currentInAmperes (setup.photocurrentAt setup.operatingFrequency) /
          physlibElementaryChargeInCoulombs ∧
      setup.figure.containsPhotocurrentAxis = false ∧
      setup.figure.containsPhotoelectronRateReadout = false ∧
      ∀ choice : AnswerChoice,
        DisplayedRateHasCompatibleUnmeasuredCurrent setup choice := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0498
