import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0880

open Dimension

/-!
# Charge on `C₃` in a mixed capacitor circuit

The primary figure shows a `9 V` battery connected across a series combination
of the capacitor `C₃` and the parallel branch `C₁ ∥ C₂`.  The printed
capacitances are respectively `4 μF`, `12 μF`, and `2 μF`.

Capacitance, charge magnitude, and potential-difference magnitude are modeled
as unit-independent Physlib `Dimensionful` quantities.  Real numbers occur
only as explicit coherent-SI readouts, scaled figure labels, and displayed
multiple-choice values.

Assumption/target split:

* governing laws: the ideal-capacitor law `Q = C V`, equal voltage on the two
  parallel capacitors, Kirchhoff voltage balance along the source-to-`C₃`
  path, and charge conservation at the floating junction;
* previous-part results: none;
* figure/data readouts: the `9 V` source, the `4 μF`, `12 μF`, and `2 μF`
  labels, the positive/negative battery terminals, and the three-node wiring
  that places `C₁` and `C₂` in parallel and `C₃` in series with that branch;
* current target: the charge magnitude on `C₃` is `16 μC`, corresponding to
  displayed choice `D`.

Neither the independent setup nor any premise contains the target charge or
the recorded answer choice.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- The dimension `M L² T⁻² C⁻¹` of electric potential difference. -/
def potentialDifferenceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `C² T² M⁻¹ L⁻²` of capacitance. -/
def capacitanceDimension : Dimension :=
  C𝓭 * C𝓭 * T𝓭 * T𝓭 * M𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- A nonnegative, unit-independent physical capacitance. -/
abbrev CapacitanceQuantity : Type :=
  Dimensionful (WithDim capacitanceDimension NNReal)

/-- A nonnegative, unit-independent capacitor charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative, unit-independent potential-difference magnitude. -/
abbrev PotentialDifferenceQuantity : Type :=
  Dimensionful (WithDim potentialDifferenceDimension NNReal)

/-- Coherent-SI readout of a capacitance in farads. -/
def capacitanceInFarads (capacitance : CapacitanceQuantity) : ℝ :=
  ((capacitance UnitChoices.SI).val : ℝ)

/-- Microfarad readout used by the three labels in the supplied figure. -/
def capacitanceInMicrofarads (capacitance : CapacitanceQuantity) : ℝ :=
  (10 : ℝ) ^ 6 * capacitanceInFarads capacitance

/-- Coherent-SI readout of a charge magnitude in coulombs. -/
def chargeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge UnitChoices.SI).val : ℝ)

/-- Microcoulomb readout used by the question and its displayed choices. -/
def chargeInMicrocoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  (10 : ℝ) ^ 6 * chargeInCoulombs charge

/-- Coherent-SI readout of a potential-difference magnitude in volts. -/
def potentialDifferenceInVolts
    (potentialDifference : PotentialDifferenceQuantity) : ℝ :=
  ((potentialDifference UnitChoices.SI).val : ℝ)

/-! ## Figure labels, nodes, and independent circuit setup -/

/-- The three capacitor labels printed in the primary image. -/
inductive CapacitorId where
  | c1
  | c2
  | c3
  deriving DecidableEq, Fintype, Repr

/-- The three equipotential conductor nodes visible in the circuit diagram. -/
inductive CircuitNode where
  | positiveRail
  | branchJunction
  | negativeRail
  deriving DecidableEq, Fintype, Repr

/-- The two polarity-marked terminals of the battery symbol. -/
inductive BatteryTerminal where
  | positive
  | negative
  deriving DecidableEq, Fintype, Repr

/-- The literal capacitor name printed for each indexed component. -/
def expectedCapacitorLabel : CapacitorId → String
  | .c1 => "C₁"
  | .c2 => "C₂"
  | .c3 => "C₃"

/-- The capacitance number, in microfarads, printed beside each capacitor. -/
def expectedCapacitanceLabelMicrofarads : CapacitorId → ℝ
  | .c1 => 4
  | .c2 => 12
  | .c3 => 2

/-!
Literal presentation and connectivity data transcribed from image `880.png`.
The two plate-node maps retain the diagram's topology rather than replacing
the circuit by a precomputed equivalent capacitance.
-/
structure MixedCapacitorCircuitFigure where
  printedBatteryVoltageVolts : ℝ
  printedCapacitorLabel : CapacitorId → String
  printedCapacitanceMicrofarads : CapacitorId → ℝ
  capacitorSymbolShown : CapacitorId → Bool
  firstPlateNode : CapacitorId → CircuitNode
  secondPlateNode : CapacitorId → CircuitNode
  batteryTerminalNode : BatteryTerminal → CircuitNode

/-!
The independent physical quantities associated with the circuit.  In
particular, `chargeMagnitude` is an observable assigned to each capacitor; it
is not defined from the desired answer or from a displayed choice.
-/
structure MixedCapacitorCircuitSetup where
  figure : MixedCapacitorCircuitFigure
  capacitance : CapacitorId → CapacitanceQuantity
  chargeMagnitude : CapacitorId → ChargeMagnitudeQuantity
  potentialDifference : CapacitorId → PotentialDifferenceQuantity
  sourcePotentialDifference : PotentialDifferenceQuantity

/-! ## Figure evidence and physical premises -/

/-!
All numeric and connectivity information read from the supplied image.  The
physical quantities are calibrated to their printed labels.  No capacitor
charge occurs numerically in this premise.
-/
structure MatchesSuppliedMixedCapacitorFigure
    (setup : MixedCapacitorCircuitSetup) : Prop where
  batteryVoltageLabel : setup.figure.printedBatteryVoltageVolts = 9
  capacitorNameLabels : ∀ capacitor,
    setup.figure.printedCapacitorLabel capacitor =
      expectedCapacitorLabel capacitor
  capacitanceNumberLabels : ∀ capacitor,
    setup.figure.printedCapacitanceMicrofarads capacitor =
      expectedCapacitanceLabelMicrofarads capacitor
  allCapacitorSymbolsShown : ∀ capacitor,
    setup.figure.capacitorSymbolShown capacitor = true
  physicalCapacitancesMatchLabels : ∀ capacitor,
    capacitanceInMicrofarads (setup.capacitance capacitor) =
      setup.figure.printedCapacitanceMicrofarads capacitor
  physicalSourceMatchesLabel :
    potentialDifferenceInVolts setup.sourcePotentialDifference =
      setup.figure.printedBatteryVoltageVolts
  c1FirstPlateOnPositiveRail :
    setup.figure.firstPlateNode .c1 = .positiveRail
  c1SecondPlateAtJunction :
    setup.figure.secondPlateNode .c1 = .branchJunction
  c2FirstPlateOnPositiveRail :
    setup.figure.firstPlateNode .c2 = .positiveRail
  c2SecondPlateAtJunction :
    setup.figure.secondPlateNode .c2 = .branchJunction
  c3FirstPlateAtJunction :
    setup.figure.firstPlateNode .c3 = .branchJunction
  c3SecondPlateOnNegativeRail :
    setup.figure.secondPlateNode .c3 = .negativeRail
  positiveBatteryTerminalOnPositiveRail :
    setup.figure.batteryTerminalNode .positive = .positiveRail
  negativeBatteryTerminalOnNegativeRail :
    setup.figure.batteryTerminalNode .negative = .negativeRail

/-- Positivity conditions selecting the ordinary passive-capacitor branch. -/
structure HasPhysicalMixedCapacitorParameters
    (setup : MixedCapacitorCircuitSetup) : Prop where
  positiveCapacitance : ∀ capacitor,
    0 < capacitanceInFarads (setup.capacitance capacitor)
  positiveSourcePotentialDifference :
    0 < potentialDifferenceInVolts setup.sourcePotentialDifference
  nonnegativeCapacitorPotentialDifference : ∀ capacitor,
    0 ≤ potentialDifferenceInVolts (setup.potentialDifference capacitor)
  nonnegativeChargeMagnitude : ∀ capacitor,
    0 ≤ chargeInCoulombs (setup.chargeMagnitude capacitor)

/-!
The governing relations for ideal capacitors after the figure topology has
identified `C₁` and `C₂` as a parallel branch and `C₃` as its series partner.
The final field is charge conservation at their isolated common junction:
the charge magnitude on `C₃` equals the sum stored on the two parallel plates.
These are general circuit laws and contain no numerical answer.
-/
structure SatisfiesIdealMixedCapacitorCircuitLaws
    (setup : MixedCapacitorCircuitSetup) : Prop where
  capacitorChargeLaw : ∀ capacitor,
    chargeInCoulombs (setup.chargeMagnitude capacitor) =
      capacitanceInFarads (setup.capacitance capacitor) *
        potentialDifferenceInVolts (setup.potentialDifference capacitor)
  equalPotentialDifferenceOnParallelPair :
    potentialDifferenceInVolts (setup.potentialDifference .c1) =
      potentialDifferenceInVolts (setup.potentialDifference .c2)
  sourcePotentialDifferenceBalance :
    potentialDifferenceInVolts setup.sourcePotentialDifference =
      potentialDifferenceInVolts (setup.potentialDifference .c1) +
        potentialDifferenceInVolts (setup.potentialDifference .c3)
  floatingJunctionChargeConservation :
    chargeInCoulombs (setup.chargeMagnitude .c3) =
      chargeInCoulombs (setup.chargeMagnitude .c1) +
        chargeInCoulombs (setup.chargeMagnitude .c2)

/-! ## Displayed choices and current target -/

/-- Labels of the four answer choices displayed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Charge magnitude in microcoulombs printed beside each answer label. -/
def AnswerChoice.chargeInMicrocoulombs : AnswerChoice → ℝ
  | .A => 5 / 2
  | .B => 15
  | .C => 55
  | .D => 16

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
For the `4 μF` and `12 μF` capacitors in parallel, the branch capacitance is
their sum, `16 μF`.  This is a derived relation, not a figure premise.
-/
lemma parallel_branch_capacitance_readout
    (setup : MixedCapacitorCircuitSetup)
    (_figure : MatchesSuppliedMixedCapacitorFigure setup) :
    capacitanceInMicrofarads (setup.capacitance .c1) +
        capacitanceInMicrofarads (setup.capacitance .c2) = 16 := by
  have hc1 :
      capacitanceInMicrofarads (setup.capacitance .c1) = 4 := by
    calc
      capacitanceInMicrofarads (setup.capacitance .c1) =
          setup.figure.printedCapacitanceMicrofarads .c1 :=
        _figure.physicalCapacitancesMatchLabels .c1
      _ = expectedCapacitanceLabelMicrofarads .c1 :=
        _figure.capacitanceNumberLabels .c1
      _ = 4 := rfl
  have hc2 :
      capacitanceInMicrofarads (setup.capacitance .c2) = 12 := by
    calc
      capacitanceInMicrofarads (setup.capacitance .c2) =
          setup.figure.printedCapacitanceMicrofarads .c2 :=
        _figure.physicalCapacitancesMatchLabels .c2
      _ = expectedCapacitanceLabelMicrofarads .c2 :=
        _figure.capacitanceNumberLabels .c2
      _ = 12 := rfl
  rw [hc1, hc2]
  norm_num

/-!
The ideal circuit laws and the supplied component data determine the charge
magnitude on `C₃` to be `16 μC`.
-/
lemma charge_on_c3_eq_sixteen_microcoulombs
    (setup : MixedCapacitorCircuitSetup)
    (_figure : MatchesSuppliedMixedCapacitorFigure setup)
    (_physical : HasPhysicalMixedCapacitorParameters setup)
    (_laws : SatisfiesIdealMixedCapacitorCircuitLaws setup) :
    chargeInMicrocoulombs (setup.chargeMagnitude .c3) = 16 := by
  have hc1Micro :
      capacitanceInMicrofarads (setup.capacitance .c1) = 4 := by
    calc
      capacitanceInMicrofarads (setup.capacitance .c1) =
          setup.figure.printedCapacitanceMicrofarads .c1 :=
        _figure.physicalCapacitancesMatchLabels .c1
      _ = expectedCapacitanceLabelMicrofarads .c1 :=
        _figure.capacitanceNumberLabels .c1
      _ = 4 := rfl
  have hc2Micro :
      capacitanceInMicrofarads (setup.capacitance .c2) = 12 := by
    calc
      capacitanceInMicrofarads (setup.capacitance .c2) =
          setup.figure.printedCapacitanceMicrofarads .c2 :=
        _figure.physicalCapacitancesMatchLabels .c2
      _ = expectedCapacitanceLabelMicrofarads .c2 :=
        _figure.capacitanceNumberLabels .c2
      _ = 12 := rfl
  have hc3Micro :
      capacitanceInMicrofarads (setup.capacitance .c3) = 2 := by
    calc
      capacitanceInMicrofarads (setup.capacitance .c3) =
          setup.figure.printedCapacitanceMicrofarads .c3 :=
        _figure.physicalCapacitancesMatchLabels .c3
      _ = expectedCapacitanceLabelMicrofarads .c3 :=
        _figure.capacitanceNumberLabels .c3
      _ = 2 := rfl
  have hc1 :
      capacitanceInFarads (setup.capacitance .c1) = (4 : ℝ) / 1000000 := by
    norm_num [capacitanceInMicrofarads] at hc1Micro
    linarith
  have hc2 :
      capacitanceInFarads (setup.capacitance .c2) = (12 : ℝ) / 1000000 := by
    norm_num [capacitanceInMicrofarads] at hc2Micro
    linarith
  have hc3 :
      capacitanceInFarads (setup.capacitance .c3) = (2 : ℝ) / 1000000 := by
    norm_num [capacitanceInMicrofarads] at hc3Micro
    linarith
  have hsource :
      potentialDifferenceInVolts setup.sourcePotentialDifference = 9 := by
    calc
      potentialDifferenceInVolts setup.sourcePotentialDifference =
          setup.figure.printedBatteryVoltageVolts :=
        _figure.physicalSourceMatchesLabel
      _ = 9 := _figure.batteryVoltageLabel
  have hq1 := _laws.capacitorChargeLaw .c1
  have hq2 := _laws.capacitorChargeLaw .c2
  have hq3 := _laws.capacitorChargeLaw .c3
  rw [hc1] at hq1
  rw [hc2] at hq2
  rw [hc3] at hq3
  norm_num at hq1 hq2 hq3
  norm_num [chargeInMicrocoulombs]
  linarith [
    hq1,
    hq2,
    hq3,
    _laws.equalPotentialDifferenceOnParallelPair,
    _laws.sourcePotentialDifferenceBalance,
    _laws.floatingJunctionChargeConservation,
    hsource
  ]

/-!
The charge on `C₃` equals the value printed for recorded choice `D`.

This is the declaration corresponding to blueprint environment
`thm:physics:phyx_mini_0880:target`.
-/
theorem charge_on_c3_matches_recorded_choice
    (setup : MixedCapacitorCircuitSetup)
    (_figure : MatchesSuppliedMixedCapacitorFigure setup)
    (_physical : HasPhysicalMixedCapacitorParameters setup)
    (_laws : SatisfiesIdealMixedCapacitorCircuitLaws setup) :
    chargeInMicrocoulombs (setup.chargeMagnitude .c3) = 16 ∧
      recordedDatasetAnswer = .D ∧
      chargeInMicrocoulombs (setup.chargeMagnitude .c3) =
        recordedDatasetAnswer.chargeInMicrocoulombs := by
  have hcharge :=
    charge_on_c3_eq_sixteen_microcoulombs setup _figure _physical _laws
  refine ⟨hcharge, rfl, ?_⟩
  simpa [recordedDatasetAnswer, AnswerChoice.chargeInMicrocoulombs] using hcharge

end PhyXMiniProblems.ProblemPhyXMini0880
