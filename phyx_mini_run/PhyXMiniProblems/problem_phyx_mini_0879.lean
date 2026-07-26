import Mathlib
import Physlib.Electromagnetism.Charge.ChargeUnit
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0879

open Dimension
open scoped BigOperators

/-!
# Equal charge on three capacitors in series

The primary image shows a `30 V` source on the left and three capacitors in a
single series branch on the right. From top to bottom they are labelled
`C₁ = 12 μF`, `C₂ = 4 μF`, and `C₃ = 6 μF`. The requested physical quantity
is the common charge magnitude carried by the three capacitors.

Potential difference, capacitance, and electric charge are represented by
unit-independent Physlib quantities. Real numbers occur only at explicit
named-unit readout boundaries and as literal data printed in the figure and
answer choices. In particular, capacitor charge is an independent field of
the setup, not a definition involving `60` or the recorded answer.

Assumption/target split:

* governing laws: the ideal-capacitor relation `Q = C ΔV`, opposite signed
  charges on the two plates, Kirchhoff voltage balance, and charge neutrality
  at each floating series junction;
* previous-part results: none;
* figure/data readouts: the source polarity and `30 V` label, the single closed
  series branch, and the `12 μF`, `4 μF`, and `6 μF` capacitor labels;
* current target conclusions: every capacitor has charge magnitude `60 μC`,
  and D is the unique displayed choice matching that derived common charge.

Neither equality of the three charge magnitudes nor their numerical value is
included in a setup field or theorem premise.
-/

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- The dimension `M L² T⁻² C⁻¹` of electric potential difference. -/
def potentialDifferenceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `C / V` of electrical capacitance. -/
def capacitanceDimension : Dimension :=
  C𝓭 * potentialDifferenceDimension⁻¹

/-- A nonnegative, unit-independent potential-difference magnitude. -/
abbrev PotentialDifferenceQuantity : Type :=
  Dimensionful (WithDim potentialDifferenceDimension NNReal)

/-- A nonnegative, unit-independent electrical capacitance. -/
abbrev CapacitanceQuantity : Type :=
  Dimensionful (WithDim capacitanceDimension NNReal)

/-- A nonnegative, unit-independent electric-charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A signed, unit-independent electric charge on one capacitor plate. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- Read a potential-difference magnitude in coherent-SI volts. -/
def potentialDifferenceInVolts
    (potentialDifference : PotentialDifferenceQuantity) : ℝ :=
  ((potentialDifference UnitChoices.SI).val : ℝ)

/-- Read an electrical capacitance in coherent-SI farads. -/
def capacitanceInFarads (capacitance : CapacitanceQuantity) : ℝ :=
  ((capacitance UnitChoices.SI).val : ℝ)

/-- Read an electrical capacitance in microfarads. -/
def capacitanceInMicrofarads (capacitance : CapacitanceQuantity) : ℝ :=
  (10 : ℝ) ^ 6 * capacitanceInFarads capacitance

/-- The charge unit `10⁻⁶ C` used by the requested answer. -/
def microCoulombs : ChargeUnit :=
  ChargeUnit.scale (1 / 10 ^ 6) ChargeUnit.coulombs

/-- Read a charge magnitude in a selected physical charge unit. -/
def chargeMagnitudeReadout
    (unit : ChargeUnit) (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge {UnitChoices.SI with charge := unit}).val : ℝ)

/-- Read a signed plate charge in a selected physical charge unit. -/
def signedChargeReadout
    (unit : ChargeUnit) (charge : SignedChargeQuantity) : ℝ :=
  (charge {UnitChoices.SI with charge := unit}).val

/-- Read a capacitor's charge magnitude in coulombs. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  chargeMagnitudeReadout ChargeUnit.coulombs charge

/-- Read a capacitor's charge magnitude in microcoulombs. -/
def chargeMagnitudeInMicrocoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  chargeMagnitudeReadout microCoulombs charge

/-- Read a signed capacitor-plate charge in coulombs. -/
def signedChargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  signedChargeReadout ChargeUnit.coulombs charge

/-! ## Circuit labels, topology, and primary-figure content -/

/-- The three capacitors, named as in the supplied image. -/
inductive CapacitorLabel where
  | C1
  | C2
  | C3
  deriving DecidableEq, Fintype, Repr

/-- The two plates of a capacitor in the image's top-to-bottom orientation. -/
inductive CapacitorPlate where
  | upper
  | lower
  deriving DecidableEq, Fintype, Repr

/-- Electrical nodes in the single closed series loop. -/
inductive CircuitNode where
  | sourcePositiveAndC1Upper
  | junctionC1C2
  | junctionC2C3
  | sourceNegativeAndC3Lower
  deriving DecidableEq, Fintype, Repr

/-- The ideal circuit interpretation of the diagram. -/
inductive CapacitorCircuitModel where
  | idealLumpedThreeCapacitorSeriesLoop
  | other
  deriving DecidableEq, Repr

/-- Literal visual information carried by image `879.png`. -/
structure ThreeSeriesCapacitorFigure where
  voltageSourceShown : Bool
  sourceDrawnOnLeft : Bool
  sourcePositiveGlyphShownAtTop : Bool
  sourceNegativeGlyphShownAtBottom : Bool
  printedSourcePotentialDifferenceVolts : ℝ
  capacitorShown : CapacitorLabel → Bool
  capacitorsDrawnOnRight : Bool
  capacitorsDrawnInSingleVerticalBranch : Bool
  printedCapacitanceMicrofarads : CapacitorLabel → ℝ
  topConnectingWireShown : Bool
  bottomConnectingWireShown : Bool

/-!
The independent physical data of the circuit. The node maps retain the
figure's connection topology. Charge magnitudes and signed plate charges are
not defined from the answer or from one another; the general capacitor and
charge-conservation laws relate them below.
-/
structure ThreeSeriesCapacitorSetup where
  model : CapacitorCircuitModel
  sourcePotentialDifference : PotentialDifferenceQuantity
  capacitance : CapacitorLabel → CapacitanceQuantity
  capacitorPotentialDrop : CapacitorLabel → PotentialDifferenceQuantity
  chargeMagnitude : CapacitorLabel → ChargeMagnitudeQuantity
  plateCharge : CapacitorLabel → CapacitorPlate → SignedChargeQuantity
  upperNode : CapacitorLabel → CircuitNode
  lowerNode : CapacitorLabel → CircuitNode
  sourcePositiveNode : CircuitNode
  sourceNegativeNode : CircuitNode
  figure : ThreeSeriesCapacitorFigure

/-! ## Scenario, figure readouts, and governing laws -/

/-- The single-branch series topology represented by the pictured wires. -/
structure MatchesThreeCapacitorSeriesTopology
    (setup : ThreeSeriesCapacitorSetup) : Prop where
  idealSeriesCircuitModel :
    setup.model = .idealLumpedThreeCapacitorSeriesLoop
  sourcePositiveNodeIsTop :
    setup.sourcePositiveNode = .sourcePositiveAndC1Upper
  sourceNegativeNodeIsBottom :
    setup.sourceNegativeNode = .sourceNegativeAndC3Lower
  C1RunsFromSourceToFirstJunction :
    setup.upperNode .C1 = .sourcePositiveAndC1Upper ∧
      setup.lowerNode .C1 = .junctionC1C2
  C2RunsBetweenFloatingJunctions :
    setup.upperNode .C2 = .junctionC1C2 ∧
      setup.lowerNode .C2 = .junctionC2C3
  C3RunsFromSecondJunctionToSource :
    setup.upperNode .C3 = .junctionC2C3 ∧
      setup.lowerNode .C3 = .sourceNegativeAndC3Lower

/-!
Primary-raster evidence and calibration of its printed values to independent
physical quantities. No charge value is printed in the image or included in
these assumptions.
-/
structure MatchesSuppliedThreeCapacitorFigure
    (setup : ThreeSeriesCapacitorSetup) : Prop where
  sourceIsShown : setup.figure.voltageSourceShown = true
  sourceIsOnLeft : setup.figure.sourceDrawnOnLeft = true
  sourcePlusAtTop : setup.figure.sourcePositiveGlyphShownAtTop = true
  sourceMinusAtBottom : setup.figure.sourceNegativeGlyphShownAtBottom = true
  printedSourceVoltage :
    setup.figure.printedSourcePotentialDifferenceVolts = 30
  sourceVoltageCalibratesPhysicalDifference :
    potentialDifferenceInVolts setup.sourcePotentialDifference =
      setup.figure.printedSourcePotentialDifferenceVolts
  everyCapacitorIsShown : ∀ capacitor,
    setup.figure.capacitorShown capacitor = true
  capacitorBranchIsOnRight : setup.figure.capacitorsDrawnOnRight = true
  capacitorsFormOneVerticalBranch :
    setup.figure.capacitorsDrawnInSingleVerticalBranch = true
  printedC1Capacitance :
    setup.figure.printedCapacitanceMicrofarads .C1 = 12
  printedC2Capacitance :
    setup.figure.printedCapacitanceMicrofarads .C2 = 4
  printedC3Capacitance :
    setup.figure.printedCapacitanceMicrofarads .C3 = 6
  capacitanceLabelsCalibratePhysicalCapacitances : ∀ capacitor,
    capacitanceInMicrofarads (setup.capacitance capacitor) =
      setup.figure.printedCapacitanceMicrofarads capacitor
  closedTopConnectionIsShown : setup.figure.topConnectingWireShown = true
  closedBottomConnectionIsShown : setup.figure.bottomConnectingWireShown = true

/-- Positivity and nondegeneracy conditions for the physical circuit. -/
structure HasPhysicalSeriesCapacitorParameters
    (setup : ThreeSeriesCapacitorSetup) : Prop where
  sourcePotentialDifferencePositive :
    0 < potentialDifferenceInVolts setup.sourcePotentialDifference
  eachCapacitancePositive : ∀ capacitor,
    0 < capacitanceInFarads (setup.capacitance capacitor)
  eachPotentialDropNonnegative : ∀ capacitor,
    0 ≤ potentialDifferenceInVolts (setup.capacitorPotentialDrop capacitor)
  sourceTerminalsDistinct :
    setup.sourcePositiveNode ≠ setup.sourceNegativeNode

/-!
The ideal-capacitor constitutive law `Q = C ΔV`, together with the opposite
signed charges on a capacitor's two plates. These laws apply uniformly to
every capacitor and contain no circuit-specific numerical charge.
-/
structure SatisfiesIdealCapacitorLaws
    (setup : ThreeSeriesCapacitorSetup) : Prop where
  chargeFromCapacitanceAndPotentialDrop : ∀ capacitor,
    chargeMagnitudeInCoulombs (setup.chargeMagnitude capacitor) =
      capacitanceInFarads (setup.capacitance capacitor) *
        potentialDifferenceInVolts (setup.capacitorPotentialDrop capacitor)
  upperPlateCharge : ∀ capacitor,
    signedChargeInCoulombs (setup.plateCharge capacitor .upper) =
      chargeMagnitudeInCoulombs (setup.chargeMagnitude capacitor)
  lowerPlateCharge : ∀ capacitor,
    signedChargeInCoulombs (setup.plateCharge capacitor .lower) =
      -chargeMagnitudeInCoulombs (setup.chargeMagnitude capacitor)

/-- Net signed charge residing on capacitor plates incident to one node. -/
noncomputable def netPlateChargeAtNodeInCoulombs
    (setup : ThreeSeriesCapacitorSetup) (node : CircuitNode) : ℝ :=
  ∑ capacitor : CapacitorLabel, (
    (if setup.upperNode capacitor = node then
        signedChargeInCoulombs (setup.plateCharge capacitor .upper)
      else 0) +
    (if setup.lowerNode capacitor = node then
        signedChargeInCoulombs (setup.plateCharge capacitor .lower)
      else 0))

/-- The two internal nodes that have no direct connection to the source. -/
def IsFloatingJunction : CircuitNode → Prop
  | .junctionC1C2 => True
  | .junctionC2C3 => True
  | _ => False

/-!
Kirchhoff voltage balance around the closed loop and conservation of charge
at every floating junction. Neutrality is stated at nodes rather than as an
assumed equality of the three requested capacitor charges.
-/
structure SatisfiesSeriesCircuitConservationLaws
    (setup : ThreeSeriesCapacitorSetup) : Prop where
  sourceVoltageEqualsSumOfDrops :
    potentialDifferenceInVolts setup.sourcePotentialDifference =
      ∑ capacitor : CapacitorLabel,
        potentialDifferenceInVolts (setup.capacitorPotentialDrop capacitor)
  floatingJunctionsAreChargeNeutral : ∀ node,
    IsFloatingJunction node →
      netPlateChargeAtNodeInCoulombs setup node = 0

/-! ## Derived common charge and displayed answer -/

/-!
The two neutral floating junctions and opposite plate signs imply that all
three capacitor charge magnitudes agree. This is derived from topology and
general conservation rather than included in a premise.
-/
lemma chargeMagnitudesAreEqual
    (setup : ThreeSeriesCapacitorSetup)
    (_topology : MatchesThreeCapacitorSeriesTopology setup)
    (_capacitor : SatisfiesIdealCapacitorLaws setup)
    (_conservation : SatisfiesSeriesCircuitConservationLaws setup) :
    chargeMagnitudeInCoulombs (setup.chargeMagnitude .C1) =
        chargeMagnitudeInCoulombs (setup.chargeMagnitude .C2) ∧
      chargeMagnitudeInCoulombs (setup.chargeMagnitude .C2) =
        chargeMagnitudeInCoulombs (setup.chargeMagnitude .C3) := by
  classical
  have hsum (f : CapacitorLabel → ℝ) :
      ∑ capacitor, f capacitor = f .C1 + f .C2 + f .C3 := by
    rw [Fintype.sum_eq_add_sum_compl .C1]
    have hc : ({.C1}ᶜ : Finset CapacitorLabel) = {.C2, .C3} := by
      ext capacitor
      fin_cases capacitor <;> simp
    rw [hc]
    simp [add_assoc]
  rcases _topology with
    ⟨_, _, _, ⟨hC1u, hC1l⟩, ⟨hC2u, hC2l⟩, ⟨hC3u, hC3l⟩⟩
  have h12 :=
    _conservation.floatingJunctionsAreChargeNeutral .junctionC1C2 (by trivial)
  have h23 :=
    _conservation.floatingJunctionsAreChargeNeutral .junctionC2C3 (by trivial)
  rw [netPlateChargeAtNodeInCoulombs, hsum] at h12 h23
  simp [hC1u, hC1l, hC2u, hC2l, hC3u, hC3l,
    _capacitor.upperPlateCharge, _capacitor.lowerPlateCharge] at h12 h23
  constructor <;> linarith

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The displayed common-charge magnitude for each choice, in microcoulombs. -/
def AnswerChoice.displayedChargeInMicrocoulombs : AnswerChoice → ℝ
  | .A => 2.5
  | .B => 35
  | .C => 55
  | .D => 60

/-- The source dataset's recorded answer, retained as answer metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A displayed choice agrees with every physical capacitor charge. -/
def AnswerMatchesCommonCharge
    (setup : ThreeSeriesCapacitorSetup) (choice : AnswerChoice) : Prop :=
  ∀ capacitor,
    chargeMagnitudeInMicrocoulombs (setup.chargeMagnitude capacitor) =
      choice.displayedChargeInMicrocoulombs

/-- Exactly one displayed choice agrees with the common physical charge. -/
def IsUniqueMatchingAnswer
    (setup : ThreeSeriesCapacitorSetup) (choice : AnswerChoice) : Prop :=
  AnswerMatchesCommonCharge setup choice ∧
    ∀ other, AnswerMatchesCommonCharge setup other → other = choice

/-!
For three ideal capacitors in series, floating-node charge conservation gives
a common charge `Q`. Substituting `ΔVᵢ = Q / Cᵢ` in Kirchhoff's voltage law
with `12 μF`, `4 μF`, `6 μF`, and `30 V` gives `Q = 60 μC`, uniquely selecting
choice D.

This declaration formalizes blueprint label
`thm:physics:phyx_mini_0879:target`. Neither equal charge, `60 μC`, nor answer
D occurs in a physical-law, scenario, topology, or figure premise.
-/
theorem problem_phyx_mini_0879
    (setup : ThreeSeriesCapacitorSetup)
    (_topology : MatchesThreeCapacitorSeriesTopology setup)
    (_figure : MatchesSuppliedThreeCapacitorFigure setup)
    (_physical : HasPhysicalSeriesCapacitorParameters setup)
    (_capacitor : SatisfiesIdealCapacitorLaws setup)
    (_conservation : SatisfiesSeriesCircuitConservationLaws setup) :
    (∀ capacitor,
      chargeMagnitudeInMicrocoulombs (setup.chargeMagnitude capacitor) = 60) ∧
      IsUniqueMatchingAnswer setup recordedDatasetAnswer := by
  classical
  have hsum (f : CapacitorLabel → ℝ) :
      ∑ capacitor, f capacitor = f .C1 + f .C2 + f .C3 := by
    rw [Fintype.sum_eq_add_sum_compl .C1]
    have hc : ({.C1}ᶜ : Finset CapacitorLabel) = {.C2, .C3} := by
      ext capacitor
      fin_cases capacitor <;> simp
    rw [hc]
    simp [add_assoc]
  have hscale :
      UnitChoices.SI.dimScale
          {UnitChoices.SI with charge := microCoulombs} C𝓭 =
        (1000000 : NNReal) := by
    apply NNReal.eq
    rw [UnitChoices.dimScale_apply]
    simp only [C𝓭, Rat.cast_zero, Rat.cast_one, NNReal.rpow_zero,
      NNReal.rpow_one]
    norm_num [UnitChoices.SI, microCoulombs, ChargeUnit.div_eq_val,
      ChargeUnit.scale, ChargeUnit.coulombs]
    rfl
  have charge_micro_eq (charge : ChargeMagnitudeQuantity) :
      chargeMagnitudeInMicrocoulombs charge =
        1000000 * chargeMagnitudeInCoulombs charge := by
    change
      (((charge
          {UnitChoices.SI with charge := microCoulombs}).val : NNReal) : ℝ) =
        1000000 * (((charge UnitChoices.SI).val : NNReal) : ℝ)
    rw [charge.property UnitChoices.SI
      {UnitChoices.SI with charge := microCoulombs}]
    simp only [WithDim.dim_apply]
    rw [hscale]
    norm_num
  have hV :
      potentialDifferenceInVolts setup.sourcePotentialDifference = 30 := by
    calc
      _ = setup.figure.printedSourcePotentialDifferenceVolts :=
        _figure.sourceVoltageCalibratesPhysicalDifference
      _ = 30 := _figure.printedSourceVoltage
  have hC1 :
      capacitanceInFarads (setup.capacitance .C1) = 12 / 1000000 := by
    have h :=
      _figure.capacitanceLabelsCalibratePhysicalCapacitances .C1
    rw [_figure.printedC1Capacitance] at h
    norm_num [capacitanceInMicrofarads] at h ⊢
    linarith
  have hC2 :
      capacitanceInFarads (setup.capacitance .C2) = 4 / 1000000 := by
    have h :=
      _figure.capacitanceLabelsCalibratePhysicalCapacitances .C2
    rw [_figure.printedC2Capacitance] at h
    norm_num [capacitanceInMicrofarads] at h ⊢
    linarith
  have hC3 :
      capacitanceInFarads (setup.capacitance .C3) = 6 / 1000000 := by
    have h :=
      _figure.capacitanceLabelsCalibratePhysicalCapacitances .C3
    rw [_figure.printedC3Capacitance] at h
    norm_num [capacitanceInMicrofarads] at h ⊢
    linarith
  have hsource := _conservation.sourceVoltageEqualsSumOfDrops
  rw [hV, hsum] at hsource
  have hcap1 :=
    _capacitor.chargeFromCapacitanceAndPotentialDrop .C1
  have hcap2 :=
    _capacitor.chargeFromCapacitanceAndPotentialDrop .C2
  have hcap3 :=
    _capacitor.chargeFromCapacitanceAndPotentialDrop .C3
  rw [hC1] at hcap1
  rw [hC2] at hcap2
  rw [hC3] at hcap3
  obtain ⟨hq12, hq23⟩ :=
    chargeMagnitudesAreEqual setup _topology _capacitor _conservation
  have hq1 :
      chargeMagnitudeInCoulombs (setup.chargeMagnitude .C1) =
        3 / 50000 := by
    norm_num at hcap1 hcap2 hcap3 ⊢
    linarith
  have hq2 :
      chargeMagnitudeInCoulombs (setup.chargeMagnitude .C2) =
        3 / 50000 := by
    linarith
  have hq3 :
      chargeMagnitudeInCoulombs (setup.chargeMagnitude .C3) =
        3 / 50000 := by
    linarith
  have hcommon : ∀ capacitor,
      chargeMagnitudeInMicrocoulombs
          (setup.chargeMagnitude capacitor) = 60 := by
    intro capacitor
    rw [charge_micro_eq]
    fin_cases capacitor <;> norm_num [hq1, hq2, hq3]
  constructor
  · exact hcommon
  · constructor
    · intro capacitor
      simpa [AnswerMatchesCommonCharge, recordedDatasetAnswer,
        AnswerChoice.displayedChargeInMicrocoulombs] using
        hcommon capacitor
    · intro other hother
      have ho := hother .C1
      have hc := hcommon .C1
      fin_cases other <;>
        norm_num [AnswerMatchesCommonCharge, recordedDatasetAnswer,
          AnswerChoice.displayedChargeInMicrocoulombs] at ho ⊢ <;>
        linarith

end PhyXMiniProblems.ProblemPhyXMini0879
