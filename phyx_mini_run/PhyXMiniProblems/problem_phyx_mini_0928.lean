import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0928

open Dimension

/-!
# Resistance required for a specified inductor time constant

The primary raster `928.png` shows a `500 Ω` resistor and an unknown resistor
`R` connected between the same pair of junctions.  A `7.5 mH` inductor closes
the source-free loop across those junctions, and the requested natural-response
time constant is `25 μs`.

Physical resistance, inductance, and duration are represented by Physlib's
unit-independent dimensionful quantities.  Real scalars are used only for SI
readouts and literal values printed in the figure or question.
-/

/-! ## Physical dimensions and coherent-SI readouts -/

/-- Energy has dimension `M L² T⁻²`. -/
def energyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Electric current has dimension charge per time. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Electric potential difference has dimension energy per charge. -/
def electricPotentialDimension : Dimension :=
  energyDimension * C𝓭⁻¹

/-- Electrical resistance has dimension potential difference per current. -/
def electricalResistanceDimension : Dimension :=
  electricPotentialDimension * electricCurrentDimension⁻¹

/-- Electrical inductance has dimension resistance times time. -/
def electricalInductanceDimension : Dimension :=
  electricalResistanceDimension * T𝓭

/-- A nonnegative, unit-independent electrical resistance. -/
abbrev ElectricalResistanceQuantity : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative, unit-independent electrical inductance. -/
abbrev ElectricalInductanceQuantity : Type :=
  Dimensionful (WithDim electricalInductanceDimension NNReal)

/-- A nonnegative, unit-independent elapsed duration. -/
abbrev DurationQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- Coherent-SI scalar readout of a nonnegative dimensionful quantity. -/
def coherentSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read an electrical resistance in ohms. -/
def resistanceInOhms (resistance : ElectricalResistanceQuantity) : ℝ :=
  coherentSIReadout resistance

/-- Read an electrical inductance in henries. -/
def inductanceInHenries (inductance : ElectricalInductanceQuantity) : ℝ :=
  coherentSIReadout inductance

/-- Read an electrical inductance in millihenries. -/
def inductanceInMillihenries
    (inductance : ElectricalInductanceQuantity) : ℝ :=
  1000 * inductanceInHenries inductance

/-- Read an elapsed duration in seconds. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  coherentSIReadout duration

/-- Read an elapsed duration in microseconds. -/
def durationInMicroseconds (duration : DurationQuantity) : ℝ :=
  1000000 * durationInSeconds duration

/-! ## Circuit roles, node geometry, and primary-raster content -/

/-- The three lumped components visible in image `928.png`. -/
inductive CircuitComponent where
  | upperFixedResistor
  | lowerUnknownResistorR
  | rightInductor
  deriving DecidableEq, Fintype, Repr

/-- The two electrically distinct junctions in the displayed circuit. -/
inductive CircuitNode where
  | leftJunction
  | rightJunction
  deriving DecidableEq, Fintype, Repr

/-- Ideal lumped-element roles assigned to the three symbols. -/
inductive ComponentModel where
  | idealResistor
  | idealInductor
  | other
  deriving DecidableEq, Repr

/-- Dynamical regime in which the passive circuit has a time constant. -/
inductive CircuitRegime where
  | sourceFreeNaturalResponse
  | externallyDriven
  | other
  deriving DecidableEq, Repr

/-- The three textual labels visible in the supplied raster. -/
inductive FigureLabel where
  | fixedResistance500Ohms
  | unknownResistanceR
  | inductance7Point5Millihenries
  deriving DecidableEq, Fintype, Repr

/-!
Literal presentation data from the primary raster.  These fields record only
visible symbols, labels, and incidence cues.  The scalar labels are calibrated
to independent physical quantities below.
-/
structure ParallelResistorInductorFigure where
  componentShown : CircuitComponent → Bool
  labelShown : FigureLabel → Bool
  upperResistorDrawnAboveLowerResistor : Bool
  resistorBranchesMeetAtBothEnds : Bool
  inductorConnectedAcrossTheSameJunctions : Bool
  closedReturnWireShown : Bool
  printedFixedResistanceInOhms : ℝ
  printedInductanceInMillihenries : ℝ

/-!
Independent physical data for the ideal circuit.  The equivalent resistance
and time constant are observables constrained by circuit laws rather than
definitions made from the requested numerical answer.
-/
structure ParallelResistorInductorSetup where
  componentModel : CircuitComponent → ComponentModel
  componentTerminals : CircuitComponent → CircuitNode × CircuitNode
  regime : CircuitRegime
  fixedResistor : ElectricalResistanceQuantity
  unknownResistorR : ElectricalResistanceQuantity
  equivalentResistanceSeenByInductor : ElectricalResistanceQuantity
  inductorInductance : ElectricalInductanceQuantity
  naturalResponseTimeConstant : DurationQuantity
  figure : ParallelResistorInductorFigure

/-! ## Assumption side: scenario, figure readouts, and governing laws -/

/-- The ideal passive-component interpretation required by the question. -/
structure MatchesIdealSourceFreeRLScenario
    (setup : ParallelResistorInductorSetup) : Prop where
  sourceFreeNaturalResponse :
    setup.regime = .sourceFreeNaturalResponse
  fixedComponentIsIdealResistor :
    setup.componentModel .upperFixedResistor = .idealResistor
  unknownComponentIsIdealResistor :
    setup.componentModel .lowerUnknownResistorR = .idealResistor
  inductorComponentIsIdeal :
    setup.componentModel .rightInductor = .idealInductor

/-!
Primary-image evidence and its calibration to the dimensionful circuit data.
Both resistors and the inductor join the same pair of electrical nodes.  The
reversed terminal order for the inductor records its drawn orientation.
-/
structure MatchesSuppliedParallelResistorInductorFigure
    (setup : ParallelResistorInductorSetup) : Prop where
  everyComponentShown : ∀ component,
    setup.figure.componentShown component = true
  everyLabelShown : ∀ label,
    setup.figure.labelShown label = true
  fixedResistorTerminals :
    setup.componentTerminals .upperFixedResistor =
      (.leftJunction, .rightJunction)
  unknownResistorTerminals :
    setup.componentTerminals .lowerUnknownResistorR =
      (.leftJunction, .rightJunction)
  inductorTerminals :
    setup.componentTerminals .rightInductor =
      (.rightJunction, .leftJunction)
  upperBranchPosition :
    setup.figure.upperResistorDrawnAboveLowerResistor = true
  resistorParallelIncidenceShown :
    setup.figure.resistorBranchesMeetAtBothEnds = true
  inductorAcrossJunctionsShown :
    setup.figure.inductorConnectedAcrossTheSameJunctions = true
  closedWireShown :
    setup.figure.closedReturnWireShown = true
  printedFixedResistanceLabel :
    setup.figure.printedFixedResistanceInOhms = 500
  printedInductanceLabel :
    setup.figure.printedInductanceInMillihenries = 15 / 2
  fixedResistanceLabelCalibration :
    resistanceInOhms setup.fixedResistor =
      setup.figure.printedFixedResistanceInOhms
  inductanceLabelCalibration :
    inductanceInMillihenries setup.inductorInductance =
      setup.figure.printedInductanceInMillihenries

/-- The requested time-constant value stated in the question text. -/
structure MatchesRequestedTimeConstant
    (setup : ParallelResistorInductorSetup) : Prop where
  requestedTimeConstantInMicroseconds :
    durationInMicroseconds setup.naturalResponseTimeConstant = 25

/-- Positivity and nondegeneracy of the passive circuit parameters. -/
structure HasPhysicalParallelRLParameters
    (setup : ParallelResistorInductorSetup) : Prop where
  fixedResistancePositive :
    0 < resistanceInOhms setup.fixedResistor
  unknownResistancePositive :
    0 < resistanceInOhms setup.unknownResistorR
  equivalentResistancePositive :
    0 < resistanceInOhms setup.equivalentResistanceSeenByInductor
  inductancePositive :
    0 < inductanceInHenries setup.inductorInductance
  timeConstantPositive :
    0 < durationInSeconds setup.naturalResponseTimeConstant

/-!
The governing ideal-circuit laws: the reciprocal rule for two parallel
resistors and the source-free RL relation `τ = L / R_eq`.  Neither law embeds
the requested value of the unknown resistor.
-/
structure SatisfiesParallelResistanceAndRLTimeConstantLaws
    (setup : ParallelResistorInductorSetup) : Prop where
  parallelEquivalentResistanceLaw :
    1 / resistanceInOhms setup.equivalentResistanceSeenByInductor =
      1 / resistanceInOhms setup.fixedResistor +
        1 / resistanceInOhms setup.unknownResistorR
  naturalResponseTimeConstantLaw :
    durationInSeconds setup.naturalResponseTimeConstant =
      inductanceInHenries setup.inductorInductance /
        resistanceInOhms setup.equivalentResistanceSeenByInductor

/-! ## Derived equivalent resistance, answer metadata, and target -/

/--
The `7.5 mH` inductance and `25 μs` time constant imply that the resistor
network seen by the inductor has equivalent resistance `300 Ω`.
-/
lemma equivalentResistanceSeenByInductor_eq_300_ohms
    (setup : ParallelResistorInductorSetup)
    (hFigure : MatchesSuppliedParallelResistorInductorFigure setup)
    (hTimeConstant : MatchesRequestedTimeConstant setup)
    (hPhysical : HasPhysicalParallelRLParameters setup)
    (hLaws : SatisfiesParallelResistanceAndRLTimeConstantLaws setup) :
    resistanceInOhms setup.equivalentResistanceSeenByInductor = 300 := by
  have hTau :
      durationInSeconds setup.naturalResponseTimeConstant = (1 : ℝ) / 40000 := by
    have h := hTimeConstant.requestedTimeConstantInMicroseconds
    unfold durationInMicroseconds at h
    norm_num at h ⊢
    linarith
  have hInductance :
      inductanceInHenries setup.inductorInductance = (3 : ℝ) / 400 := by
    have h := hFigure.inductanceLabelCalibration
    rw [hFigure.printedInductanceLabel] at h
    unfold inductanceInMillihenries at h
    norm_num at h ⊢
    linarith
  have hEquivalentResistanceNe :
      resistanceInOhms setup.equivalentResistanceSeenByInductor ≠ 0 :=
    ne_of_gt hPhysical.equivalentResistancePositive
  have hTimeConstantLaw := hLaws.naturalResponseTimeConstantLaw
  rw [hTau, hInductance] at hTimeConstantLaw
  have hProduct :=
    (eq_div_iff hEquivalentResistanceNe).mp hTimeConstantLaw
  norm_num at hProduct ⊢
  linarith

/-- Labels of the four resistance choices printed in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Resistance in ohms displayed beside each answer label. -/
def AnswerChoice.displayedResistanceInOhms : AnswerChoice → ℝ
  | .A => 1000
  | .B => 750
  | .C => 500
  | .D => 700

/-- Dataset answer label retained as metadata and never used as a premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- A displayed choice equals the independently modeled unknown resistance. -/
def AnswerMatchesUnknownResistance
    (setup : ParallelResistorInductorSetup) (choice : AnswerChoice) : Prop :=
  resistanceInOhms setup.unknownResistorR =
    choice.displayedResistanceInOhms

/-- A choice is the unique exact match among the four displayed resistances. -/
def IsUniqueMatchingAnswer
    (setup : ParallelResistorInductorSetup) (choice : AnswerChoice) : Prop :=
  AnswerMatchesUnknownResistance setup choice ∧
    ∀ other : AnswerChoice,
      AnswerMatchesUnknownResistance setup other → other = choice

/-!
From `L / τ = 300 Ω` and `1/300 = 1/500 + 1/R`, the unknown resistance is
`750 Ω`, uniquely matching choice B.  This is the declaration corresponding to
`thm:physics:phyx_mini_0928:target`.
-/
theorem problem_phyx_mini_0928
    (setup : ParallelResistorInductorSetup)
    (hScenario : MatchesIdealSourceFreeRLScenario setup)
    (hFigure : MatchesSuppliedParallelResistorInductorFigure setup)
    (hTimeConstant : MatchesRequestedTimeConstant setup)
    (hPhysical : HasPhysicalParallelRLParameters setup)
    (hLaws : SatisfiesParallelResistanceAndRLTimeConstantLaws setup) :
    resistanceInOhms setup.unknownResistorR = 750 ∧
      IsUniqueMatchingAnswer setup recordedDatasetAnswer := by
  have hEquivalentResistance :=
    equivalentResistanceSeenByInductor_eq_300_ohms
      setup hFigure hTimeConstant hPhysical hLaws
  have hFixedResistance :
      resistanceInOhms setup.fixedResistor = 500 := by
    calc
      resistanceInOhms setup.fixedResistor =
          setup.figure.printedFixedResistanceInOhms :=
        hFigure.fixedResistanceLabelCalibration
      _ = 500 := hFigure.printedFixedResistanceLabel
  have hUnknownResistanceNe :
      resistanceInOhms setup.unknownResistorR ≠ 0 :=
    ne_of_gt hPhysical.unknownResistancePositive
  have hParallelLaw := hLaws.parallelEquivalentResistanceLaw
  rw [hEquivalentResistance, hFixedResistance] at hParallelLaw
  field_simp [hUnknownResistanceNe] at hParallelLaw
  have hUnknownResistance :
      resistanceInOhms setup.unknownResistorR = 750 := by
    linarith
  refine ⟨hUnknownResistance, ?_⟩
  constructor
  · simpa [AnswerMatchesUnknownResistance, recordedDatasetAnswer,
      AnswerChoice.displayedResistanceInOhms] using hUnknownResistance
  · intro other hOther
    unfold AnswerMatchesUnknownResistance at hOther
    rw [hUnknownResistance] at hOther
    cases other with
    | A =>
        norm_num [AnswerChoice.displayedResistanceInOhms] at hOther
    | B =>
        rfl
    | C =>
        norm_num [AnswerChoice.displayedResistanceInOhms] at hOther
    | D =>
        norm_num [AnswerChoice.displayedResistanceInOhms] at hOther

end PhyXMiniProblems.ProblemPhyXMini0928
