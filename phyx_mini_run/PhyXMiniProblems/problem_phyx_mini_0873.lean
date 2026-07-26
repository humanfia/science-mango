import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0873

open Dimension

/-!
# Capacitance of two oppositely charged metal spheres

The primary figure shows two metal spheres.  The left sphere carries the
label `+20 nC`, the right sphere carries the label `-20 nC`, and a horizontal
double-headed arrow between them is labelled `ΔV = 100 V`.

Charge, potential difference, and capacitance are represented as
unit-independent Physlib quantities.  Real numbers occur only as calibrated
readouts in coulombs, volts, farads, and their nano-scaled units.

Assumption/target split:

* governing laws: the spheres carry equal and opposite charge, and the charge
  magnitude of a two-conductor capacitor obeys `|Q| = C ΔV`;
* previous-part results: none;
* figure/data readouts: two metal spheres at the left and right, their sign
  glyphs and `+20 nC`/`-20 nC` labels, and the horizontal double-headed
  `ΔV = 100 V` arrow;
* target conclusions: the capacitance is `0.20 nF` and therefore matches the
  recorded answer D.

Neither the requested capacitance nor its matching answer is a setup field or
premise.
-/

/-! ## Dimensionful electrical quantities and unit readouts -/

/-- The dimension `M L² T⁻² C⁻¹` of electric potential difference. -/
def potentialDifferenceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Capacitance has dimension charge divided by potential difference. -/
def capacitanceDimension : Dimension :=
  C𝓭 * potentialDifferenceDimension⁻¹

/-- A signed, unit-independent physical electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative, unit-independent potential-difference magnitude. -/
abbrev PotentialDifferenceQuantity : Type :=
  Dimensionful (WithDim potentialDifferenceDimension NNReal)

/-- A nonnegative, unit-independent physical capacitance. -/
abbrev CapacitanceQuantity : Type :=
  Dimensionful (WithDim capacitanceDimension NNReal)

/-- Coherent-SI readout of a signed electric charge, in coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Nanocoulomb readout used by the two charge labels in the figure. -/
def chargeInNanocoulombs (charge : SignedChargeQuantity) : ℝ :=
  (10 : ℝ) ^ 9 * chargeInCoulombs charge

/-- Coherent-SI readout of a potential difference, in volts. -/
def potentialDifferenceInVolts
    (potentialDifference : PotentialDifferenceQuantity) : ℝ :=
  ((potentialDifference UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of a capacitance, in farads. -/
def capacitanceInFarads (capacitance : CapacitanceQuantity) : ℝ :=
  ((capacitance UnitChoices.SI).val : ℝ)

/-- Nanofarad readout used by the four displayed answer choices. -/
def capacitanceInNanofarads (capacitance : CapacitanceQuantity) : ℝ :=
  (10 : ℝ) ^ 9 * capacitanceInFarads capacitance

/-! ## Named spheres and primary-figure content -/

/-- The two physical spheres, named by their positions in the figure. -/
inductive SphereLabel where
  | leftSphere
  | rightSphere
  deriving DecidableEq, Fintype, Repr

/-- Horizontal positions available to the two sphere drawings. -/
inductive HorizontalPosition where
  | left
  | right
  deriving DecidableEq, Repr

/-- Material classification needed to state that both bodies are metal. -/
inductive BodyMaterial where
  | metal
  | other
  deriving DecidableEq, Repr

/-- Shape classification needed to preserve the spherical geometry. -/
inductive BodyShape where
  | sphere
  | other
  deriving DecidableEq, Repr

/-- Sign glyph drawn at the centre of a sphere in the supplied image. -/
inductive FigureChargeSign where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- Horizontal position expected for each named sphere. -/
def expectedHorizontalPosition : SphereLabel → HorizontalPosition
  | .leftSphere => .left
  | .rightSphere => .right

/-- Sign glyph expected inside each sphere. -/
def expectedChargeSign : SphereLabel → FigureChargeSign
  | .leftSphere => .plus
  | .rightSphere => .minus

/-- Signed nanocoulomb value printed above each sphere. -/
def expectedPrintedChargeInNanocoulombs : SphereLabel → ℝ
  | .leftSphere => 20
  | .rightSphere => -20

/-- Literal presentation data transcribed from image `873.png`. -/
structure TwoSphereFigure where
  sphereCircleShown : SphereLabel → Bool
  horizontalPosition : SphereLabel → HorizontalPosition
  chargeSignGlyph : SphereLabel → FigureChargeSign
  printedChargeInNanocoulombs : SphereLabel → ℝ
  potentialDifferenceArrowShown : Bool
  potentialDifferenceArrowIsHorizontal : Bool
  potentialDifferenceArrowIsDoubleHeaded : Bool
  voltageLabel : PotentialDifferenceQuantity
  printedPotentialDifferenceInVolts : ℝ

/-!
The independent physical bodies and electrical observables.  In particular,
`capacitance` is not defined from the charge and voltage labels or from an
answer choice; it is constrained only by the governing law below.
-/
structure TwoMetalSphereCapacitorSetup where
  figure : TwoSphereFigure
  material : SphereLabel → BodyMaterial
  shape : SphereLabel → BodyShape
  charge : SphereLabel → SignedChargeQuantity
  potentialDifference : PotentialDifferenceQuantity
  capacitance : CapacitanceQuantity

/-! ## Problem statement and figure-derived assumptions -/

/--
The material, geometry, and numerical labels supplied by the question and its
primary image.  No capacitance value or answer label occurs in these data.
-/
structure MatchesProblemAndFigureReadouts
    (setup : TwoMetalSphereCapacitorSetup) : Prop where
  bothBodiesAreMetal : ∀ sphere, setup.material sphere = .metal
  bothBodiesAreSpheres : ∀ sphere, setup.shape sphere = .sphere
  bothSphereCirclesShown : ∀ sphere,
    setup.figure.sphereCircleShown sphere = true
  spherePositions : ∀ sphere,
    setup.figure.horizontalPosition sphere = expectedHorizontalPosition sphere
  chargeSignGlyphs : ∀ sphere,
    setup.figure.chargeSignGlyph sphere = expectedChargeSign sphere
  printedChargeLabels : ∀ sphere,
    setup.figure.printedChargeInNanocoulombs sphere =
      expectedPrintedChargeInNanocoulombs sphere
  physicalChargesMatchPrintedLabels : ∀ sphere,
    chargeInNanocoulombs (setup.charge sphere) =
      setup.figure.printedChargeInNanocoulombs sphere
  voltageArrowShown : setup.figure.potentialDifferenceArrowShown = true
  voltageArrowHorizontal :
    setup.figure.potentialDifferenceArrowIsHorizontal = true
  voltageArrowDoubleHeaded :
    setup.figure.potentialDifferenceArrowIsDoubleHeaded = true
  voltageLabelIsPhysicalPotentialDifference :
    setup.figure.voltageLabel = setup.potentialDifference
  printedVoltageLabel :
    setup.figure.printedPotentialDifferenceInVolts = 100
  physicalVoltageMatchesPrintedLabel :
    potentialDifferenceInVolts setup.potentialDifference =
      setup.figure.printedPotentialDifferenceInVolts

/-- Positivity and sign conditions selecting the physical configuration. -/
structure HasPhysicalParameters
    (setup : TwoMetalSphereCapacitorSetup) : Prop where
  leftSpherePositivelyCharged :
    0 < chargeInCoulombs (setup.charge .leftSphere)
  rightSphereNegativelyCharged :
    chargeInCoulombs (setup.charge .rightSphere) < 0
  potentialDifferencePositive :
    0 < potentialDifferenceInVolts setup.potentialDifference
  capacitancePositive :
    0 < capacitanceInFarads setup.capacitance

/-! ## Governing capacitance law -/

/-!
For a two-conductor capacitor, the conductors carry equal and opposite charge
and the magnitude on either conductor satisfies `|Q| = C ΔV`.  This is the
general capacitor law in coherent SI readouts and contains no numerical
capacitance from the current question.
-/
structure SatisfiesTwoConductorCapacitanceLaw
    (setup : TwoMetalSphereCapacitorSetup) : Prop where
  chargesAreEqualAndOpposite :
    chargeInCoulombs (setup.charge .leftSphere) =
      -chargeInCoulombs (setup.charge .rightSphere)
  chargeVoltageRelation : ∀ sphere,
    |chargeInCoulombs (setup.charge sphere)| =
      capacitanceInFarads setup.capacitance *
        potentialDifferenceInVolts setup.potentialDifference

/-! ## Derived capacitance and displayed answer -/

/-- The capacitor law can be rearranged to `C = |Q| / ΔV`. -/
lemma capacitance_eq_chargeMagnitude_div_potentialDifference
    (setup : TwoMetalSphereCapacitorSetup)
    (hPhysical : HasPhysicalParameters setup)
    (hLaw : SatisfiesTwoConductorCapacitanceLaw setup) :
    capacitanceInFarads setup.capacitance =
      |chargeInCoulombs (setup.charge .leftSphere)| /
        potentialDifferenceInVolts setup.potentialDifference := by
  apply (eq_div_iff (ne_of_gt hPhysical.potentialDifferencePositive)).2
  exact (hLaw.chargeVoltageRelation .leftSphere).symm

/-!
Substituting `|Q| = 20 nC` and `ΔV = 100 V` gives
`C = 2 * 10⁻¹⁰ F = 0.20 nF`.
-/
lemma capacitance_eq_oneFifth_nanofarad
    (setup : TwoMetalSphereCapacitorSetup)
    (hData : MatchesProblemAndFigureReadouts setup)
    (hPhysical : HasPhysicalParameters setup)
    (hLaw : SatisfiesTwoConductorCapacitanceLaw setup) :
    capacitanceInNanofarads setup.capacitance = (1 / 5 : ℝ) := by
  have hChargeNano :
      chargeInNanocoulombs (setup.charge .leftSphere) = 20 := by
    simpa [expectedPrintedChargeInNanocoulombs] using
      (hData.physicalChargesMatchPrintedLabels .leftSphere).trans
        (hData.printedChargeLabels .leftSphere)
  have hVoltage :
      potentialDifferenceInVolts setup.potentialDifference = 100 :=
    hData.physicalVoltageMatchesPrintedLabel.trans hData.printedVoltageLabel
  have hCap := capacitance_eq_chargeMagnitude_div_potentialDifference
    setup hPhysical hLaw
  rw [abs_of_pos hPhysical.leftSpherePositivelyCharged, hVoltage] at hCap
  norm_num [chargeInNanocoulombs] at hChargeNano
  norm_num [capacitanceInNanofarads]
  linarith

/-- Labels of the four capacitance choices printed in the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Capacitance in nanofarads printed beside each answer choice. -/
def answerCapacitanceInNanofarads : AnswerChoice → ℝ
  | .A => 22 / 100
  | .B => 120 / 100
  | .C => 25 / 100
  | .D => 20 / 100

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A displayed choice matches the independently modeled capacitance. -/
def AnswerMatchesCapacitance
    (setup : TwoMetalSphereCapacitorSetup) (choice : AnswerChoice) : Prop :=
  capacitanceInNanofarads setup.capacitance =
    answerCapacitanceInNanofarads choice

/-!
The two metal spheres carry charge magnitude `20 nC` across `100 V`, so the
two-conductor capacitance law gives `C = 0.20 nF`, which is answer D.

This declaration formalizes `thm:physics:phyx_mini_0873:target`.  Neither the
`0.20 nF` result nor the matching answer occurs in any premise.
-/
theorem problem_phyx_mini_0873
    (setup : TwoMetalSphereCapacitorSetup)
    (hData : MatchesProblemAndFigureReadouts setup)
    (hPhysical : HasPhysicalParameters setup)
    (hLaw : SatisfiesTwoConductorCapacitanceLaw setup) :
    capacitanceInNanofarads setup.capacitance = (1 / 5 : ℝ) ∧
      AnswerMatchesCapacitance setup recordedDatasetAnswer := by
  refine
    ⟨capacitance_eq_oneFifth_nanofarad setup hData hPhysical hLaw, ?_⟩
  norm_num [AnswerMatchesCapacitance, recordedDatasetAnswer,
    answerCapacitanceInNanofarads,
    capacitance_eq_oneFifth_nanofarad setup hData hPhysical hLaw]

end PhyXMiniProblems.ProblemPhyXMini0873
