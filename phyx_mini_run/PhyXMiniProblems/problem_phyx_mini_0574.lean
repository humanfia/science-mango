import Mathlib
import Physlib.Units.Dimension

/- USER: The assigned source file did not exist when this autoformalization task began. -/

namespace PhyXMiniProblems.ProblemPhyXMini0574

/-!
# Endpoint of the five-step neptunium decay scheme

The source image plots mass number `A` vertically and proton number `Z`
horizontally.  Starting at the labelled neptunium-237 nuclide, the five
pictured displacements are classified, in decay order, as alpha, beta-minus,
alpha, alpha, beta-minus.

Mass number and proton number are dimensionless nucleon counts, so they are
modeled by natural numbers rather than dimensionful real quantities.  An
isotope nevertheless remains a structured physical object carrying both its
mass number and its chemical-element identity.

Assumption/target boundary:

* `MatchesSuppliedDecayFigure` records only the axes, labels, visible path,
  source isotope, question-mark location, and decay modes read from the image.
* `SatisfiesDecayNumberLaws` states the general `A` and `Z` changes for every
  alpha or beta-minus step.
* There are no previous-part results.
* The endpoint coordinates, actinium-225 identity, and answer choice `C` occur
  only in theorem conclusions.
-/

/-! ## Isotopes and the relevant periodic-table data -/

/-- Chemical elements occurring in the displayed decay-chain segment or choices. -/
inductive ChemicalElement where
  | radium
  | actinium
  | thorium
  | protactinium
  | uranium
  | neptunium
  deriving DecidableEq, Fintype, Repr

/-- Proton number `Z` of each chemical element relevant to this problem. -/
def ChemicalElement.atomicNumber : ChemicalElement → ℕ
  | .radium => 88
  | .actinium => 89
  | .thorium => 90
  | .protactinium => 91
  | .uranium => 92
  | .neptunium => 93

/--
A nuclide specified by mass number `A` and chemical element.  Its proton
number is the atomic number of the element; the inequality excludes nuclides
with more protons than nucleons.
-/
structure NuclearIsotope where
  massNumber : ℕ
  element : ChemicalElement
  atomicNumber_le_massNumber : element.atomicNumber ≤ massNumber

/-- Proton-number coordinate `Z` of a nuclide on the supplied plot. -/
def NuclearIsotope.protonNumber (isotope : NuclearIsotope) : ℕ :=
  isotope.element.atomicNumber

/-- The labelled source nuclide, neptunium-237. -/
def neptunium237 : NuclearIsotope where
  massNumber := 237
  element := .neptunium
  atomicNumber_le_massNumber := by decide

/-- Radium-225, displayed as answer choice A. -/
def radium225 : NuclearIsotope where
  massNumber := 225
  element := .radium
  atomicNumber_le_massNumber := by decide

/-- Actinium-229, displayed as answer choice B. -/
def actinium229 : NuclearIsotope where
  massNumber := 229
  element := .actinium
  atomicNumber_le_massNumber := by decide

/-- Actinium-225, displayed as answer choice C. -/
def actinium225 : NuclearIsotope where
  massNumber := 225
  element := .actinium
  atomicNumber_le_massNumber := by decide

/-- Thorium-223, displayed as answer choice D. -/
def thorium223 : NuclearIsotope where
  massNumber := 223
  element := .thorium
  atomicNumber_le_massNumber := by decide

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A | B | C | D
  deriving DecidableEq, Fintype, Repr

/-- Isotope printed beside each answer-choice label. -/
def answerIsotope : AnswerChoice → NuclearIsotope
  | .A => radium225
  | .B => actinium229
  | .C => actinium225
  | .D => thorium223

/-! ## Plot axes, path points, and decay modes -/

/-- Geometric axes of the supplied decay-scheme plot. -/
inductive PlotAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Nuclear count plotted on an axis; both quantities are dimensionless. -/
inductive NuclearPlotQuantity where
  | massNumberA
  | protonNumberZ
  deriving DecidableEq, Fintype, Repr

/--
Physical dimension of either nuclear count plotted in the figure.  Physlib's
multiplicative identity dimension records that `A` and `Z` are dimensionless;
their integer readouts remain natural numbers.
-/
def NuclearPlotQuantity.physicalDimension : NuclearPlotQuantity → Dimension
  | .massNumberA => 1
  | .protonNumberZ => 1

/-- The six black dots, ordered from neptunium-237 toward the question mark. -/
inductive DecayPathPoint where
  | sourceNeptunium237
  | afterFirstDecay
  | afterSecondDecay
  | afterThirdDecay
  | afterFourthDecay
  | questionMark
  deriving DecidableEq, Fintype, Repr

/-- The five green line segments, ordered in the physical decay direction. -/
inductive DecayStep where
  | first | second | third | fourth | fifth
  deriving DecidableEq, Fintype, Repr

/-- Initial plotted point of a green decay segment. -/
def DecayStep.startPoint : DecayStep → DecayPathPoint
  | .first => .sourceNeptunium237
  | .second => .afterFirstDecay
  | .third => .afterSecondDecay
  | .fourth => .afterThirdDecay
  | .fifth => .afterFourthDecay

/-- Final plotted point of a green decay segment. -/
def DecayStep.endPoint : DecayStep → DecayPathPoint
  | .first => .afterFirstDecay
  | .second => .afterSecondDecay
  | .third => .afterThirdDecay
  | .fourth => .afterFourthDecay
  | .fifth => .questionMark

/-- The two kinds of radioactive decay stipulated for the plotted segments. -/
inductive DecayMode where
  | alpha
  | betaMinus
  deriving DecidableEq, Fintype, Repr

/-! ## Independent setup and primary-image evidence -/

/-- Raster-level content of the supplied `A`-versus-`Z` diagram. -/
structure DecaySchemeFigure where
  axisQuantity : PlotAxis → NuclearPlotQuantity
  axisLabel : PlotAxis → String
  pointShown : DecayPathPoint → Bool
  greenSegmentShown : DecayStep → Bool
  sourceLabelPoint : DecayPathPoint
  sourceLabelText : String
  questionMarkPoint : DecayPathPoint

/-!
Independent quantities in the five-step scheme.  In particular, the isotope
at the question mark is an unconstrained field until figure evidence and the
general decay laws are supplied.
-/
structure FiveStepDecayScheme where
  isotopeAt : DecayPathPoint → NuclearIsotope
  decayModeAt : DecayStep → DecayMode
  figure : DecaySchemeFigure

/-!
Facts read from the primary image.  The sloping down-left displacements in the
decay direction are alpha steps, while the same-`A`, one-column-right
displacements are beta-minus steps.  No endpoint isotope is asserted here.
-/
structure MatchesSuppliedDecayFigure (scheme : FiveStepDecayScheme) : Prop where
  horizontalAxisPlotsZ :
    scheme.figure.axisQuantity .horizontal = .protonNumberZ
  verticalAxisPlotsA :
    scheme.figure.axisQuantity .vertical = .massNumberA
  horizontalAxisLabel : scheme.figure.axisLabel .horizontal = "Z"
  verticalAxisLabel : scheme.figure.axisLabel .vertical = "A"
  everyPointShown : ∀ point, scheme.figure.pointShown point = true
  everyGreenSegmentShown :
    ∀ step, scheme.figure.greenSegmentShown step = true
  sourceLabelLocation :
    scheme.figure.sourceLabelPoint = .sourceNeptunium237
  sourceLabelText : scheme.figure.sourceLabelText = "²³⁷Np"
  sourceIsNeptunium237 :
    scheme.isotopeAt .sourceNeptunium237 = neptunium237
  questionMarkLocation : scheme.figure.questionMarkPoint = .questionMark
  firstStepIsAlpha : scheme.decayModeAt .first = .alpha
  secondStepIsBetaMinus : scheme.decayModeAt .second = .betaMinus
  thirdStepIsAlpha : scheme.decayModeAt .third = .alpha
  fourthStepIsAlpha : scheme.decayModeAt .fourth = .alpha
  fifthStepIsBetaMinus : scheme.decayModeAt .fifth = .betaMinus

/-! ## Governing nuclear-number laws -/

/--
Conservation-number effect of one decay.  Alpha decay removes two protons and
four nucleons from the parent; beta-minus decay preserves `A` and converts a
neutron into a proton, increasing the daughter's `Z` by one.
-/
def IsDecayProduct
    (mode : DecayMode) (parent daughter : NuclearIsotope) : Prop :=
  match mode with
  | .alpha =>
      parent.massNumber = daughter.massNumber + 4 ∧
      parent.protonNumber = daughter.protonNumber + 2
  | .betaMinus =>
      parent.massNumber = daughter.massNumber ∧
      daughter.protonNumber = parent.protonNumber + 1

/-- Every pictured segment obeys the number law for its classified mode. -/
structure SatisfiesDecayNumberLaws (scheme : FiveStepDecayScheme) : Prop where
  decayLawAtStep : ∀ step,
    IsDecayProduct (scheme.decayModeAt step)
      (scheme.isotopeAt step.startPoint)
      (scheme.isotopeAt step.endPoint)

/-! ## Target conclusions -/

/--
The five decay-number updates determine the two endpoint coordinates:
mass number `A = 225` and proton number `Z = 89`.
-/
theorem questionMark_coordinates
    (scheme : FiveStepDecayScheme)
    (hFigure : MatchesSuppliedDecayFigure scheme)
    (hLaws : SatisfiesDecayNumberLaws scheme) :
    (scheme.isotopeAt .questionMark).massNumber = 225 ∧
      (scheme.isotopeAt .questionMark).protonNumber = 89 := by
  have hFirst := hLaws.decayLawAtStep .first
  have hSecond := hLaws.decayLawAtStep .second
  have hThird := hLaws.decayLawAtStep .third
  have hFourth := hLaws.decayLawAtStep .fourth
  have hFifth := hLaws.decayLawAtStep .fifth
  have hNeptuniumMass : neptunium237.massNumber = 237 := rfl
  have hNeptuniumProton : neptunium237.protonNumber = 93 := rfl
  simp [hFigure.firstStepIsAlpha, IsDecayProduct, DecayStep.startPoint,
    DecayStep.endPoint, hFigure.sourceIsNeptunium237, hNeptuniumMass,
    hNeptuniumProton] at hFirst
  simp [hFigure.secondStepIsBetaMinus, IsDecayProduct, DecayStep.startPoint,
    DecayStep.endPoint] at hSecond
  simp [hFigure.thirdStepIsAlpha, IsDecayProduct, DecayStep.startPoint,
    DecayStep.endPoint] at hThird
  simp [hFigure.fourthStepIsAlpha, IsDecayProduct, DecayStep.startPoint,
    DecayStep.endPoint] at hFourth
  simp [hFigure.fifthStepIsBetaMinus, IsDecayProduct, DecayStep.startPoint,
    DecayStep.endPoint] at hFifth
  omega

/--
Consequently, the isotope at the question mark is actinium-225, which is
answer choice C.

Blueprint: `thm:physics:phyx_mini_0574:target`.
-/
theorem questionMark_isotope_is_choice_C
    (scheme : FiveStepDecayScheme)
    (hFigure : MatchesSuppliedDecayFigure scheme)
    (hLaws : SatisfiesDecayNumberLaws scheme) :
    scheme.isotopeAt .questionMark = answerIsotope .C := by
  obtain ⟨hMass, hProton⟩ :=
    questionMark_coordinates scheme hFigure hLaws
  rcases hQuestion : scheme.isotopeAt .questionMark with ⟨mass, element, hLe⟩
  have hMass' : mass = 225 := by
    simpa [hQuestion] using hMass
  have hProton' : element.atomicNumber = 89 := by
    simpa [NuclearIsotope.protonNumber, hQuestion] using hProton
  cases element <;>
    simp [ChemicalElement.atomicNumber, answerIsotope, actinium225,
      hMass'] at hProton' ⊢

end PhyXMiniProblems.ProblemPhyXMini0574
