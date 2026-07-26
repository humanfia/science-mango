import Mathlib
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Force needed to open a pressure-loaded cylinder valve

The primary figure shows a valve face at the top of a cylinder.  The fluid
below the valve is labelled `P_cyl`, the region reached by the outlet pipe is
labelled `P_outside`, and the valve face is labelled `A_valve`.  A piston is
also drawn below the cylinder fluid.

Pressure and area use Physlib's unit-independent dimensional quantities.  The
opening-force magnitude is built from the same `Dimensionful` and `WithDim`
infrastructure with dimension `M L T⁻²`.  Real numbers occur only in named-unit
readouts, in the scalar statics balance, and in the displayed answer values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0661

open Dimension

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical force magnitude, independent of the chosen units. -/
abbrev ForceMagnitude : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Coherent-SI square-metre readout of a physical area. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Square-centimetre readout used for the valve-area datum. -/
def areaInSquareCentimeters (area : DimArea) : ℝ :=
  10000 * areaInSquareMeters area

/-- Coherent-SI pascal readout of a physical pressure. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Kilopascal readout used for both pressure data in the problem. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Coherent-SI newton readout of a physical force magnitude. -/
def forceInNewtons (force : ForceMagnitude) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-!
The normal-force magnitude exerted by a uniform pressure on a planar area,
using the coherent SI identity `1 Pa * 1 m² = 1 N`.
-/
def pressureForceInNewtons (pressure : DimPressure) (area : DimArea) : ℝ :=
  pressureInPascals pressure * areaInSquareMeters area

/-! ## Apparatus and primary-figure vocabulary -/

/-- Literal symbolic labels visible in the supplied raster `661.png`. -/
inductive FigureLabel where
  | cylinderPressure
  | outsidePressure
  | valveArea
  deriving DecidableEq, Fintype, Repr

/-- Regions or components to which the visible labels are attached. -/
inductive FigureRegion where
  | cylinderFluid
  | outsidePipe
  | valveFace
  deriving DecidableEq, Fintype, Repr

/-- Qualitative information represented by the piston-cylinder diagram. -/
structure ValveFigure where
  printedSymbol : FigureLabel → String
  labelRegion : FigureLabel → FigureRegion
  showsCylinder : Bool
  showsFluidInCylinder : Bool
  showsPistonBelowFluid : Bool
  showsValveAtCylinderTop : Bool
  showsValveStem : Bool
  showsCurvedPipeLeadingOutside : Bool
  valveSeparatesCylinderFromOutside : Bool

/-!
The independent physical quantities of the problem.  In particular,
`requiredOpeningForce` is not defined from a displayed answer choice.
-/
structure ValveOpeningSetup where
  cylinderPressure : DimPressure
  outsidePressure : DimPressure
  valveCrossSectionalArea : DimArea
  requiredOpeningForce : ForceMagnitude
  cylinderPressureUniform : Bool
  outsidePressureUniformOverValve : Bool
  figure : ValveFigure

/-! ## Scenario, data readouts, figure evidence, and governing law -/

/-- The two stated pressures are uniform loads on opposite sides of the valve. -/
structure MatchesValveCylinderScenario (setup : ValveOpeningSetup) : Prop where
  cylinderSidePressureIsUniform : setup.cylinderPressureUniform = true
  outsideSidePressureIsUniform : setup.outsidePressureUniformOverValve = true

/-!
Primary-image evidence.  This records the three labels and the qualitative
piston, valve, stem, and pipe geometry without imposing a force value.
-/
structure MatchesSuppliedValveFigure (setup : ValveOpeningSetup) : Prop where
  cylinderPressureSymbol :
    setup.figure.printedSymbol .cylinderPressure = "P_cyl"
  outsidePressureSymbol :
    setup.figure.printedSymbol .outsidePressure = "P_outside"
  valveAreaSymbol :
    setup.figure.printedSymbol .valveArea = "A_valve"
  cylinderPressureRegion :
    setup.figure.labelRegion .cylinderPressure = .cylinderFluid
  outsidePressureRegion :
    setup.figure.labelRegion .outsidePressure = .outsidePipe
  valveAreaRegion :
    setup.figure.labelRegion .valveArea = .valveFace
  cylinderShown : setup.figure.showsCylinder = true
  cylinderFluidShown : setup.figure.showsFluidInCylinder = true
  pistonShownBelowFluid : setup.figure.showsPistonBelowFluid = true
  valveShownAtCylinderTop : setup.figure.showsValveAtCylinderTop = true
  valveStemShown : setup.figure.showsValveStem = true
  outsidePipeShown : setup.figure.showsCurvedPipeLeadingOutside = true
  valveSeparatesRegions :
    setup.figure.valveSeparatesCylinderFromOutside = true

/-!
Numerical values stated in the problem.  This contains no opening-force
readout and selects no answer choice.
-/
structure MatchesProblemReadouts (setup : ValveOpeningSetup) : Prop where
  valveAreaSquareCentimeters :
    areaInSquareCentimeters setup.valveCrossSectionalArea = 11
  cylinderPressureKilopascals :
    pressureInKilopascals setup.cylinderPressure = 735
  outsidePressureKilopascals :
    pressureInKilopascals setup.outsidePressure = 99

/-!
Quasistatic normal-force balance at the threshold of opening.  The pressure
load from the cylinder side is balanced by the opposing outside-pressure load
and the applied opening-force magnitude.  This is the governing statics law;
it contains no problem-specific numerical force and no answer label.
-/
structure SatisfiesValveOpeningStatics (setup : ValveOpeningSetup) : Prop where
  incipientOpeningNormalForceBalance :
    pressureForceInNewtons setup.cylinderPressure
        setup.valveCrossSectionalArea =
      pressureForceInNewtons setup.outsidePressure
          setup.valveCrossSectionalArea +
        forceInNewtons setup.requiredOpeningForce

/-! ## Displayed choices and current target -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
Newton values printed beside the four answer labels.  This records the
candidate list without asserting which candidate follows from the model.
-/
def displayedForceInNewtons : AnswerChoice → ℝ
  | .A => 836
  | .B => 70
  | .C => 634
  | .D => 700

/-- A force readout rounds to a displayed whole-newton value. -/
def RoundsToNearestNewton (force : ForceMagnitude) (displayed : ℝ) : Prop :=
  displayed - 1 / 2 ≤ forceInNewtons force ∧
    forceInNewtons force < displayed + 1 / 2

/-- A displayed force choice is at least as close as every alternative. -/
def IsNearestDisplayedForce
    (setup : ValveOpeningSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |forceInNewtons setup.requiredOpeningForce -
        displayedForceInNewtons choice| ≤
      |forceInNewtons setup.requiredOpeningForce -
        displayedForceInNewtons other|

/-!
The pressure difference is `735 - 99 = 636 kPa` and the valve area is
`11 cm² = 11 / 10000 m²`.  Thus the exact force readout is

`636000 Pa * (11 / 10000) m² = 3498 / 5 N = 699.6 N`.

It rounds to `700 N`, and choice D is the unique nearest displayed answer.
This formalizes `thm:physics:phyx_mini_0661:target`.
-/
theorem problem_phyx_mini_0661
    (setup : ValveOpeningSetup)
    (hScenario : MatchesValveCylinderScenario setup)
    (hFigure : MatchesSuppliedValveFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hStatics : SatisfiesValveOpeningStatics setup) :
    forceInNewtons setup.requiredOpeningForce = 3498 / 5 ∧
      RoundsToNearestNewton setup.requiredOpeningForce
        (displayedForceInNewtons .D) ∧
      IsNearestDisplayedForce setup .D ∧
      ∀ choice : AnswerChoice,
        IsNearestDisplayedForce setup choice → choice = .D := by
  have hAreaReadout := hReadouts.valveAreaSquareCentimeters
  have hCylinderReadout := hReadouts.cylinderPressureKilopascals
  have hOutsideReadout := hReadouts.outsidePressureKilopascals
  rw [areaInSquareCentimeters] at hAreaReadout
  rw [pressureInKilopascals] at hCylinderReadout hOutsideReadout
  have hArea :
      areaInSquareMeters setup.valveCrossSectionalArea = (11 : ℝ) / 10000 := by
    linarith
  have hCylinder :
      pressureInPascals setup.cylinderPressure = 735000 := by
    linarith
  have hOutside :
      pressureInPascals setup.outsidePressure = 99000 := by
    linarith
  have hForce : forceInNewtons setup.requiredOpeningForce = 3498 / 5 := by
    have hBalance := hStatics.incipientOpeningNormalForceBalance
    rw [pressureForceInNewtons, pressureForceInNewtons,
      hCylinder, hOutside, hArea] at hBalance
    norm_num at hBalance ⊢
    linarith
  refine ⟨hForce, ?_, ?_, ?_⟩
  · simp [RoundsToNearestNewton, displayedForceInNewtons, hForce]
    norm_num
  · intro other
    rw [hForce]
    cases other <;> norm_num [displayedForceInNewtons]
  · intro choice hNearest
    cases choice with
    | A =>
        have h := hNearest .D
        rw [hForce] at h
        norm_num [displayedForceInNewtons] at h
    | B =>
        have h := hNearest .D
        rw [hForce] at h
        norm_num [displayedForceInNewtons] at h
    | C =>
        have h := hNearest .D
        rw [hForce] at h
        norm_num [displayedForceInNewtons] at h
    | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0661
