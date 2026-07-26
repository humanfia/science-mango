import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0335

open Dimension

/-!
# Moment of inertia of a nitrogen molecule

A nitrogen molecule is idealized as two small point masses, each having the
mass of one nitrogen atom, joined by a rigid massless rod. The atom-to-atom
separation is `d = 2 r = 188 pm`. The requested rotation axis passes through
the bond midpoint and is perpendicular to the molecular axis.

Masses, lengths, speeds, angular speeds, and moments of inertia are represented
by unit-independent Physlib quantities. Real numbers occur only as readouts in
explicitly selected units and as displayed multiple-choice values. The
point-mass inertia law is stated independently of the requested numerical
answer.
-/

/-- The physical dimension of translational speed. -/
def speedDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- The physical dimension of angular speed; radians are dimensionless. -/
def angularSpeedDimension : Dimension := T𝓭⁻¹

/-- The physical dimension of moment of inertia, mass times length squared. -/
def momentOfInertiaDimension : Dimension := M𝓭 * L𝓭 * L𝓭

/-- A nonnegative physical mass, independent of its readout unit. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length, independent of its readout unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative translational speed magnitude. -/
abbrev SpeedMagnitudeQuantity : Type :=
  Dimensionful (WithDim speedDimension NNReal)

/-- A nonnegative angular-speed magnitude. -/
abbrev AngularSpeedMagnitudeQuantity : Type :=
  Dimensionful (WithDim angularSpeedDimension NNReal)

/-- A nonnegative physical moment of inertia about a specified axis. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read speed in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedMagnitudeQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read angular speed in radians per selected time unit. -/
def angularSpeedReadout
    (timeUnit : TimeUnit) (angularSpeed : AngularSpeedMagnitudeQuantity) : ℝ :=
  ((angularSpeed {UnitChoices.SI with time := timeUnit}).val : ℝ)

/-- Read moment of inertia in coherent selected mass and length units. -/
def momentOfInertiaReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia {UnitChoices.SI with
    mass := massUnit, length := lengthUnit}).val : ℝ)

/-- Kilogram readout of an atom's physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Meter readout used in the coherent SI inertia law. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Picometer readout used for the stated molecular separation. -/
def lengthInPicometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.picometers length

/-- SI readout of a moment of inertia, in kilogram-meter squared. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  momentOfInertiaReadout MassUnit.kilograms LengthUnit.meters inertia

/-! ## Molecular model and the supplied before/after figure -/

/-- The two nitrogen-atom sites at the ends of the molecular bond. -/
inductive AtomSite where
  | first
  | second
  deriving DecidableEq, Fintype, Repr

/-- The molecular species stated in the problem. -/
inductive MolecularSpecies where
  | diatomicNitrogen
  deriving DecidableEq, Repr

/-- The idealization of each orange ball as a small point mass. -/
inductive AtomBodyModel where
  | smallPointMass
  deriving DecidableEq, Repr

/-- The idealization of the connector between the two atom sites. -/
inductive BondRodModel where
  | rigidMassless
  deriving DecidableEq, Repr

/-- Geometry of the axis about which the moment of inertia is requested. -/
inductive RotationAxisGeometry where
  | throughBondMidpointPerpendicularToMolecularAxis
  deriving DecidableEq, Repr

/-- The two panels explicitly captioned in the supplied image. -/
inductive FigurePanel where
  | before
  | after
  deriving DecidableEq, Fintype, Repr

/-- The upper and lower dumbbells separated by the dashed horizontal line. -/
inductive FigureMolecule where
  | upper
  | lower
  deriving DecidableEq, Fintype, Repr

/-- Orientations of a dumbbell rod appearing in the raster image. -/
inductive RodOrientation where
  | vertical
  | tiltedUpwardRight
  deriving DecidableEq, Repr

/-- Horizontal senses of the green arrows labelled `v_i`. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- Rotation senses of the curved arrows labelled `omega`. -/
inductive RotationSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-!
Data represented in the supplied raster image. The image depicts two
dumbbells before and after an interaction. The common `v_i` and `omega`
labels are retained as dimensionful speed magnitudes, even though neither is
needed to calculate the molecule's static moment of inertia.
-/
structure SuppliedBeforeAfterFigure where
  showsMolecule : FigurePanel → FigureMolecule → Bool
  rodOrientation : FigurePanel → FigureMolecule → RodOrientation
  panelCaption : FigurePanel → String
  initialVelocityArrowShown : FigureMolecule → Bool
  initialVelocityLabel : String
  initialSpeedVi : SpeedMagnitudeQuantity
  initialVelocityDirection : FigureMolecule → HorizontalDirection
  angularVelocityArrowShown : FigureMolecule → Bool
  angularVelocityLabel : String
  angularSpeedOmega : AngularSpeedMagnitudeQuantity
  afterRotationSense : FigureMolecule → RotationSense
  dashedHorizontalDividerShown : Bool

/-!
Independent physical quantities in the molecular model. In particular, the
moment of inertia is an observable constrained only by the governing law
below; it is not defined to equal a displayed answer.
-/
structure NitrogenMoleculeSetup where
  species : MolecularSpecies
  atomBodyModel : AtomBodyModel
  bondRodModel : BondRodModel
  askedAxisGeometry : RotationAxisGeometry
  atomMass : AtomSite → MassQuantity
  bondLengthD : LengthQuantity
  radiusFromMidpointR : LengthQuantity
  distanceFromAskedAxis : AtomSite → LengthQuantity
  momentOfInertiaAboutAskedAxis : MomentOfInertiaQuantity
  suppliedFigure : SuppliedBeforeAfterFigure

/-- The qualitative molecular and rotation-axis model stated in the prose. -/
structure MatchesNitrogenMoleculeScenario
    (setup : NitrogenMoleculeSetup) : Prop where
  nitrogenMolecule : setup.species = .diatomicNitrogen
  atomsAreSmallPointMasses : setup.atomBodyModel = .smallPointMass
  connectorIsRigidAndMassless : setup.bondRodModel = .rigidMassless
  requestedAxis : setup.askedAxisGeometry =
    .throughBondMidpointPerpendicularToMolecularAxis

/-!
The numerical data printed in the question: each atom has mass
`2.3 * 10^-26 kg`, and the atom-to-atom separation is `188 pm`. The requested
moment of inertia does not occur in these readouts.
-/
structure MatchesProblemReadouts (setup : NitrogenMoleculeSetup) : Prop where
  nitrogenAtomMassKilograms :
    ∀ site : AtomSite,
      massInKilograms (setup.atomMass site) = (23 / 10 ^ 27 : ℝ)
  bondLengthPicometers : lengthInPicometers setup.bondLengthD = 188

/-!
The stated relation `d = 2 r` and the midpoint-axis geometry. Both atom sites
are one half-separation from the perpendicular axis. These are geometric
inputs, not the requested inertia value.
-/
structure MatchesMidpointAxisGeometry
    (setup : NitrogenMoleculeSetup) : Prop where
  bondLengthIsTwiceRadius :
    ∀ unit : LengthUnit,
      lengthReadout unit setup.bondLengthD =
        2 * lengthReadout unit setup.radiusFromMidpointR
  bothAtomsAtRadiusR :
    ∀ (site : AtomSite) (unit : LengthUnit),
      lengthReadout unit (setup.distanceFromAskedAxis site) =
        lengthReadout unit setup.radiusFromMidpointR

/-!
Literal panel captions, arrow labels, orientations, and motion senses read
from the primary image. The upper initial arrow points right, the lower one
points left, and the two after-panel angular arrows have opposite senses.
The dashed divider is recorded without interpreting it as the rotation axis.
-/
structure MatchesSuppliedBeforeAfterFigure
    (setup : NitrogenMoleculeSetup) : Prop where
  everyMoleculeShown :
    ∀ (panel : FigurePanel) (molecule : FigureMolecule),
      setup.suppliedFigure.showsMolecule panel molecule = true
  beforeCaption : setup.suppliedFigure.panelCaption .before = "BEFORE"
  afterCaption : setup.suppliedFigure.panelCaption .after = "AFTER"
  beforeRodsVertical :
    ∀ molecule : FigureMolecule,
      setup.suppliedFigure.rodOrientation .before molecule = .vertical
  afterRodsTilted :
    ∀ molecule : FigureMolecule,
      setup.suppliedFigure.rodOrientation .after molecule = .tiltedUpwardRight
  bothInitialVelocityArrowsShown :
    ∀ molecule : FigureMolecule,
      setup.suppliedFigure.initialVelocityArrowShown molecule = true
  initialVelocityText : setup.suppliedFigure.initialVelocityLabel = "v_i"
  upperInitialVelocityPointsRight :
    setup.suppliedFigure.initialVelocityDirection .upper = .right
  lowerInitialVelocityPointsLeft :
    setup.suppliedFigure.initialVelocityDirection .lower = .left
  bothAngularVelocityArrowsShown :
    ∀ molecule : FigureMolecule,
      setup.suppliedFigure.angularVelocityArrowShown molecule = true
  angularVelocityText : setup.suppliedFigure.angularVelocityLabel = "omega"
  upperRotatesClockwise :
    setup.suppliedFigure.afterRotationSense .upper = .clockwise
  lowerRotatesCounterclockwise :
    setup.suppliedFigure.afterRotationSense .lower = .counterclockwise
  dashedDivider : setup.suppliedFigure.dashedHorizontalDividerShown = true

/-- Positivity and nondegeneracy conditions for the modeled quantities. -/
structure HasPhysicalNitrogenMoleculeParameters
    (setup : NitrogenMoleculeSetup) : Prop where
  everyAtomHasPositiveMass :
    ∀ site : AtomSite, 0 < massInKilograms (setup.atomMass site)
  bondLengthPositive : 0 < lengthInMeters setup.bondLengthD
  radiusPositive : 0 < lengthInMeters setup.radiusFromMidpointR
  initialSpeedPositive :
    0 < speedReadout LengthUnit.meters TimeUnit.seconds
      setup.suppliedFigure.initialSpeedVi
  afterAngularSpeedPositive :
    0 < angularSpeedReadout TimeUnit.seconds
      setup.suppliedFigure.angularSpeedOmega

/-!
The general point-mass law `I = sum m_i rho_i^2`, stated in every coherent
mass and length unit. Its radii are independent setup observables related to
`d / 2` only by the separate geometry hypotheses. Thus this law contains
neither the simplified molecular formula nor the numerical answer.
-/
structure SatisfiesTwoPointMassInertiaLaw
    (setup : NitrogenMoleculeSetup) : Prop where
  inertiaIsPointMassSum :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit),
      momentOfInertiaReadout massUnit lengthUnit
          setup.momentOfInertiaAboutAskedAxis =
        ∑ site : AtomSite,
          massReadout massUnit (setup.atomMass site) *
            lengthReadout lengthUnit
                (setup.distanceFromAskedAxis site) ^ 2

/-! ## Displayed answers and derived conclusions -/

/-- The four answer labels printed beside the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed moments of inertia, read in kilogram-meter squared. -/
def displayedMomentOfInertia : AnswerChoice → ℝ
  | .A => 41 / 10 ^ 47
  | .B => 51 / 10 ^ 47
  | .C => 47 / 10 ^ 47
  | .D => 61 / 10 ^ 47

/-- One unit in the final displayed digit of every answer choice. -/
def displayedResolution : ℝ := 1 / 10 ^ 47

/-- Rounding agreement with a displayed answer choice. -/
def MatchesAnswerChoice
    (setup : NitrogenMoleculeSetup) (choice : AnswerChoice) : Prop :=
  |momentOfInertiaInKilogramMetersSquared
        setup.momentOfInertiaAboutAskedAxis -
      displayedMomentOfInertia choice| < displayedResolution / 2

/-- The midpoint relation gives `r = d / 2` in meter readouts. -/
lemma midpoint_radius_in_meters
    (setup : NitrogenMoleculeSetup)
    (hGeometry : MatchesMidpointAxisGeometry setup) :
    lengthInMeters setup.radiusFromMidpointR =
      lengthInMeters setup.bondLengthD / 2 := by
  have h := hGeometry.bondLengthIsTwiceRadius LengthUnit.meters
  change lengthInMeters setup.bondLengthD =
    2 * lengthInMeters setup.radiusFromMidpointR at h
  linarith

/-!
The two equal point masses and the midpoint geometry give the familiar
diatomic formula `I = m d^2 / 2` in SI readouts. This is derived rather than
assumed by the governing-law interface.
-/
lemma diatomic_point_mass_inertia_formula
    (setup : NitrogenMoleculeSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hGeometry : MatchesMidpointAxisGeometry setup)
    (hInertia : SatisfiesTwoPointMassInertiaLaw setup) :
    momentOfInertiaInKilogramMetersSquared
        setup.momentOfInertiaAboutAskedAxis =
      massInKilograms (setup.atomMass .first) *
        lengthInMeters setup.bondLengthD ^ 2 / 2 := by
  have hI :=
    hInertia.inertiaIsPointMassSum
      MassUnit.kilograms LengthUnit.meters
  change
    momentOfInertiaInKilogramMetersSquared
        setup.momentOfInertiaAboutAskedAxis =
      ∑ site : AtomSite,
        massInKilograms (setup.atomMass site) *
          lengthInMeters (setup.distanceFromAskedAxis site) ^ 2 at hI
  have huniv : (Finset.univ : Finset AtomSite) = {.first, .second} := by
    ext site
    cases site <;> simp
  rw [hI, huniv]
  simp only [Finset.mem_singleton, reduceCtorEq, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton]
  have hDistFirst :
      lengthInMeters (setup.distanceFromAskedAxis .first) =
        lengthInMeters setup.radiusFromMidpointR :=
    hGeometry.bothAtomsAtRadiusR .first LengthUnit.meters
  have hDistSecond :
      lengthInMeters (setup.distanceFromAskedAxis .second) =
        lengthInMeters setup.radiusFromMidpointR :=
    hGeometry.bothAtomsAtRadiusR .second LengthUnit.meters
  have hMass :
      massInKilograms (setup.atomMass .second) =
        massInKilograms (setup.atomMass .first) :=
    (hReadouts.nitrogenAtomMassKilograms .second).trans
      (hReadouts.nitrogenAtomMassKilograms .first).symm
  rw [hDistFirst, hDistSecond, hMass,
    midpoint_radius_in_meters setup hGeometry]
  ring

/-!
The stated mass and separation give the exact SI readout
`406456 / 10^51 kg m^2 = 4.06456 * 10^-46 kg m^2`. It rounds to
`4.1 * 10^-46 kg m^2`, choice A, which is uniquely closest among the four
displayed choices.

This is the formal target corresponding to
`thm:physics:phyx_mini_0335:target`.
-/
theorem nitrogen_molecule_moment_of_inertia
    (setup : NitrogenMoleculeSetup)
    (hScenario : MatchesNitrogenMoleculeScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hGeometry : MatchesMidpointAxisGeometry setup)
    (hFigure : MatchesSuppliedBeforeAfterFigure setup)
    (hPhysical : HasPhysicalNitrogenMoleculeParameters setup)
    (hInertia : SatisfiesTwoPointMassInertiaLaw setup) :
    momentOfInertiaInKilogramMetersSquared
          setup.momentOfInertiaAboutAskedAxis =
        (406456 / 10 ^ 51 : ℝ) ∧
      MatchesAnswerChoice setup .A ∧
      ∀ choice : AnswerChoice, choice ≠ .A →
        |momentOfInertiaInKilogramMetersSquared
              setup.momentOfInertiaAboutAskedAxis -
            displayedMomentOfInertia .A| <
          |momentOfInertiaInKilogramMetersSquared
              setup.momentOfInertiaAboutAskedAxis -
            displayedMomentOfInertia choice| := by
  have picometers_eq_trillion_meters (length : LengthQuantity) :
      lengthInPicometers length = 10 ^ 12 * lengthInMeters length := by
    rw [lengthInPicometers, lengthInMeters, lengthReadout, lengthReadout]
    rw [length.2
      ({UnitChoices.SI with length := LengthUnit.meters})
      ({UnitChoices.SI with length := LengthUnit.picometers})]
    simp [UnitChoices.dimScale, LengthUnit.picometers,
      LengthUnit.scale, LengthUnit.div_eq_val]
    left
    field_simp [LengthUnit.val_ne_zero]
    norm_num
    rfl
  have hBondMeters :
      lengthInMeters setup.bondLengthD = 188 / 10 ^ 12 := by
    have h := picometers_eq_trillion_meters setup.bondLengthD
    rw [hReadouts.bondLengthPicometers] at h
    norm_num at h ⊢
    linarith
  have hExact :
      momentOfInertiaInKilogramMetersSquared
          setup.momentOfInertiaAboutAskedAxis =
        (406456 / 10 ^ 51 : ℝ) := by
    rw [diatomic_point_mass_inertia_formula
        setup hReadouts hGeometry hInertia,
      hReadouts.nitrogenAtomMassKilograms .first, hBondMeters]
    norm_num
  refine ⟨hExact, ?_, ?_⟩
  · rw [MatchesAnswerChoice, hExact]
    norm_num [displayedMomentOfInertia, displayedResolution,
      abs_of_nonneg, abs_of_neg]
  · intro choice hChoice
    rw [hExact]
    cases choice <;>
      norm_num [displayedMomentOfInertia, abs_of_nonneg, abs_of_neg] at *

end PhyXMiniProblems.ProblemPhyXMini0335
