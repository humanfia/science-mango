import Mathlib
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0383

open Dimension

/-!
# Force needed to open a pressure-loaded cylinder valve

The supplied figure labels the valve area by `A_valve`, the cylinder pressure
by `P_cyl`, and the exterior pressure by `P_outside`.  The pressure values and
valve area are represented by unit-independent Physlib quantities.  Real
numbers occur only as explicit named-unit readouts and displayed answer values.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/--
A nonnegative force magnitude, independent of the unit used to read it.

Physlib supplies dimensionful pressure and area types but no named force type,
so the standard force dimension `M L T⁻²` is instantiated with its existing
`Dimensionful`/`WithDim` infrastructure.
-/
abbrev ForceMagnitude : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical area in square metres. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Read a physical area in square centimetres. -/
def areaInSquareCentimeters (area : DimArea) : ℝ :=
  ((area {UnitChoices.SI with length := LengthUnit.centimeters}).val : ℝ)

/-- Read a dimensionful pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a dimensionful pressure in kilopascals. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/--
Read a force magnitude in newtons.  In coherent SI units, a quantity of
dimension `M L T⁻²` has numerical unit kilograms-metres-per-second-squared,
which is one newton.
-/
def forceInNewtons (force : ForceMagnitude) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-! ## Figure vocabulary and physical setup -/

/-!
Information visible in the primary image.  The physical quantities attached
to the labels are independent observables; in particular, the opening force is
not stored in the figure.
-/
structure SuppliedValveFigure where
  /-- Cross-sectional area carrying the figure label `A_valve`. -/
  valveAreaAValve : DimArea
  /-- Interior pressure carrying the figure label `P_cyl`. -/
  cylinderPressurePCyl : DimPressure
  /-- Exterior pressure carrying the figure label `P_outside`. -/
  outsidePressurePOutside : DimPressure
  showsCylindricalChamber : Bool
  showsPiston : Bool
  showsValveAtCylinderTop : Bool
  showsInteriorFluidOrGas : Bool
  showsAreaLabelAValve : Bool
  showsPressureLabelPCyl : Bool
  showsPressureLabelPOutside : Bool

/-!
The pressure-loaded valve and the requested force magnitude.  The force is an
independent physical observable constrained by the governing law below; it is
not defined from the recorded answer.
-/
structure ValveCylinderSetup where
  figure : SuppliedValveFigure
  requiredOpeningForce : ForceMagnitude
  pressureIsUniformOnEachValveFace : Bool
  pressureActsNormallyOnValve : Bool
  otherAxialResistanceIsNeglected : Bool

/-!
Qualitative information read from the raster image.  These fields record only
geometry and labels, not the requested force.
-/
def MatchesSuppliedValveFigure (setup : ValveCylinderSetup) : Prop :=
  setup.figure.showsCylindricalChamber = true ∧
    setup.figure.showsPiston = true ∧
    setup.figure.showsValveAtCylinderTop = true ∧
    setup.figure.showsInteriorFluidOrGas = true ∧
    setup.figure.showsAreaLabelAValve = true ∧
    setup.figure.showsPressureLabelPCyl = true ∧
    setup.figure.showsPressureLabelPOutside = true

/-!
The numerical data stated in the problem.  The area is read in `cm²`, and the
two absolute pressures are read in `kPa`.  No force value occurs here.
-/
structure MatchesProblemData (setup : ValveCylinderSetup) : Prop where
  valveAreaSquareCentimeters :
    areaInSquareCentimeters setup.figure.valveAreaAValve = 11
  cylinderPressureKilopascals :
    pressureInKilopascals setup.figure.cylinderPressurePCyl = 735
  outsidePressureKilopascals :
    pressureInKilopascals setup.figure.outsidePressurePOutside = 99

/-- Positivity and ordering conditions selecting the physical pressure state. -/
structure HasPhysicalValveParameters (setup : ValveCylinderSetup) : Prop where
  valveAreaPositive :
    0 < areaInSquareMeters setup.figure.valveAreaAValve
  cylinderPressurePositive :
    0 < pressureInPascals setup.figure.cylinderPressurePCyl
  outsidePressurePositive :
    0 < pressureInPascals setup.figure.outsidePressurePOutside
  cylinderPressureExceedsOutside :
    pressureInPascals setup.figure.outsidePressurePOutside <
      pressureInPascals setup.figure.cylinderPressurePCyl

/-!
The idealized model used by the pressure-force balance: pressure is uniform
and normal to each valve face, and weight, friction, spring loading, and other
axial resistances are omitted.
-/
structure MatchesPressureOnlyOpeningModel
    (setup : ValveCylinderSetup) : Prop where
  pressureUniform : setup.pressureIsUniformOnEachValveFace = true
  pressureNormal : setup.pressureActsNormallyOnValve = true
  noOtherAxialResistance : setup.otherAxialResistanceIsNeglected = true

/-!
Governing pressure-force law in coherent SI readouts.  The two pressures act on
opposite faces of the same valve, so the required opening-force magnitude is
the pressure difference times the cross-sectional area.  This law is generic:
it contains none of the supplied numbers or answer choices.
-/
structure SatisfiesValvePressureForceLaw
    (setup : ValveCylinderSetup) : Prop where
  pressureDifferenceTimesArea :
    forceInNewtons setup.requiredOpeningForce =
      (pressureInPascals setup.figure.cylinderPressurePCyl -
          pressureInPascals setup.figure.outsidePressurePOutside) *
        areaInSquareMeters setup.figure.valveAreaAValve

/-! ## Multiple-choice display and target -/

/-- Labels printed beside the four proposed force magnitudes. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Force in newtons printed beside each answer label. -/
def displayedForceInNewtons : AnswerChoice → ℝ
  | .A => 490
  | .B => 700
  | .C => 154
  | .D => 51 / 5

/-!
A choice is the unique closest displayed force to the derived, unrounded
opening-force magnitude.
-/
def IsUniqueClosestAnswer
    (forceNewtons : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice,
    otherChoice ≠ choice →
      |forceNewtons - displayedForceInNewtons choice| <
        |forceNewtons - displayedForceInNewtons otherChoice|

/-!
The pressure difference is `636 kPa` and the valve area is `11 cm²`, giving
the unrounded SI force `699.6 N = 3498/5 N`.  Therefore `700 N`, answer B, is
the unique closest displayed choice.

This formalizes `thm:physics:phyx_mini_0383:target`.
-/
theorem problem_phyx_mini_0383
    (setup : ValveCylinderSetup)
    (hFigure : MatchesSuppliedValveFigure setup)
    (hData : MatchesProblemData setup)
    (hPhysical : HasPhysicalValveParameters setup)
    (hModel : MatchesPressureOnlyOpeningModel setup)
    (hLaw : SatisfiesValvePressureForceLaw setup) :
    forceInNewtons setup.requiredOpeningForce = 3498 / 5 ∧
      IsUniqueClosestAnswer
        (forceInNewtons setup.requiredOpeningForce) .B := by
  have area_centimeters_eq (area : DimArea) :
      areaInSquareCentimeters area = 10000 * areaInSquareMeters area := by
    change
      ((area {UnitChoices.SI with length := LengthUnit.centimeters}).val : ℝ) =
        10000 * ((area UnitChoices.SI).val : ℝ)
    rw [area.2 UnitChoices.SI
      {UnitChoices.SI with length := LengthUnit.centimeters}]
    have hscale :
        UnitChoices.dimScale UnitChoices.SI
          {UnitChoices.SI with length := LengthUnit.centimeters}
          (dim (WithDim (L𝓭 * L𝓭) NNReal)) = 10000 := by
      apply NNReal.eq
      norm_num [UnitChoices.dimScale, LengthUnit.centimeters,
        LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val]
      change (((100 : NNReal) : ℝ) ^ 2 = 10000)
      norm_num
    rw [hscale]
    norm_num [WithDim.smul_val, NNReal.smul_def, smul_eq_mul]
  have hArea := hData.valveAreaSquareCentimeters
  rw [area_centimeters_eq] at hArea
  have hAreaSI :
      areaInSquareMeters setup.figure.valveAreaAValve = 11 / 10000 := by
    linarith
  have hCyl := hData.cylinderPressureKilopascals
  have hOutside := hData.outsidePressureKilopascals
  norm_num [pressureInKilopascals] at hCyl hOutside
  have hCylPa :
      pressureInPascals setup.figure.cylinderPressurePCyl = 735000 := by
    linarith
  have hOutsidePa :
      pressureInPascals setup.figure.outsidePressurePOutside = 99000 := by
    linarith
  have hForce :
      forceInNewtons setup.requiredOpeningForce = 3498 / 5 := by
    rw [hLaw.pressureDifferenceTimesArea, hCylPa, hOutsidePa, hAreaSI]
    norm_num
  constructor
  · exact hForce
  · rw [hForce]
    unfold IsUniqueClosestAnswer
    intro other hother
    cases other with
    | A => norm_num [displayedForceInNewtons]
    | B => exact (hother rfl).elim
    | C => norm_num [displayedForceInNewtons]
    | D => norm_num [displayedForceInNewtons]

end PhyXMiniProblems.ProblemPhyXMini0383
