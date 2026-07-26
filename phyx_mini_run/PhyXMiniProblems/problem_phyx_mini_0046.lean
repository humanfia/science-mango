import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/-!
# Wavelength from a double-slit bright fringe

This file models the double-slit apparatus shown in the primary figure.  Slit
separation, screen distance, fringe displacement, and wavelength are physical
lengths.  Real scalars occur only as unit readouts and as a dimensionless angle
in radians.

The figure's `9.49 mm` arrow runs from the central bright fringe (`m = 0`) to
the upper `m = 3` bright fringe.  Thus it is the third-fringe displacement,
not the spacing between adjacent fringes.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0046

open Dimension

/-- A signed physical length, represented independently of a chosen unit system. -/
abbrev DimLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Read a physical length as a real scalar in the specified length unit. -/
def lengthValueIn (unit : LengthUnit) (length : DimLength) : ℝ :=
  (length ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- The metre readout of a physical length. -/
def metersValue (length : DimLength) : ℝ :=
  lengthValueIn LengthUnit.meters length

/-- The millimetre readout used for the slit separation and fringe displacement. -/
def millimetersValue (length : DimLength) : ℝ :=
  lengthValueIn LengthUnit.millimeters length

/-- The nanometre readout used by the answer choices. -/
def nanometersValue (length : DimLength) : ℝ :=
  lengthValueIn LengthUnit.nanometers length

/--
The monochromatic light, the pair of slits, and the screen in the depicted
apparatus.  `screenDistanceAlongX` is the figure's horizontal distance `R`,
while `slitSeparation` is its label `d`.
-/
structure DoubleSlitApparatus where
  /-- Separation `d` between the two illuminated slits. -/
  slitSeparation : DimLength
  /-- Distance `R` from the slit plane to the screen along the optical `x` axis. -/
  screenDistanceAlongX : DimLength
  /-- Vacuum wavelength `λ` of the monochromatic incident light. -/
  lightWavelength : DimLength

/--
The signed order, vertical screen coordinate, and ray angle of one bright
fringe.  The central bright fringe is at vertical coordinate zero and order
zero; the observed fringe in the figure lies above it at order `+3`.
-/
structure BrightFringeObservation where
  /-- Signed bright-fringe order `m`. -/
  order : ℤ
  /-- Signed `y` displacement from the central bright fringe on the screen. -/
  verticalDisplacementFromCentral : DimLength
  /-- Propagation angle from the positive optical axis, measured in radians. -/
  angleRadians : ℝ

/--
The four numerical labels read from the problem text and primary figure.
This predicate deliberately contains no readout of the unknown wavelength.
-/
def HasStatedFigureReadouts
    (apparatus : DoubleSlitApparatus)
    (observation : BrightFringeObservation) : Prop :=
  millimetersValue apparatus.slitSeparation = 0.200 ∧
    metersValue apparatus.screenDistanceAlongX = 1.00 ∧
    observation.order = 3 ∧
    millimetersValue observation.verticalDisplacementFromCentral = 9.49

/--
The exact straight-line screen geometry and constructive double-slit
interference law for the observed bright fringe:

* `y = R tan θ`, and
* `d sin θ = m λ`.

The equations use metre readouts so every term in each dimensional equation
has the same scalar unit.  They contain no numerical value for the requested
wavelength.
-/
def SatisfiesDoubleSlitBrightFringeLaws
    (apparatus : DoubleSlitApparatus)
    (observation : BrightFringeObservation) : Prop :=
  0 < metersValue apparatus.slitSeparation ∧
    0 < metersValue apparatus.screenDistanceAlongX ∧
    0 < metersValue apparatus.lightWavelength ∧
    0 < observation.order ∧
    0 < metersValue observation.verticalDisplacementFromCentral ∧
    0 < observation.angleRadians ∧
    observation.angleRadians < Real.pi / 2 ∧
    metersValue observation.verticalDisplacementFromCentral =
      metersValue apparatus.screenDistanceAlongX * Real.tan observation.angleRadians ∧
    metersValue apparatus.slitSeparation * Real.sin observation.angleRadians =
      (observation.order : ℝ) * metersValue apparatus.lightWavelength

/-- Labels of the four multiple-choice answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Each displayed answer choice, expressed as a whole number of nanometres. -/
def answerWavelengthNanometers : AnswerChoice → ℤ
  | .A => 643
  | .B => 633
  | .C => 639
  | .D => 533

/--
The wavelength inferred from the `m = 3` bright-fringe position rounds to
`633 nm`, the dataset's recorded answer choice B.

This formalizes `thm:physics:phyx_mini_0046:target`.
-/
theorem wavelength_rounds_to_recordedAnswerB
    (apparatus : DoubleSlitApparatus)
    (observation : BrightFringeObservation)
    (h_readouts : HasStatedFigureReadouts apparatus observation)
    (h_interference : SatisfiesDoubleSlitBrightFringeLaws apparatus observation) :
    round (nanometersValue apparatus.lightWavelength) =
      answerWavelengthNanometers .B := by
  rcases h_readouts with ⟨hslit_mm, hscreen_m, horder, hdisp_mm⟩
  rcases h_interference with
    ⟨hslit_pos, hscreen_pos, hlambda_pos, horder_pos, hdisp_pos,
      htheta_pos, htheta_upper, hscreen_geometry, hbright⟩
  have millimeters_eq (length : DimLength) :
      millimetersValue length = 1000 * metersValue length := by
    have h := congrArg WithDim.val
      (length.2 ({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices)
        ({ UnitChoices.SI with length := LengthUnit.millimeters } : UnitChoices))
    change millimetersValue length = _ * metersValue length at h
    norm_num [UnitChoices.dimScale, LengthUnit.millimeters, LengthUnit.scale,
      LengthUnit.div_eq_val, LengthUnit.meters, NNReal.smul_def] at h ⊢
    exact h
  have nanometers_eq (length : DimLength) :
      nanometersValue length = 1000000000 * metersValue length := by
    have h := congrArg WithDim.val
      (length.2 ({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices)
        ({ UnitChoices.SI with length := LengthUnit.nanometers } : UnitChoices))
    change nanometersValue length = _ * metersValue length at h
    norm_num [UnitChoices.dimScale, LengthUnit.nanometers, LengthUnit.scale,
      LengthUnit.div_eq_val, LengthUnit.meters, NNReal.smul_def] at h ⊢
    exact h
  have hslit_m : metersValue apparatus.slitSeparation = (1 : ℝ) / 5000 := by
    nlinarith only [hslit_mm, millimeters_eq apparatus.slitSeparation]
  have hdisp_m :
      metersValue observation.verticalDisplacementFromCentral = (949 : ℝ) / 100000 := by
    nlinarith only [hdisp_mm, millimeters_eq observation.verticalDisplacementFromCentral]
  have htan : Real.tan observation.angleRadians = (949 : ℝ) / 100000 := by
    rw [hdisp_m, hscreen_m] at hscreen_geometry
    norm_num at hscreen_geometry ⊢
    linarith only [hscreen_geometry]
  have hneg : -(Real.pi / 2) < observation.angleRadians := by
    have hpi : 0 < Real.pi := Real.pi_pos
    linarith only [hpi, htheta_pos]
  have hcos_pos : 0 < Real.cos observation.angleRadians :=
    Real.cos_pos_of_mem_Ioo ⟨hneg, htheta_upper⟩
  have hratio :
      Real.sin observation.angleRadians =
        (949 : ℝ) / 100000 * Real.cos observation.angleRadians := by
    rw [Real.tan_eq_sin_div_cos] at htan
    field_simp [ne_of_gt hcos_pos] at htan
    linarith only [htan]
  have hratio_sq := congrArg (fun z : ℝ => z ^ 2) hratio
  have htrig := Real.sin_sq_add_cos_sq observation.angleRadians
  have hsin_sq :
      (10000900601 : ℝ) * Real.sin observation.angleRadians ^ 2 = 900601 := by
    nlinarith only [hratio_sq, htrig]
  set x : ℝ := nanometersValue apparatus.lightWavelength
  have hxpos : 0 < x := by
    change 0 < nanometersValue apparatus.lightWavelength
    rw [nanometers_eq apparatus.lightWavelength]
    nlinarith only [hlambda_pos]
  have hx :
      x = (200000 : ℝ) / 3 * Real.sin observation.angleRadians := by
    change nanometersValue apparatus.lightWavelength =
      (200000 : ℝ) / 3 * Real.sin observation.angleRadians
    rw [nanometers_eq apparatus.lightWavelength]
    rw [hslit_m, horder] at hbright
    norm_num at hbright ⊢
    nlinarith only [hbright]
  have hx_sq := congrArg (fun z : ℝ => z ^ 2) hx
  have hpoly :
      (9 * 10000900601 : ℝ) * x ^ 2 = 40000000000 * 900601 := by
    nlinarith only [hsin_sq, hx_sq]
  have hl_sq : ((1265 : ℝ) / 2) ^ 2 ≤ x ^ 2 := by
    nlinarith only [hpoly]
  have hu_sq : x ^ 2 < ((1267 : ℝ) / 2) ^ 2 := by
    nlinarith only [hpoly]
  have hl : (1265 : ℝ) / 2 ≤ x := by
    nlinarith only [hxpos, hl_sq]
  have hu : x < (1267 : ℝ) / 2 := by
    nlinarith only [hxpos, hu_sq]
  change round x = (633 : ℤ)
  rw [round_eq_iff]
  change ((633 : ℝ) - 1 / 2) ≤ x ∧ x < ((633 : ℝ) + 1 / 2)
  constructor
  · norm_num
    exact hl
  · norm_num
    exact hu

end PhyXMiniProblems.ProblemPhyXMini0046
