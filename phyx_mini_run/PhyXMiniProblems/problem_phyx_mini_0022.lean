import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0022

/-!
# Pfund's refractive-index method

The slab thickness and dark-circle diameter are genuine dimensionful length
quantities.  Numerical coordinates in the diagram and the final answer are
explicit centimeter readouts.  Refractive indices are dimensionless, and the
critical angle is represented by its real-valued radian readout.
-/

open Dimension

/-- A physical length, represented independently of any particular unit choice. -/
abbrev DimLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- SI base units with centimeters, rather than meters, chosen for length. -/
def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The numerical value of a dimensionful length when measured in centimeters. -/
def lengthInCentimeters (length : DimLength) : ℝ :=
  (length centimeterUnitChoices).val

/-- The two optical media meeting at the slab's clear upper face. -/
inductive PfundMedium where
  | glassSlab
  | exteriorAir
  deriving DecidableEq, Repr

/-- The painted lower face and clear upper face shown in the figure. -/
inductive SlabFace where
  | paintedSurface
  | clearSurface
  deriving DecidableEq, Repr

/-- All point labels explicitly shown on the left half of the Pfund diagram. -/
inductive PfundPointLabel where
  | sourceP
  | surfaceA
  | surfaceB
  | surfaceC
  | outgoingAPrime
  | paintedBPrime
  | paintedCPrime
  deriving DecidableEq, Repr

/-- The three labelled ray paths `PAA'`, `PBB'`, and `PCC'`. -/
inductive PfundRayLabel where
  | paaPrime
  | pbbPrime
  | pccPrime
  deriving DecidableEq, Repr

/-- The interface behavior assigned to each labelled ray by the figure. -/
inductive ClearSurfaceBehavior where
  | emergesIntoAir
  | criticalReflection
  | totalInternalReflection
  deriving DecidableEq, Repr

/-- A two-dimensional coordinate readout, with both components measured in centimeters. -/
structure FigurePointCentimeters where
  horizontal : ℝ
  vertical : ℝ

/-- Scalar readouts taken from the Pfund-method diagram. -/
structure PfundFigureReadout where
  point : PfundPointLabel → FigurePointCentimeters
  faceHeightCentimeters : SlabFace → ℝ
  rayBehavior : PfundRayLabel → ClearSurfaceBehavior

/--
The physical quantities and material data of one Pfund-method experiment.
The diameter is an unknown physical length; no numerical answer is stored in
this structure.
-/
structure PfundExperiment where
  figure : PfundFigureReadout
  slabThickness : DimLength
  darkCircleDiameter : DimLength
  refractiveIndexDimensionless : PfundMedium → ℝ
  criticalAngleRadians : ℝ

/--
The labelled surface incidences, ray behaviors, and dark-circle boundary read
from the figure.  The diameter relation only says that rotational symmetry
makes the full diameter twice the left critical-ray radius `PB'`; it does not
state the requested numerical value or the derived `4 t tan θ_c` formula.
-/
structure MatchesPfundFigure (setup : PfundExperiment) : Prop where
  paintedHeight :
    setup.figure.faceHeightCentimeters .paintedSurface = 0
  clearHeight :
    setup.figure.faceHeightCentimeters .clearSurface =
      lengthInCentimeters setup.slabThickness
  sourceOnPainted :
    (setup.figure.point .sourceP).vertical =
      setup.figure.faceHeightCentimeters .paintedSurface
  bPrimeOnPainted :
    (setup.figure.point .paintedBPrime).vertical =
      setup.figure.faceHeightCentimeters .paintedSurface
  cPrimeOnPainted :
    (setup.figure.point .paintedCPrime).vertical =
      setup.figure.faceHeightCentimeters .paintedSurface
  aOnClear :
    (setup.figure.point .surfaceA).vertical =
      setup.figure.faceHeightCentimeters .clearSurface
  bOnClear :
    (setup.figure.point .surfaceB).vertical =
      setup.figure.faceHeightCentimeters .clearSurface
  cOnClear :
    (setup.figure.point .surfaceC).vertical =
      setup.figure.faceHeightCentimeters .clearSurface
  aPrimeAboveClear :
    setup.figure.faceHeightCentimeters .clearSurface <
      (setup.figure.point .outgoingAPrime).vertical
  criticalRayLeftToRight :
    (setup.figure.point .paintedBPrime).horizontal <
      (setup.figure.point .surfaceB).horizontal ∧
    (setup.figure.point .surfaceB).horizontal <
      (setup.figure.point .sourceP).horizontal
  rayAemerges :
    setup.figure.rayBehavior .paaPrime = .emergesIntoAir
  rayBisCritical :
    setup.figure.rayBehavior .pbbPrime = .criticalReflection
  rayCtotallyReflects :
    setup.figure.rayBehavior .pccPrime = .totalInternalReflection
  diameterFromCriticalBoundary :
    lengthInCentimeters setup.darkCircleDiameter =
      2 * ((setup.figure.point .sourceP).horizontal -
        (setup.figure.point .paintedBPrime).horizontal)

/--
The right-triangle geometry of the incident critical segment `PB` and the
reflected segment `BB'`.  Equal incident and reflection angles, together with
the common slab thickness, give the same horizontal run for both segments.
-/
structure SatisfiesCriticalRayGeometry (setup : PfundExperiment) : Prop where
  incidentHorizontalRun :
    (setup.figure.point .sourceP).horizontal -
        (setup.figure.point .surfaceB).horizontal =
      lengthInCentimeters setup.slabThickness *
        Real.tan setup.criticalAngleRadians
  reflectedHorizontalRun :
    (setup.figure.point .surfaceB).horizontal -
        (setup.figure.point .paintedBPrime).horizontal =
      lengthInCentimeters setup.slabThickness *
        Real.tan setup.criticalAngleRadians

/--
Snell's law at the glass--air critical angle, with the physical acute-angle
branch and positive material indices made explicit.
-/
structure SatisfiesPfundCriticalAngleLaw (setup : PfundExperiment) : Prop where
  exteriorIndexPositive :
    0 < setup.refractiveIndexDimensionless .exteriorAir
  glassIndexLarger :
    setup.refractiveIndexDimensionless .exteriorAir <
      setup.refractiveIndexDimensionless .glassSlab
  slabThicknessPositive :
    0 < lengthInCentimeters setup.slabThickness
  criticalAnglePositive :
    0 < setup.criticalAngleRadians
  criticalAngleAcute :
    setup.criticalAngleRadians < Real.pi / 2
  snellAtCriticalAngle :
    setup.refractiveIndexDimensionless .glassSlab *
        Real.sin setup.criticalAngleRadians =
      setup.refractiveIndexDimensionless .exteriorAir

/-- The four printed multiple-choice labels. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The diameter in centimeters displayed beside each answer choice. -/
def answerDiameterCentimeters : AnswerChoice → ℝ
  | .A => 1.99
  | .B => 1.82
  | .C => 2.10
  | .D => 2.48

/-- Agreement with a diameter displayed to the nearest hundredth centimeter. -/
def MatchesAnswerToNearestHundredth
    (diameter : DimLength) (choice : AnswerChoice) : Prop :=
  |lengthInCentimeters diameter - answerDiameterCentimeters choice| ≤ 0.005

/-
The two equal horizontal runs of the critical ray make the dark-circle radius
`2 t tan θ_c`; rotational symmetry therefore makes its diameter
`4 t tan θ_c`.
-/
lemma critical_ray_diameter_formula
    (setup : PfundExperiment)
    (figure : MatchesPfundFigure setup)
    (geometry : SatisfiesCriticalRayGeometry setup) :
    lengthInCentimeters setup.darkCircleDiameter =
      4 * lengthInCentimeters setup.slabThickness *
        Real.tan setup.criticalAngleRadians := by
  calc
    lengthInCentimeters setup.darkCircleDiameter =
        2 * ((setup.figure.point .sourceP).horizontal -
          (setup.figure.point .paintedBPrime).horizontal) :=
      figure.diameterFromCriticalBoundary
    _ = 2 * (((setup.figure.point .sourceP).horizontal -
          (setup.figure.point .surfaceB).horizontal) +
        ((setup.figure.point .surfaceB).horizontal -
          (setup.figure.point .paintedBPrime).horizontal)) := by ring
    _ = 4 * lengthInCentimeters setup.slabThickness *
        Real.tan setup.criticalAngleRadians := by
      rw [geometry.incidentHorizontalRun, geometry.reflectedHorizontalRun]
      ring

/-
For glass of refractive index `1.52` in air and a `0.600 cm` slab, Snell's
critical-angle law and the figure geometry make the dark-circle diameter
round to `2.10 cm`, answer choice C.

This is the formalization of `thm:physics:phyx_mini_0022:target`.
-/
theorem problem_phyx_mini_0022
    (setup : PfundExperiment)
    (figure : MatchesPfundFigure setup)
    (geometry : SatisfiesCriticalRayGeometry setup)
    (optics : SatisfiesPfundCriticalAngleLaw setup)
    (glassIndexReadout :
      setup.refractiveIndexDimensionless .glassSlab = 1.52)
    (airIndexReadout :
      setup.refractiveIndexDimensionless .exteriorAir = 1.00)
    (thicknessReadout :
      lengthInCentimeters setup.slabThickness = 0.600) :
    lengthInCentimeters setup.darkCircleDiameter =
        4 * lengthInCentimeters setup.slabThickness *
          Real.tan setup.criticalAngleRadians ∧
      MatchesAnswerToNearestHundredth setup.darkCircleDiameter .C := by
  have diameterFormula :=
    critical_ray_diameter_formula setup figure geometry
  constructor
  · exact diameterFormula
  · have hsin :
        Real.sin setup.criticalAngleRadians = (25 : ℝ) / 38 := by
      have hsnell := optics.snellAtCriticalAngle
      rw [glassIndexReadout, airIndexReadout] at hsnell
      norm_num at hsnell ⊢
      linarith
    have hcosPos :
        0 < Real.cos setup.criticalAngleRadians := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith [optics.criticalAnglePositive, Real.pi_pos]
      · exact optics.criticalAngleAcute
    have hcosSq :
        Real.cos setup.criticalAngleRadians ^ 2 = (819 : ℝ) / 1444 := by
      have htrig := Real.sin_sq_add_cos_sq setup.criticalAngleRadians
      rw [hsin] at htrig
      norm_num at htrig ⊢
      linarith
    have htanCos :
        Real.tan setup.criticalAngleRadians *
            Real.cos setup.criticalAngleRadians = (25 : ℝ) / 38 := by
      rw [Real.tan_mul_cos hcosPos.ne', hsin]
    have htanSq :
        Real.tan setup.criticalAngleRadians ^ 2 = (625 : ℝ) / 819 := by
      have hsq := congrArg (fun x : ℝ => x ^ 2) htanCos
      ring_nf at hsq
      rw [hcosSq] at hsq
      norm_num at hsq ⊢
      linarith
    have htanPos :
        0 < Real.tan setup.criticalAngleRadians :=
      Real.tan_pos_of_pos_of_lt_pi_div_two
        optics.criticalAnglePositive optics.criticalAngleAcute
    have htanLower :
        (419 : ℝ) / 480 ≤ Real.tan setup.criticalAngleRadians := by
      nlinarith [sq_nonneg
        (Real.tan setup.criticalAngleRadians - (419 : ℝ) / 480)]
    have htanUpper :
        Real.tan setup.criticalAngleRadians ≤ (421 : ℝ) / 480 := by
      nlinarith [sq_nonneg
        (Real.tan setup.criticalAngleRadians - (421 : ℝ) / 480)]
    rw [MatchesAnswerToNearestHundredth, answerDiameterCentimeters,
      diameterFormula, thicknessReadout, abs_le]
    norm_num
    constructor <;> linarith

end PhyXMiniProblems.ProblemPhyXMini0022
