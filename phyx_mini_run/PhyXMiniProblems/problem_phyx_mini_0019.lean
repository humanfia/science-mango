import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0019

/-!
# Critical refraction at a flint-glass prism

The refractive indices are dimensionless physical quantities represented with
Physlib's unit-independent `Dimensionful (WithDim 1 ℝ)` type.  Angles and
displayed numerical answers are scalar readouts in radians and decimal form.

Assumption/target boundary:

* `SnellLawAtInterface` and the two total-internal-reflection predicates are
  governing-law interfaces.
* There are no previous-part results.
* `PrismRayDiagram` and the corresponding hypotheses record the labels and
  geometry read from the primary image.  The separate hypothesis
  `hFlintGlassTable` records the non-figure material calibration `n₁ = 1.66`.
* The original-water reflection and lower-interface refraction describe the
  initial ray branch shown in the figure.
* The symbolic critical relation, rounded threshold, and answer choice C
  occur only as conclusions or in the independent answer-choice table.
-/

/-- A unit-independent dimensionless refractive index. -/
abbrev RefractiveIndexQuantity : Type :=
  Dimensionful (WithDim (1 : Dimension) ℝ)

/-- The scalar readout of a dimensionless refractive index. -/
def refractiveIndexValue (index : RefractiveIndexQuantity) : ℝ :=
  (index UnitChoices.SI).val

/--
An optical medium together with its positive, dimensionless refractive index.
This keeps the physical role of `n₁` and `n₂` explicit while exposing the
scalar readout used by Snell's law.
-/
structure OpticalMedium where
  refractiveIndex : RefractiveIndexQuantity
  refractiveIndex_pos : 0 < refractiveIndexValue refractiveIndex

/-- Convert an angle readout in degrees to its value in radians. -/
def radiansOfDegrees (angleDegrees : ℝ) : ℝ :=
  angleDegrees * Real.pi / 180

/--
The angle labels read from the prism diagram.  Every angle is measured in
radians.  Incidence and refraction angles are measured from the local surface
normal, while the two vertex angles are interior prism angles.
-/
structure PrismRayDiagram where
  /-- The `60.0°` interior angle at the upper-left vertex. -/
  upperLeftVertexAngle : ℝ
  /-- The `30.0°` interior angle at the right vertex. -/
  rightVertexAngle : ℝ
  /-- Incidence angle where the horizontal ray enters the vertical face. -/
  entryIncidenceAngle : ℝ
  /-- Figure label `θ₁`: incidence angle at point `P` on the sloping face. -/
  theta1AtP : ℝ
  /-- Figure label `θ₂`: incidence angle at the lower horizontal face. -/
  theta2AtBase : ℝ
  /-- Figure label `θ₃`: transmitted angle in the surrounding liquid. -/
  theta3Outside : ℝ

/--
Snell's law at an interface.  Refractive indices are dimensionless, and the
two real angles are radian readouts measured from the interface normal.
-/
def SnellLawAtInterface
    (incident transmitted : OpticalMedium)
    (incidenceAngle transmittedAngle : ℝ) : Prop :=
  0 ≤ incidenceAngle ∧ incidenceAngle ≤ Real.pi / 2 ∧
    0 ≤ transmittedAngle ∧ transmittedAngle ≤ Real.pi / 2 ∧
      refractiveIndexValue incident.refractiveIndex * Real.sin incidenceAngle =
        refractiveIndexValue transmitted.refractiveIndex * Real.sin transmittedAngle

/--
The total-internal-reflection regime for a ray going from `incident` to
`transmitted`: the incident medium has the larger refractive index and the
Snell-law sine demand exceeds the largest value available in the transmitted
medium.
-/
def TotalInternalReflectionAt
    (incident transmitted : OpticalMedium) (incidenceAngle : ℝ) : Prop :=
  0 ≤ incidenceAngle ∧ incidenceAngle ≤ Real.pi / 2 ∧
    refractiveIndexValue transmitted.refractiveIndex <
        refractiveIndexValue incident.refractiveIndex ∧
      refractiveIndexValue transmitted.refractiveIndex <
        refractiveIndexValue incident.refractiveIndex * Real.sin incidenceAngle

/--
The threshold at which total internal reflection ceases.  At the critical
configuration the transmitted ray is tangent to the interface, so its angle
from the normal is `π / 2` and Snell's law holds at that angle.
-/
def TotalInternalReflectionCeasesAt
    (incident transmitted : OpticalMedium) (incidenceAngle : ℝ) : Prop :=
  refractiveIndexValue transmitted.refractiveIndex <
      refractiveIndexValue incident.refractiveIndex ∧
    SnellLawAtInterface incident transmitted incidenceAngle (Real.pi / 2)

/-- The four numerical choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq

/-- Dimensionless refractive-index readout associated with an answer choice. -/
def answerChoiceValue : AnswerChoice → ℝ
  | .A => 2.01
  | .B => 1.82
  | .C => 1.44
  | .D => 1.50

/--
`value` rounds to `displayed` to the hundredth place.  The strict half-unit
interval avoids assigning a midpoint to both neighboring displayed values.
-/
def RoundsToHundredth (value displayed : ℝ) : Prop :=
  |value - displayed| < (1 : ℝ) / 200

/--
At the critical configuration, Snell's law gives the symbolic value of the
surrounding medium's threshold refractive index.  This is the governing
relation behind the numerical answer and does not assume that answer.
-/
lemma criticalRefraction_thresholdRelation
    (flintGlass thresholdSolution : OpticalMedium)
    (incidenceAngleAtP : ℝ)
    (hCessation :
      TotalInternalReflectionCeasesAt
        flintGlass thresholdSolution incidenceAngleAtP) :
    refractiveIndexValue thresholdSolution.refractiveIndex =
      refractiveIndexValue flintGlass.refractiveIndex *
        Real.sin incidenceAngleAtP := by
  rcases hCessation with ⟨_, _, _, _, _, hSnell⟩
  simpa [SnellLawAtInterface] using hSnell.symm

/--
For the `30°-60°-90°` flint-glass prism in the figure, increasing the liquid's
index until total internal reflection just ceases at `P` gives a threshold
that rounds to `1.44`, hence answer choice C.

`hFlintGlassTable` is the material-data readout `n₁ = 1.66`.  The hypotheses
about the original water and the lower interface record the reflected branch
shown in the figure before the dissolved substance raises the surrounding
index.  The current target is only the rounded threshold value; it is not a
field or hypothesis.

Blueprint: `thm:physics:phyx_mini_0019:target`.
-/
theorem dissolvedSubstanceThreshold_isChoiceC
    (flintGlass originalWater thresholdSolution : OpticalMedium)
    (diagram : PrismRayDiagram)
    (hFlintGlassTable :
      refractiveIndexValue flintGlass.refractiveIndex = 1.66)
    (hUpperLeftVertex :
      diagram.upperLeftVertexAngle = radiansOfDegrees 60)
    (hRightVertex : diagram.rightVertexAngle = radiansOfDegrees 30)
    (hNormalEntry : diagram.entryIncidenceAngle = 0)
    (hPointPGeometry : diagram.theta1AtP = radiansOfDegrees 60)
    (hReflectedRayGeometry : diagram.theta2AtBase = radiansOfDegrees 30)
    (hInitialWaterTIR :
      TotalInternalReflectionAt flintGlass originalWater diagram.theta1AtP)
    (hBaseRefraction :
      SnellLawAtInterface
        flintGlass originalWater diagram.theta2AtBase diagram.theta3Outside)
    (hDissolvedSubstanceIncreasesIndex :
      refractiveIndexValue originalWater.refractiveIndex ≤
        refractiveIndexValue thresholdSolution.refractiveIndex)
    (hCessationAtP :
      TotalInternalReflectionCeasesAt
        flintGlass thresholdSolution diagram.theta1AtP) :
    RoundsToHundredth
      (refractiveIndexValue thresholdSolution.refractiveIndex)
      (answerChoiceValue .C) := by
  have hThreshold :=
    criticalRefraction_thresholdRelation
      flintGlass thresholdSolution diagram.theta1AtP hCessationAtP
  rw [hPointPGeometry, hFlintGlassTable] at hThreshold
  have hSixtyDegrees : radiansOfDegrees 60 = Real.pi / 3 := by
    unfold radiansOfDegrees
    ring
  rw [hSixtyDegrees, Real.sin_pi_div_three] at hThreshold
  rw [hThreshold]
  unfold RoundsToHundredth answerChoiceValue
  rw [abs_lt]
  have hSqrtSq : (Real.sqrt 3) ^ 2 = 3 := by
    norm_num
  have hSqrtNonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0019
