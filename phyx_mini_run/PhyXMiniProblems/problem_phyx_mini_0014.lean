import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems
namespace Problem0014

open Dimension

/-- A physical length, represented independently of the units used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The scalar coordinate of a physical length in the fixed SI metre chart. -/
def valueInMeters (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Convert a scalar angle read in degrees from the figure to Mathlib's angle type. -/
def angleOfDegrees (degrees : ℝ) : Real.Angle :=
  (degrees * Real.pi / 180 : ℝ)

/--
The two labelled mirrors are the vertical line segments at `leftMirrorX` and
`rightMirrorX`, with their common vertical span running from `lowerEdgeY` to
`upperEdgeY`. The last two coordinate fields locate the ray's initial contact.
All six coordinates are dimensionful physical lengths; `incidenceAngle` is
measured above the horizontal normal to the vertical mirrors.
-/
structure ParallelMirrorSetup where
  leftMirrorX : LengthQuantity
  rightMirrorX : LengthQuantity
  lowerEdgeY : LengthQuantity
  upperEdgeY : LengthQuantity
  initialContactX : LengthQuantity
  initialContactY : LengthQuantity
  incidenceAngle : Real.Angle

/--
The unfolded candidate contact heights of the labelled reflected beam, together
with the finite sets of indices at which the beam actually strikes each mirror.
Index `0` is the initial contact with the right mirror, so positive odd indices
belong to the left mirror and positive even indices return to the right mirror.
-/
structure ReflectedBeamTrace where
  contactHeight : ℕ → LengthQuantity
  leftMirrorReflectionIndices : Finset ℕ
  rightMirrorReflectionIndices : Finset ℕ

/--
The metric and angular data read directly from Figure 14: the mirrors have a
one-metre gap and a one-metre common height, while the ray begins at the lower
endpoint of the right mirror at five degrees above the horizontal.
-/
def HasFigureReadout (setup : ParallelMirrorSetup) : Prop :=
  valueInMeters setup.rightMirrorX - valueInMeters setup.leftMirrorX = 1 ∧
  valueInMeters setup.upperEdgeY - valueInMeters setup.lowerEdgeY = 1 ∧
  setup.initialContactX = setup.rightMirrorX ∧
  setup.initialContactY = setup.lowerEdgeY ∧
  setup.incidenceAngle = angleOfDegrees 5

/--
The specular-reflection and straight-line propagation law for the apparatus.
Unfolding equal-angle reflections makes every crossing raise the ray by the
mirror separation times the tangent of the incidence angle. The equation is
stated in every unit system. A candidate contact is an actual reflection
exactly when its SI height lies on the finite vertical segment; parity selects
the left or right mirror.
-/
def ObeysSpecularReflection (setup : ParallelMirrorSetup)
    (trace : ReflectedBeamTrace) : Prop :=
  (∀ (units : UnitChoices) (n : ℕ),
    (trace.contactHeight n units).val =
      (setup.initialContactY units).val +
        (n : ℝ) *
          ((setup.rightMirrorX units).val - (setup.leftMirrorX units).val) *
          Real.Angle.tan setup.incidenceAngle) ∧
  (∀ n : ℕ,
    n ∈ trace.leftMirrorReflectionIndices ↔
      Odd n ∧
      valueInMeters setup.lowerEdgeY ≤ valueInMeters (trace.contactHeight n) ∧
      valueInMeters (trace.contactHeight n) ≤ valueInMeters setup.upperEdgeY) ∧
  (∀ n : ℕ,
    n ∈ trace.rightMirrorReflectionIndices ↔
      0 < n ∧ Even n ∧
      valueInMeters setup.lowerEdgeY ≤ valueInMeters (trace.contactHeight n) ∧
      valueInMeters (trace.contactHeight n) ≤ valueInMeters setup.upperEdgeY)

/--
For the one-metre by one-metre parallel-mirror apparatus and the five-degree
incident beam in Figure 14, the beam is reflected six times by the left mirror
(answer choice C).

Blueprint label: `thm:physics:phyx_mini_0014:target`.
-/
theorem leftMirrorReflectionCount_eq_six
    (setup : ParallelMirrorSetup) (trace : ReflectedBeamTrace)
    (hfigure : HasFigureReadout setup)
    (hspecular : ObeysSpecularReflection setup trace) :
    trace.leftMirrorReflectionIndices.card = 6 := by
  rcases hfigure with ⟨hgap, hspan, _hinitialX, hinitialY, hangle⟩
  rcases hspecular with ⟨hheight, hleft, _hright⟩
  have hcontact (n : ℕ) :
      valueInMeters (trace.contactHeight n) =
        valueInMeters setup.lowerEdgeY + (n : ℝ) * Real.tan (Real.pi / 36) := by
    simp only [valueInMeters] at hgap ⊢
    rw [hheight UnitChoices.SI n, hinitialY, hangle, angleOfDegrees,
      Real.Angle.tan_coe, hgap]
    have hanglecalc : 5 * Real.pi / 180 = Real.pi / 36 := by ring
    rw [hanglecalc]
    ring
  have htanUpper : 11 * Real.tan (Real.pi / 36) < 1 := by
    have hpi0 : 0 < Real.pi := Real.pi_pos
    have hpib : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
    have hx0 : 0 ≤ Real.pi / 36 := by positivity
    have hsin : Real.sin (Real.pi / 36) ≤ Real.pi / 36 :=
      Real.sin_le hx0
    have hcos : 1 - (Real.pi / 36) ^ 2 / 2 ≤ Real.cos (Real.pi / 36) :=
      Real.one_sub_sq_div_two_le_cos
    have hcospos : 0 < Real.cos (Real.pi / 36) := by
      nlinarith [sq_nonneg (Real.pi - 3.15)]
    rw [Real.tan_eq_sin_div_cos]
    calc
      11 * (Real.sin (Real.pi / 36) / Real.cos (Real.pi / 36)) =
          (11 * Real.sin (Real.pi / 36)) / Real.cos (Real.pi / 36) := by ring
      _ < 1 := (div_lt_iff₀ hcospos).2 (by
        nlinarith [sq_nonneg (Real.pi - 3.15)])
  have htanLower : 1 < 13 * Real.tan (Real.pi / 36) := by
    have hx0 : 0 < Real.pi / 36 := by positivity
    have hxpi : Real.pi / 36 < Real.pi / 2 := by
      nlinarith [Real.pi_pos]
    have h := Real.lt_tan hx0 hxpi
    nlinarith [Real.pi_gt_three]
  have htanPos : 0 < Real.tan (Real.pi / 36) := by
    nlinarith [htanLower]
  have hwithin (n : ℕ) (hn : n ≤ 11) :
      valueInMeters setup.lowerEdgeY ≤ valueInMeters (trace.contactHeight n) ∧
        valueInMeters (trace.contactHeight n) ≤ valueInMeters setup.upperEdgeY := by
    rw [hcontact]
    constructor
    · have hprod :
          0 ≤ (n : ℝ) * Real.tan (Real.pi / 36) :=
        mul_nonneg (by positivity) htanPos.le
      linarith
    · have hn' : (n : ℝ) ≤ 11 := by exact_mod_cast hn
      nlinarith [hspan]
  have hindices :
      trace.leftMirrorReflectionIndices = {1, 3, 5, 7, 9, 11} := by
    ext n
    rw [hleft]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hodd, _hlower, hupper⟩
      have hnlt : n < 13 := by
        by_contra hn
        have hn13 : 13 ≤ n := by omega
        have hn13' : (13 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn13
        rw [hcontact] at hupper
        have hmul :
            13 * Real.tan (Real.pi / 36) ≤
              (n : ℝ) * Real.tan (Real.pi / 36) :=
          mul_le_mul_of_nonneg_right hn13' htanPos.le
        nlinarith [hspan]
      rcases hodd with ⟨k, hk⟩
      omega
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
        constructor
        · norm_num [Odd]
        · exact hwithin _ (by norm_num)
  rw [hindices]
  norm_num

end Problem0014
end PhyXMiniProblems
