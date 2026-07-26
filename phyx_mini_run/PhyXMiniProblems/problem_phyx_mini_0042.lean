import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0042

open Dimension

/-!
# Apparent depth of a swimming pool

All depths and offsets are physical lengths.  Their scalar SI readouts are in
metres.  Refractive indices and paraxial ray slopes are dimensionless.

The observer looks along the normal to the water surface.  Apparent depth is
determined by a neighbouring, noncentral ray in the paraxial bundle: the
underwater ray and its backward extension share a lateral offset, while the
linearized form of Snell's law relates their slopes.  This keeps the standard
apparent-depth approximation explicit instead of assuming the requested
numeric answer.
-/

/-- A physical length represented coherently in every choice of units. -/
abbrev DimLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The scalar SI readout of a physical length, in metres. -/
def lengthInMeters (length : DimLength) : ℝ :=
  (length UnitChoices.SI).val

/-- The two homogeneous media separated by the pool surface. -/
inductive OpticalMedium where
  | water
  | air
  deriving DecidableEq, Repr

/-- Labels visible in the refraction figure. -/
inductive FigurePoint where
  | P
  | PPrime
  | Q
  | QPrime
  | V
  | observer
  deriving DecidableEq, Repr

/-- Direction of the central viewing axis relative to the water surface. -/
inductive ViewingAxis where
  | surfaceNormal
  | oblique
  deriving DecidableEq, Repr

/--
The physical quantities and labelled paths in the apparent-depth diagram.

The slopes are horizontal displacement divided by vertical displacement for
a neighbouring ray in the paraxial bundle.  `lateralOffset` is the common
horizontal displacement used by the actual ray and its backward extension.
-/
structure ApparentDepthSetup where
  trueDepth : DimLength
  apparentDepth : DimLength
  lateralOffset : DimLength
  refractiveIndex : OpticalMedium → ℝ
  incidentSlope : ℝ
  refractedSlope : ℝ
  viewingAxis : ViewingAxis
  actualLightPath : List FigurePoint
  virtualBackwardExtension : List FigurePoint
  trueDepthReference : List FigurePoint
  apparentDepthReference : List FigurePoint

/--
Problem data: the true pool depth is `2.00 m`, the water refractive index is
`1.33`, and the air refractive index is `1.00`.
-/
def HasPoolReadouts (setup : ApparentDepthSetup) : Prop :=
  lengthInMeters setup.trueDepth = 2 ∧
    setup.refractiveIndex .water = 133 / 100 ∧
    setup.refractiveIndex .air = 1

/--
Figure readout: `P` and `P′` mark the actual and apparent object levels,
`Q` and `Q′` are the corresponding ray points, `V` is the interface point,
and the observer's central viewing axis is normal to the surface.
-/
def MatchesPoolFigure (setup : ApparentDepthSetup) : Prop :=
  setup.viewingAxis = .surfaceNormal ∧
    setup.actualLightPath = [.Q, .V, .observer] ∧
    setup.virtualBackwardExtension = [.observer, .V, .QPrime] ∧
    setup.trueDepthReference = [.P, .Q] ∧
    setup.apparentDepthReference = [.PPrime, .QPrime]

/--
Physical branch assumptions for the two media, both depths, and the
neighbouring noncentral paraxial ray.
-/
def HasPhysicalOpticalParameters (setup : ApparentDepthSetup) : Prop :=
  0 < setup.refractiveIndex .water ∧
    0 < setup.refractiveIndex .air ∧
    0 < lengthInMeters setup.trueDepth ∧
    0 < lengthInMeters setup.apparentDepth ∧
    0 < lengthInMeters setup.lateralOffset ∧
    0 < setup.incidentSlope ∧
    0 < setup.refractedSlope

/--
Paraxial ray geometry at `Q`, `Q′`, and `V`.  The two products express that
slope times vertical depth equals the common lateral offset.
-/
def HasParaxialRayGeometry (setup : ApparentDepthSetup) : Prop :=
  setup.incidentSlope * lengthInMeters setup.trueDepth =
      lengthInMeters setup.lateralOffset ∧
    setup.refractedSlope * lengthInMeters setup.apparentDepth =
      lengthInMeters setup.lateralOffset

/--
First-order Snell law for a ray leaving water for air:
`n_water * slope_water = n_air * slope_air`.
-/
def ObeysParaxialSnellLaw (setup : ApparentDepthSetup) : Prop :=
  setup.refractiveIndex .water * setup.incidentSlope =
    setup.refractiveIndex .air * setup.refractedSlope

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The depth printed beside each answer choice, as a scalar metre readout. -/
def answerDepthInMeters : AnswerChoice → ℝ
  | .A => 856 / 1000
  | .B => 15 / 10
  | .C => 995 / 1000
  | .D => 1814 / 1000

/--
`reported` is a nearest-tenth metre readout of `exact`: it is an integer number
of tenths and differs from the exact value by at most half a tenth.
-/
def IsNearestTenthMeterReadout (exact reported : ℝ) : Prop :=
  (∃ tenths : ℤ, reported = (tenths : ℝ) / 10) ∧
    |exact - reported| ≤ 1 / 20

/-- A selected answer is strictly closer to the exact depth than every rival. -/
def IsClosestDepthAnswer (exact : ℝ) (selected : AnswerChoice) : Prop :=
  ∀ other, other ≠ selected →
    |exact - answerDepthInMeters selected| <
      |exact - answerDepthInMeters other|

/--
The generic paraxial geometry and linearized Snell law imply the usual
apparent-depth relation `s′ = s * n_air / n_water`.
-/
lemma apparentDepth_eq_trueDepth_mul_indexRatio
    (setup : ApparentDepthSetup)
    (hPhysical : HasPhysicalOpticalParameters setup)
    (hGeometry : HasParaxialRayGeometry setup)
    (hSnell : ObeysParaxialSnellLaw setup) :
    lengthInMeters setup.apparentDepth =
      lengthInMeters setup.trueDepth *
        setup.refractiveIndex .air / setup.refractiveIndex .water := by
  rcases hPhysical with ⟨hWater, _, _, _, _, hIncident, _⟩
  rcases hGeometry with ⟨hActual, hVirtual⟩
  have hIndex : setup.refractiveIndex .water ≠ 0 := ne_of_gt hWater
  have hSlope : setup.incidentSlope ≠ 0 := ne_of_gt hIncident
  have hDepths :
      setup.incidentSlope * lengthInMeters setup.trueDepth =
        setup.refractedSlope * lengthInMeters setup.apparentDepth :=
    hActual.trans hVirtual.symm
  apply (eq_div_iff hIndex).2
  apply mul_left_cancel₀ hSlope
  calc
    setup.incidentSlope *
          (lengthInMeters setup.apparentDepth *
            setup.refractiveIndex .water) =
        lengthInMeters setup.apparentDepth *
          (setup.refractiveIndex .water * setup.incidentSlope) := by ring
    _ = lengthInMeters setup.apparentDepth *
          (setup.refractiveIndex .air * setup.refractedSlope) := by
            rw [hSnell]
    _ = setup.refractiveIndex .air *
          (setup.refractedSlope * lengthInMeters setup.apparentDepth) := by ring
    _ = setup.refractiveIndex .air *
          (setup.incidentSlope * lengthInMeters setup.trueDepth) := by
            rw [hDepths]
    _ = setup.incidentSlope *
          (lengthInMeters setup.trueDepth *
            setup.refractiveIndex .air) := by ring

/--
For a `2.00 m` pool with water index `1.33` and air index `1.00`, the paraxial
apparent depth is exactly `200/133 m` in the stated decimal-data model.  Its
nearest-tenth readout is `1.5 m`, and this is uniquely the closest displayed
answer, choice B.

This formalizes `thm:physics:phyx_mini_0042:target`.
-/
theorem problem_phyx_mini_0042
    (setup : ApparentDepthSetup)
    (hData : HasPoolReadouts setup)
    (hFigure : MatchesPoolFigure setup)
    (hPhysical : HasPhysicalOpticalParameters setup)
    (hGeometry : HasParaxialRayGeometry setup)
    (hSnell : ObeysParaxialSnellLaw setup) :
    lengthInMeters setup.apparentDepth = 200 / 133 ∧
      IsNearestTenthMeterReadout
        (lengthInMeters setup.apparentDepth)
        (answerDepthInMeters .B) ∧
      IsClosestDepthAnswer (lengthInMeters setup.apparentDepth) .B := by
  rcases hData with ⟨hTrueDepth, hWater, hAir⟩
  have hApparent :=
    apparentDepth_eq_trueDepth_mul_indexRatio
      setup hPhysical hGeometry hSnell
  rw [hTrueDepth, hWater, hAir] at hApparent
  norm_num at hApparent
  refine ⟨hApparent, ?_, ?_⟩
  · rw [hApparent]
    constructor
    · refine ⟨15, ?_⟩
      norm_num [answerDepthInMeters]
    · norm_num [IsNearestTenthMeterReadout, answerDepthInMeters, abs_of_nonneg,
        abs_of_nonpos]
  · rw [hApparent]
    intro other hOther
    cases other with
    | A =>
        norm_num [answerDepthInMeters, abs_of_nonneg, abs_of_nonpos]
    | B =>
        exact (hOther rfl).elim
    | C =>
        norm_num [answerDepthInMeters, abs_of_nonneg, abs_of_nonpos]
    | D =>
        norm_num [answerDepthInMeters, abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0042
