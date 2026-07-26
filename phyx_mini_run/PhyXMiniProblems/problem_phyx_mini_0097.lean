import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0097

/-!
# Critical refraction in a right-angle glass prism

The supplied cross-section has two perpendicular sloping faces. A ray in air
meets the left face, refracts through the glass, and reaches the opposite face
at the point labelled `A`. All ray angles are represented by Mathlib's
`Real.Angle` and are measured from the normal to the face in question.
Refractive indices are positive dimensionless scalar readouts.

The figure's `40.0°` arc is the angle of the ray in the glass from the entry
normal. The requested `θₐ` is the external incidence angle at that same face.

The dataset records answer A (`90°`), but that value contradicts the pictured
geometry and Snell's law. The optical laws instead determine an angle of about
`57°`, for which B (`60°`) is the closest printed choice.
-/

/-- The two homogeneous optical media traversed by the pictured ray. -/
inductive OpticalMedium where
  | ambientAir
  | prismGlass
  deriving DecidableEq, Repr

/-- The three faces in the triangular prism cross-section. -/
inductive PrismFace where
  | entryFace
  | oppositeFaceAtA
  | base
  deriving DecidableEq, Repr

/-- The three vertices in the triangular prism cross-section. -/
inductive PrismVertex where
  | rightAngleApex
  | lowerLeft
  | lowerRight
  deriving DecidableEq, Repr

/-- The two ray-interaction points distinguished in the figure. -/
inductive FigurePoint where
  | entryPoint
  | A
  deriving DecidableEq, Repr

/-- The prism face on which each distinguished interaction point lies. -/
def FigurePoint.face : FigurePoint → PrismFace
  | .entryPoint => .entryFace
  | .A => .oppositeFaceAtA

/-- The three consecutive directed portions of the optical path. -/
inductive RaySegment where
  | incidentInAir
  | refractedInGlass
  | limitingTransmittedAtA
  deriving DecidableEq, Repr

/-- The physical medium occupied by each portion of the optical path. -/
def RaySegment.medium : RaySegment → OpticalMedium
  | .incidentInAir => .ambientAir
  | .refractedInGlass => .prismGlass
  | .limitingTransmittedAtA => .ambientAir

/-- The two transparent interfaces encountered by the ray, in path order. -/
inductive PrismInterface where
  | entry
  | atA
  deriving DecidableEq, Repr

/-- The labelled point at which an interface crossing occurs. -/
def PrismInterface.point : PrismInterface → FigurePoint
  | .entry => .entryPoint
  | .atA => .A

/-- The segment incident on a given interface. -/
def PrismInterface.incidentSegment : PrismInterface → RaySegment
  | .entry => .incidentInAir
  | .atA => .refractedInGlass

/-- The limiting or actual transmitted segment at a given interface. -/
def PrismInterface.transmittedSegment : PrismInterface → RaySegment
  | .entry => .refractedInGlass
  | .atA => .limitingTransmittedAtA

/-- The qualitative refraction regime shown at a transparent interface. -/
inductive BoundaryBehavior where
  | ordinaryPartialRefraction
  | criticalTransmission
  deriving DecidableEq, Repr

/-- Convert a numerical degree readout to Mathlib's physical angle type. -/
def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/--
The material data and angular readouts for the pictured prism and ray.

`angleToNormal segment face` records a genuine normal-relative angle, rather
than replacing the light ray or prism by a scalar. Only the combinations
selected below by the two interfaces have a role in the physical laws.
-/
structure RightAnglePrismRaySetup where
  /-- Dimensionless refractive index of air and prism glass. -/
  refractiveIndex : OpticalMedium → WithDim 1 ℝ
  /-- Interior angle at each of the three prism vertices. -/
  prismInteriorAngle : PrismVertex → Real.Angle
  /-- Normal-relative angle of a ray segment at a prism face. -/
  angleToNormal : RaySegment → PrismFace → Real.Angle
  /-- Whether the corresponding dashed surface normal is drawn. -/
  surfaceNormalShown : PrismFace → Bool
  /-- Optical behavior at each of the two boundary interactions. -/
  behaviorAt : PrismInterface → BoundaryBehavior

/-- The angle labelled `θₐ`, measured in air from the entry-face normal. -/
def thetaA (setup : RightAnglePrismRaySetup) : Real.Angle :=
  setup.angleToNormal .incidentInAir .entryFace

/-- The refracted angle in the glass immediately after the entry face. -/
def entryRefractionAngle (setup : RightAnglePrismRaySetup) : Real.Angle :=
  setup.angleToNormal .refractedInGlass .entryFace

/-- The internal incidence angle at point `A`, measured from its face normal. -/
def incidenceAngleAtA (setup : RightAnglePrismRaySetup) : Real.Angle :=
  setup.angleToNormal .refractedInGlass .oppositeFaceAtA

/-- The limiting transmitted angle in air at `A`, measured from the normal. -/
def transmissionAngleAtA (setup : RightAnglePrismRaySetup) : Real.Angle :=
  setup.angleToNormal .limitingTransmittedAtA .oppositeFaceAtA

/-- A normal-relative ray angle on the physical branch from `0°` to `90°`. -/
def IsPhysicalNormalAngle (angle : Real.Angle) : Prop :=
  angle.toReal ∈ Set.Icc 0 (Real.pi / 2)

/-- Positivity, optical ordering, and physical angle branches for the setup. -/
def HasPhysicalParameters (setup : RightAnglePrismRaySetup) : Prop :=
  (∀ medium, 0 < (setup.refractiveIndex medium).val) ∧
    (setup.refractiveIndex .ambientAir).val <
      (setup.refractiveIndex .prismGlass).val ∧
    (∀ interface : PrismInterface,
      IsPhysicalNormalAngle
          (setup.angleToNormal interface.incidentSegment interface.point.face) ∧
        IsPhysicalNormalAngle
          (setup.angleToNormal interface.transmittedSegment interface.point.face))

/-!
## Assumption/target split

`MatchesProblemAndFigure` contains only literal diagram readouts.
`SatisfiesRightAnglePrismGeometry`, `SatisfiesSnellLawAt`, and
`IsAtCriticalAngleAtA` contain governing geometry and optics. The value of
`thetaA` occurs only as the conclusion of `problem_phyx_mini_0097`.
-/

/--
Literal data from the problem and image: the apex between the two crossed
faces is a right angle, the entry normal is shown, the first crossing is an
ordinary partial refraction, and the in-glass entry angle is `40.0°`.
-/
def MatchesProblemAndFigure (setup : RightAnglePrismRaySetup) : Prop :=
  setup.prismInteriorAngle .rightAngleApex = degrees 90 ∧
    setup.surfaceNormalShown .entryFace = true ∧
    setup.behaviorAt .entry = .ordinaryPartialRefraction ∧
    entryRefractionAngle setup = degrees 40

/--
Plane geometry for a ray crossing two prism faces meeting at the apex: its
two internal normal-relative angles add to the angle between those faces.
-/
def SatisfiesRightAnglePrismGeometry
    (setup : RightAnglePrismRaySetup) : Prop :=
  (entryRefractionAngle setup).toReal + (incidenceAngleAtA setup).toReal =
    (setup.prismInteriorAngle .rightAngleApex).toReal

/--
Snell's law at either transparent prism face: refractive index times the sine
of the normal-relative ray angle is conserved across the interface.
-/
def SatisfiesSnellLawAt
    (setup : RightAnglePrismRaySetup) (interface : PrismInterface) : Prop :=
  (setup.refractiveIndex interface.incidentSegment.medium).val *
      Real.Angle.sin
        (setup.angleToNormal interface.incidentSegment interface.point.face) =
    (setup.refractiveIndex interface.transmittedSegment.medium).val *
      Real.Angle.sin
        (setup.angleToNormal interface.transmittedSegment interface.point.face)

/-- Snell refraction governs both transparent boundary interactions. -/
def ObeysSnellRefraction (setup : RightAnglePrismRaySetup) : Prop :=
  ∀ interface, SatisfiesSnellLawAt setup interface

/--
At `A` the ray is at the critical incidence: the limiting transmitted ray is
tangent to the opposite face and hence is `90°` from that face's normal.
-/
def IsAtCriticalAngleAtA (setup : RightAnglePrismRaySetup) : Prop :=
  setup.behaviorAt .atA = .criticalTransmission ∧
    transmissionAngleAtA setup = degrees 90

/-- Labels of the four multiple-choice answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Numerical degree readout printed beside each answer label. -/
def answerAngleDegrees : AnswerChoice → ℝ
  | .A => 90
  | .B => 60
  | .C => 45
  | .D => 135

/-- The answer label stored in the dataset, retained only as source metadata. -/
def recordedAnswerChoice : AnswerChoice := .A

/--
For the pictured right-angle glass prism, the two internal normal-relative
angles are complementary, so the incidence at `A` is `50°`. Critical
transmission at `A` and Snell refraction at the entry face then give

`sin θₐ = sin 40° / sin 50°`.

Because `θₐ` is on the physical branch from `0°` to `90°`, its exact value is
the principal arcsine below (approximately `57°`). Thus B (`60°`) is the
closest offered choice. The recorded choice A is represented separately by
`recordedAnswerChoice`; it is not asserted as the physical conclusion.

The conclusion is not present in `MatchesProblemAndFigure`, either optical
law, the critical-angle predicate, or the geometry predicate.

Blueprint: `thm:physics:phyx_mini_0097:target`.
-/
theorem problem_phyx_mini_0097
    (setup : RightAnglePrismRaySetup)
    (h_physical : HasPhysicalParameters setup)
    (h_figure : MatchesProblemAndFigure setup)
    (h_geometry : SatisfiesRightAnglePrismGeometry setup)
    (h_snell : ObeysSnellRefraction setup)
    (h_critical_at_A : IsAtCriticalAngleAtA setup) :
    thetaA setup =
      ((Real.arcsin
        (Real.Angle.sin (degrees 40) / Real.Angle.sin (degrees 50)) : ℝ) :
          Real.Angle) := by
  rcases h_physical with ⟨h_pos, _, h_angles⟩
  rcases h_figure with ⟨h_apex, _, _, h_entry⟩
  rcases h_critical_at_A with ⟨_, h_transmission⟩
  have h_degrees_toReal
      (value : ℝ) (h0 : 0 ≤ value) (h180 : value ≤ 180) :
      (degrees value).toReal = value * Real.pi / 180 := by
    apply Real.Angle.toReal_coe_eq_self_iff.mpr
    constructor <;> nlinarith [Real.pi_pos]
  have h_incidence : incidenceAngleAtA setup = degrees 50 := by
    apply Real.Angle.toReal_injective
    unfold SatisfiesRightAnglePrismGeometry at h_geometry
    rw [h_entry, h_apex,
      h_degrees_toReal 40 (by norm_num) (by norm_num),
      h_degrees_toReal 90 (by norm_num) (by norm_num)] at h_geometry
    rw [h_degrees_toReal 50 (by norm_num) (by norm_num)]
    linarith
  have h_snell_entry := h_snell .entry
  have h_snell_A := h_snell .atA
  simp only [SatisfiesSnellLawAt, PrismInterface.incidentSegment,
    PrismInterface.transmittedSegment, PrismInterface.point, FigurePoint.face,
    RaySegment.medium] at h_snell_entry h_snell_A
  change
    (setup.refractiveIndex .ambientAir).val *
        Real.Angle.sin (thetaA setup) =
      (setup.refractiveIndex .prismGlass).val *
        Real.Angle.sin (entryRefractionAngle setup)
    at h_snell_entry
  change
    (setup.refractiveIndex .prismGlass).val *
        Real.Angle.sin (incidenceAngleAtA setup) =
      (setup.refractiveIndex .ambientAir).val *
        Real.Angle.sin (transmissionAngleAtA setup)
    at h_snell_A
  rw [h_entry] at h_snell_entry
  rw [h_incidence, h_transmission] at h_snell_A
  have h_sin90 : Real.Angle.sin (degrees 90) = 1 := by
    rw [degrees, Real.Angle.sin_coe,
      show (90 : ℝ) * Real.pi / 180 = Real.pi / 2 by ring,
      Real.sin_pi_div_two]
  rw [h_sin90, mul_one] at h_snell_A
  have h_glass_ne : (setup.refractiveIndex .prismGlass).val ≠ 0 :=
    ne_of_gt (h_pos .prismGlass)
  have h_air_ne : (setup.refractiveIndex .ambientAir).val ≠ 0 :=
    ne_of_gt (h_pos .ambientAir)
  have h_sin50_ne : Real.Angle.sin (degrees 50) ≠ 0 := by
    intro h_zero
    rw [h_zero, mul_zero] at h_snell_A
    exact h_air_ne h_snell_A.symm
  have h_sin_theta :
      Real.Angle.sin (thetaA setup) =
        Real.Angle.sin (degrees 40) / Real.Angle.sin (degrees 50) := by
    apply (eq_div_iff h_sin50_ne).2
    apply mul_left_cancel₀ h_glass_ne
    calc
      (setup.refractiveIndex .prismGlass).val *
          (Real.Angle.sin (thetaA setup) * Real.Angle.sin (degrees 50)) =
        ((setup.refractiveIndex .prismGlass).val *
            Real.Angle.sin (degrees 50)) *
          Real.Angle.sin (thetaA setup) := by ring
      _ =
          (setup.refractiveIndex .ambientAir).val *
            Real.Angle.sin (thetaA setup) := by
        rw [h_snell_A]
      _ =
          (setup.refractiveIndex .prismGlass).val *
            Real.Angle.sin (degrees 40) :=
        h_snell_entry
  have h_theta_bounds := (h_angles .entry).1
  change
    0 ≤ (thetaA setup).toReal ∧
      (thetaA setup).toReal ≤ Real.pi / 2
    at h_theta_bounds
  have h_theta_lower : -(Real.pi / 2) ≤ (thetaA setup).toReal := by
    nlinarith [Real.pi_pos, h_theta_bounds.1]
  calc
    thetaA setup = (((thetaA setup).toReal : ℝ) : Real.Angle) :=
      (Real.Angle.coe_toReal _).symm
    _ =
        ((Real.arcsin (Real.sin (thetaA setup).toReal) : ℝ) :
          Real.Angle) := by
      rw [Real.arcsin_sin h_theta_lower h_theta_bounds.2]
    _ =
        ((Real.arcsin
          (Real.Angle.sin (degrees 40) /
            Real.Angle.sin (degrees 50)) : ℝ) : Real.Angle) := by
      rw [Real.Angle.sin_toReal, h_sin_theta]

end PhyXMiniProblems.ProblemPhyXMini0097
