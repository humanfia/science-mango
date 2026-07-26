import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Physlib.Optics.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0096

/-!
# Largest entry angle giving total internal reflection in a transparent block

The source image shows a ray entering the horizontal top of a transparent
rectangular block from air and then reaching the perpendicular vertical face
at the labeled point `A`. The figure label `θₐ` is the air-side incidence
angle measured from the dashed normal to the top face.

Refractive indices are dimensionless real readouts. Optical angles use
Mathlib's `Real.Angle`; real numbers occur only when an ordered canonical
radian representative or a displayed degree readout is required.
-/

/-- The two homogeneous optical media crossed by the depicted ray. -/
inductive OpticalMedium where
  | ambientAir
  | transparentSolid
  deriving DecidableEq, Repr

/-- The two perpendicular faces encountered by the ray. -/
inductive BlockFace where
  | horizontalEntry
  | verticalFaceAtA
  deriving DecidableEq, Repr

/-- The only point explicitly labeled in the source figure. -/
inductive FigurePoint where
  | A
  deriving DecidableEq, Repr

/-- The block-face orientations visible in the source figure. -/
inductive FaceOrientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- The propagation sense of the arrow after it enters the block. -/
inductive RayTravelSense where
  | downwardTowardA
  deriving DecidableEq, Repr

/-- The face on which each labeled figure point lies. -/
def FigurePoint.face : FigurePoint → BlockFace
  | .A => .verticalFaceAtA

/-- Convert a scalar degree readout into a physical angle. -/
def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-- The canonical degree readout of a physical angle. -/
def degreeReadout (angle : Real.Angle) : ℝ :=
  angle.toReal * 180 / Real.pi

/--
Material data and the geometry of the transparent block.

`criticalAngleSolidToAir` is measured inside the solid from the normal to the
vertical face. `criticalTransmissionAngleInAir` is the air-side angle of the
limiting transmitted ray at that face.
-/
structure TransparentBlockSetup where
  /-- Positive dimensionless refractive-index readout in each medium. -/
  refractiveIndex : OpticalMedium → ℝ
  /-- Orientation of each named planar block face. -/
  faceOrientation : BlockFace → FaceOrientation
  /-- Solid-side critical angle at the vertical solid--air boundary. -/
  criticalAngleSolidToAir : Real.Angle
  /-- Air-side transmission angle of the limiting, face-grazing ray. -/
  criticalTransmissionAngleInAir : Real.Angle

/--
One ray following the route shown in the figure.

All three angles are unsigned normal-relative optical angles. In particular,
`incidenceAngleThetaA` is the requested figure quantity `θₐ` in ambient air.
-/
structure BlockRayPath where
  entryFace : BlockFace
  internalReflectionFace : BlockFace
  interactionPoint : FigurePoint
  travelSense : RayTravelSense
  incidenceAngleThetaA : Real.Angle
  refractionAngleInSolidFromTopNormal : Real.Angle
  incidenceAngleAtVerticalFace : Real.Angle

/-- The two encountered faces have the horizontal/vertical layout in the image. -/
def HasDepictedBlockLayout (setup : TransparentBlockSetup) : Prop :=
  setup.faceOrientation .horizontalEntry = .horizontal ∧
    setup.faceOrientation .verticalFaceAtA = .vertical

/-- The ray enters through the top and reaches the vertical face at point `A`. -/
def FollowsDepictedRoute (ray : BlockRayPath) : Prop :=
  ray.entryFace = .horizontalEntry ∧
    ray.internalReflectionFace = .verticalFaceAtA ∧
    ray.interactionPoint = .A ∧
    ray.interactionPoint.face = .verticalFaceAtA ∧
    ray.travelSense = .downwardTowardA

/--
The dimensionless scalar readouts supplied by the problem. Air is modeled by
index one and the transparent solid by index `1.38`. No value of `θₐ` occurs
in this predicate.
-/
def MatchesProblemReadouts (setup : TransparentBlockSetup) : Prop :=
  setup.refractiveIndex .ambientAir = 1 ∧
    setup.refractiveIndex .transparentSolid = (1.38 : ℝ)

/-- A normal-relative optical angle on the physical branch from `0` to `90°`. -/
def IsPhysicalNormalAngle (angle : Real.Angle) : Prop :=
  angle.toReal ∈ Set.Icc 0 (Real.pi / 2)

/-- The critical angle is strictly between normal and grazing incidence. -/
def IsStrictlyAcuteNormalAngle (angle : Real.Angle) : Prop :=
  angle.toReal ∈ Set.Ioo 0 (Real.pi / 2)

/--
Positivity, optical density ordering, and the physical branch for the limiting
solid--air ray. These conditions do not assign the requested entry angle.
-/
def HasPhysicalOpticalParameters (setup : TransparentBlockSetup) : Prop :=
  (∀ medium, 0 < setup.refractiveIndex medium) ∧
    setup.refractiveIndex .ambientAir <
      setup.refractiveIndex .transparentSolid ∧
    IsStrictlyAcuteNormalAngle setup.criticalAngleSolidToAir ∧
    IsPhysicalNormalAngle setup.criticalTransmissionAngleInAir

/-- All normal-relative angles of a depicted candidate ray use the acute branch. -/
def HasPhysicalRayAngles (ray : BlockRayPath) : Prop :=
  IsPhysicalNormalAngle ray.incidenceAngleThetaA ∧
    IsPhysicalNormalAngle ray.refractionAngleInSolidFromTopNormal ∧
    IsPhysicalNormalAngle ray.incidenceAngleAtVerticalFace

/--
Snell's law at the horizontal entry face: index times the sine of the angle
from the local normal is conserved across transmission from air into solid.
-/
def SatisfiesEntrySnellLaw
    (setup : TransparentBlockSetup) (ray : BlockRayPath) : Prop :=
  setup.refractiveIndex .ambientAir *
      Real.Angle.sin ray.incidenceAngleThetaA =
    setup.refractiveIndex .transparentSolid *
      Real.Angle.sin ray.refractionAngleInSolidFromTopNormal

/--
The entry and vertical faces are perpendicular. Hence the solid-ray angle
from the top-face normal and its incidence angle from the vertical-face normal
are complementary on the physical branch.
-/
def SatisfiesPerpendicularFaceGeometry (ray : BlockRayPath) : Prop :=
  ray.refractionAngleInSolidFromTopNormal.toReal +
      ray.incidenceAngleAtVerticalFace.toReal =
    Real.pi / 2

/--
Snell's law for the limiting solid--air ray at the vertical face, together
with the physical statement that its transmitted ray grazes that face at
`90°` from the normal. This determines the critical angle, not the requested
largest air-side entry angle.
-/
def SatisfiesCriticalAngleSnellLaw (setup : TransparentBlockSetup) : Prop :=
  setup.criticalTransmissionAngleInAir = degrees 90 ∧
    setup.refractiveIndex .transparentSolid *
        Real.Angle.sin setup.criticalAngleSolidToAir =
      setup.refractiveIndex .ambientAir *
        Real.Angle.sin setup.criticalTransmissionAngleInAir

/--
A ray is on the total-internal-reflection side of the critical boundary when
its incidence at the vertical face is at least the solid--air critical angle.
The equality case is retained as the limiting onset used by the multiple-
choice problem's phrase "largest angle".
-/
def UndergoesTotalInternalReflectionAtA
    (setup : TransparentBlockSetup) (ray : BlockRayPath) : Prop :=
  setup.criticalAngleSolidToAir.toReal ≤
    ray.incidenceAngleAtVerticalFace.toReal

/--
An air-side incidence readout is admissible when some physical ray with that
canonical radian readout follows the depicted route, obeys Snell's law and the
perpendicular-face geometry, and reaches the vertical face on the TIR side of
the critical boundary. No maximality assertion occurs in this predicate.
-/
def AdmissibleTIRIncidenceRadians
    (setup : TransparentBlockSetup) (thetaRadians : ℝ) : Prop :=
  ∃ ray : BlockRayPath,
    ray.incidenceAngleThetaA.toReal = thetaRadians ∧
      FollowsDepictedRoute ray ∧
      HasPhysicalRayAngles ray ∧
      SatisfiesEntrySnellLaw setup ray ∧
      SatisfiesPerpendicularFaceGeometry ray ∧
      UndergoesTotalInternalReflectionAtA setup ray

/-- The ordered set of all air-side incidence-angle radian readouts giving TIR. -/
def tirPermittingIncidenceRadians
    (setup : TransparentBlockSetup) : Set ℝ :=
  {theta | AdmissibleTIRIncidenceRadians setup theta}

/--
At the limiting ray the internal refraction angle from the top normal is the
complement of the vertical-face critical angle. Entry-face Snell refraction
therefore predicts
`arcsin ((n_solid / n_air) * cos criticalAngle)`.

This is a candidate derived from the governing laws, not an assumed answer.
-/
def predictedMaximumAirIncidenceAngle
    (setup : TransparentBlockSetup) : Real.Angle :=
  ((Real.arcsin
      (setup.refractiveIndex .transparentSolid /
          setup.refractiveIndex .ambientAir *
        Real.Angle.cos setup.criticalAngleSolidToAir) : ℝ) : Real.Angle)

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The angle in degrees displayed beside each answer label. -/
def answerAngleDegrees : AnswerChoice → ℝ
  | .A => 72.1
  | .B => 73.2
  | .C => 70.8
  | .D => 71.9

/-- The answer label recorded by the source dataset. -/
def recordedAnswerChoice : AnswerChoice := .A

/--
Compatibility with a displayed angle using a `0.15°` source tolerance. The
tolerance is explicit because the exact calculation from the rounded index
`1.38` is about `71.989°`, whereas the dataset records `72.1°`.
-/
def MatchesDisplayedAngleWithinSourceTolerance
    (angle : Real.Angle) (choice : AnswerChoice) : Prop :=
  |degreeReadout angle - answerAngleDegrees choice| ≤ (3 / 20 : ℝ)

/--
The critical ray gives the greatest air-side incidence angle whose refracted
solid ray still reaches the vertical face at or above its critical angle.

This is the maximality part of `thm:physics:phyx_mini_0096:target`.
-/
lemma predictedMaximum_isGreatestTIRIncidence
    (setup : TransparentBlockSetup)
    (h_layout : HasDepictedBlockLayout setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_physical : HasPhysicalOpticalParameters setup)
    (h_critical : SatisfiesCriticalAngleSnellLaw setup) :
    IsGreatest (tirPermittingIncidenceRadians setup)
      (predictedMaximumAirIncidenceAngle setup).toReal := by
  rcases h_layout with ⟨_, _⟩
  rcases h_readouts with ⟨h_air, h_solid⟩
  rcases h_physical with
    ⟨h_indices_pos, h_index_order, h_critical_angle, h_transmission_angle⟩
  rcases h_critical with ⟨h_transmission, h_critical_snell⟩
  change
    setup.criticalAngleSolidToAir.toReal ∈ Set.Ioo 0 (Real.pi / 2)
    at h_critical_angle
  have h_critical_pos : 0 < setup.criticalAngleSolidToAir.toReal :=
    h_critical_angle.1
  have h_critical_lt :
      setup.criticalAngleSolidToAir.toReal < Real.pi / 2 :=
    h_critical_angle.2
  have h_sin_ninety : Real.Angle.sin (degrees 90) = 1 := by
    rw [degrees, Real.Angle.sin_coe]
    rw [show (90 : ℝ) * Real.pi / 180 = Real.pi / 2 by ring,
      Real.sin_pi_div_two]
  have h_sin_critical :
      Real.Angle.sin setup.criticalAngleSolidToAir = 50 / 69 := by
    rw [h_transmission, h_sin_ninety, h_air, h_solid] at h_critical_snell
    norm_num at h_critical_snell ⊢
    linarith
  have h_cos_critical_pos :
      0 < Real.Angle.cos setup.criticalAngleSolidToAir := by
    rw [Real.Angle.cos_pos_iff_abs_toReal_lt_pi_div_two,
      abs_of_pos h_critical_pos]
    exact h_critical_lt
  have h_trig :
      (Real.Angle.sin setup.criticalAngleSolidToAir) ^ 2 +
          (Real.Angle.cos setup.criticalAngleSolidToAir) ^ 2 = 1 := by
    rw [← Real.Angle.sin_toReal, ← Real.Angle.cos_toReal]
    exact Real.sin_sq_add_cos_sq _
  have h_cos_critical_sq :
      (Real.Angle.cos setup.criticalAngleSolidToAir) ^ 2 = 2261 / 4761 := by
    rw [h_sin_critical] at h_trig
    norm_num at h_trig ⊢
    linarith
  let criticalArgument : ℝ :=
    (69 / 50 : ℝ) * Real.Angle.cos setup.criticalAngleSolidToAir
  have h_argument_pos : 0 < criticalArgument := by
    dsimp [criticalArgument]
    positivity
  have h_argument_lt_one : criticalArgument < 1 := by
    have h_argument_sq : criticalArgument ^ 2 = 2261 / 2500 := by
      dsimp [criticalArgument]
      rw [mul_pow, h_cos_critical_sq]
      norm_num
    nlinarith
  have h_argument_mem : criticalArgument ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by linarith, h_argument_lt_one.le⟩
  have h_arcsin_pos : 0 < Real.arcsin criticalArgument :=
    Real.arcsin_pos.2 h_argument_pos
  have h_arcsin_lt : Real.arcsin criticalArgument < Real.pi / 2 :=
    Real.arcsin_lt_pi_div_two.2 h_argument_lt_one
  have h_predicted_toReal :
      (predictedMaximumAirIncidenceAngle setup).toReal =
        Real.arcsin criticalArgument := by
    rw [predictedMaximumAirIncidenceAngle, h_air, h_solid]
    norm_num [criticalArgument]
    apply Real.Angle.toReal_coe_eq_self_iff.2
    constructor <;> linarith [Real.pi_pos]
  constructor
  · change AdmissibleTIRIncidenceRadians setup
      (predictedMaximumAirIncidenceAngle setup).toReal
    let limitingRay : BlockRayPath :=
      { entryFace := .horizontalEntry
        internalReflectionFace := .verticalFaceAtA
        interactionPoint := .A
        travelSense := .downwardTowardA
        incidenceAngleThetaA := predictedMaximumAirIncidenceAngle setup
        refractionAngleInSolidFromTopNormal :=
          ((Real.pi / 2 -
            setup.criticalAngleSolidToAir.toReal : ℝ) : Real.Angle)
        incidenceAngleAtVerticalFace := setup.criticalAngleSolidToAir }
    refine ⟨limitingRay, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp [limitingRay, FollowsDepictedRoute, FigurePoint.face]
    · refine ⟨?_, ?_, ?_⟩
      · rw [IsPhysicalNormalAngle, h_predicted_toReal]
        exact ⟨h_arcsin_pos.le, h_arcsin_lt.le⟩
      · rw [IsPhysicalNormalAngle]
        change
          (((Real.pi / 2 -
            setup.criticalAngleSolidToAir.toReal : ℝ) : Real.Angle).toReal) ∈
            Set.Icc 0 (Real.pi / 2)
        rw [Real.Angle.toReal_coe_eq_self_iff.2]
        · exact ⟨by linarith only [h_critical_lt],
            by linarith only [h_critical_pos]⟩
        · constructor <;>
            linarith only [h_critical_pos, h_critical_lt, Real.pi_pos]
      · exact ⟨h_critical_pos.le, h_critical_lt.le⟩
    · rw [SatisfiesEntrySnellLaw]
      change
        setup.refractiveIndex .ambientAir *
            Real.Angle.sin (predictedMaximumAirIncidenceAngle setup) =
          setup.refractiveIndex .transparentSolid *
            Real.Angle.sin
              (((Real.pi / 2 -
                setup.criticalAngleSolidToAir.toReal : ℝ) : Real.Angle))
      rw [predictedMaximumAirIncidenceAngle, h_air, h_solid,
        Real.Angle.sin_coe, Real.Angle.sin_coe,
        Real.sin_pi_div_two_sub, Real.Angle.cos_toReal]
      norm_num
      change Real.sin (Real.arcsin criticalArgument) =
        (69 / 50 : ℝ) * Real.Angle.cos setup.criticalAngleSolidToAir
      rw [Real.sin_arcsin h_argument_mem.1 h_argument_mem.2]
    · rw [SatisfiesPerpendicularFaceGeometry]
      change
        (((Real.pi / 2 -
          setup.criticalAngleSolidToAir.toReal : ℝ) : Real.Angle).toReal) +
            setup.criticalAngleSolidToAir.toReal =
          Real.pi / 2
      rw [Real.Angle.toReal_coe_eq_self_iff.2]
      · ring
      · constructor <;>
          linarith only [h_critical_pos, h_critical_lt, Real.pi_pos]
    · exact le_rfl
  · intro theta h_theta
    change AdmissibleTIRIncidenceRadians setup theta at h_theta
    rcases h_theta with
      ⟨ray, rfl, h_route, h_ray_physical, h_entry_snell,
        h_perpendicular, h_tir⟩
    rcases h_ray_physical with ⟨h_incidence, h_refraction, h_vertical⟩
    change
      ray.incidenceAngleThetaA.toReal ∈ Set.Icc 0 (Real.pi / 2)
      at h_incidence
    change
      ray.refractionAngleInSolidFromTopNormal.toReal ∈
        Set.Icc 0 (Real.pi / 2)
      at h_refraction
    have h_incidence_nonneg : 0 ≤ ray.incidenceAngleThetaA.toReal :=
      h_incidence.1
    have h_refraction_nonneg :
        0 ≤ ray.refractionAngleInSolidFromTopNormal.toReal :=
      h_refraction.1
    change
      ray.refractionAngleInSolidFromTopNormal.toReal +
          ray.incidenceAngleAtVerticalFace.toReal =
        Real.pi / 2
      at h_perpendicular
    change
      setup.criticalAngleSolidToAir.toReal ≤
        ray.incidenceAngleAtVerticalFace.toReal
      at h_tir
    have h_refraction_le :
        ray.refractionAngleInSolidFromTopNormal.toReal ≤
          Real.pi / 2 - setup.criticalAngleSolidToAir.toReal := by
      linarith
    have h_complement_mem :
        Real.pi / 2 - setup.criticalAngleSolidToAir.toReal ∈
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;>
        linarith only [h_critical_pos, h_critical_lt, Real.pi_pos]
    have h_sin_refraction_le :
        Real.Angle.sin ray.refractionAngleInSolidFromTopNormal ≤
          Real.Angle.cos setup.criticalAngleSolidToAir := by
      rw [← Real.Angle.sin_toReal, ← Real.Angle.cos_toReal,
        ← Real.sin_pi_div_two_sub]
      exact Real.monotoneOn_sin
        ⟨by linarith only [h_refraction_nonneg, Real.pi_pos],
          h_refraction.2⟩
        h_complement_mem h_refraction_le
    have h_sin_incidence :
        Real.Angle.sin ray.incidenceAngleThetaA =
          (69 / 50 : ℝ) *
            Real.Angle.sin ray.refractionAngleInSolidFromTopNormal := by
      rw [SatisfiesEntrySnellLaw, h_air, h_solid] at h_entry_snell
      norm_num at h_entry_snell ⊢
      linarith
    rw [h_predicted_toReal]
    apply (Real.le_arcsin_iff_sin_le
      ⟨by linarith only [h_incidence_nonneg, Real.pi_pos],
        h_incidence.2⟩ h_argument_mem).2
    rw [Real.Angle.sin_toReal, h_sin_incidence]
    dsimp [criticalArgument]
    exact mul_le_mul_of_nonneg_left h_sin_refraction_le (by norm_num)

/--
For the supplied index `1.38`, the exact critical-ray expression is compatible
with the dataset's recorded option A under the stated source tolerance.

This is the recorded-answer part of `thm:physics:phyx_mini_0096:target`.
-/
lemma predictedMaximum_matches_recorded_choice
    (setup : TransparentBlockSetup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_physical : HasPhysicalOpticalParameters setup)
    (h_critical : SatisfiesCriticalAngleSnellLaw setup) :
    MatchesDisplayedAngleWithinSourceTolerance
      (predictedMaximumAirIncidenceAngle setup) recordedAnswerChoice := by
  rcases h_readouts with ⟨h_air, h_solid⟩
  rcases h_physical with
    ⟨h_indices_pos, h_index_order, h_critical_angle, h_transmission_angle⟩
  rcases h_critical with ⟨h_transmission, h_critical_snell⟩
  change
    setup.criticalAngleSolidToAir.toReal ∈ Set.Ioo 0 (Real.pi / 2)
    at h_critical_angle
  have h_critical_pos : 0 < setup.criticalAngleSolidToAir.toReal :=
    h_critical_angle.1
  have h_critical_lt :
      setup.criticalAngleSolidToAir.toReal < Real.pi / 2 :=
    h_critical_angle.2
  have h_sin_ninety : Real.Angle.sin (degrees 90) = 1 := by
    rw [degrees, Real.Angle.sin_coe]
    rw [show (90 : ℝ) * Real.pi / 180 = Real.pi / 2 by ring,
      Real.sin_pi_div_two]
  have h_sin_critical :
      Real.Angle.sin setup.criticalAngleSolidToAir = 50 / 69 := by
    rw [h_transmission, h_sin_ninety, h_air, h_solid] at h_critical_snell
    norm_num at h_critical_snell ⊢
    linarith
  have h_cos_critical_pos :
      0 < Real.Angle.cos setup.criticalAngleSolidToAir := by
    rw [Real.Angle.cos_pos_iff_abs_toReal_lt_pi_div_two,
      abs_of_pos h_critical_pos]
    exact h_critical_lt
  have h_trig :
      (Real.Angle.sin setup.criticalAngleSolidToAir) ^ 2 +
          (Real.Angle.cos setup.criticalAngleSolidToAir) ^ 2 = 1 := by
    rw [← Real.Angle.sin_toReal, ← Real.Angle.cos_toReal]
    exact Real.sin_sq_add_cos_sq _
  have h_cos_critical_sq :
      (Real.Angle.cos setup.criticalAngleSolidToAir) ^ 2 = 2261 / 4761 := by
    rw [h_sin_critical] at h_trig
    norm_num at h_trig ⊢
    linarith
  let criticalArgument : ℝ :=
    (69 / 50 : ℝ) * Real.Angle.cos setup.criticalAngleSolidToAir
  have h_argument_pos : 0 < criticalArgument := by
    dsimp [criticalArgument]
    positivity
  have h_argument_sq : criticalArgument ^ 2 = 2261 / 2500 := by
    dsimp [criticalArgument]
    rw [mul_pow, h_cos_critical_sq]
    norm_num
  have h_argument_lt_one : criticalArgument < 1 := by
    nlinarith
  have h_argument_mem : criticalArgument ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by linarith, h_argument_lt_one.le⟩
  have h_arcsin_pos : 0 < Real.arcsin criticalArgument :=
    Real.arcsin_pos.2 h_argument_pos
  have h_arcsin_lt : Real.arcsin criticalArgument < Real.pi / 2 :=
    Real.arcsin_lt_pi_div_two.2 h_argument_lt_one
  have h_predicted_toReal :
      (predictedMaximumAirIncidenceAngle setup).toReal =
        Real.arcsin criticalArgument := by
    rw [predictedMaximumAirIncidenceAngle, h_air, h_solid]
    norm_num [criticalArgument]
    apply Real.Angle.toReal_coe_eq_self_iff.2
    constructor <;> linarith [Real.pi_pos]
  have h_argument_lower : (9509 : ℝ) / 10000 < criticalArgument := by
    nlinarith only [h_argument_sq, h_argument_pos]
  have h_sqrt_five_sq : (Real.sqrt 5) ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num)
  have h_sqrt_five_nonneg : 0 ≤ Real.sqrt 5 :=
    Real.sqrt_nonneg 5
  have h_sqrt_five_lower : (2236 : ℝ) / 1000 < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have h_sqrt_five_upper : Real.sqrt 5 < (223607 : ℝ) / 100000 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  have h_sin_seventy_two_sq :
      (Real.sin (2 * Real.pi / 5)) ^ 2 =
        (5 + Real.sqrt 5) / 8 := by
    rw [show 2 * Real.pi / 5 = Real.pi / 2 - Real.pi / 10 by ring,
      Real.sin_pi_div_two_sub, Real.cos_sq,
      show 2 * (Real.pi / 10) = Real.pi / 5 by ring,
      Real.cos_pi_div_five]
    ring
  have h_sin_seventy_two_pos :
      0 < Real.sin (2 * Real.pi / 5) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by
      nlinarith only [Real.pi_pos])
  have h_sin_seventy_two_upper :
      Real.sin (2 * Real.pi / 5) < (9511 : ℝ) / 10000 := by
    nlinarith only [h_sin_seventy_two_sq, h_sin_seventy_two_pos,
      h_sqrt_five_upper]
  have h_cos_seventy_two :
      Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
    rw [show 2 * Real.pi / 5 = 2 * (Real.pi / 5) by ring,
      Real.cos_two_mul, Real.cos_pi_div_five]
    nlinarith only [h_sqrt_five_sq]
  have h_cos_seventy_two_lower :
      (309 : ℝ) / 1000 < Real.cos (2 * Real.pi / 5) := by
    rw [h_cos_seventy_two]
    linarith only [h_sqrt_five_lower]
  have h_pi_lower : (3 : ℝ) < Real.pi := by
    have h0 : (9956 : ℝ) / 10000 < Real.cos ((3 : ℝ) / 32) := by
      have hb := Real.cos_bound (x := (3 : ℝ) / 32)
        (by norm_num [abs_of_nonneg])
      rw [abs_le] at hb
      norm_num [abs_of_nonneg] at hb ⊢
      linarith
    have h1 : (9824 : ℝ) / 10000 < Real.cos ((3 : ℝ) / 16) := by
      rw [show (3 : ℝ) / 16 = 2 * (3 / 32) by norm_num,
        Real.cos_two_mul]
      nlinarith only [h0]
    have h2 : (9300 : ℝ) / 10000 < Real.cos ((3 : ℝ) / 8) := by
      rw [show (3 : ℝ) / 8 = 2 * (3 / 16) by norm_num,
        Real.cos_two_mul]
      nlinarith only [h1]
    have h3 : (7298 : ℝ) / 10000 < Real.cos ((3 : ℝ) / 4) := by
      rw [show (3 : ℝ) / 4 = 2 * (3 / 8) by norm_num,
        Real.cos_two_mul]
      nlinarith only [h2]
    have h4 : 0 < Real.cos ((3 : ℝ) / 2) := by
      rw [show (3 : ℝ) / 2 = 2 * (3 / 4) by norm_num,
        Real.cos_two_mul]
      nlinarith only [h3]
    by_contra h
    have h_half : Real.pi / 2 ≤ (3 : ℝ) / 2 := by
      linarith
    have h_nonpos :=
      Real.cos_nonpos_of_pi_div_two_le_of_le h_half (by
        nlinarith only [Real.two_le_pi])
    linarith only [h4, h_nonpos]
  let delta : ℝ := Real.pi / 3600
  have h_delta_pos : 0 < delta := by
    dsimp [delta]
    positivity
  have h_delta_lower : (1 : ℝ) / 1200 < delta := by
    dsimp [delta]
    nlinarith only [h_pi_lower]
  have h_delta_upper : delta ≤ (1 : ℝ) / 900 := by
    dsimp [delta]
    nlinarith only [Real.pi_le_four]
  have h_delta_le_one : delta ≤ 1 := by
    linarith only [h_delta_upper]
  have h_sin_delta_lower : (83 : ℝ) / 100000 < Real.sin delta := by
    have h_delta_cube : delta ^ 3 ≤ ((1 : ℝ) / 900) ^ 3 :=
      pow_le_pow_left₀ h_delta_pos.le h_delta_upper 3
    have h_delta_fourth : delta ^ 4 ≤ ((1 : ℝ) / 900) ^ 4 :=
      pow_le_pow_left₀ h_delta_pos.le h_delta_upper 4
    have hb := Real.sin_bound (x := delta) (by
      rw [abs_of_pos h_delta_pos]
      exact h_delta_le_one)
    rw [abs_of_pos h_delta_pos, abs_le] at hb
    nlinarith only [hb.1, h_delta_lower, h_delta_cube, h_delta_fourth]
  have h_sin_lower_endpoint :
      Real.sin (1439 * Real.pi / 3600) < criticalArgument := by
    have h_first_term :
        Real.sin (2 * Real.pi / 5) * Real.cos delta ≤
          Real.sin (2 * Real.pi / 5) :=
      mul_le_of_le_one_right h_sin_seventy_two_pos.le
        (Real.cos_le_one delta)
    have h_second_term :
        (309 : ℝ) / 1000 * ((83 : ℝ) / 100000) <
          Real.cos (2 * Real.pi / 5) * Real.sin delta :=
      mul_lt_mul'' h_cos_seventy_two_lower h_sin_delta_lower
        (by norm_num) (by norm_num)
    rw [show 1439 * Real.pi / 3600 =
        2 * Real.pi / 5 - delta by
      dsimp [delta]
      ring,
      Real.sin_sub]
    nlinarith only [h_first_term, h_second_term,
      h_sin_seventy_two_upper, h_argument_lower]
  have h_argument_lt_sin_seventy_two :
      criticalArgument < Real.sin (2 * Real.pi / 5) := by
    nlinarith only [h_argument_sq, h_argument_pos,
      h_sin_seventy_two_sq, h_sin_seventy_two_pos,
      h_sqrt_five_lower]
  have h_arc_lower :
      1439 * Real.pi / 3600 < Real.arcsin criticalArgument := by
    apply (Real.lt_arcsin_iff_sin_lt' (by
      constructor <;> nlinarith only [Real.pi_pos])).2
    exact h_sin_lower_endpoint
  have h_arc_upper :
      Real.arcsin criticalArgument < 2 * Real.pi / 5 := by
    apply (Real.arcsin_lt_iff_lt_sin' (by
      constructor <;> nlinarith only [Real.pi_pos])).2
    exact h_argument_lt_sin_seventy_two
  have h_degree_lower :
      (71.95 : ℝ) <
        Real.arcsin criticalArgument * 180 / Real.pi := by
    calc
      (71.95 : ℝ) = (1439 * Real.pi / 3600) * 180 / Real.pi := by
        field_simp
        ring
      _ < Real.arcsin criticalArgument * 180 / Real.pi := by
        exact div_lt_div_of_pos_right
          (mul_lt_mul_of_pos_right h_arc_lower (by norm_num)) Real.pi_pos
  have h_degree_upper :
      Real.arcsin criticalArgument * 180 / Real.pi < (72 : ℝ) := by
    calc
      Real.arcsin criticalArgument * 180 / Real.pi <
          (2 * Real.pi / 5) * 180 / Real.pi := by
        exact div_lt_div_of_pos_right
          (mul_lt_mul_of_pos_right h_arc_upper (by norm_num)) Real.pi_pos
      _ = (72 : ℝ) := by
        field_simp
        ring
  rw [MatchesDisplayedAngleWithinSourceTolerance, degreeReadout,
    recordedAnswerChoice, answerAngleDegrees, h_predicted_toReal]
  rw [abs_le]
  constructor <;> norm_num at * <;>
    linarith only [h_degree_lower, h_degree_upper]

/--
For a ray entering air-to-solid through the top of the `n = 1.38` block, the
greatest air-side incidence angle that remains on the total-internal-
reflection side at the perpendicular vertical face is the critical-ray value.
Its degree readout is compatible with recorded answer A, `72.1°`, under the
explicit source tolerance.

This formalizes `thm:physics:phyx_mini_0096:target`.
-/
theorem problem_phyx_mini_0096
    (setup : TransparentBlockSetup)
    (h_layout : HasDepictedBlockLayout setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_physical : HasPhysicalOpticalParameters setup)
    (h_critical : SatisfiesCriticalAngleSnellLaw setup) :
    IsGreatest (tirPermittingIncidenceRadians setup)
        (predictedMaximumAirIncidenceAngle setup).toReal ∧
      MatchesDisplayedAngleWithinSourceTolerance
        (predictedMaximumAirIncidenceAngle setup) recordedAnswerChoice := by
  exact ⟨predictedMaximum_isGreatestTIRIncidence setup h_layout h_readouts
      h_physical h_critical,
    predictedMaximum_matches_recorded_choice setup h_readouts h_physical h_critical⟩

end PhyXMiniProblems.ProblemPhyXMini0096
