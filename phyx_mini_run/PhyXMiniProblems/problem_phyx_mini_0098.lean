import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

namespace PhyXMiniProblems.ProblemPhyXMini0098

noncomputable section

/-!
# Acceptance angle of a step-index optical fiber

The figure shows a cylindrical core of refractive index `n₁`, a surrounding
cladding of refractive index `n₂`, the dashed central fiber axis, and an
incoming ray making the angle `θᵢ` with that axis.  Refractive indices are
unit-independent quantities carrying Physlib's identity dimension, attached
to typed optical regions.  Angles use Mathlib's physical angle type
`Real.Angle`.
-/

/-- A unit-independent physical scalar with the identity (dimensionless) dimension. -/
abbrev DimensionlessOpticalIndex : Type :=
  Dimensionful (WithDim (1 : Dimension) ℝ)

/-- The real SI readout of a dimensionless optical refractive index. -/
def refractiveIndexReadout (index : DimensionlessOpticalIndex) : ℝ :=
  (index UnitChoices.SI).val

/-- The three homogeneous optical regions traversed by the depicted ray. -/
inductive OpticalFiberRegion where
  /-- The exterior medium, idealized as air. -/
  | ambientAir
  /-- The germanium-doped silica core, labelled `n₁` in the figure. -/
  | core
  /-- The pure-silica cladding, labelled `n₂` in the figure. -/
  | cladding
  deriving DecidableEq, Repr

/-- Convert a numerical degree readout into a physical angle. -/
def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-- Express the acute representative of a physical angle in degrees. -/
def degreeReadout (angle : Real.Angle) : ℝ :=
  angle.toReal * 180 / Real.pi

/--
The dimensionless optical data and angles of the limiting guided ray.

`thetaI` is the figure label `θᵢ`, measured from the dashed fiber axis (and
hence from the entrance-face normal).  Inside the core, the same ray makes
`coreRayAngleToAxis` with the axis and `coreCladdingIncidenceAngle` with the
normal to the cylindrical core--cladding interface.
-/
structure StepIndexFiberSetup where
  /-- Unit-independent refractive index of each optical region. -/
  refractiveIndex : OpticalFiberRegion → DimensionlessOpticalIndex
  /-- The limiting external acceptance angle `θᵢ` shown in the figure. -/
  thetaI : Real.Angle
  /-- Angle of the refracted core ray to the dashed central axis. -/
  coreRayAngleToAxis : Real.Angle
  /-- Incidence angle at the core--cladding wall, measured from its normal. -/
  coreCladdingIncidenceAngle : Real.Angle

/--
Numerical material readouts from the problem, together with the usual
idealization that the unlabelled exterior region is air of index one.
-/
structure MatchesOpticalFiberFigure (setup : StepIndexFiberSetup) : Prop where
  ambientAirIndexReadout :
    refractiveIndexReadout (setup.refractiveIndex .ambientAir) = 1
  coreIndexReadoutNOne :
    refractiveIndexReadout (setup.refractiveIndex .core) = (1465 : ℝ) / 1000
  claddingIndexReadoutNTwo :
    refractiveIndexReadout (setup.refractiveIndex .cladding) = (1450 : ℝ) / 1000

/-- Select the acute representative appropriate for an angle in the diagram. -/
def IsAcuteOpticalAngle (angle : Real.Angle) : Prop :=
  0 ≤ angle.toReal ∧ angle.toReal ≤ Real.pi / 2

/--
The geometrical-optics laws for the limiting ray accepted by the fiber.

At the entrance face the ray obeys Snell's law.  The normal to the cylindrical
wall is perpendicular to the fiber axis, so the two internal angles are
complementary.  At the limiting acceptance angle, transmission into the
cladding would be tangential; the final field is precisely Snell's law for
that critical condition.  None of these laws contains the requested
one-decimal answer.
-/
structure SatisfiesLimitingGuidanceLaws (setup : StepIndexFiberSetup) : Prop where
  refractiveIndicesPositive :
    ∀ region : OpticalFiberRegion,
      0 < refractiveIndexReadout (setup.refractiveIndex region)
  claddingIndexLowerThanCore :
    refractiveIndexReadout (setup.refractiveIndex .cladding) <
      refractiveIndexReadout (setup.refractiveIndex .core)
  thetaIAcute :
    IsAcuteOpticalAngle setup.thetaI
  coreRayAngleAcute :
    IsAcuteOpticalAngle setup.coreRayAngleToAxis
  coreCladdingIncidenceAngleAcute :
    IsAcuteOpticalAngle setup.coreCladdingIncidenceAngle
  snellLawAtEntranceFace :
    refractiveIndexReadout (setup.refractiveIndex .ambientAir) *
        Real.Angle.sin setup.thetaI =
      refractiveIndexReadout (setup.refractiveIndex .core) *
        Real.Angle.sin setup.coreRayAngleToAxis
  cylindricalWallGeometry :
    setup.coreRayAngleToAxis + setup.coreCladdingIncidenceAngle =
      degrees 90
  criticalSnellLawAtCoreCladdingInterface :
    refractiveIndexReadout (setup.refractiveIndex .core) *
        Real.Angle.sin setup.coreCladdingIncidenceAngle =
      refractiveIndexReadout (setup.refractiveIndex .cladding) *
        Real.Angle.sin (degrees 90)

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The degree value printed beside each answer choice. -/
def AnswerChoice.angleDegrees : AnswerChoice → ℝ
  | .A => 121 / 10
  | .B => 131 / 10
  | .C => 119 / 10
  | .D => 132 / 10

/--
A displayed one-decimal choice matches a physical angle when its degree
readout differs by at most half of one tenth of a degree.
-/
def MatchesNearestTenthDegree
    (angle : Real.Angle) (choice : AnswerChoice) : Prop :=
  |degreeReadout angle - choice.angleDegrees| ≤ 1 / 20

/--
The entrance and critical-interface laws imply the standard numerical-aperture
relation.  This intermediate result contains no answer-choice value.
-/
lemma acceptance_angle_numerical_aperture_relation
    (setup : StepIndexFiberSetup)
    (laws : SatisfiesLimitingGuidanceLaws setup) :
    (refractiveIndexReadout (setup.refractiveIndex .ambientAir) *
        Real.Angle.sin setup.thetaI) ^ 2 =
      refractiveIndexReadout (setup.refractiveIndex .core) ^ 2 -
        refractiveIndexReadout (setup.refractiveIndex .cladding) ^ 2 := by
  have hdegrees : degrees 90 = ((Real.pi / 2 : ℝ) : Real.Angle) := by
    simp [degrees]
    ring_nf
  have hcomplement :
      setup.coreCladdingIncidenceAngle =
        ((Real.pi / 2 : ℝ) : Real.Angle) - setup.coreRayAngleToAxis := by
    apply (eq_sub_iff_add_eq).2
    rw [add_comm, laws.cylindricalWallGeometry, hdegrees]
  have hsin_wall :
      Real.Angle.sin setup.coreCladdingIncidenceAngle =
        Real.Angle.cos setup.coreRayAngleToAxis := by
    rw [hcomplement, Real.Angle.sin_pi_div_two_sub]
  have hsin_right : Real.Angle.sin (degrees 90) = 1 := by
    rw [hdegrees, Real.Angle.sin_coe, Real.sin_pi_div_two]
  have hcritical := laws.criticalSnellLawAtCoreCladdingInterface
  rw [hsin_wall, hsin_right, mul_one] at hcritical
  have htrig := Real.Angle.cos_sq_add_sin_sq setup.coreRayAngleToAxis
  rw [laws.snellLawAtEntranceFace]
  calc
    (refractiveIndexReadout (setup.refractiveIndex .core) *
          Real.Angle.sin setup.coreRayAngleToAxis) ^ 2 =
        refractiveIndexReadout (setup.refractiveIndex .core) ^ 2 *
          Real.Angle.sin setup.coreRayAngleToAxis ^ 2 := by ring
    _ = refractiveIndexReadout (setup.refractiveIndex .core) ^ 2 *
          (1 - Real.Angle.cos setup.coreRayAngleToAxis ^ 2) := by
        rw [← htrig]
        ring
    _ = refractiveIndexReadout (setup.refractiveIndex .core) ^ 2 -
          (refractiveIndexReadout (setup.refractiveIndex .core) *
            Real.Angle.cos setup.coreRayAngleToAxis) ^ 2 := by ring
    _ = refractiveIndexReadout (setup.refractiveIndex .core) ^ 2 -
          refractiveIndexReadout (setup.refractiveIndex .cladding) ^ 2 := by
        rw [hcritical]

/--
For a germanium-doped silica core with `n₁ = 1.465` and pure-silica cladding
with `n₂ = 1.450`, the limiting input angle `θᵢ` rounds to `12.1°`, answer A.

Blueprint: `thm:physics:phyx_mini_0098:target`.
-/
theorem theta_i_matches_choice_A
    (setup : StepIndexFiberSetup)
    (figure : MatchesOpticalFiberFigure setup)
    (laws : SatisfiesLimitingGuidanceLaws setup) :
    MatchesNearestTenthDegree setup.thetaI .A := by
  let x := setup.thetaI.toReal
  have hx_acute : 0 ≤ x ∧ x ≤ Real.pi / 2 := laws.thetaIAcute
  have hsin_nonneg : 0 ≤ Real.sin x := by
    exact Real.sin_nonneg_of_nonneg_of_le_pi hx_acute.1
      (hx_acute.2.trans (half_le_self Real.pi_nonneg))
  have hsq :
      Real.sin x ^ 2 = (1749 : ℝ) / 40000 := by
    have h := acceptance_angle_numerical_aperture_relation setup laws
    rw [figure.ambientAirIndexReadout, figure.coreIndexReadoutNOne,
      figure.claddingIndexReadoutNTwo] at h
    norm_num at h
    simpa [x, Real.Angle.sin_toReal] using h
  have hsin_lower_boundary :
      Real.sin ((263 : ℝ) / 1250) ^ 2 < (1749 : ℝ) / 40000 := by
    let a : ℝ := 263 / 1250
    let u : ℝ := a - a ^ 3 / 6 + |a| ^ 4 * (5 / 96)
    have hb := Real.sin_bound (x := a) (by norm_num [a])
    rw [abs_le] at hb
    have hsin_le : Real.sin a ≤ u := by
      dsimp [u]
      linarith [hb.2]
    have hu_nonneg : 0 ≤ u := by norm_num [u, a]
    have hp : 0 ≤ (u - Real.sin a) * (u + Real.sin a) := by
      apply mul_nonneg
      · linarith
      · have hs : 0 ≤ Real.sin a :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num [a])
            (le_trans (by norm_num [a] : a ≤ 2) Real.two_le_pi)
        linarith
    have hu_sq : u ^ 2 < (1749 : ℝ) / 40000 := by
      norm_num [u, a]
    nlinarith
  have hsin_upper_boundary :
      (1749 : ℝ) / 40000 < Real.sin ((53 : ℝ) / 250) ^ 2 := by
    let b : ℝ := 53 / 250
    let l : ℝ := b - b ^ 3 / 6 - |b| ^ 4 * (5 / 96)
    have hb := Real.sin_bound (x := b) (by norm_num [b])
    rw [abs_le] at hb
    have hl_le : l ≤ Real.sin b := by
      dsimp [l]
      linarith [hb.1]
    have hl_nonneg : 0 ≤ l := by norm_num [l, b]
    have hp : 0 ≤ (Real.sin b - l) * (Real.sin b + l) := by
      apply mul_nonneg
      · linarith
      · have hs : 0 ≤ Real.sin b :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num [b])
            (le_trans (by norm_num [b] : b ≤ 2) Real.two_le_pi)
        linarith
    have hl_sq : (1749 : ℝ) / 40000 < l ^ 2 := by
      norm_num [l, b]
    nlinarith
  have hx_lower : (263 : ℝ) / 1250 ≤ x := by
    by_contra h
    have hlt : x < (263 : ℝ) / 1250 := lt_of_not_ge h
    have hsin_lt :
        Real.sin x < Real.sin ((263 : ℝ) / 1250) :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (by linarith [hx_acute.1, Real.pi_pos])
        (le_trans (by norm_num : (263 : ℝ) / 1250 ≤ 1)
          Real.one_le_pi_div_two)
        hlt
    have hboundary_nonneg :
        0 ≤ Real.sin ((263 : ℝ) / 1250) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num)
        (le_trans (by norm_num : (263 : ℝ) / 1250 ≤ 2) Real.two_le_pi)
    have hsquares :
        Real.sin x ^ 2 < Real.sin ((263 : ℝ) / 1250) ^ 2 :=
      (sq_lt_sq₀ hsin_nonneg hboundary_nonneg).2 hsin_lt
    linarith
  have hx_upper : x ≤ (53 : ℝ) / 250 := by
    by_contra h
    have hlt : (53 : ℝ) / 250 < x := lt_of_not_ge h
    have hsin_lt :
        Real.sin ((53 : ℝ) / 250) < Real.sin x :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (by linarith [Real.pi_pos])
        hx_acute.2
        hlt
    have hboundary_nonneg :
        0 ≤ Real.sin ((53 : ℝ) / 250) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num)
        (le_trans (by norm_num : (53 : ℝ) / 250 ≤ 2) Real.two_le_pi)
    have hsquares :
        Real.sin ((53 : ℝ) / 250) ^ 2 < Real.sin x ^ 2 :=
      (sq_lt_sq₀ hboundary_nonneg hsin_nonneg).2 hsin_lt
    linarith
  have hpi_lower_half : (3141 : ℝ) / 2000 < Real.pi / 2 := by
    let y : ℝ := 3141 / 128000
    have hy : |y| ≤ 1 := by norm_num [y]
    have hb := Real.cos_bound hy
    have hc0 : (99969889 : ℝ) / 100000000 ≤ Real.cos y := by
      rw [abs_le] at hb
      norm_num [y] at hb ⊢
      linarith
    have hc1 : (9987957 : ℝ) / 10000000 ≤ Real.cos (2 * y) := by
      rw [Real.cos_two_mul]
      have hp : 0 ≤
          (Real.cos y - (99969889 : ℝ) / 100000000) *
            (Real.cos y + (99969889 : ℝ) / 100000000) := by
        positivity
      nlinarith
    have hc2 :
        (9951856 : ℝ) / 10000000 ≤ Real.cos (2 * (2 * y)) := by
      rw [Real.cos_two_mul]
      have hp : 0 ≤
          (Real.cos (2 * y) - (9987957 : ℝ) / 10000000) *
            (Real.cos (2 * y) + (9987957 : ℝ) / 10000000) := by
        positivity
      nlinarith
    have hc3 :
        (9807887 : ℝ) / 10000000 ≤ Real.cos (2 * (2 * (2 * y))) := by
      rw [Real.cos_two_mul]
      have hp : 0 ≤
          (Real.cos (2 * (2 * y)) - (9951856 : ℝ) / 10000000) *
            (Real.cos (2 * (2 * y)) + (9951856 : ℝ) / 10000000) := by
        positivity
      nlinarith
    have hc4 :
        (923892 : ℝ) / 1000000 ≤
          Real.cos (2 * (2 * (2 * (2 * y)))) := by
      rw [Real.cos_two_mul]
      have hp : 0 ≤
          (Real.cos (2 * (2 * (2 * y))) - (9807887 : ℝ) / 10000000) *
            (Real.cos (2 * (2 * (2 * y))) +
              (9807887 : ℝ) / 10000000) := by
        positivity
      nlinarith
    have hc5 :
        (70715 : ℝ) / 100000 ≤
          Real.cos (2 * (2 * (2 * (2 * (2 * y))))) := by
      rw [Real.cos_two_mul]
      have hp : 0 ≤
          (Real.cos (2 * (2 * (2 * (2 * y)))) -
              (923892 : ℝ) / 1000000) *
            (Real.cos (2 * (2 * (2 * (2 * y)))) +
              (923892 : ℝ) / 1000000) := by
        positivity
      nlinarith
    have hc6 :
        0 < Real.cos (2 * (2 * (2 * (2 * (2 * (2 * y)))))) := by
      rw [Real.cos_two_mul]
      have hp : 0 ≤
          (Real.cos (2 * (2 * (2 * (2 * (2 * y))))) -
              (70715 : ℝ) / 100000) *
            (Real.cos (2 * (2 * (2 * (2 * (2 * y))))) +
              (70715 : ℝ) / 100000) := by
        positivity
      norm_num at hp ⊢
      nlinarith
    have hcos : 0 < Real.cos ((3141 : ℝ) / 2000) := by
      norm_num [y] at hc6 ⊢
      exact hc6
    by_contra h
    have hroot : Real.pi / 2 ≤ (3141 : ℝ) / 2000 := le_of_not_gt h
    have hcos_nonpos : Real.cos ((3141 : ℝ) / 2000) ≤ 0 := by
      calc
        Real.cos ((3141 : ℝ) / 2000) ≤ Real.cos (Real.pi / 2) :=
          Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
            (by linarith [Real.two_le_pi]) hroot
        _ = 0 := Real.cos_pi_div_two
    linarith
  have hpi_upper_half : Real.pi / 2 < (1571 : ℝ) / 1000 := by
    let y : ℝ := 1571 / 64000
    have hy : |y| ≤ 1 := by norm_num [y]
    have hb := Real.cos_bound hy
    have hc0 : Real.cos y ≤ (99969875 : ℝ) / 100000000 := by
      rw [abs_le] at hb
      norm_num [y] at hb ⊢
      linarith
    have hc1 : Real.cos (2 * y) ≤ (9987952 : ℝ) / 10000000 := by
      rw [Real.cos_two_mul]
      have hcp : 0 ≤ Real.cos y := (Real.cos_pos_of_le_one hy).le
      have hp : 0 ≤
          ((99969875 : ℝ) / 100000000 - Real.cos y) *
            ((99969875 : ℝ) / 100000000 + Real.cos y) := by
        positivity
      nlinarith
    have hc2 : Real.cos (2 * (2 * y)) ≤ (9951838 : ℝ) / 10000000 := by
      rw [Real.cos_two_mul]
      have hcp : 0 ≤ Real.cos (2 * y) :=
        (Real.cos_pos_of_le_one (x := 2 * y) (by norm_num [y])).le
      have hp : 0 ≤
          ((9987952 : ℝ) / 10000000 - Real.cos (2 * y)) *
            ((9987952 : ℝ) / 10000000 + Real.cos (2 * y)) := by
        positivity
      nlinarith
    have hc3 :
        Real.cos (2 * (2 * (2 * y))) ≤ (980782 : ℝ) / 1000000 := by
      rw [Real.cos_two_mul]
      have hcp : 0 ≤ Real.cos (2 * (2 * y)) :=
        (Real.cos_pos_of_le_one (x := 2 * (2 * y))
          (by norm_num [y])).le
      have hp : 0 ≤
          ((9951838 : ℝ) / 10000000 - Real.cos (2 * (2 * y))) *
            ((9951838 : ℝ) / 10000000 + Real.cos (2 * (2 * y))) := by
        positivity
      nlinarith
    have hc4 :
        Real.cos (2 * (2 * (2 * (2 * y)))) ≤ (92387 : ℝ) / 100000 := by
      rw [Real.cos_two_mul]
      have hcp : 0 ≤ Real.cos (2 * (2 * (2 * y))) :=
        (Real.cos_pos_of_le_one (x := 2 * (2 * (2 * y)))
          (by norm_num [y])).le
      have hp : 0 ≤
          ((980782 : ℝ) / 1000000 - Real.cos (2 * (2 * (2 * y)))) *
            ((980782 : ℝ) / 1000000 +
              Real.cos (2 * (2 * (2 * y)))) := by
        positivity
      nlinarith
    have hc5 :
        Real.cos (2 * (2 * (2 * (2 * (2 * y))))) ≤
          (70708 : ℝ) / 100000 := by
      rw [Real.cos_two_mul]
      have hcp : 0 ≤ Real.cos (2 * (2 * (2 * (2 * y)))) :=
        (Real.cos_pos_of_le_one (x := 2 * (2 * (2 * (2 * y))))
          (by norm_num [y])).le
      have hp : 0 ≤
          ((92387 : ℝ) / 100000 -
              Real.cos (2 * (2 * (2 * (2 * y))))) *
            ((92387 : ℝ) / 100000 +
              Real.cos (2 * (2 * (2 * (2 * y))))) := by
        positivity
      nlinarith
    have hc6 :
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * y)))))) < 0 := by
      rw [Real.cos_two_mul]
      have hcp : 0 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * y))))) :=
        (Real.cos_pos_of_le_one
          (x := 2 * (2 * (2 * (2 * (2 * y))))) (by norm_num [y])).le
      have hp : 0 ≤
          ((70708 : ℝ) / 100000 -
              Real.cos (2 * (2 * (2 * (2 * (2 * y)))))) *
            ((70708 : ℝ) / 100000 +
              Real.cos (2 * (2 * (2 * (2 * (2 * y)))))) := by
        positivity
      norm_num at hp ⊢
      nlinarith
    have hcos : Real.cos ((1571 : ℝ) / 1000) < 0 := by
      norm_num [y] at hc6 ⊢
      exact hc6
    by_contra h
    have hr : (1571 : ℝ) / 1000 ≤ Real.pi / 2 := le_of_not_gt h
    have hcos_nonneg : 0 ≤ Real.cos ((1571 : ℝ) / 1000) := by
      calc
        0 = Real.cos (Real.pi / 2) := Real.cos_pi_div_two.symm
        _ ≤ Real.cos ((1571 : ℝ) / 1000) :=
          Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
            (by linarith [Real.two_le_pi]) hr
    linarith
  have hpi_lower : (3141 : ℝ) / 1000 < Real.pi := by
    linarith
  have hpi_upper : Real.pi < (1571 : ℝ) / 500 := by
    linarith
  have hdegree_lower : (241 : ℝ) / 20 ≤ x * 180 / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).2
    linarith
  have hdegree_upper : x * 180 / Real.pi ≤ (243 : ℝ) / 20 := by
    apply (div_le_iff₀ Real.pi_pos).2
    linarith
  change |x * 180 / Real.pi - (121 : ℝ) / 10| ≤ 1 / 20
  rw [abs_le]
  constructor <;> linarith

end

end PhyXMiniProblems.ProblemPhyXMini0098
