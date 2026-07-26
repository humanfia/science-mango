import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Optics.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0143

/-!
# Refraction through a flat aquarium wall

The figure shows one ray crossing, in order, air, a flat glass wall, and the
water inside an aquarium. Refractive indices are dimensionless quantities
tagged with Physlib's identity dimension; numerical data access their scalar
readouts. Angles are physical angles modulo a full turn, represented by
Mathlib's `Real.Angle`, and are measured from the indicated interface normal.
-/

/-- The three homogeneous optical media traversed by the ray. -/
inductive OpticalMedium where
  | air
  | glass
  | water
  deriving DecidableEq, Repr

/-- The two planar faces of the aquarium's glass wall. -/
inductive RefractionInterface where
  | airGlass
  | glassWater
  deriving DecidableEq, Repr

/-- Labels for the perpendiculars at the two refraction points. -/
inductive NormalLabel where
  | entryNormal
  | exitNormal
  deriving DecidableEq, Repr

/-- The three successive segments of the single ray shown in the figure. -/
inductive RaySegment where
  | inAir
  | inGlass
  | inWater
  deriving DecidableEq, Repr

def RefractionInterface.incidentMedium :
    RefractionInterface → OpticalMedium
  | .airGlass => .air
  | .glassWater => .glass

def RefractionInterface.transmittedMedium :
    RefractionInterface → OpticalMedium
  | .airGlass => .glass
  | .glassWater => .water

def RefractionInterface.incidentRay : RefractionInterface → RaySegment
  | .airGlass => .inAir
  | .glassWater => .inGlass

def RefractionInterface.transmittedRay : RefractionInterface → RaySegment
  | .airGlass => .inGlass
  | .glassWater => .inWater

def RefractionInterface.normal : RefractionInterface → NormalLabel
  | .airGlass => .entryNormal
  | .glassWater => .exitNormal

/--
Physical quantities attached to the three-layer ray diagram.

The function `angleToNormal` retains both the ray-segment label and the normal
label so that parallel-face geometry can explicitly relate the two angles of
the glass segment.
-/
structure AquariumRefractionSetup where
  refractiveIndex : OpticalMedium → WithDim (1 : Dimension) ℝ
  angleToNormal : RaySegment → NormalLabel → Real.Angle

/-- The unit-independent scalar readout of a dimensionless refractive index. -/
def refractiveIndexReadout
    (setup : AquariumRefractionSetup) (medium : OpticalMedium) : ℝ :=
  (setup.refractiveIndex medium).val

/-- Convert a scalar degree readout to a physical angle. -/
def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-- Read the principal representative of a physical angle in degrees. -/
def degreeReadout (angle : Real.Angle) : ℝ :=
  angle.toReal * 180 / Real.pi

/-- The incident angle in air, shown as `43.5°` from the entry normal. -/
def airIncidenceAngle (setup : AquariumRefractionSetup) : Real.Angle :=
  setup.angleToNormal .inAir .entryNormal

/-- The refracted glass angle at the air--glass face. -/
def glassRefractionAngleAtEntry
    (setup : AquariumRefractionSetup) : Real.Angle :=
  setup.angleToNormal .inGlass .entryNormal

/-- The incidence angle of the same glass segment at the glass--water face. -/
def glassIncidenceAngleAtExit
    (setup : AquariumRefractionSetup) : Real.Angle :=
  setup.angleToNormal .inGlass .exitNormal

/-- The requested refracted angle in water, measured from the exit normal. -/
def waterRefractionAngle (setup : AquariumRefractionSetup) : Real.Angle :=
  setup.angleToNormal .inWater .exitNormal

/-- A normal angle is on the physical acute branch used by this diagram. -/
def IsPhysicalRefractionAngle (angle : Real.Angle) : Prop :=
  angle.toReal ∈ Set.Icc 0 (Real.pi / 2)

/-- Positivity and acute-angle conditions for the depicted ray path. -/
structure HasPhysicalRefractionConfiguration
    (setup : AquariumRefractionSetup) : Prop where
  refractive_indices_positive :
    ∀ medium, 0 < refractiveIndexReadout setup medium
  air_angle_physical : IsPhysicalRefractionAngle (airIncidenceAngle setup)
  glass_entry_angle_physical :
    IsPhysicalRefractionAngle (glassRefractionAngleAtEntry setup)
  glass_exit_angle_physical :
    IsPhysicalRefractionAngle (glassIncidenceAngleAtExit setup)
  water_angle_physical :
    IsPhysicalRefractionAngle (waterRefractionAngle setup)

/--
Numerical readouts stated in the problem or supplied by the standard material
model. The glass index is the stated `1.54`; `1` and `1.33` are respectively
the ambient-air and water index readouts used at the displayed precision.
-/
structure MatchesProblemData (setup : AquariumRefractionSetup) : Prop where
  air_refractive_index : refractiveIndexReadout setup .air = 1
  glass_refractive_index : refractiveIndexReadout setup .glass = 1.54
  water_refractive_index : refractiveIndexReadout setup .water = 1.33
  incident_angle_from_figure : airIncidenceAngle setup = degrees 43.5

/--
The two flat faces of the glass wall are parallel, so their normals are
parallel and the straight glass segment makes the same angle with each.
-/
def HasParallelGlassFaceGeometry (setup : AquariumRefractionSetup) : Prop :=
  glassRefractionAngleAtEntry setup = glassIncidenceAngleAtExit setup

/-- Snell's law at one of the two material interfaces. -/
def SatisfiesSnellLawAt
    (setup : AquariumRefractionSetup)
    (interface : RefractionInterface) : Prop :=
  refractiveIndexReadout setup interface.incidentMedium *
      Real.Angle.sin
        (setup.angleToNormal interface.incidentRay interface.normal) =
    refractiveIndexReadout setup interface.transmittedMedium *
      Real.Angle.sin
        (setup.angleToNormal interface.transmittedRay interface.normal)

/--
For parallel faces, applying Snell's law twice cancels the intermediate glass
index and relates the air and water angles directly.
-/
lemma net_snell_law_across_parallel_glass
    (setup : AquariumRefractionSetup)
    (hParallel : HasParallelGlassFaceGeometry setup)
    (hSnell : ∀ interface, SatisfiesSnellLawAt setup interface) :
    refractiveIndexReadout setup .air *
        Real.Angle.sin (airIncidenceAngle setup) =
      refractiveIndexReadout setup .water *
        Real.Angle.sin (waterRefractionAngle setup) := by
  have hEntry := hSnell .airGlass
  have hExit := hSnell .glassWater
  change
    refractiveIndexReadout setup .air *
        Real.Angle.sin (airIncidenceAngle setup) =
      refractiveIndexReadout setup .glass *
        Real.Angle.sin (glassRefractionAngleAtEntry setup) at hEntry
  change
    refractiveIndexReadout setup .glass *
        Real.Angle.sin (glassIncidenceAngleAtExit setup) =
      refractiveIndexReadout setup .water *
        Real.Angle.sin (waterRefractionAngle setup) at hExit
  calc
    _ = refractiveIndexReadout setup .glass *
          Real.Angle.sin (glassRefractionAngleAtEntry setup) := hEntry
    _ = refractiveIndexReadout setup .glass *
          Real.Angle.sin (glassIncidenceAngleAtExit setup) := by
            rw [hParallel]
    _ = _ := hExit

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The degree readout printed beside each answer label. -/
def answerInDegrees : AnswerChoice → ℝ
  | .A => 41.2
  | .B => 21.2
  | .C => 31.2
  | .D => 36.2

/-- Agreement with a choice displayed to the nearest tenth of a degree. -/
def MatchesAnswerToNearestTenth
    (angle : Real.Angle) (choice : AnswerChoice) : Prop :=
  |degreeReadout angle - answerInDegrees choice| ≤ 0.05

/-- A choice is the unique closest displayed angle to a degree readout. -/
def IsUniqueClosestAnswer
    (angle : Real.Angle) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |degreeReadout angle - answerInDegrees choice| <
      |degreeReadout angle - answerInDegrees other|

/--
The ray refracts into the water at `31.2°` to the displayed precision, making
choice C the unique closest answer.

This formalizes `thm:physics:phyx_mini_0143:target`.
-/
theorem water_refraction_angle_is_choice_C
    (setup : AquariumRefractionSetup)
    (_data : MatchesProblemData setup)
    (_physical : HasPhysicalRefractionConfiguration setup)
    (_parallel : HasParallelGlassFaceGeometry setup)
    (_snell : ∀ interface, SatisfiesSnellLawAt setup interface) :
    MatchesAnswerToNearestTenth (waterRefractionAngle setup) .C ∧
      IsUniqueClosestAnswer (waterRefractionAngle setup) .C := by
  have sin_lt_self {x : ℝ} (hx : 0 < x) : Real.sin x < x := by
    rcases lt_or_ge 1 x with hx_one | hx_one
    · exact (Real.sin_le_one x).trans_lt hx_one
    have hx_abs : |x| = x := abs_of_nonneg hx.le
    have hBound :=
      le_of_abs_le (Real.sin_bound (show |x| ≤ 1 by rwa [hx_abs]))
    rw [sub_le_iff_le_add', hx_abs] at hBound
    apply hBound.trans_lt
    rw [sub_add, sub_lt_self_iff, sub_pos, div_eq_mul_inv (x ^ 3)]
    refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos hx 3)
    apply pow_le_pow_of_le_one hx.le hx_one
    simp
  -- First derive decimal bounds for π from the imported half-angle identity.
  have hSeriesUpper :
      Real.sqrtTwoAddSeries 0 4 ≤ (1447 : ℝ) / 727 := by
    have h₁ : √(2 : ℝ) ≤ (338 : ℝ) / 239 := by
      have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have hnonneg := Real.sqrt_nonneg (2 : ℝ)
      nlinarith only [hsq, hnonneg]
    have h₂ : √(2 + √(2 : ℝ)) ≤ (704 : ℝ) / 381 := by
      have hsq :=
        Real.sq_sqrt (show (0 : ℝ) ≤ 2 + √(2 : ℝ) by positivity)
      have hnonneg := Real.sqrt_nonneg (2 + √(2 : ℝ))
      nlinarith only [h₁, hsq, hnonneg]
    have h₃ :
        √(2 + √(2 + √(2 : ℝ))) ≤ (1940 : ℝ) / 989 := by
      have hsq :=
        Real.sq_sqrt
          (show (0 : ℝ) ≤ 2 + √(2 + √(2 : ℝ)) by positivity)
      have hnonneg := Real.sqrt_nonneg (2 + √(2 + √(2 : ℝ)))
      nlinarith only [h₂, hsq, hnonneg]
    have h₄ :
        √(2 + √(2 + √(2 + √(2 : ℝ)))) ≤
          (1447 : ℝ) / 727 := by
      have hsq :=
        Real.sq_sqrt
          (show (0 : ℝ) ≤ 2 + √(2 + √(2 + √(2 : ℝ))) by
            positivity)
      have hnonneg :=
        Real.sqrt_nonneg (2 + √(2 + √(2 + √(2 : ℝ))))
      nlinarith only [h₃, hsq, hnonneg]
    norm_num [Real.sqrtTwoAddSeries]
    exact h₄
  -- The matching lower bound on the nested radical gives an upper bound on π.
  have hSeriesLower :
      (412 : ℝ) / 207 ≤ Real.sqrtTwoAddSeries 0 4 := by
    have h₁ : (41 : ℝ) / 29 ≤ √(2 : ℝ) := by
      have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have hnonneg := Real.sqrt_nonneg (2 : ℝ)
      nlinarith only [hsq, hnonneg]
    have h₂ : (109 : ℝ) / 59 ≤ √(2 + √(2 : ℝ)) := by
      have hsq :=
        Real.sq_sqrt (show (0 : ℝ) ≤ 2 + √(2 : ℝ) by positivity)
      have hnonneg := Real.sqrt_nonneg (2 + √(2 : ℝ))
      nlinarith only [h₁, hsq, hnonneg]
    have h₃ :
        (865 : ℝ) / 441 ≤ √(2 + √(2 + √(2 : ℝ))) := by
      have hsq :=
        Real.sq_sqrt
          (show (0 : ℝ) ≤ 2 + √(2 + √(2 : ℝ)) by positivity)
      have hnonneg := Real.sqrt_nonneg (2 + √(2 + √(2 : ℝ)))
      nlinarith only [h₂, hsq, hnonneg]
    have h₄ :
        (412 : ℝ) / 207 ≤
          √(2 + √(2 + √(2 + √(2 : ℝ)))) := by
      have hsq :=
        Real.sq_sqrt
          (show (0 : ℝ) ≤ 2 + √(2 + √(2 + √(2 : ℝ))) by
            positivity)
      have hnonneg :=
        Real.sqrt_nonneg (2 + √(2 + √(2 + √(2 : ℝ))))
      nlinarith only [h₃, hsq, hnonneg]
    norm_num [Real.sqrtTwoAddSeries]
    exact h₄
  -- These coarse bounds are sufficient for all small-angle estimates below.
  have hPiLower : (3.14 : ℝ) < Real.pi := by
    have hSinLower :
        (3.14 : ℝ) / 64 < Real.sin (Real.pi / 64) := by
      rw [show (64 : ℝ) = 2 ^ (4 + 2) by norm_num,
        Real.sin_pi_over_two_pow_succ]
      have hrad : 0 ≤ 2 - Real.sqrtTwoAddSeries 0 4 :=
        sub_nonneg.mpr (Real.sqrtTwoAddSeries_lt_two 4).le
      have hsq := Real.sq_sqrt hrad
      have hnonneg :=
        Real.sqrt_nonneg (2 - Real.sqrtTwoAddSeries 0 4)
      nlinarith only [hSeriesUpper, hsq, hnonneg]
    have hSinUpper :=
      sin_lt_self (show 0 < Real.pi / 64 by positivity)
    nlinarith only [hSinLower, hSinUpper]
  -- Bound π above by reversing the same sine estimate.
  have hPiUpper : Real.pi < (3.15 : ℝ) := by
    have hSinUpper :
        Real.sin (Real.pi / 64) < (0.04916 : ℝ) := by
      rw [show (64 : ℝ) = 2 ^ (4 + 2) by norm_num,
        Real.sin_pi_over_two_pow_succ]
      have hrad : 0 ≤ 2 - Real.sqrtTwoAddSeries 0 4 :=
        sub_nonneg.mpr (Real.sqrtTwoAddSeries_lt_two 4).le
      have hsq := Real.sq_sqrt hrad
      have hnonneg :=
        Real.sqrt_nonneg (2 - Real.sqrtTwoAddSeries 0 4)
      nlinarith only [hSeriesLower, hsq, hnonneg]
    let x : ℝ := Real.pi / 64
    have hxPos : 0 < x := by
      dsimp [x]
      positivity
    have hxLe : x ≤ (1 : ℝ) / 16 := by
      dsimp [x]
      nlinarith only [Real.pi_le_four]
    have hxAbs : |x| = x := abs_of_pos hxPos
    have hBound :=
      neg_le_of_abs_le
        (Real.sin_bound (x := x) (by
          rw [hxAbs]
          linarith only [hxLe]))
    rw [hxAbs] at hBound
    have hxCube : x ^ 3 ≤ ((1 : ℝ) / 16) ^ 3 :=
      pow_le_pow_left₀ hxPos.le hxLe 3
    have hxFourth : x ^ 4 ≤ ((1 : ℝ) / 16) ^ 4 :=
      pow_le_pow_left₀ hxPos.le hxLe 4
    have hSinX : Real.sin x < (0.04916 : ℝ) := by
      simpa [x] using hSinUpper
    dsimp [x] at hBound hxCube hxFourth hSinX ⊢
    nlinarith only [hBound, hxCube, hxFourth, hSinX]
  -- Rational square-root bounds control the exact 30° and 45° values.
  have hSqrtTwoLower : (1.4142 : ℝ) < √2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hSqrtTwoUpper : √2 < (1.4143 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hSqrtThreeLower : (1.732 : ℝ) < √3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hSqrtThreeUpper : √3 < (1.733 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  -- The two-interface law fixes the sine of the water angle.
  have hNet :=
    net_snell_law_across_parallel_glass setup _parallel _snell
  rw [_data.air_refractive_index, _data.water_refractive_index,
    _data.incident_angle_from_figure] at hNet
  norm_num [degrees, Real.Angle.sin_coe] at hNet
  have hIncidentAngle :
      (87 / 2 : ℝ) * Real.pi / 180 = 29 * Real.pi / 120 := by
    ring
  rw [hIncidentAngle] at hNet
  have hSinWater :
      Real.sin (waterRefractionAngle setup).toReal =
        (100 : ℝ) / 133 * Real.sin (29 * Real.pi / 120) := by
    rw [Real.Angle.sin_toReal]
    nlinarith only [hNet]
  -- Estimate the incident sine by writing 43.5° as 45° minus 1.5°.
  let incidentDelta : ℝ := Real.pi / 120
  have hIncidentDeltaPos : 0 < incidentDelta := by
    dsimp [incidentDelta]
    positivity
  have hIncidentDeltaUpper : incidentDelta < (0.02625 : ℝ) := by
    dsimp [incidentDelta]
    nlinarith only [hPiUpper]
  have hIncidentDeltaLeOne : incidentDelta ≤ 1 := by
    linarith only [hIncidentDeltaUpper]
  have hIncidentDeltaAbs : |incidentDelta| = incidentDelta :=
    abs_of_pos hIncidentDeltaPos
  have hIncidentDeltaSq :
      incidentDelta ^ 2 ≤ (0.02625 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hIncidentDeltaPos.le hIncidentDeltaUpper.le 2
  have hIncidentDeltaCube :
      incidentDelta ^ 3 ≤ (0.02625 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hIncidentDeltaPos.le hIncidentDeltaUpper.le 3
  have hIncidentDeltaFourth :
      incidentDelta ^ 4 ≤ (0.02625 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hIncidentDeltaPos.le hIncidentDeltaUpper.le 4
  have hSinIncidentDeltaLower :
      (0.02616 : ℝ) < Real.sin incidentDelta := by
    have hDeltaLower : (0.026166 : ℝ) < incidentDelta := by
      dsimp [incidentDelta]
      nlinarith only [hPiLower]
    have hBound :=
      neg_le_of_abs_le
        (Real.sin_bound (x := incidentDelta) (by
          rw [hIncidentDeltaAbs]
          exact hIncidentDeltaLeOne))
    rw [hIncidentDeltaAbs] at hBound
    nlinarith only
      [hBound, hDeltaLower, hIncidentDeltaCube,
        hIncidentDeltaFourth]
  have hSinIncidentDeltaUpper :
      Real.sin incidentDelta < (0.02625 : ℝ) :=
    (sin_lt_self hIncidentDeltaPos).trans
      (hIncidentDeltaUpper.trans_le (by norm_num))
  have hCosIncidentDeltaLower :
      (0.99965 : ℝ) < Real.cos incidentDelta := by
    have hBound :=
      neg_le_of_abs_le
        (Real.cos_bound (x := incidentDelta) (by
          rw [hIncidentDeltaAbs]
          exact hIncidentDeltaLeOne))
    rw [hIncidentDeltaAbs] at hBound
    nlinarith only
      [hBound, hIncidentDeltaSq, hIncidentDeltaFourth]
  have hIncidentDifferencePos :
      0 < Real.cos incidentDelta - Real.sin incidentDelta := by
    nlinarith only [hCosIncidentDeltaLower, hSinIncidentDeltaUpper]
  have hIncidentDifferenceLower :
      (0.9734 : ℝ) <
        Real.cos incidentDelta - Real.sin incidentDelta := by
    nlinarith only [hCosIncidentDeltaLower, hSinIncidentDeltaUpper]
  have hIncidentDifferenceUpper :
      Real.cos incidentDelta - Real.sin incidentDelta <
        (0.97384 : ℝ) := by
    nlinarith only [Real.cos_le_one incidentDelta,
      hSinIncidentDeltaLower]
  have hIncidentProductLower :
      (1.4142 : ℝ) * 0.9734 <
        √2 * (Real.cos incidentDelta - Real.sin incidentDelta) := by
    exact mul_lt_mul hSqrtTwoLower hIncidentDifferenceLower.le
      (by norm_num) (Real.sqrt_nonneg 2)
  have hIncidentProductUpper :
      √2 * (Real.cos incidentDelta - Real.sin incidentDelta) <
        (1.4143 : ℝ) * 0.97384 := by
    exact mul_lt_mul hSqrtTwoUpper hIncidentDifferenceUpper.le
      hIncidentDifferencePos (by norm_num)
  have hIncidentIdentity :
      Real.sin (29 * Real.pi / 120) =
        √2 / 2 *
          (Real.cos incidentDelta - Real.sin incidentDelta) := by
    have hAngle :
        29 * Real.pi / 120 = Real.pi / 4 - incidentDelta := by
      dsimp [incidentDelta]
      ring
    rw [hAngle, Real.sin_sub, Real.sin_pi_div_four,
      Real.cos_pi_div_four]
    ring
  have hIncidentSineLower :
      (0.5175 : ℝ) <
        (100 : ℝ) / 133 * Real.sin (29 * Real.pi / 120) := by
    rw [hIncidentIdentity]
    nlinarith only [hIncidentProductLower]
  have hIncidentSineUpper :
      (100 : ℝ) / 133 * Real.sin (29 * Real.pi / 120) <
        (0.5178 : ℝ) := by
    rw [hIncidentIdentity]
    nlinarith only [hIncidentProductUpper]
  -- The sine at the lower rounding boundary is below the Snell-law value.
  let lowerDelta : ℝ := 23 * Real.pi / 3600
  have hLowerDeltaPos : 0 < lowerDelta := by
    dsimp [lowerDelta]
    positivity
  have hLowerDeltaUpper : lowerDelta < (0.020125 : ℝ) := by
    dsimp [lowerDelta]
    nlinarith only [hPiUpper]
  have hSinLowerDeltaUpper :
      Real.sin lowerDelta < (0.020125 : ℝ) :=
    (sin_lt_self hLowerDeltaPos).trans hLowerDeltaUpper
  have hSinLowerDeltaPos : 0 < Real.sin lowerDelta := by
    apply Real.sin_pos_of_pos_of_lt_pi hLowerDeltaPos
    dsimp [lowerDelta]
    nlinarith only [Real.pi_pos]
  have hLowerProductUpper :
      √3 * Real.sin lowerDelta < (1.733 : ℝ) * 0.020125 := by
    exact mul_lt_mul hSqrtThreeUpper hSinLowerDeltaUpper.le
      hSinLowerDeltaPos (by norm_num)
  have hLowerBoundaryIdentity :
      Real.sin ((31.15 : ℝ) * Real.pi / 180) =
        (1 : ℝ) / 2 * Real.cos lowerDelta +
          √3 / 2 * Real.sin lowerDelta := by
    have hAngle :
        (31.15 : ℝ) * Real.pi / 180 =
          Real.pi / 6 + lowerDelta := by
      dsimp [lowerDelta]
      ring
    rw [hAngle, Real.sin_add, Real.sin_pi_div_six,
      Real.cos_pi_div_six]
  have hLowerBoundaryUpper :
      Real.sin ((31.15 : ℝ) * Real.pi / 180) <
        (0.51745 : ℝ) := by
    rw [hLowerBoundaryIdentity]
    nlinarith only [Real.cos_le_one lowerDelta, hLowerProductUpper]
  have hLowerBoundarySine :
      Real.sin ((31.15 : ℝ) * Real.pi / 180) <
        (100 : ℝ) / 133 * Real.sin (29 * Real.pi / 120) := by
    linarith only [hLowerBoundaryUpper, hIncidentSineLower]
  -- The sine at the upper rounding boundary is above the Snell-law value.
  let upperDelta : ℝ := Real.pi / 144
  have hUpperDeltaPos : 0 < upperDelta := by
    dsimp [upperDelta]
    positivity
  have hUpperDeltaLower : (0.021805 : ℝ) < upperDelta := by
    dsimp [upperDelta]
    nlinarith only [hPiLower]
  have hUpperDeltaUpper : upperDelta < (0.021875 : ℝ) := by
    dsimp [upperDelta]
    nlinarith only [hPiUpper]
  have hUpperDeltaLeOne : upperDelta ≤ 1 := by
    linarith only [hUpperDeltaUpper]
  have hUpperDeltaAbs : |upperDelta| = upperDelta :=
    abs_of_pos hUpperDeltaPos
  have hUpperDeltaSq :
      upperDelta ^ 2 ≤ (0.021875 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hUpperDeltaPos.le hUpperDeltaUpper.le 2
  have hUpperDeltaCube :
      upperDelta ^ 3 ≤ (0.021875 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hUpperDeltaPos.le hUpperDeltaUpper.le 3
  have hUpperDeltaFourth :
      upperDelta ^ 4 ≤ (0.021875 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hUpperDeltaPos.le hUpperDeltaUpper.le 4
  have hSinUpperDeltaLower :
      (0.0218 : ℝ) < Real.sin upperDelta := by
    have hBound :=
      neg_le_of_abs_le
        (Real.sin_bound (x := upperDelta) (by
          rw [hUpperDeltaAbs]
          exact hUpperDeltaLeOne))
    rw [hUpperDeltaAbs] at hBound
    nlinarith only
      [hBound, hUpperDeltaLower, hUpperDeltaCube,
        hUpperDeltaFourth]
  have hCosUpperDeltaLower :
      (0.99975 : ℝ) < Real.cos upperDelta := by
    have hBound :=
      neg_le_of_abs_le
        (Real.cos_bound (x := upperDelta) (by
          rw [hUpperDeltaAbs]
          exact hUpperDeltaLeOne))
    rw [hUpperDeltaAbs] at hBound
    nlinarith only
      [hBound, hUpperDeltaSq, hUpperDeltaFourth]
  have hUpperProductLower :
      (1.732 : ℝ) * 0.0218 <
        √3 * Real.sin upperDelta := by
    exact mul_lt_mul hSqrtThreeLower hSinUpperDeltaLower.le
      (by norm_num) (Real.sqrt_nonneg 3)
  have hUpperBoundaryIdentity :
      Real.sin ((31.25 : ℝ) * Real.pi / 180) =
        (1 : ℝ) / 2 * Real.cos upperDelta +
          √3 / 2 * Real.sin upperDelta := by
    have hAngle :
        (31.25 : ℝ) * Real.pi / 180 =
          Real.pi / 6 + upperDelta := by
      dsimp [upperDelta]
      ring
    rw [hAngle, Real.sin_add, Real.sin_pi_div_six,
      Real.cos_pi_div_six]
  have hUpperBoundaryLower :
      (0.5187 : ℝ) <
        Real.sin ((31.25 : ℝ) * Real.pi / 180) := by
    rw [hUpperBoundaryIdentity]
    nlinarith only [hCosUpperDeltaLower, hUpperProductLower]
  have hUpperBoundarySine :
      (100 : ℝ) / 133 * Real.sin (29 * Real.pi / 120) <
        Real.sin ((31.25 : ℝ) * Real.pi / 180) := by
    linarith only [hIncidentSineUpper, hUpperBoundaryLower]
  -- Monotonicity of sine on the physical acute branch traps the water angle.
  have hWaterPhysical := _physical.water_angle_physical
  rcases hWaterPhysical with ⟨hWaterNonneg, hWaterLe⟩
  have hLowerAngleLe :
      (31.15 : ℝ) * Real.pi / 180 ≤ Real.pi / 2 := by
    nlinarith only [Real.pi_pos]
  have hWaterLower :
      (31.15 : ℝ) * Real.pi / 180 ≤
        (waterRefractionAngle setup).toReal := by
    by_contra hNot
    have hWaterLt :
        (waterRefractionAngle setup).toReal <
          (31.15 : ℝ) * Real.pi / 180 :=
      lt_of_not_ge hNot
    have hSinLt :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (show -(Real.pi / 2) ≤
            (waterRefractionAngle setup).toReal by
          nlinarith only [hWaterNonneg, Real.pi_pos])
        hLowerAngleLe hWaterLt
    rw [hSinWater] at hSinLt
    linarith only [hSinLt, hLowerBoundarySine]
  have hWaterUpper :
      (waterRefractionAngle setup).toReal ≤
        (31.25 : ℝ) * Real.pi / 180 := by
    by_contra hNot
    have hUpperLt :
        (31.25 : ℝ) * Real.pi / 180 <
          (waterRefractionAngle setup).toReal :=
      lt_of_not_ge hNot
    have hSinLt :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (show -(Real.pi / 2) ≤
            (31.25 : ℝ) * Real.pi / 180 by
          nlinarith only [Real.pi_pos])
        hWaterLe hUpperLt
    rw [hSinWater] at hSinLt
    linarith only [hSinLt, hUpperBoundarySine]
  -- Convert the radian inequalities back to the displayed degree readout.
  have hDegreeLower :
      (31.15 : ℝ) ≤ degreeReadout (waterRefractionAngle setup) := by
    unfold degreeReadout
    calc
      (31.15 : ℝ) =
          ((31.15 : ℝ) * Real.pi / 180) *
            (180 / Real.pi) := by
              field_simp [ne_of_gt Real.pi_pos]
      _ ≤ (waterRefractionAngle setup).toReal *
            (180 / Real.pi) :=
        mul_le_mul_of_nonneg_right hWaterLower (by positivity)
      _ = (waterRefractionAngle setup).toReal * 180 / Real.pi := by
        ring
  have hDegreeUpper :
      degreeReadout (waterRefractionAngle setup) ≤ (31.25 : ℝ) := by
    unfold degreeReadout
    calc
      (waterRefractionAngle setup).toReal * 180 / Real.pi =
          (waterRefractionAngle setup).toReal *
            (180 / Real.pi) := by ring
      _ ≤ ((31.25 : ℝ) * Real.pi / 180) *
            (180 / Real.pi) :=
        mul_le_mul_of_nonneg_right hWaterUpper (by positivity)
      _ = (31.25 : ℝ) := by
        field_simp [ne_of_gt Real.pi_pos]
  -- The rounding interval proves the match and separates C from every rival.
  constructor
  · unfold MatchesAnswerToNearestTenth answerInDegrees
    rw [abs_le]
    constructor <;> norm_num <;>
      linarith only [hDegreeLower, hDegreeUpper]
  · intro other hOther
    have hChosenError :
        |degreeReadout (waterRefractionAngle setup) - 31.2| ≤
          (0.05 : ℝ) := by
      rw [abs_le]
      constructor <;> linarith only [hDegreeLower, hDegreeUpper]
    cases other with
    | A =>
        simp only [answerInDegrees]
        have hFar :=
          neg_le_abs
            (degreeReadout (waterRefractionAngle setup) - (41.2 : ℝ))
        linarith only [hChosenError, hFar, hDegreeUpper]
    | B =>
        simp only [answerInDegrees]
        have hFar :=
          le_abs_self
            (degreeReadout (waterRefractionAngle setup) - (21.2 : ℝ))
        linarith only [hChosenError, hFar, hDegreeLower]
    | C =>
        exact (hOther rfl).elim
    | D =>
        simp only [answerInDegrees]
        have hFar :=
          neg_le_abs
            (degreeReadout (waterRefractionAngle setup) - (36.2 : ℝ))
        linarith only [hChosenError, hFar, hDegreeUpper]

end PhyXMiniProblems.ProblemPhyXMini0143
