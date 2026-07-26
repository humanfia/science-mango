import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0072

open Dimension

/-!
# Minimum entry displacement for a laser to leave a water-filled box

In the top-view figure, side A is the vertical boundary of the water and side B
is the perpendicular horizontal boundary.  A laser in air is `10 cm` along the
normal from side A.  Its ray enters side A a distance `x` above the foot of that
normal, refracts into the water, and then reaches side B.

Lengths belonging to the apparatus use Physlib's dimensionful quantities.
Real numbers are used only for dimensionless refractive indices, radian angles,
and explicitly named centimeter readouts such as the displayed coordinate `x`.
-/

/-- A nonnegative physical length, represented independently of unit choice. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- The scalar readout of a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length { UnitChoices.SI with length := unit }).val : ℝ)

/-- The scalar centimeter readout of a physical length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- The two perpendicular container sides named in the figure. -/
inductive ContainerSide where
  | A
  | B
  deriving DecidableEq, Repr

/-- Top-view orientations of the two boundary segments. -/
inductive BoundaryOrientation where
  | vertical
  | horizontal
  deriving DecidableEq, Repr

/-- The homogeneous media crossed by the laser ray. -/
inductive OpticalMedium where
  | ambientAir
  | boxWater
  deriving DecidableEq, Repr

/--
The fixed apparatus and material data.  The critical angle is measured in
water from the normal to a water--air interface.
-/
structure RectangularWaterBoxSetup where
  sourceNormalDistanceFromSideA : LengthQuantity
  wallThickness : LengthQuantity
  refractiveIndex : OpticalMedium → ℝ
  criticalAngleWaterToAir : ℝ
  sideOrientation : ContainerSide → BoundaryOrientation
  interiorMedium : OpticalMedium
  exteriorMedium : OpticalMedium
  laserSourceMedium : OpticalMedium

/--
One candidate ray through the two named sides.  The entry displacement is the
centimeter readout labeled `x`; all angles are in radians and are measured from
the normal of the boundary at which they occur.
-/
structure LaserRayPath where
  entrySide : ContainerSide
  exitSide : ContainerSide
  entryDisplacementXInCentimeters : ℝ
  incidentAngleAtSideA : ℝ
  refractedAngleInWaterFromSideANormal : ℝ
  incidenceAngleAtSideB : ℝ

/-- Side labels, orientations, media, and the negligible-wall idealization. -/
def HasDepictedRectangularLayout (setup : RectangularWaterBoxSetup) : Prop :=
  setup.sideOrientation .A = .vertical ∧
    setup.sideOrientation .B = .horizontal ∧
    setup.interiorMedium = .boxWater ∧
    setup.exteriorMedium = .ambientAir ∧
    setup.laserSourceMedium = .ambientAir ∧
    lengthInCentimeters setup.wallThickness = 0

/-!
The given/calibrated numerical readouts: source distance `10 cm`, air index
`1.00`, and water index `1.33`.  No value for `x` occurs in this predicate.
-/
def MatchesProblemAndFigureReadouts
    (setup : RectangularWaterBoxSetup) : Prop :=
  lengthInCentimeters setup.sourceNormalDistanceFromSideA = 10 ∧
    setup.refractiveIndex .ambientAir = 1.00 ∧
    setup.refractiveIndex .boxWater = 1.33

/-- Positive optical data and the acute physical branch for the critical ray. -/
def HasPhysicalOpticalParameters
    (setup : RectangularWaterBoxSetup) : Prop :=
  (∀ medium, 0 < setup.refractiveIndex medium) ∧
    setup.refractiveIndex .ambientAir <
      setup.refractiveIndex .boxWater ∧
    0 < lengthInCentimeters setup.sourceNormalDistanceFromSideA ∧
    setup.criticalAngleWaterToAir ∈ Set.Ioo 0 (Real.pi / 2)

/-!
Snell's law for the limiting water--air ray.  At the critical angle the
transmitted air ray is tangent to side B, so its sine is one.
-/
def SatisfiesWaterAirCriticalAngleLaw
    (setup : RectangularWaterBoxSetup) : Prop :=
  setup.refractiveIndex .boxWater *
      Real.sin setup.criticalAngleWaterToAir =
    setup.refractiveIndex .ambientAir

/-- The ray enters through side A and reaches side B, as depicted. -/
def FollowsDepictedSideRoute (ray : LaserRayPath) : Prop :=
  ray.entrySide = .A ∧ ray.exitSide = .B

/-!
The displacement is nonnegative and all normal-relative ray angles lie on the
physical acute branch.  The strict upper bounds at side A exclude Lean's
totalized `tan (π / 2) = 0` endpoint from the geometric model.
-/
def HasPhysicalRayParameters (ray : LaserRayPath) : Prop :=
  0 ≤ ray.entryDisplacementXInCentimeters ∧
    ray.incidentAngleAtSideA ∈ Set.Ico 0 (Real.pi / 2) ∧
    ray.refractedAngleInWaterFromSideANormal ∈
      Set.Ico 0 (Real.pi / 2) ∧
    ray.incidenceAngleAtSideB ∈ Set.Icc 0 (Real.pi / 2)

/-!
Right-triangle geometry outside side A: `x = d tan θ_air`, where `d` is the
normal source distance and both lengths are read in centimeters.
-/
def SatisfiesSourceToEntryGeometry
    (setup : RectangularWaterBoxSetup) (ray : LaserRayPath) : Prop :=
  ray.entryDisplacementXInCentimeters =
    lengthInCentimeters setup.sourceNormalDistanceFromSideA *
      Real.tan ray.incidentAngleAtSideA

/-!
Because sides A and B are perpendicular, the water-ray angle from the side-A
normal complements its incidence angle from the side-B normal.
-/
def SatisfiesPerpendicularSideGeometry (ray : LaserRayPath) : Prop :=
  ray.refractedAngleInWaterFromSideANormal +
      ray.incidenceAngleAtSideB =
    Real.pi / 2

/-- Snell's law at side A for transmission from ambient air into water. -/
def SatisfiesSnellLawAtSideA
    (setup : RectangularWaterBoxSetup) (ray : LaserRayPath) : Prop :=
  setup.refractiveIndex .ambientAir *
      Real.sin ray.incidentAngleAtSideA =
    setup.refractiveIndex .boxWater *
      Real.sin ray.refractedAngleInWaterFromSideANormal

/-!
A water ray emerges through side B on the modeled branch exactly when its
incidence angle is no larger than the water--air critical angle.
-/
def EmergesIntoAirThroughSideB
    (setup : RectangularWaterBoxSetup) (ray : LaserRayPath) : Prop :=
  ray.incidenceAngleAtSideB ≤ setup.criticalAngleWaterToAir

/-!
A displacement is admissible when a physical ray with that displayed readout
follows the depicted route and satisfies the geometry, both refraction laws,
and the side-B escape criterion.  This predicate contains no answer choice and
does not assert that any particular displacement is minimal.
-/
def AdmissibleEntryDisplacementInCentimeters
    (setup : RectangularWaterBoxSetup) (xInCentimeters : ℝ) : Prop :=
  ∃ ray : LaserRayPath,
    ray.entryDisplacementXInCentimeters = xInCentimeters ∧
      FollowsDepictedSideRoute ray ∧
      HasPhysicalRayParameters ray ∧
      SatisfiesSourceToEntryGeometry setup ray ∧
      SatisfiesPerpendicularSideGeometry ray ∧
      SatisfiesSnellLawAtSideA setup ray ∧
      EmergesIntoAirThroughSideB setup ray

/-- The set of centimeter readouts for which the ray can escape at side B. -/
def admissibleEntryDisplacementsInCentimeters
    (setup : RectangularWaterBoxSetup) : Set ℝ :=
  {x | AdmissibleEntryDisplacementInCentimeters setup x}

/-!
The critical-ray candidate threshold.  At threshold the water-side angle from
the side-A normal is complementary to the side-B critical angle.  Snell's law
then gives `sin θ_air = (n_water / n_air) cos θc`, followed by
`x = d tan θ_air`.  Naming this candidate does not assert its minimality.
-/
def criticalThresholdEntryDisplacementInCentimeters
    (setup : RectangularWaterBoxSetup) : ℝ :=
  lengthInCentimeters setup.sourceNormalDistanceFromSideA *
    Real.tan
      (Real.arcsin
        (setup.refractiveIndex .boxWater /
          setup.refractiveIndex .ambientAir *
            Real.cos setup.criticalAngleWaterToAir))

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The centimeter readout printed beside each answer label. -/
def answerEntryDisplacementInCentimeters : AnswerChoice → ℝ
  | .A => 20
  | .B => 15.0
  | .C => 18.2
  | .D => 15.3

/-- Agreement with an answer displayed to the nearest tenth of a centimeter. -/
def MatchesEntryDisplacementChoice
    (xInCentimeters : ℝ) (choice : AnswerChoice) : Prop :=
  |xInCentimeters - answerEntryDisplacementInCentimeters choice| ≤ 0.05

/-!
The ray at the critical threshold is the least admissible entry displacement.
This is a derived conclusion from the side-A Snell law, perpendicular-side
geometry, side-B critical-angle law, and the acute physical branches.
-/
lemma criticalThreshold_isLeastAdmissible
    (setup : RectangularWaterBoxSetup)
    (h_layout : HasDepictedRectangularLayout setup)
    (h_readouts : MatchesProblemAndFigureReadouts setup)
    (h_physical : HasPhysicalOpticalParameters setup)
    (h_critical : SatisfiesWaterAirCriticalAngleLaw setup) :
    IsLeast (admissibleEntryDisplacementsInCentimeters setup)
      (criticalThresholdEntryDisplacementInCentimeters setup) := by
  rcases h_readouts with ⟨hdistance, hair, hwater⟩
  norm_num at hair hwater
  rcases h_physical with
    ⟨hindex_pos, _, hdistance_pos, hcritical_pos, hcritical_lt⟩
  change setup.refractiveIndex .boxWater *
      Real.sin setup.criticalAngleWaterToAir =
    setup.refractiveIndex .ambientAir at h_critical
  let c : ℝ := setup.criticalAngleWaterToAir
  let z : ℝ :=
    setup.refractiveIndex .boxWater /
      setup.refractiveIndex .ambientAir * Real.cos c
  let θ : ℝ := Real.arcsin z
  let r : ℝ := Real.pi / 2 - c
  have hc_pos : 0 < c := by
    exact hcritical_pos
  have hc_lt : c < Real.pi / 2 := by
    exact hcritical_lt
  have hc_cos_pos : 0 < Real.cos c :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hc_lt⟩
  have hcritical_sin : (133 / 100 : ℝ) * Real.sin c = 1 := by
    dsimp [c]
    rw [← hwater, ← hair]
    exact h_critical
  have hz_pos : 0 < z := by
    dsimp [z]
    rw [hair, hwater]
    norm_num only [div_one]
    positivity
  have hz_sq : z ^ 2 = (7689 / 10000 : ℝ) := by
    dsimp [z]
    rw [hair, hwater]
    norm_num only [div_one]
    nlinarith [Real.sin_sq_add_cos_sq c]
  have hz_lt : z < 1 := by
    apply (sq_lt_sq₀ hz_pos.le (by norm_num)).mp
    rw [hz_sq]
    norm_num
  have hθ_pos : 0 < θ := Real.arcsin_pos.2 hz_pos
  have hθ_lt : θ < Real.pi / 2 :=
    Real.arcsin_lt_pi_div_two.2 hz_lt
  have hθ_sin : Real.sin θ = z := by
    dsimp [θ]
    exact Real.sin_arcsin (by linarith) hz_lt.le
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    linarith
  have hr_lt : r < Real.pi / 2 := by
    dsimp [r]
    linarith
  have hthreshold_snell :
      setup.refractiveIndex .ambientAir * Real.sin θ =
        setup.refractiveIndex .boxWater * Real.sin r := by
    rw [hθ_sin]
    dsimp [z, r]
    rw [Real.sin_pi_div_two_sub]
    field_simp [ne_of_gt (hindex_pos .ambientAir)]
  have hthreshold_nonneg :
      0 ≤ criticalThresholdEntryDisplacementInCentimeters setup := by
    change 0 ≤
      lengthInCentimeters setup.sourceNormalDistanceFromSideA *
        Real.tan θ
    exact mul_nonneg hdistance_pos.le
      (Real.tan_nonneg_of_nonneg_of_le_pi_div_two hθ_pos.le hθ_lt.le)
  constructor
  · change AdmissibleEntryDisplacementInCentimeters setup
      (criticalThresholdEntryDisplacementInCentimeters setup)
    let criticalRay : LaserRayPath :=
      { entrySide := .A
        exitSide := .B
        entryDisplacementXInCentimeters :=
          criticalThresholdEntryDisplacementInCentimeters setup
        incidentAngleAtSideA := θ
        refractedAngleInWaterFromSideANormal := r
        incidenceAngleAtSideB := c }
    refine ⟨criticalRay, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [FollowsDepictedSideRoute, criticalRay]
    · exact ⟨hthreshold_nonneg, ⟨hθ_pos.le, hθ_lt⟩,
        ⟨hr_nonneg, hr_lt⟩, ⟨hc_pos.le, hc_lt.le⟩⟩
    · rfl
    · dsimp [SatisfiesPerpendicularSideGeometry, criticalRay, r]
      ring
    · exact hthreshold_snell
    · exact le_rfl
  · intro x hx
    change AdmissibleEntryDisplacementInCentimeters setup x at hx
    rcases hx with
      ⟨ray, hentry, _, hray_physical, hsource_geometry,
        hperpendicular_geometry, hsnell, hemerges⟩
    rcases hray_physical with
      ⟨_, hincident_mem, hrefracted_mem, hsideB_mem⟩
    change ray.refractedAngleInWaterFromSideANormal +
        ray.incidenceAngleAtSideB = Real.pi / 2 at hperpendicular_geometry
    change setup.refractiveIndex .ambientAir *
        Real.sin ray.incidentAngleAtSideA =
      setup.refractiveIndex .boxWater *
        Real.sin ray.refractedAngleInWaterFromSideANormal at hsnell
    change ray.incidenceAngleAtSideB ≤ c at hemerges
    have hrefracted_ge : r ≤
        ray.refractedAngleInWaterFromSideANormal := by
      dsimp [r]
      linarith
    have hsin_refracted :
        Real.sin r ≤
          Real.sin ray.refractedAngleInWaterFromSideANormal := by
      exact Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [Real.pi_pos]) hrefracted_mem.2.le hrefracted_ge
    have hsin_incident :
        Real.sin θ ≤ Real.sin ray.incidentAngleAtSideA := by
      rw [hair, hwater] at hthreshold_snell hsnell
      nlinarith
    have hincident_ge : θ ≤ ray.incidentAngleAtSideA := by
      exact (Real.strictMonoOn_sin.le_iff_le
        ⟨by linarith [Real.pi_pos], hθ_lt.le⟩
        ⟨by linarith [Real.pi_pos, hincident_mem.1],
          hincident_mem.2.le⟩).mp
          hsin_incident
    have htan_incident :
        Real.tan θ ≤ Real.tan ray.incidentAngleAtSideA := by
      exact Real.strictMonoOn_tan.monotoneOn
        ⟨by linarith [Real.pi_pos], hθ_lt⟩
        ⟨by linarith [Real.pi_pos, hincident_mem.1], hincident_mem.2⟩
        hincident_ge
    calc
      criticalThresholdEntryDisplacementInCentimeters setup =
          lengthInCentimeters setup.sourceNormalDistanceFromSideA *
            Real.tan θ := rfl
      _ ≤ lengthInCentimeters setup.sourceNormalDistanceFromSideA *
            Real.tan ray.incidentAngleAtSideA :=
        mul_le_mul_of_nonneg_left htan_incident hdistance_pos.le
      _ = ray.entryDisplacementXInCentimeters :=
        hsource_geometry.symm
      _ = x := hentry

/-!
For the `10 cm`, `n_air = 1.00`, and `n_water = 1.33` readouts, the critical
threshold is within `0.05 cm` of `18.2 cm`.
-/
lemma criticalThreshold_matches_choice_C
    (setup : RectangularWaterBoxSetup)
    (h_readouts : MatchesProblemAndFigureReadouts setup)
    (h_physical : HasPhysicalOpticalParameters setup)
    (h_critical : SatisfiesWaterAirCriticalAngleLaw setup) :
    MatchesEntryDisplacementChoice
      (criticalThresholdEntryDisplacementInCentimeters setup) .C := by
  rcases h_readouts with ⟨hdistance, hair, hwater⟩
  norm_num at hair hwater
  rcases h_physical with
    ⟨_, _, _, hcritical_pos, hcritical_lt⟩
  change setup.refractiveIndex .boxWater *
      Real.sin setup.criticalAngleWaterToAir =
    setup.refractiveIndex .ambientAir at h_critical
  have hcritical_cos_pos :
      0 < Real.cos setup.criticalAngleWaterToAir := by
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
      hcritical_lt⟩
  let z : ℝ :=
    (133 / 100 : ℝ) * Real.cos setup.criticalAngleWaterToAir
  have hcritical_sin :
      (133 / 100 : ℝ) *
          Real.sin setup.criticalAngleWaterToAir = 1 := by
    rw [← hwater, ← hair]
    exact h_critical
  have hz_pos : 0 < z := by
    dsimp [z]
    positivity
  have hz_sq : z ^ 2 = (7689 / 10000 : ℝ) := by
    dsimp [z]
    nlinarith [Real.sin_sq_add_cos_sq
      setup.criticalAngleWaterToAir]
  have hradicand_pos : 0 < 1 - z ^ 2 := by
    rw [hz_sq]
    norm_num
  have hsqrt_pos : 0 < Real.sqrt (1 - z ^ 2) :=
    Real.sqrt_pos.2 hradicand_pos
  have hsqrt_sq :
      Real.sqrt (1 - z ^ 2) ^ 2 = (2311 / 10000 : ℝ) := by
    rw [Real.sq_sqrt hradicand_pos.le, hz_sq]
    norm_num
  have hlower_mul :
      (363 / 200 : ℝ) * Real.sqrt (1 - z ^ 2) ≤ z := by
    apply (sq_le_sq₀ (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      hz_pos.le).mp
    rw [mul_pow, hsqrt_sq, hz_sq]
    norm_num
  have hupper_mul :
      z ≤ (365 / 200 : ℝ) * Real.sqrt (1 - z ^ 2) := by
    nlinarith [sq_nonneg
      (z - (365 / 200 : ℝ) * Real.sqrt (1 - z ^ 2))]
  change
    |lengthInCentimeters setup.sourceNormalDistanceFromSideA *
          Real.tan
            (Real.arcsin
              (setup.refractiveIndex .boxWater /
                setup.refractiveIndex .ambientAir *
                  Real.cos setup.criticalAngleWaterToAir)) -
        18.2| ≤ 0.05
  rw [hdistance, hair, hwater]
  norm_num only [div_one]
  change
    |10 * Real.tan (Real.arcsin z) - (91 / 5 : ℝ)| ≤
      (1 / 20 : ℝ)
  rw [Real.tan_arcsin, abs_le]
  constructor
  · have hquotient :
        (363 / 200 : ℝ) ≤ z / Real.sqrt (1 - z ^ 2) :=
      (le_div_iff₀ hsqrt_pos).2 hlower_mul
    nlinarith
  · have hquotient :
        z / Real.sqrt (1 - z ^ 2) ≤ (365 / 200 : ℝ) :=
      (div_le_iff₀ hsqrt_pos).2 hupper_mul
    nlinarith

/-!
The least displacement for which the beam enters through side A, reaches the
perpendicular side B, and emerges into air rounds to answer choice C,
`18.2 cm`.

This formalizes `thm:physics:phyx_mini_0072:target`.
-/
theorem problem_phyx_mini_0072
    (setup : RectangularWaterBoxSetup)
    (h_layout : HasDepictedRectangularLayout setup)
    (h_readouts : MatchesProblemAndFigureReadouts setup)
    (h_physical : HasPhysicalOpticalParameters setup)
    (h_critical : SatisfiesWaterAirCriticalAngleLaw setup) :
    IsLeast (admissibleEntryDisplacementsInCentimeters setup)
        (criticalThresholdEntryDisplacementInCentimeters setup) ∧
      MatchesEntryDisplacementChoice
        (criticalThresholdEntryDisplacementInCentimeters setup) .C := by
  exact ⟨criticalThreshold_isLeastAdmissible setup h_layout h_readouts
    h_physical h_critical,
    criticalThreshold_matches_choice_C setup h_readouts h_physical h_critical⟩

end PhyXMiniProblems.ProblemPhyXMini0072
