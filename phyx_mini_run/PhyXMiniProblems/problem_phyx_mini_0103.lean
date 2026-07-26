import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Physlib.Optics.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0103

/-!
# Completely polarized wall reflection entering water

Unpolarized sunlight in air strikes the vertical plastic wall, reflects back
through the air, and then crosses the horizontal water surface.  Refractive
indices are dimensionless.  Every scalar angle is a radian readout measured
from the normal to the interface where that interaction occurs.
-/

/-- The three homogeneous optical media involved in the ray path. -/
inductive OpticalMedium where
  | plasticWall
  | air
  | water
  deriving DecidableEq, Repr

/-- The two planar interfaces labelled in the tank cross-section. -/
inductive TankInterface where
  | verticalPlasticWall
  | horizontalWaterSurface
  deriving DecidableEq, Repr

/-- The three directed portions of the depicted sunlight path. -/
inductive RaySegment where
  | incidentSunlightInAir
  | reflectedFromWallInAir
  | refractedIntoWater
  deriving DecidableEq, Repr

/-- Qualitative polarization state of an optical beam. -/
inductive PolarizationState where
  | unpolarized
  | partiallyPolarized
  | completelyPolarized
  deriving DecidableEq, Repr

/-- The two-dimensional plane of the tank ray diagram. -/
abbrev DiagramPlane := EuclideanSpace ℝ (Fin 2)

/--
Physical quantities and labelled geometry in the wall--air--water diagram.

`normalTowardAir` points into the air at both interfaces.  Thus an incoming
propagation vector is negated when its angle is read against that normal, while
the water-side refracted vector is compared with the opposite normal.  The
requested quantity is `waterRefractionAngleRadians`; no numerical value for it
is stored in this structure.
-/
structure TankWallReflectionSetup where
  /-- Schematic point at which each planar interface is met by the ray. -/
  interfacePoint : TankInterface → DiagramPlane
  /-- Unit normal pointing from the relevant material region into the air. -/
  normalTowardAir : TankInterface → DiagramPlane
  /-- Propagation direction of each labelled ray segment. -/
  rayDirection : RaySegment → DiagramPlane
  /-- Positive schematic parameter along the wall-reflected segment. -/
  wallToWaterPathParameter : ℝ
  /-- Dimensionless refractive index of each homogeneous optical medium. -/
  refractiveIndex : OpticalMedium → WithDim (1 : Dimension) ℝ
  /-- Incidence angle at the plastic wall, measured from its horizontal normal. -/
  wallIncidenceAngleRadians : ℝ
  /-- Reflection angle at the plastic wall, measured from the same normal. -/
  wallReflectionAngleRadians : ℝ
  /-- Incidence angle at the water surface, measured from its vertical normal. -/
  waterIncidenceAngleRadians : ℝ
  /-- Angle inside the water, measured from the water-side surface normal. -/
  waterRefractionAngleRadians : ℝ
  /-- Polarization state before the sunlight reaches the wall. -/
  incidentPolarization : PolarizationState
  /-- Polarization state after reflection from the plastic wall. -/
  wallReflectedPolarization : PolarizationState
  /-- The incident beam is sunlight, as specified in the problem. -/
  incidentBeamIsSunlight : Prop
  /-- The wall-reflected segment is the segment that subsequently enters the water. -/
  wallReflectedBeamEntersWater : Prop

/--
The four scalar angle fields are the geometric normal-angle readouts of their
corresponding direction vectors.
-/
def HasTankNormalAngleReadouts (setup : TankWallReflectionSetup) : Prop :=
  setup.wallIncidenceAngleRadians =
      InnerProductGeometry.angle
        (-setup.rayDirection .incidentSunlightInAir)
        (setup.normalTowardAir .verticalPlasticWall) ∧
    setup.wallReflectionAngleRadians =
      InnerProductGeometry.angle
        (setup.rayDirection .reflectedFromWallInAir)
        (setup.normalTowardAir .verticalPlasticWall) ∧
    setup.waterIncidenceAngleRadians =
      InnerProductGeometry.angle
        (-setup.rayDirection .reflectedFromWallInAir)
        (setup.normalTowardAir .horizontalWaterSurface) ∧
    setup.waterRefractionAngleRadians =
      InnerProductGeometry.angle
        (setup.rayDirection .refractedIntoWater)
        (-setup.normalTowardAir .horizontalWaterSurface)

/-- Snell's law at the horizontal air--water boundary. -/
def SatisfiesSnellLawAtWaterSurface
    (setup : TankWallReflectionSetup) : Prop :=
  (setup.refractiveIndex .air).val * Real.sin setup.waterIncidenceAngleRadians =
    (setup.refractiveIndex .water).val * Real.sin setup.waterRefractionAngleRadians

/--
Brewster's polarization criterion for unpolarized light incident from air on
the plastic wall: complete polarization of the reflected beam is equivalent
to `n_air tan θ_B = n_plastic` on the physical acute-angle branch.
-/
def SatisfiesBrewsterPolarizationLaw
    (setup : TankWallReflectionSetup) : Prop :=
  setup.incidentPolarization = .unpolarized →
    (setup.wallReflectedPolarization = .completelyPolarized ↔
      (setup.refractiveIndex .air).val * Real.tan setup.wallIncidenceAngleRadians =
        (setup.refractiveIndex .plasticWall).val)

/--
Problem and standard-medium readouts.  The stated plastic index is `1.61`;
ordinary air and water are represented by the standard dimensionless values
`1.00` and `1.33`.  The complete polarization observation is data, not the
requested numerical water angle.
-/
structure MatchesTankWallProblemData (setup : TankWallReflectionSetup) : Prop where
  sunlight : setup.incidentBeamIsSunlight
  incidentUnpolarized : setup.incidentPolarization = .unpolarized
  reflectedCompletelyPolarized :
    setup.wallReflectedPolarization = .completelyPolarized
  reflectedBeamEntersWater : setup.wallReflectedBeamEntersWater
  plasticIndexReadout :
    (setup.refractiveIndex .plasticWall).val = (161 : ℝ) / 100
  airIndexReadout :
    (setup.refractiveIndex .air).val = 1
  waterIndexReadout :
    (setup.refractiveIndex .water).val = (133 : ℝ) / 100
  unitInterfaceNormals :
    ∀ interface : TankInterface, ‖setup.normalTowardAir interface‖ = 1
  unitRayDirections :
    ∀ segment : RaySegment, ‖setup.rayDirection segment‖ = 1

/--
Relations read from the cross-sectional figure.  The vertical wall and
horizontal water surface have perpendicular normals.  The reflected ray runs
from the wall interaction point to the water interaction point, and its
normal-angle readouts at the perpendicular interfaces are complementary.
-/
structure SatisfiesTankFigureGeometry (setup : TankWallReflectionSetup) : Prop where
  normalAngleReadouts : HasTankNormalAngleReadouts setup
  perpendicularInterfaceNormals :
    InnerProductGeometry.angle
        (setup.normalTowardAir .verticalPlasticWall)
        (setup.normalTowardAir .horizontalWaterSurface) =
      Real.pi / 2
  wallToWaterPathParameterPositive : 0 < setup.wallToWaterPathParameter
  reflectedSegmentConnectsInterfaces :
    setup.interfacePoint .horizontalWaterSurface -
        setup.interfacePoint .verticalPlasticWall =
      setup.wallToWaterPathParameter •
        setup.rayDirection .reflectedFromWallInAir
  reflectedAndWaterIncidenceAnglesComplementary :
    setup.wallReflectionAngleRadians + setup.waterIncidenceAngleRadians =
      Real.pi / 2

/--
Governing physical laws and principal-branch conditions.  None of these fields
mentions a numerical value for the angle inside the water or an answer choice.
-/
structure SatisfiesTankOpticsLaws (setup : TankWallReflectionSetup) : Prop where
  refractiveIndicesPositive :
    ∀ medium : OpticalMedium, 0 < (setup.refractiveIndex medium).val
  wallIncidenceAngleAcute :
    setup.wallIncidenceAngleRadians ∈ Set.Ioo 0 (Real.pi / 2)
  wallReflectionAngleAcute :
    setup.wallReflectionAngleRadians ∈ Set.Ioo 0 (Real.pi / 2)
  waterIncidenceAngleAcute :
    setup.waterIncidenceAngleRadians ∈ Set.Ioo 0 (Real.pi / 2)
  waterRefractionAngleAcute :
    setup.waterRefractionAngleRadians ∈ Set.Ioo 0 (Real.pi / 2)
  lawOfReflection :
    setup.wallReflectionAngleRadians = setup.wallIncidenceAngleRadians
  brewsterPolarization : SatisfiesBrewsterPolarizationLaw setup
  snellAtWaterSurface : SatisfiesSnellLawAtWaterSurface setup

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Degree value printed beside each answer choice. -/
def answerAngleDegrees : AnswerChoice → ℝ
  | .A => (233 : ℝ) / 10
  | .B => (253 : ℝ) / 10
  | .C => (242 : ℝ) / 10
  | .D => (226 : ℝ) / 10

/-- Convert a real-valued degree readout to the radian scalar used by Mathlib. -/
def degreesToRadians (angleDegrees : ℝ) : ℝ :=
  angleDegrees * Real.pi / 180

/-- A printed choice is uniquely closest to the physical radian-angle readout. -/
def IsClosestAnswerChoice
    (angleRadians : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |angleRadians - degreesToRadians (answerAngleDegrees choice)| <
      |angleRadians - degreesToRadians (answerAngleDegrees other)|

/--
The perpendicular wall/water geometry and Snell's law relate the requested
water angle to the wall reflection angle.  This physical relation does not
assume or state a numerical answer choice.
-/
lemma reflected_wall_ray_air_water_relation
    (setup : TankWallReflectionSetup)
    (_geometry : SatisfiesTankFigureGeometry setup)
    (_laws : SatisfiesTankOpticsLaws setup) :
    (setup.refractiveIndex .air).val * Real.cos setup.wallReflectionAngleRadians =
      (setup.refractiveIndex .water).val *
        Real.sin setup.waterRefractionAngleRadians := by
  have hcomplement :
      setup.waterIncidenceAngleRadians =
        Real.pi / 2 - setup.wallReflectionAngleRadians := by
    linarith [_geometry.reflectedAndWaterIncidenceAnglesComplementary]
  calc
    (setup.refractiveIndex .air).val *
          Real.cos setup.wallReflectionAngleRadians =
        (setup.refractiveIndex .air).val *
          Real.sin setup.waterIncidenceAngleRadians := by
            rw [hcomplement, Real.sin_pi_div_two_sub]
    _ = (setup.refractiveIndex .water).val *
          Real.sin setup.waterRefractionAngleRadians :=
      _laws.snellAtWaterSurface

/--
For unpolarized sunlight reflecting from plastic of refractive index `1.61`,
Brewster's criterion fixes the wall angle.  The perpendicular interface
geometry and Snell's law then make the angle from the normal inside ordinary
water closest to `23.3°`, answer A.

Blueprint: `thm:physics:phyx_mini_0103:target`.
-/
theorem completelyPolarizedWallReflection_waterAngle_is_answer_A
    (setup : TankWallReflectionSetup)
    (_problemData : MatchesTankWallProblemData setup)
    (_geometry : SatisfiesTankFigureGeometry setup)
    (_laws : SatisfiesTankOpticsLaws setup) :
    IsClosestAnswerChoice setup.waterRefractionAngleRadians .A := by
  have hbrewster :
      (setup.refractiveIndex .air).val *
          Real.tan setup.wallIncidenceAngleRadians =
        (setup.refractiveIndex .plasticWall).val :=
    (_laws.brewsterPolarization _problemData.incidentUnpolarized).mp
      _problemData.reflectedCompletelyPolarized
  rw [_problemData.airIndexReadout, _problemData.plasticIndexReadout,
    one_mul] at hbrewster
  have htan :
      Real.tan setup.wallReflectionAngleRadians = (161 : ℝ) / 100 := by
    rw [_laws.lawOfReflection]
    exact hbrewster
  have hcos_pos : 0 < Real.cos setup.wallReflectionAngleRadians := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [_laws.wallReflectionAngleAcute.1, Real.pi_pos]
    · exact _laws.wallReflectionAngleAcute.2
  have htan' := htan
  rw [Real.tan_eq_sin_div_cos] at htan'
  have hsin_cos :
      Real.sin setup.wallReflectionAngleRadians =
        ((161 : ℝ) / 100) * Real.cos setup.wallReflectionAngleRadians :=
    (div_eq_iff hcos_pos.ne').mp htan'
  have htrig := Real.sin_sq_add_cos_sq setup.wallReflectionAngleRadians
  rw [hsin_cos] at htrig
  have hcos_sq :
      Real.cos setup.wallReflectionAngleRadians ^ 2 =
        (10000 : ℝ) / 35921 := by
    nlinarith only [htrig]
  have hrel :=
    reflected_wall_ray_air_water_relation setup _geometry _laws
  rw [_problemData.airIndexReadout, _problemData.waterIndexReadout,
    one_mul] at hrel
  have hrel_sq := congrArg (fun x : ℝ => x ^ 2) hrel
  rw [hcos_sq] at hrel_sq
  have hwater_sin_sq :
      Real.sin setup.waterRefractionAngleRadians ^ 2 =
        (100000000 : ℝ) / (17689 * 35921) := by
    nlinarith only [hrel_sq]
  have hwater_sin_pos :
      0 < Real.sin setup.waterRefractionAngleRadians := by
    exact Real.sin_pos_of_pos_of_lt_pi
      _laws.waterRefractionAngleAcute.1
      (_laws.waterRefractionAngleAcute.2.trans (by
        linarith [Real.pi_pos]))
  have hwater_sin_lower :
      (793 : ℝ) / 2000 <
        Real.sin setup.waterRefractionAngleRadians := by
    nlinarith only [hwater_sin_sq, hwater_sin_pos]
  have hwater_sin_upper :
      Real.sin setup.waterRefractionAngleRadians <
        (397 : ℝ) / 1000 := by
    nlinarith only [hwater_sin_sq, hwater_sin_pos]
  have hsin_lower :
      Real.sin ((203 : ℝ) / 500) < (793 : ℝ) / 2000 := by
    have hb := Real.sin_bound (x := (203 : ℝ) / 500)
      (by norm_num [abs_of_nonneg])
    rcases abs_le.mp hb with ⟨hb₁, hb₂⟩
    norm_num [abs_of_nonneg] at hb₁ hb₂ ⊢
    linarith
  have hsin_upper :
      (397 : ℝ) / 1000 < Real.sin ((41 : ℝ) / 100) := by
    have hb := Real.sin_bound (x := (41 : ℝ) / 100)
      (by norm_num [abs_of_nonneg])
    rcases abs_le.mp hb with ⟨hb₁, hb₂⟩
    norm_num [abs_of_nonneg] at hb₁ hb₂ ⊢
    linarith
  have hwater_angle_pos : 0 < setup.waterRefractionAngleRadians :=
    _laws.waterRefractionAngleAcute.1
  have hwater_angle_upper :
      setup.waterRefractionAngleRadians < Real.pi / 2 :=
    _laws.waterRefractionAngleAcute.2
  have hwater_angle_mem :
      setup.waterRefractionAngleRadians ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hlower_mem :
      (203 : ℝ) / 500 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.two_le_pi]
  have hupper_mem :
      (41 : ℝ) / 100 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.two_le_pi]
  have hwater_angle_lower :
      (203 : ℝ) / 500 < setup.waterRefractionAngleRadians :=
    (Real.strictMonoOn_sin.lt_iff_lt hlower_mem hwater_angle_mem).mp
      (hsin_lower.trans hwater_sin_lower)
  have hwater_angle_lt :
      setup.waterRefractionAngleRadians < (41 : ℝ) / 100 :=
    (Real.strictMonoOn_sin.lt_iff_lt hwater_angle_mem hupper_mem).mp
      (hwater_sin_upper.trans hsin_upper)
  have hpi_argument : |Real.pi / 6| ≤ (1 : ℝ) := by
    rw [abs_of_pos (div_pos Real.pi_pos (by norm_num))]
    nlinarith [Real.pi_le_four]
  have hpi_sine_bound := Real.sin_bound hpi_argument
  rw [Real.sin_pi_div_six,
    abs_of_pos (div_pos Real.pi_pos (by norm_num))] at hpi_sine_bound
  rcases abs_le.mp hpi_sine_bound with
    ⟨hpi_sine_bound_lower, hpi_sine_bound_upper⟩
  have hpi_three : (3 : ℝ) < Real.pi := by
    by_contra h
    have hp_le : Real.pi ≤ (3 : ℝ) := le_of_not_gt h
    have hp3_lower : (2 : ℝ) ^ 3 ≤ Real.pi ^ 3 := by
      gcongr
      exact Real.two_le_pi
    have hp4_upper : Real.pi ^ 4 ≤ (3 : ℝ) ^ 4 := by
      gcongr
    nlinarith only [hpi_sine_bound_upper, hp_le, hp3_lower, hp4_upper]
  have hpi_31 : (31 : ℝ) / 10 < Real.pi := by
    by_contra h
    have hp_le : Real.pi ≤ (31 : ℝ) / 10 := le_of_not_gt h
    have hp3_lower : (3 : ℝ) ^ 3 ≤ Real.pi ^ 3 := by
      gcongr
    have hp4_upper : Real.pi ^ 4 ≤ ((31 : ℝ) / 10) ^ 4 := by
      gcongr
    nlinarith only [hpi_sine_bound_upper, hp_le, hp3_lower, hp4_upper]
  have hpi_lower : (311 : ℝ) / 100 < Real.pi := by
    by_contra h
    have hp_le : Real.pi ≤ (311 : ℝ) / 100 := le_of_not_gt h
    have hp3_lower : ((31 : ℝ) / 10) ^ 3 ≤ Real.pi ^ 3 := by
      gcongr
    have hp4_upper : Real.pi ^ 4 ≤ ((311 : ℝ) / 100) ^ 4 := by
      gcongr
    nlinarith only [hpi_sine_bound_upper, hp_le, hp3_lower, hp4_upper]
  have hpi_35 : Real.pi < (7 : ℝ) / 2 := by
    by_contra h
    have hp_lower : (7 : ℝ) / 2 ≤ Real.pi := le_of_not_gt h
    have hp3_upper : Real.pi ^ 3 ≤ (4 : ℝ) ^ 3 :=
      pow_le_pow_left₀ Real.pi_pos.le Real.pi_le_four 3
    have hp4_upper : Real.pi ^ 4 ≤ (4 : ℝ) ^ 4 :=
      pow_le_pow_left₀ Real.pi_pos.le Real.pi_le_four 4
    nlinarith only [hpi_sine_bound_lower, hp_lower, hp3_upper, hp4_upper]
  have hpi_33 : Real.pi < (33 : ℝ) / 10 := by
    by_contra h
    have hp_lower : (33 : ℝ) / 10 ≤ Real.pi := le_of_not_gt h
    have hp3_upper : Real.pi ^ 3 ≤ ((7 : ℝ) / 2) ^ 3 :=
      pow_le_pow_left₀ Real.pi_pos.le hpi_35.le 3
    have hp4_upper : Real.pi ^ 4 ≤ ((7 : ℝ) / 2) ^ 4 :=
      pow_le_pow_left₀ Real.pi_pos.le hpi_35.le 4
    nlinarith only [hpi_sine_bound_lower, hp_lower, hp3_upper, hp4_upper]
  have hpi_32 : Real.pi < (16 : ℝ) / 5 := by
    by_contra h
    have hp_lower : (16 : ℝ) / 5 ≤ Real.pi := le_of_not_gt h
    have hp3_upper : Real.pi ^ 3 ≤ ((33 : ℝ) / 10) ^ 3 :=
      pow_le_pow_left₀ Real.pi_pos.le hpi_33.le 3
    have hp4_upper : Real.pi ^ 4 ≤ ((33 : ℝ) / 10) ^ 4 :=
      pow_le_pow_left₀ Real.pi_pos.le hpi_33.le 4
    nlinarith only [hpi_sine_bound_lower, hp_lower, hp3_upper, hp4_upper]
  have hpi_upper : Real.pi < (159 : ℝ) / 50 := by
    by_contra h
    have hp_lower : (159 : ℝ) / 50 ≤ Real.pi := le_of_not_gt h
    have hp3_upper : Real.pi ^ 3 ≤ ((16 : ℝ) / 5) ^ 3 :=
      pow_le_pow_left₀ Real.pi_pos.le hpi_32.le 3
    have hp4_upper : Real.pi ^ 4 ≤ ((16 : ℝ) / 5) ^ 4 :=
      pow_le_pow_left₀ Real.pi_pos.le hpi_32.le 4
    nlinarith only [hpi_sine_bound_lower, hp_lower, hp3_upper, hp4_upper]
  have hlower_midpoint :
      (51 : ℝ) * Real.pi / 400 <
        setup.waterRefractionAngleRadians := by
    nlinarith only [hwater_angle_lower, hpi_upper]
  have hupper_midpoint :
      setup.waterRefractionAngleRadians <
        (19 : ℝ) * Real.pi / 144 := by
    nlinarith only [hwater_angle_lt, hpi_lower]
  unfold IsClosestAnswerChoice
  intro other hother
  cases other with
  | A => exact (hother rfl).elim
  | B =>
      simp only [answerAngleDegrees, degreesToRadians]
      apply (sq_lt_sq).mp
      nlinarith only [hupper_midpoint, Real.pi_pos]
  | C =>
      simp only [answerAngleDegrees, degreesToRadians]
      apply (sq_lt_sq).mp
      nlinarith only [hupper_midpoint, Real.pi_pos]
  | D =>
      simp only [answerAngleDegrees, degreesToRadians]
      apply (sq_lt_sq).mp
      nlinarith only [hlower_midpoint, Real.pi_pos]

end PhyXMiniProblems.ProblemPhyXMini0103
