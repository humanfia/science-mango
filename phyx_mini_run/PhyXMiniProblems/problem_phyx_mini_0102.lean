import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.LinearAlgebra.Ray
import Physlib.Units.WithDim.Basic

/-!
# Lateral displacement through a parallel glass plate

This file formalizes `phyx_mini_0102`. A light ray crosses a plane-parallel
glass plate surrounded by air. Lengths are dimensionful Physlib quantities,
refractive indices are dimensionless real readouts, and optical angles are
real radian readouts measured from the propagation-oriented surface normals.

The source figure's points `P` and `Q` are retained: `P` is the ray's exit
point on the lower face and `Q` lies on the unrefracted continuation of the
incident ray, with `PQ` perpendicular to that continuation. Thus `PQ` reads
the lateral displacement `d` shown in the figure.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0102

open CarriesDimension Dimension

/-! ## Units and labelled geometry -/

/-- A physical length, independent of the unit system used to read it. -/
abbrev DimLength := Dimensionful (WithDim L𝓭 ℝ)

/-- Unit choices in which physical lengths are read in centimeters. -/
def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The real-valued centimeter readout of a dimensionful length. -/
def valueInCentimeters (length : DimLength) : ℝ :=
  (length centimeterUnitChoices).val

/-- Convert a degree readout to the radian scalar used by `Real.sin`. -/
def degreesToRadians (angleDegrees : ℝ) : ℝ :=
  angleDegrees * Real.pi / 180

/-- The two-dimensional plane of the ray diagram, with centimeter coordinates. -/
abbrev DiagramPlane := EuclideanSpace ℝ (Fin 2)

/-- A propagation direction is represented by a nonzero diagram vector. -/
abbrev RayDirection := RayVector ℝ DiagramPlane

/-- The three homogeneous optical regions traversed by the ray. -/
inductive OpticalRegion where
  | incidentAir
  | glassPlate
  | emergentAir
  deriving DecidableEq, Repr

/-- The plane and parallel upper and lower faces of the plate. -/
inductive PlateFace where
  | entryFace
  | exitFace
  deriving DecidableEq, Repr

/-- The three directed portions of the light path. -/
inductive RaySegment where
  | incoming
  | insideGlass
  | outgoing
  deriving DecidableEq, Repr

/-- Point labels retained from the primary figure. -/
inductive FigurePoint where
  /-- The unlabeled point where the ray meets the upper plate face. -/
  | entry
  /-- Figure point `P`, where the actual ray leaves the lower plate face. -/
  | P
  /-- Figure point `Q`, on the unrefracted continuation of the incoming ray. -/
  | Q
  deriving DecidableEq, Repr

/-- Incident optical region at each face, in propagation order. -/
def incidentRegion : PlateFace → OpticalRegion
  | .entryFace => .incidentAir
  | .exitFace => .glassPlate

/-- Transmitted optical region at each face, in propagation order. -/
def transmittedRegion : PlateFace → OpticalRegion
  | .entryFace => .glassPlate
  | .exitFace => .emergentAir

/-- Ray segment incident on each plate face. -/
def incidentSegment : PlateFace → RaySegment
  | .entryFace => .incoming
  | .exitFace => .insideGlass

/-- Ray segment transmitted through each plate face. -/
def transmittedSegment : PlateFace → RaySegment
  | .entryFace => .insideGlass
  | .exitFace => .outgoing

/-! ## Physical setup and assumptions -/

/--
Physical quantities and figure readouts for the parallel glass plate.

For a face, `incidenceAngleRadians` is the angle on the incident side and
`refractionAngleRadians` is the angle on the transmitted side. Consequently
the four values carry the figure labels `θ_a`, `θ'_b`, `θ_b`, and `θ'_a` at
the entry-incidence, entry-refraction, exit-incidence, and exit-refraction
positions respectively.
-/
structure ParallelGlassPlateSetup where
  /-- Figure label `t`, the normal thickness of the glass plate. -/
  thickness : DimLength
  /-- Figure label `d`, the perpendicular lateral displacement. -/
  lateralDisplacement : DimLength
  /-- Dimensionless refractive index in each homogeneous optical region. -/
  refractiveIndex : OpticalRegion → ℝ
  /-- The transparent-material property stated for the glass plate. -/
  glassIsTransparent : Prop
  /-- Nonzero propagation direction of each portion of the ray. -/
  rayDirection : RaySegment → RayDirection
  /-- Propagation-oriented normal at each planar plate face. -/
  faceNormalDirection : PlateFace → RayDirection
  /-- Scalar incidence angle from the face normal at each interface. -/
  incidenceAngleRadians : PlateFace → ℝ
  /-- Scalar transmitted/refraction angle from the normal at each interface. -/
  refractionAngleRadians : PlateFace → ℝ
  /-- Positions of the entry point and the figure points `P` and `Q`. -/
  pointPosition : FigurePoint → DiagramPlane

/-- The undirected radian angle between two nonzero diagram directions. -/
def angleBetweenDirections (first second : RayDirection) : ℝ :=
  InnerProductGeometry.angle first.1 second.1

/-- An angle readout lies on the physical acute branch of geometrical optics. -/
def IsPhysicalAcuteAngle (angleRadians : ℝ) : Prop :=
  angleRadians ∈ Set.Ioo 0 (Real.pi / 2)

/--
Problem-statement readouts: a transparent `2.40 cm` glass plate of refractive
index `1.80`, a `66.0°` incidence angle in air, and air of index one on both
sides. No value of the requested lateral displacement occurs here.
-/
structure MatchesProblemData (setup : ParallelGlassPlateSetup) : Prop where
  transparentGlass : setup.glassIsTransparent
  thicknessReadout : valueInCentimeters setup.thickness = 2.40
  entryIncidenceReadout :
    setup.incidenceAngleRadians .entryFace = degreesToRadians 66.0
  incidentAirIndexReadout : setup.refractiveIndex .incidentAir = 1
  glassIndexReadout : setup.refractiveIndex .glassPlate = 1.80
  emergentAirIndexReadout : setup.refractiveIndex .emergentAir = 1

/-- Positivity and principal-angle-branch conditions for the optical model. -/
structure HasPhysicalOpticalParameters (setup : ParallelGlassPlateSetup) : Prop where
  thicknessPositive : 0 < valueInCentimeters setup.thickness
  lateralDisplacementNonnegative :
    0 ≤ valueInCentimeters setup.lateralDisplacement
  refractiveIndexPositive : ∀ region, 0 < setup.refractiveIndex region
  incidenceAnglesPhysical :
    ∀ face, IsPhysicalAcuteAngle (setup.incidenceAngleRadians face)
  refractionAnglesPhysical :
    ∀ face, IsPhysicalAcuteAngle (setup.refractionAngleRadians face)

/--
The plane-parallel surface geometry and the `P`--`Q` construction shown in the
figure. The final field is the general parallel-plate displacement relation

`d = t sin (θ_a - θ'_b) / cos θ'_b`.

It relates arbitrary physical readouts and does not assign the requested
numerical value of `d`.
-/
structure SatisfiesParallelPlateGeometry (setup : ParallelGlassPlateSetup) : Prop where
  parallelFaceNormals :
    setup.faceNormalDirection .entryFace =
      setup.faceNormalDirection .exitFace
  incidenceAngleFromDirections :
    ∀ face,
      setup.incidenceAngleRadians face =
        angleBetweenDirections
          (setup.rayDirection (incidentSegment face))
          (setup.faceNormalDirection face)
  refractionAngleFromDirections :
    ∀ face,
      setup.refractionAngleRadians face =
        angleBetweenDirections
          (setup.rayDirection (transmittedSegment face))
          (setup.faceNormalDirection face)
  internalAnglePreservedByParallelFaces :
    setup.refractionAngleRadians .entryFace =
      setup.incidenceAngleRadians .exitFace
  pointPReachedAlongInternalRay :
    ∃ scale : ℝ, 0 < scale ∧
      setup.pointPosition .P - setup.pointPosition .entry =
        scale • (setup.rayDirection .insideGlass).1
  pointQOnUnrefractedIncidentExtension :
    ∃ scale : ℝ, 0 < scale ∧
      setup.pointPosition .Q - setup.pointPosition .entry =
        scale • (setup.rayDirection .incoming).1
  pqPerpendicularToIncidentExtension :
    inner ℝ
        (setup.pointPosition .P - setup.pointPosition .Q)
        (setup.rayDirection .incoming).1 = 0
  lateralDisplacementIsPQ :
    valueInCentimeters setup.lateralDisplacement =
      ‖setup.pointPosition .P - setup.pointPosition .Q‖
  parallelPlateDisplacementRelation :
    valueInCentimeters setup.lateralDisplacement =
      valueInCentimeters setup.thickness *
        Real.sin
          (setup.incidenceAngleRadians .entryFace -
            setup.refractionAngleRadians .entryFace) /
        Real.cos (setup.refractionAngleRadians .entryFace)

/-- Snell's law `n₁ sin θ₁ = n₂ sin θ₂` at one plate face. -/
def SatisfiesSnellsLawAt
    (setup : ParallelGlassPlateSetup) (face : PlateFace) : Prop :=
  setup.refractiveIndex (incidentRegion face) *
      Real.sin (setup.incidenceAngleRadians face) =
    setup.refractiveIndex (transmittedRegion face) *
      Real.sin (setup.refractionAngleRadians face)

/-- The ray obeys Snell's law at the entry and exit faces. -/
structure ObeysSnellsLaw (setup : ParallelGlassPlateSetup) : Prop where
  atFace : ∀ face, SatisfiesSnellsLawAt setup face

/-! ## Multiple-choice target -/

/-- The four displayed answer labels. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Lateral-displacement readout in centimeters printed beside each choice. -/
def AnswerChoice.displacementCentimeters : AnswerChoice → ℝ
  | .A => 1.62
  | .B => 1.54
  | .C => 1.75
  | .D => 1.59

/-- Dataset metadata recording answer A; this definition is not a premise. -/
def recordedAnswerChoice : AnswerChoice := .A

/--
A physical length rounds to a displayed hundredth-centimeter answer when its
centimeter readout differs from that answer by at most `0.005 cm`.
-/
def MatchesAnswerToNearestHundredthCentimeter
    (length : DimLength) (choice : AnswerChoice) : Prop :=
  |valueInCentimeters length - choice.displacementCentimeters| ≤ (1 : ℝ) / 200

/--
For a `2.40 cm` parallel glass plate with refractive index `1.80` in air and a
`66.0°` incidence angle, the Snell-law refraction angle and the `P`--`Q`
geometry make the lateral displacement round to `1.62 cm`, answer A.

Blueprint: `thm:physics:phyx_mini_0102:target`.
-/
theorem lateralDisplacementIsAnswerA
    (setup : ParallelGlassPlateSetup)
    (_problemData : MatchesProblemData setup)
    (_physical : HasPhysicalOpticalParameters setup)
    (_geometry : SatisfiesParallelPlateGeometry setup)
    (_snell : ObeysSnellsLaw setup) :
    MatchesAnswerToNearestHundredthCentimeter
      setup.lateralDisplacement .A := by
  have hentryAngle :
      setup.incidenceAngleRadians .entryFace =
        Real.pi / 6 + Real.pi / 5 := by
    rw [_problemData.entryIncidenceReadout]
    norm_num [degreesToRadians]
    ring

  have hsqrt3_sq : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt5_sq : (Real.sqrt 5) ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt3_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hsqrt5_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hsqrt3_lower : (173205 : ℝ) / 100000 ≤ Real.sqrt 3 := by
    nlinarith only [hsqrt3_sq, hsqrt3_nonneg,
      sq_nonneg (Real.sqrt 3 - (173205 : ℝ) / 100000)]
  have hsqrt3_upper : Real.sqrt 3 ≤ (86603 : ℝ) / 50000 := by
    nlinarith only [hsqrt3_sq, hsqrt3_nonneg,
      sq_nonneg (Real.sqrt 3 - (86603 : ℝ) / 50000)]
  have hsqrt5_lower : (111803 : ℝ) / 50000 ≤ Real.sqrt 5 := by
    nlinarith only [hsqrt5_sq, hsqrt5_nonneg,
      sq_nonneg (Real.sqrt 5 - (111803 : ℝ) / 50000)]
  have hsqrt5_upper : Real.sqrt 5 ≤ (223607 : ℝ) / 100000 := by
    nlinarith only [hsqrt5_sq, hsqrt5_nonneg,
      sq_nonneg (Real.sqrt 5 - (223607 : ℝ) / 100000)]

  have hsin36_pos : 0 < Real.sin (Real.pi / 5) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · nlinarith [Real.pi_pos]
  have htrig36 := Real.sin_sq_add_cos_sq (Real.pi / 5)
  have hcos36 :
      Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 :=
    Real.cos_pi_div_five
  have hcos36_lower :
      (161803 : ℝ) / 200000 ≤ Real.cos (Real.pi / 5) := by
    rw [hcos36]
    linarith only [hsqrt5_lower]
  have hcos36_upper :
      Real.cos (Real.pi / 5) ≤ (323607 : ℝ) / 400000 := by
    rw [hcos36]
    linarith only [hsqrt5_upper]
  have hsin36_lower :
      (29389 : ℝ) / 50000 ≤ Real.sin (Real.pi / 5) := by
    nlinarith only [htrig36, hcos36_lower, hcos36_upper, hsin36_pos,
      sq_nonneg
        (Real.cos (Real.pi / 5) - (323607 : ℝ) / 400000),
      sq_nonneg
        (Real.sin (Real.pi / 5) - (29389 : ℝ) / 50000)]
  have hsin36_upper :
      Real.sin (Real.pi / 5) ≤ (2939 : ℝ) / 5000 := by
    nlinarith only [htrig36, hcos36_lower, hcos36_upper, hsin36_pos,
      sq_nonneg
        (Real.cos (Real.pi / 5) - (161803 : ℝ) / 200000),
      sq_nonneg
        (Real.sin (Real.pi / 5) - (2939 : ℝ) / 5000)]

  have hsqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hcos36_pos : 0 < Real.cos (Real.pi / 5) := by
    linarith only [hcos36_lower]
  have hsqrt3_sin36_lower :
      ((173205 : ℝ) / 100000) * ((29389 : ℝ) / 50000) ≤
        Real.sqrt 3 * Real.sin (Real.pi / 5) :=
    mul_le_mul hsqrt3_lower hsin36_lower
      (by positivity) hsqrt3_pos.le
  have hsqrt3_sin36_upper :
      Real.sqrt 3 * Real.sin (Real.pi / 5) ≤
        ((86603 : ℝ) / 50000) * ((2939 : ℝ) / 5000) :=
    mul_le_mul hsqrt3_upper hsin36_upper hsin36_pos.le (by norm_num)
  have hsqrt3_cos36_lower :
      ((173205 : ℝ) / 100000) * ((161803 : ℝ) / 200000) ≤
        Real.sqrt 3 * Real.cos (Real.pi / 5) :=
    mul_le_mul hsqrt3_lower hcos36_lower
      (by positivity) hsqrt3_pos.le
  have hsqrt3_cos36_upper :
      Real.sqrt 3 * Real.cos (Real.pi / 5) ≤
        ((86603 : ℝ) / 50000) * ((323607 : ℝ) / 400000) :=
    mul_le_mul hsqrt3_upper hcos36_upper hcos36_pos.le (by norm_num)

  have hsinEntry_lower :
      (9134 : ℝ) / 10000 ≤
        Real.sin (setup.incidenceAngleRadians .entryFace) := by
    rw [hentryAngle, Real.sin_add, Real.sin_pi_div_six,
      Real.cos_pi_div_six]
    nlinarith only [hcos36_lower, hsqrt3_sin36_lower]
  have hsinEntry_upper :
      Real.sin (setup.incidenceAngleRadians .entryFace) ≤
        (9138 : ℝ) / 10000 := by
    rw [hentryAngle, Real.sin_add, Real.sin_pi_div_six,
      Real.cos_pi_div_six]
    nlinarith only [hcos36_upper, hsqrt3_sin36_upper]
  have hcosEntry_lower :
      (4066 : ℝ) / 10000 ≤
        Real.cos (setup.incidenceAngleRadians .entryFace) := by
    rw [hentryAngle, Real.cos_add, Real.sin_pi_div_six,
      Real.cos_pi_div_six]
    nlinarith only [hsqrt3_cos36_lower, hsin36_upper]
  have hcosEntry_upper :
      Real.cos (setup.incidenceAngleRadians .entryFace) ≤
        (4069 : ℝ) / 10000 := by
    rw [hentryAngle, Real.cos_add, Real.sin_pi_div_six,
      Real.cos_pi_div_six]
    nlinarith only [hsqrt3_cos36_upper, hsin36_lower]

  have hsnell := _snell.atFace .entryFace
  have hsinRefracted :
      Real.sin (setup.refractionAngleRadians .entryFace) =
        (5 : ℝ) / 9 *
          Real.sin (setup.incidenceAngleRadians .entryFace) := by
    simp only [SatisfiesSnellsLawAt, incidentRegion, transmittedRegion] at hsnell
    rw [_problemData.incidentAirIndexReadout,
      _problemData.glassIndexReadout] at hsnell
    norm_num at hsnell ⊢
    nlinarith only [hsnell]

  have hrefractedPhysical :
      setup.refractionAngleRadians .entryFace ∈
        Set.Ioo 0 (Real.pi / 2) :=
    _physical.refractionAnglesPhysical .entryFace
  have hcosRefracted_pos :
      0 < Real.cos (setup.refractionAngleRadians .entryFace) := by
    apply Real.cos_pos_of_mem_Ioo
    exact
      ⟨lt_trans (neg_lt_zero.mpr Real.pi_div_two_pos)
        hrefractedPhysical.1, hrefractedPhysical.2⟩
  have hsinRefracted_pos :
      0 < Real.sin (setup.refractionAngleRadians .entryFace) := by
    rw [hsinRefracted]
    positivity
  have hsinRefracted_lower :
      (5 : ℝ) / 9 * ((9134 : ℝ) / 10000) ≤
        Real.sin (setup.refractionAngleRadians .entryFace) := by
    rw [hsinRefracted]
    nlinarith only [hsinEntry_lower]
  have hsinRefracted_upper :
      Real.sin (setup.refractionAngleRadians .entryFace) ≤
        (5 : ℝ) / 9 * ((9138 : ℝ) / 10000) := by
    rw [hsinRefracted]
    nlinarith only [hsinEntry_upper]
  have hsinRefracted_sq_upper :
      Real.sin (setup.refractionAngleRadians .entryFace) ^ 2 ≤
        ((5 : ℝ) / 9 * ((9138 : ℝ) / 10000)) ^ 2 := by
    nlinarith only [hsinRefracted_upper, hsinRefracted_pos, mul_nonneg
      (sub_nonneg.mpr hsinRefracted_upper)
      (add_nonneg
        (by norm_num :
          0 ≤ (5 : ℝ) / 9 * ((9138 : ℝ) / 10000))
        hsinRefracted_pos.le)]
  have hsinRefracted_sq_lower :
      ((5 : ℝ) / 9 * ((9134 : ℝ) / 10000)) ^ 2 ≤
        Real.sin (setup.refractionAngleRadians .entryFace) ^ 2 := by
    nlinarith only [hsinRefracted_lower, hsinRefracted_pos, mul_nonneg
      (sub_nonneg.mpr hsinRefracted_lower)
      (add_nonneg
        (by norm_num :
          0 ≤ (5 : ℝ) / 9 * ((9134 : ℝ) / 10000))
        hsinRefracted_pos.le)]
  have hrefractedTrig :=
    Real.sin_sq_add_cos_sq (setup.refractionAngleRadians .entryFace)
  have hcosRefracted_lower :
      (861 : ℝ) / 1000 ≤
        Real.cos (setup.refractionAngleRadians .entryFace) := by
    nlinarith only [hrefractedTrig, hsinRefracted_sq_upper,
      hcosRefracted_pos, sq_nonneg
      (Real.cos (setup.refractionAngleRadians .entryFace) -
        (861 : ℝ) / 1000)]
  have hcosRefracted_upper :
      Real.cos (setup.refractionAngleRadians .entryFace) ≤
        (862 : ℝ) / 1000 := by
    nlinarith only [hrefractedTrig, hsinRefracted_sq_lower,
      hcosRefracted_pos, sq_nonneg
      (Real.cos (setup.refractionAngleRadians .entryFace) -
        (862 : ℝ) / 1000)]

  have hcosEntry_pos :
      0 < Real.cos (setup.incidenceAngleRadians .entryFace) := by
    nlinarith only [hcosEntry_lower]
  have hproduct_lower :
      ((4066 : ℝ) / 10000) *
          ((5 : ℝ) / 9 * ((9134 : ℝ) / 10000)) ≤
        Real.cos (setup.incidenceAngleRadians .entryFace) *
          Real.sin (setup.refractionAngleRadians .entryFace) := by
    exact mul_le_mul hcosEntry_lower hsinRefracted_lower
      (by positivity) hcosEntry_pos.le
  have hproduct_upper :
      Real.cos (setup.incidenceAngleRadians .entryFace) *
          Real.sin (setup.refractionAngleRadians .entryFace) ≤
        ((4069 : ℝ) / 10000) *
          ((5 : ℝ) / 9 * ((9138 : ℝ) / 10000)) := by
    exact mul_le_mul hcosEntry_upper hsinRefracted_upper
      hsinRefracted_pos.le (by norm_num)
  have hratio_lower :
      (((4066 : ℝ) / 10000) *
          ((5 : ℝ) / 9 * ((9134 : ℝ) / 10000))) /
            ((862 : ℝ) / 1000) ≤
        Real.cos (setup.incidenceAngleRadians .entryFace) *
            Real.sin (setup.refractionAngleRadians .entryFace) /
          Real.cos (setup.refractionAngleRadians .entryFace) := by
    exact div_le_div₀
      (mul_nonneg hcosEntry_pos.le hsinRefracted_pos.le)
      hproduct_lower hcosRefracted_pos hcosRefracted_upper
  have hratio_upper :
      Real.cos (setup.incidenceAngleRadians .entryFace) *
            Real.sin (setup.refractionAngleRadians .entryFace) /
          Real.cos (setup.refractionAngleRadians .entryFace) ≤
        (((4069 : ℝ) / 10000) *
          ((5 : ℝ) / 9 * ((9138 : ℝ) / 10000))) /
            ((861 : ℝ) / 1000) := by
    exact div_le_div₀ (by positivity) hproduct_upper
      (by norm_num) hcosRefracted_lower

  have hdisplacement :
      valueInCentimeters setup.lateralDisplacement =
        (12 : ℝ) / 5 *
          (Real.sin (setup.incidenceAngleRadians .entryFace) -
            Real.cos (setup.incidenceAngleRadians .entryFace) *
                Real.sin (setup.refractionAngleRadians .entryFace) /
              Real.cos (setup.refractionAngleRadians .entryFace)) := by
    rw [_geometry.parallelPlateDisplacementRelation,
      _problemData.thicknessReadout, Real.sin_sub]
    norm_num
    field_simp [hcosRefracted_pos.ne']

  rw [MatchesAnswerToNearestHundredthCentimeter,
    AnswerChoice.displacementCentimeters]
  apply abs_le.mpr
  constructor
  · nlinarith only [hdisplacement, hsinEntry_lower, hratio_upper]
  · nlinarith only [hdisplacement, hsinEntry_upper, hratio_lower]

end PhyXMiniProblems.ProblemPhyXMini0102
