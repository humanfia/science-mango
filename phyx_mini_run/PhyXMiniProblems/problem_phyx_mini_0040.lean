import Mathlib
import Physlib.Units.WithDim.Basic
import Physlib.SpaceAndTime.Space.LengthUnit

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0040

/-!
# Lateral magnification at a hemispherical refracting surface

The figure shows a small axial object `P` in air, the vertex of the rounded
end of a cylindrical glass rod, the center of curvature `C`, and the real image
`P'` inside the glass.  All axial positions and radii are dimensionful lengths.
Refractive indices and lateral magnification are dimensionless real readouts.

Positive object and image distances are measured along the displayed light
path: from `P` to the vertex and from the vertex to `P'`, respectively.  The
radius is positive because `C` lies in the transmitted (glass) medium.
-/

/-- A signed physical length whose readout changes coherently with unit choice. -/
abbrev OpticalLength : Type := Dimensionful (WithDim Dimension.L𝓭 ℝ)

/-- The physical length having scalar readout `magnitude` in the chosen unit. -/
def lengthIn (unit : LengthUnit) (magnitude : ℝ) : OpticalLength :=
  CarriesDimension.toDimensionful { UnitChoices.SI with length := unit } ⟨magnitude⟩

/-- The scalar readout of a physical length in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : OpticalLength) : ℝ :=
  (length { UnitChoices.SI with length := unit }).val

/-- The two homogeneous optical media on the incident and transmitted sides. -/
inductive OpticalMedium where
  | air
  | glassRod
  deriving DecidableEq, Repr

/-- Axial point labels appearing in the source figure. -/
inductive AxialPoint where
  | P
  | vertex
  | C
  | PPrime
  deriving DecidableEq, Repr

/-- The overall shape of the transparent solid in the physical scenario. -/
inductive RodShape where
  | cylindrical
  deriving DecidableEq, Repr

/-- The shape ground onto the incident end of the glass rod. -/
inductive EndSurfaceShape where
  | hemispherical
  deriving DecidableEq, Repr

/--
Physical and geometric quantities attached to the air--glass refraction
diagram.  The axial coordinate is signed, while `surfaceRadius` is a positive
physical length when the setup is physically admissible.
-/
structure HemisphericalRodSetup where
  rodShape : RodShape
  endSurfaceShape : EndSurfaceShape
  refractiveIndex : OpticalMedium → ℝ
  axialPosition : AxialPoint → OpticalLength
  surfaceRadius : OpticalLength

/-- Signed axial separation from `start` to `finish`, read in the selected unit. -/
def axialSeparationReadout
    (setup : HemisphericalRodSetup) (unit : LengthUnit)
    (start finish : AxialPoint) : ℝ :=
  lengthReadout unit (setup.axialPosition finish) -
    lengthReadout unit (setup.axialPosition start)

/-- Figure label `s`: positive object distance from `P` to the surface vertex. -/
def objectDistanceReadout
    (setup : HemisphericalRodSetup) (unit : LengthUnit) : ℝ :=
  axialSeparationReadout setup unit .P .vertex

/-- Figure label `s'`: positive real-image distance from the vertex to `P'`. -/
def imageDistanceReadout
    (setup : HemisphericalRodSetup) (unit : LengthUnit) : ℝ :=
  axialSeparationReadout setup unit .vertex .PPrime

/-- Scalar readout of the hemispherical surface's physical radius. -/
def radiusReadout
    (setup : HemisphericalRodSetup) (unit : LengthUnit) : ℝ :=
  lengthReadout unit setup.surfaceRadius

/--
Problem and figure readouts.  They fix the rod and end shapes, the two
dimensionless refractive indices, `s = 8.00 cm`, and `R = 2.00 cm`.  The
relation between the vertex and `C` records that `C` is the center of the
hemisphere.  No numerical value is assigned to the derived image distance.
-/
def MatchesFigureReadout (setup : HemisphericalRodSetup) : Prop :=
  setup.rodShape = .cylindrical ∧
    setup.endSurfaceShape = .hemispherical ∧
    setup.refractiveIndex .air = 1.00 ∧
    setup.refractiveIndex .glassRod = 1.52 ∧
    objectDistanceReadout setup LengthUnit.centimeters = 8.00 ∧
    radiusReadout setup LengthUnit.centimeters = 2.00 ∧
    axialSeparationReadout setup LengthUnit.centimeters .vertex .C =
      radiusReadout setup LengthUnit.centimeters

/--
Physical branch information visible in the diagram: refractive indices and
radius are positive, and the labels occur in the order `P`, vertex, `C`, `P'`
along the propagation axis.
-/
def HasPhysicalFigureGeometry (setup : HemisphericalRodSetup) : Prop :=
  0 < setup.refractiveIndex .air ∧
    0 < setup.refractiveIndex .glassRod ∧
    0 < radiusReadout setup LengthUnit.centimeters ∧
    lengthReadout LengthUnit.centimeters (setup.axialPosition .P) <
      lengthReadout LengthUnit.centimeters (setup.axialPosition .vertex) ∧
    lengthReadout LengthUnit.centimeters (setup.axialPosition .vertex) <
      lengthReadout LengthUnit.centimeters (setup.axialPosition .C) ∧
    lengthReadout LengthUnit.centimeters (setup.axialPosition .C) <
      lengthReadout LengthUnit.centimeters (setup.axialPosition .PPrime)

/--
At transverse height `rayHeight`, this is the axial offset of the incident
point on the left-hand hemispherical surface.  The formula is the exact circle
geometry `R - sqrt (R^2 - h^2)`, not a paraxial replacement.
-/
def surfaceAxialOffsetReadout
    (setup : HemisphericalRodSetup) (unit : LengthUnit)
    (rayHeight : ℝ) : ℝ :=
  radiusReadout setup unit -
    Real.sqrt (radiusReadout setup unit ^ 2 - rayHeight ^ 2)

/-- Exact direction angle of the ray from the axial object `P` to the surface. -/
def incidentRayAngle
    (setup : HemisphericalRodSetup) (unit : LengthUnit)
    (rayHeight : ℝ) : ℝ :=
  Real.arctan
    (rayHeight /
      (objectDistanceReadout setup unit +
        surfaceAxialOffsetReadout setup unit rayHeight))

/--
Exact direction angle of the inward surface normal.  At a point above the
axis it points downwards from the spherical surface toward `C`.
-/
def inwardNormalAngle
    (setup : HemisphericalRodSetup) (unit : LengthUnit)
    (rayHeight : ℝ) : ℝ :=
  -Real.arcsin (rayHeight / radiusReadout setup unit)

/-- Exact direction angle from the surface point to the proposed axial image `P'`. -/
def imageRayAngle
    (setup : HemisphericalRodSetup) (unit : LengthUnit)
    (rayHeight : ℝ) : ℝ :=
  -Real.arctan
    (rayHeight /
      (imageDistanceReadout setup unit -
        surfaceAxialOffsetReadout setup unit rayHeight))

/--
Difference between the two sides of exact Snell's law for the incident ray and
the ray aimed at `P'`.  All angles are signed radian readouts relative to the
propagation axis.
-/
def axialSnellResidual
    (setup : HemisphericalRodSetup) (unit : LengthUnit)
    (rayHeight : ℝ) : ℝ :=
  setup.refractiveIndex .air *
      Real.sin (incidentRayAngle setup unit rayHeight -
        inwardNormalAngle setup unit rayHeight) -
    setup.refractiveIndex .glassRod *
      Real.sin (imageRayAngle setup unit rayHeight -
        inwardNormalAngle setup unit rayHeight)

/--
`P'` is the first-order, or paraxial, image selected by exact spherical
geometry and Snell's law.  The derivative condition says that the exact Snell
residual is `o(rayHeight)` at the optical axis.  It does not assert exact
stigmatic imaging for finite-height rays, which a spherical surface generally
does not provide.
-/
def HasFirstOrderParaxialImage (setup : HemisphericalRodSetup) : Prop :=
  ∀ units : UnitChoices,
    HasDerivAt (axialSnellResidual setup units.length) 0 0

/-- A physical map from transverse object displacement to image displacement. -/
abbrev TransverseImageMap : Type := OpticalLength → OpticalLength

/--
Scalar readout, in one length unit, of a physical transverse image map.
Its derivative is dimensionless because input and output have the same
physical dimension.
-/
def transverseImageReadout
    (imageMap : TransverseImageMap) (unit : LengthUnit)
    (objectHeight : ℝ) : ℝ :=
  lengthReadout unit (imageMap (lengthIn unit objectHeight))

/--
Exact Snell residual for the chief ray that passes through the surface vertex.
The incident ray starts at the displaced object point, and the transmitted ray
ends at the displacement supplied by `imageMap` in the plane through `P'`.
-/
def vertexSnellResidual
    (setup : HemisphericalRodSetup) (imageMap : TransverseImageMap)
    (unit : LengthUnit) (objectHeight : ℝ) : ℝ :=
  setup.refractiveIndex .air *
      Real.sin (-Real.arctan
        (objectHeight / objectDistanceReadout setup unit)) -
    setup.refractiveIndex .glassRod *
      Real.sin (Real.arctan
        (transverseImageReadout imageMap unit objectHeight /
          imageDistanceReadout setup unit))

/--
The local/asymptotic contract defining signed lateral magnification.

The map fixes the optical axis, has derivative `lateralMagnification` there in
every unit system, and satisfies exact Snell refraction through the vertex to
first order.  Consequently the familiar formula
`m = -nₐ s' / (n_b s)` is a theorem about the derivative, rather than a
globally exact finite-angle premise.  A negative derivative represents image
inversion.
-/
def HasFirstOrderLateralMagnification
    (setup : HemisphericalRodSetup) (imageMap : TransverseImageMap)
    (lateralMagnification : ℝ) : Prop :=
  (∀ units : UnitChoices,
      transverseImageReadout imageMap units.length 0 = 0) ∧
    (∀ units : UnitChoices,
      HasDerivAt
        (transverseImageReadout imageMap units.length)
        lateralMagnification 0) ∧
    (∀ units : UnitChoices,
      HasDerivAt
        (vertexSnellResidual setup imageMap units.length) 0 0)

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Dimensionless lateral-magnification value printed beside each choice. -/
def answerMagnification : AnswerChoice → ℝ
  | .A => -0.856
  | .B => -0.929
  | .C => 0.995
  | .D => -0.814

/-- A choice is uniquely closest to the exact physical value displayed by the model. -/
def IsUniqueClosestAnswer (actual : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |actual - answerMagnification choice| <
      |actual - answerMagnification other|

/--
The spherical-interface equation determines the derived image distance
`s' = 304/27 cm`; this value is not included among the problem data.
-/
lemma imageDistanceInCentimeters_eq
    (setup : HemisphericalRodSetup)
    (h_figure : MatchesFigureReadout setup)
    (h_physical : HasPhysicalFigureGeometry setup)
    (h_axial_image : HasFirstOrderParaxialImage setup) :
    imageDistanceReadout setup LengthUnit.centimeters = (304 / 27 : ℝ) := by
  rcases h_figure with
    ⟨_, _, h_air, h_glass, h_object, h_radius, h_center⟩
  rcases h_physical with
    ⟨_, _, _, _, h_vertex_center, h_center_image⟩
  norm_num at h_air h_glass h_object h_radius
  have h_image_pos :
      0 < imageDistanceReadout setup LengthUnit.centimeters := by
    unfold imageDistanceReadout axialSeparationReadout
    linarith
  have h_image_ne :
      imageDistanceReadout setup LengthUnit.centimeters ≠ 0 :=
    ne_of_gt h_image_pos
  have h_surface_zero :
      surfaceAxialOffsetReadout setup LengthUnit.centimeters 0 = 0 := by
    norm_num [surfaceAxialOffsetReadout, h_radius]
  have h_surface :
      HasDerivAt
        (surfaceAxialOffsetReadout setup LengthUnit.centimeters) 0 0 := by
    unfold surfaceAxialOffsetReadout
    rw [h_radius]
    have h_inside : HasDerivAt (fun x : ℝ => 4 - x ^ 2) 0 0 := by
      simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
        pow_one, zero_mul, mul_zero, neg_zero] using
          ((hasDerivAt_id (0 : ℝ)).pow 2).const_sub 4
    have h_sqrt :
        HasDerivAt (fun x : ℝ => Real.sqrt (4 - x ^ 2)) 0 0 := by
      simpa only [zero_div] using h_inside.sqrt (by norm_num)
    rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
    simpa only [neg_zero] using h_sqrt.const_sub 2
  have h_incident :
      HasDerivAt
        (incidentRayAngle setup LengthUnit.centimeters) (1 / 8) 0 := by
    unfold incidentRayAngle
    rw [h_object]
    have h_denominator :
        HasDerivAt
          (fun x : ℝ =>
            8 + surfaceAxialOffsetReadout setup LengthUnit.centimeters x)
          0 0 :=
      h_surface.const_add 8
    have h_fraction :=
      (hasDerivAt_id (0 : ℝ)).fun_div h_denominator (by
        norm_num [h_surface_zero])
    have h_fraction' :
        HasDerivAt
          (fun x : ℝ =>
            x /
              (8 +
                surfaceAxialOffsetReadout setup LengthUnit.centimeters x))
          (1 / 8) 0 := by
      convert! h_fraction using 1 <;> norm_num [h_surface_zero]
    convert! h_fraction'.arctan using 1 <;> norm_num [h_surface_zero]
  have h_normal :
      HasDerivAt
        (inwardNormalAngle setup LengthUnit.centimeters) (-1 / 2) 0 := by
    unfold inwardNormalAngle
    rw [h_radius]
    have h_fraction :
        HasDerivAt (fun x : ℝ => x / 2) (1 / 2) 0 := by
      convert! (hasDerivAt_id (0 : ℝ)).div_const (2 : ℝ) using 1
    have h_arcsin :=
      (Real.hasDerivAt_arcsin (x := (0 : ℝ)) (by norm_num) (by norm_num)).comp_of_eq
        0 h_fraction (by norm_num)
    convert! h_arcsin.neg using 1 <;> norm_num
  have h_image :
      HasDerivAt
        (imageRayAngle setup LengthUnit.centimeters)
        (-1 / imageDistanceReadout setup LengthUnit.centimeters) 0 := by
    unfold imageRayAngle
    have h_denominator :
        HasDerivAt
          (fun x : ℝ =>
            imageDistanceReadout setup LengthUnit.centimeters -
              surfaceAxialOffsetReadout setup LengthUnit.centimeters x)
          0 0 := by
      simpa only [neg_zero] using
        h_surface.const_sub
          (imageDistanceReadout setup LengthUnit.centimeters)
    have h_fraction :=
      (hasDerivAt_id (0 : ℝ)).fun_div h_denominator (by
        simpa only [h_surface_zero, sub_zero] using h_image_ne)
    have h_fraction' :
        HasDerivAt
          (fun x : ℝ =>
            x /
              (imageDistanceReadout setup LengthUnit.centimeters -
                surfaceAxialOffsetReadout setup LengthUnit.centimeters x))
          (1 / imageDistanceReadout setup LengthUnit.centimeters) 0 := by
      convert! h_fraction using 1
      rw [h_surface_zero]
      norm_num
      field_simp [h_image_ne]
    have h_arctan := h_fraction'.arctan
    norm_num [h_surface_zero] at h_arctan
    convert! h_arctan.neg using 1
    rw [div_eq_mul_inv]
    simp
  have h_residual :
      HasDerivAt
        (axialSnellResidual setup LengthUnit.centimeters)
        (5 / 8 -
          (38 / 25) *
            (-1 / imageDistanceReadout setup LengthUnit.centimeters + 1 / 2))
        0 := by
    unfold axialSnellResidual
    have h_incident_sin := (h_incident.sub h_normal).sin
    have h_image_sin := (h_image.sub h_normal).sin
    have h_incident_zero :
        incidentRayAngle setup LengthUnit.centimeters 0 = 0 := by
      norm_num [incidentRayAngle, h_object, h_surface_zero]
    have h_normal_zero :
        inwardNormalAngle setup LengthUnit.centimeters 0 = 0 := by
      norm_num [inwardNormalAngle, h_radius]
    have h_image_zero :
        imageRayAngle setup LengthUnit.centimeters 0 = 0 := by
      norm_num [imageRayAngle, h_surface_zero]
    rw [h_air, h_glass]
    have h_combined :=
      (h_incident_sin.const_mul (1 : ℝ)).sub
        (h_image_sin.const_mul (38 / 25 : ℝ))
    norm_num [Pi.sub_apply, h_incident_zero, h_normal_zero, h_image_zero] at h_combined
    convert! h_combined using 1
    funext x
    simp only [Pi.sub_apply, one_mul]
  have h_zero :
      HasDerivAt (axialSnellResidual setup LengthUnit.centimeters) 0 0 :=
    h_axial_image
      { UnitChoices.SI with length := LengthUnit.centimeters }
  have h_equation := h_zero.unique h_residual
  field_simp [h_image_ne] at h_equation ⊢
  nlinarith

/--
For the `1.52` glass rod in air, with object distance `8.00 cm` and
hemispherical radius `2.00 cm`, the signed lateral magnification is exactly
`-25/27`.  Among the supplied numerical answers, `-0.929` (choice B) is the
unique closest value.

This formalizes `thm:physics:phyx_mini_0040:target`.
-/
theorem problem_phyx_mini_0040
    (setup : HemisphericalRodSetup)
    (imageMap : TransverseImageMap)
    (lateralMagnification : ℝ)
    (h_figure : MatchesFigureReadout setup)
    (h_physical : HasPhysicalFigureGeometry setup)
    (h_axial_image : HasFirstOrderParaxialImage setup)
    (h_magnification :
      HasFirstOrderLateralMagnification
        setup imageMap lateralMagnification) :
    lateralMagnification = (-25 / 27 : ℝ) ∧
      IsUniqueClosestAnswer lateralMagnification .B := by
  have h_image_distance :=
    imageDistanceInCentimeters_eq setup h_figure h_physical h_axial_image
  rcases h_figure with
    ⟨_, _, h_air, h_glass, h_object, _, _⟩
  rcases h_magnification with
    ⟨h_axis, h_map_derivative, h_vertex_refraction⟩
  norm_num at h_air h_glass h_object
  let centimeterUnits : UnitChoices :=
    { UnitChoices.SI with length := LengthUnit.centimeters }
  have h_map_zero :
      transverseImageReadout imageMap LengthUnit.centimeters 0 = 0 :=
    h_axis centimeterUnits
  have h_map :
      HasDerivAt
        (transverseImageReadout imageMap LengthUnit.centimeters)
        lateralMagnification 0 :=
    h_map_derivative centimeterUnits
  have h_vertex_zero :
      HasDerivAt
        (vertexSnellResidual setup imageMap LengthUnit.centimeters) 0 0 :=
    h_vertex_refraction centimeterUnits
  have h_object_fraction :
      HasDerivAt
        (fun x : ℝ =>
          x / objectDistanceReadout setup LengthUnit.centimeters)
        (1 / 8) 0 := by
    rw [h_object]
    convert! (hasDerivAt_id (0 : ℝ)).div_const (8 : ℝ) using 1
  have h_object_angle :
      HasDerivAt
        (fun x : ℝ =>
          -Real.arctan
            (x / objectDistanceReadout setup LengthUnit.centimeters))
        (-1 / 8) 0 := by
    have h_arctan := h_object_fraction.arctan
    norm_num at h_arctan
    convert! h_arctan.neg using 1
    norm_num
  have h_image_fraction :
      HasDerivAt
        (fun x : ℝ =>
          transverseImageReadout imageMap LengthUnit.centimeters x /
            imageDistanceReadout setup LengthUnit.centimeters)
        (lateralMagnification /
          imageDistanceReadout setup LengthUnit.centimeters) 0 := by
    convert!
      h_map.div_const
        (imageDistanceReadout setup LengthUnit.centimeters) using 1
  have h_image_angle :
      HasDerivAt
        (fun x : ℝ =>
          Real.arctan
            (transverseImageReadout imageMap LengthUnit.centimeters x /
              imageDistanceReadout setup LengthUnit.centimeters))
        (lateralMagnification /
          imageDistanceReadout setup LengthUnit.centimeters) 0 := by
    have h_arctan := h_image_fraction.arctan
    norm_num [h_map_zero] at h_arctan
    convert! h_arctan using 1
  have h_residual :
      HasDerivAt
        (vertexSnellResidual setup imageMap LengthUnit.centimeters)
        ((-1 / 8) -
          (38 / 25) *
            (lateralMagnification /
              imageDistanceReadout setup LengthUnit.centimeters)) 0 := by
    unfold vertexSnellResidual
    have h_object_sin := h_object_angle.sin
    have h_image_sin := h_image_angle.sin
    have h_object_angle_zero :
        -Real.arctan
            ((0 : ℝ) / objectDistanceReadout setup LengthUnit.centimeters) =
          0 := by
      norm_num
    have h_image_angle_zero :
        Real.arctan
            (transverseImageReadout imageMap LengthUnit.centimeters 0 /
              imageDistanceReadout setup LengthUnit.centimeters) =
          0 := by
      rw [h_map_zero]
      norm_num
    rw [h_air, h_glass]
    have h_combined :=
      (h_object_sin.const_mul (1 : ℝ)).sub
        (h_image_sin.const_mul (38 / 25 : ℝ))
    norm_num [h_object_angle_zero, h_image_angle_zero] at h_combined
    convert! h_combined using 1
    · funext x
      simp only [Pi.sub_apply, one_mul, Real.sin_neg]
    · ring
  have h_magnification_equation := h_vertex_zero.unique h_residual
  rw [h_image_distance] at h_magnification_equation
  norm_num at h_magnification_equation
  have h_magnification_value :
      lateralMagnification = (-25 / 27 : ℝ) := by
    linarith
  refine ⟨h_magnification_value, ?_⟩
  rw [h_magnification_value]
  intro other h_other
  cases other with
  | A =>
      norm_num [answerMagnification, abs_of_nonneg, abs_of_neg]
  | B =>
      exact (h_other rfl).elim
  | C =>
      norm_num [answerMagnification, abs_of_nonneg, abs_of_neg]
  | D =>
      norm_num [answerMagnification, abs_of_nonneg, abs_of_neg]

end PhyXMiniProblems.ProblemPhyXMini0040
