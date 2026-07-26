import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0018

open Dimension

/-!
# Refraction through a quarter-circular material

The radius `R` and incoming-ray height `L` are dimensionful lengths.
Refractive indices are dimensionless real readouts, while all angle fields are
radian readouts measured from the relevant interface normal. The curved-face
normal is the radius through the entry point, and the vertical exit face has a
horizontal normal.
-/

/-- A physical length, independent of the unit used to read its value. -/
abbrev DimLength : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- The scalar meter readout of a dimensionful length. -/
def lengthInMeters (length : DimLength) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/--
A homogeneous optical medium together with its positive, dimensionless
refractive index.
-/
structure OpticalMedium where
  refractiveIndex : ℝ
  refractiveIndex_pos : 0 < refractiveIndex

/-- The two material interfaces crossed by the ray in the figure. -/
inductive OpticalInterface where
  /-- The circular vacuum--material entry face. -/
  | curvedEntry
  /-- The vertical material--vacuum exit face. -/
  | flatExit
  deriving DecidableEq, Repr

/--
Physical quantities and angle labels for the quarter-circle ray diagram.

The body is the quarter disk of radius `radius`; `incomingHeightAboveBase` is
the figure label `L`. The internal and outgoing directions are recorded as
positive angles below the horizontal base direction, matching the dashed
horizontal normal at the flat exit face.
-/
structure QuarterCircleRefractionSetup where
  vacuum : OpticalMedium
  material : OpticalMedium
  /-- Figure label `R`, the quarter-circle radius. -/
  radius : DimLength
  /-- Figure label `L`, the height of the incoming horizontal ray. -/
  incomingHeightAboveBase : DimLength
  /-- Direction of the incoming ray relative to the horizontal base. -/
  incomingAngleToBaseRad : ℝ
  /-- Angle `α` from the radius normal to the incident ray at the curved face. -/
  curvedIncidenceAngleRad : ℝ
  /-- Angle `β` from the radius normal to the refracted ray inside the material. -/
  curvedRefractionAngleRad : ℝ
  /--
  Angle `δ` below the horizontal base; this is also the incidence angle from
  the horizontal normal at the vertical exit face.
  -/
  internalAngleBelowBaseRad : ℝ
  /-- Figure label `θ`, the outgoing angle below the horizontal exit normal. -/
  emergenceAngleRad : ℝ

/--
The nondegenerate material and length conditions in the pictured situation.
The surrounding vacuum has index one and the material is optically denser.
-/
def HasPhysicalParameters (setup : QuarterCircleRefractionSetup) : Prop :=
  setup.vacuum.refractiveIndex = 1 ∧
    setup.vacuum.refractiveIndex < setup.material.refractiveIndex ∧
    0 < lengthInMeters setup.radius ∧
    0 < lengthInMeters setup.incomingHeightAboveBase ∧
    lengthInMeters setup.incomingHeightAboveBase < lengthInMeters setup.radius

/--
All four normal-based ray angles use their acute physical branches. These
conditions select the intended inverse-sine branches and assert that the ray
emerges rather than undergoing total internal reflection.
-/
def HasPhysicalRayAngles (setup : QuarterCircleRefractionSetup) : Prop :=
  setup.curvedIncidenceAngleRad ∈ Set.Ioo 0 (Real.pi / 2) ∧
    setup.curvedRefractionAngleRad ∈ Set.Ioo 0 (Real.pi / 2) ∧
    setup.internalAngleBelowBaseRad ∈ Set.Ioo 0 (Real.pi / 2) ∧
    setup.emergenceAngleRad ∈ Set.Ioo 0 (Real.pi / 2)

/--
Geometry read from the quarter-circle figure. The incoming ray is parallel to
the base. The radius through its entry point has vertical component `L`, so
the entry incidence angle is `arcsin (L / R)`. Subtracting the inside-normal
angle gives the ray's angle below the horizontal flat-face normal.
-/
def ObeysQuarterCircleGeometry (setup : QuarterCircleRefractionSetup) : Prop :=
  setup.incomingAngleToBaseRad = 0 ∧
    setup.curvedIncidenceAngleRad =
      Real.arcsin
        (lengthInMeters setup.incomingHeightAboveBase /
          lengthInMeters setup.radius) ∧
    setup.internalAngleBelowBaseRad =
      setup.curvedIncidenceAngleRad - setup.curvedRefractionAngleRad

/--
Snell's law at either interface: refractive index times the sine of the angle
from the interface normal is conserved.
-/
def SatisfiesSnellLawAt
    (setup : QuarterCircleRefractionSetup)
    (interface : OpticalInterface) : Prop :=
  match interface with
  | .curvedEntry =>
      setup.vacuum.refractiveIndex *
          Real.sin setup.curvedIncidenceAngleRad =
        setup.material.refractiveIndex *
          Real.sin setup.curvedRefractionAngleRad
  | .flatExit =>
      setup.material.refractiveIndex *
          Real.sin setup.internalAngleBelowBaseRad =
        setup.vacuum.refractiveIndex *
          Real.sin setup.emergenceAngleRad

/--
The entry-face geometry and Snell's law determine the in-material angle
`β = arcsin (L / (n R))`. This is a derived intermediate result, not a
governing-law assumption.
-/
lemma curvedRefractionAngle_eq_arcsin
    (setup : QuarterCircleRefractionSetup)
    (h_parameters : HasPhysicalParameters setup)
    (h_angles : HasPhysicalRayAngles setup)
    (h_geometry : ObeysQuarterCircleGeometry setup)
    (h_entry_snell : SatisfiesSnellLawAt setup .curvedEntry) :
    setup.curvedRefractionAngleRad =
      Real.arcsin
        (lengthInMeters setup.incomingHeightAboveBase /
          (setup.material.refractiveIndex * lengthInMeters setup.radius)) := by
  rcases h_parameters with
    ⟨h_vacuum, _h_vacuum_lt_material, h_radius_pos, h_height_pos,
      h_height_lt_radius⟩
  rcases h_angles with
    ⟨_h_incidence, h_refraction, _h_internal, _h_emergence⟩
  rcases h_geometry with
    ⟨_h_horizontal, h_incidence_eq, _h_internal_eq⟩
  change
    setup.vacuum.refractiveIndex *
        Real.sin setup.curvedIncidenceAngleRad =
      setup.material.refractiveIndex *
        Real.sin setup.curvedRefractionAngleRad
    at h_entry_snell
  have h_ratio_pos :
      0 <
        lengthInMeters setup.incomingHeightAboveBase /
          lengthInMeters setup.radius :=
    div_pos h_height_pos h_radius_pos
  have h_ratio_le :
      lengthInMeters setup.incomingHeightAboveBase /
          lengthInMeters setup.radius ≤
        1 :=
    (div_le_one h_radius_pos).2 (le_of_lt h_height_lt_radius)
  have h_sin_incidence :
      Real.sin setup.curvedIncidenceAngleRad =
        lengthInMeters setup.incomingHeightAboveBase /
          lengthInMeters setup.radius := by
    rw [h_incidence_eq, Real.sin_arcsin (by linarith) h_ratio_le]
  rw [h_vacuum, one_mul, h_sin_incidence] at h_entry_snell
  have h_radius_ne : lengthInMeters setup.radius ≠ 0 :=
    ne_of_gt h_radius_pos
  have h_index_ne : setup.material.refractiveIndex ≠ 0 :=
    ne_of_gt setup.material.refractiveIndex_pos
  have h_sin_refraction :
      Real.sin setup.curvedRefractionAngleRad =
        lengthInMeters setup.incomingHeightAboveBase /
          (setup.material.refractiveIndex *
            lengthInMeters setup.radius) := by
    apply (eq_div_iff (mul_ne_zero h_index_ne h_radius_ne)).2
    calc
      Real.sin setup.curvedRefractionAngleRad *
            (setup.material.refractiveIndex *
              lengthInMeters setup.radius) =
          (setup.material.refractiveIndex *
              Real.sin setup.curvedRefractionAngleRad) *
            lengthInMeters setup.radius := by
              ring
      _ = lengthInMeters setup.incomingHeightAboveBase :=
        ((div_eq_iff h_radius_ne).mp h_entry_snell).symm
  have h_refraction_lower :
      -(Real.pi / 2) ≤ setup.curvedRefractionAngleRad := by
    calc
      -(Real.pi / 2) ≤ 0 :=
        neg_nonpos.mpr (div_nonneg (le_of_lt Real.pi_pos) (by norm_num))
      _ ≤ setup.curvedRefractionAngleRad := le_of_lt h_refraction.1
  rw [← h_sin_refraction]
  exact
    (Real.arcsin_sin
      h_refraction_lower
      (le_of_lt h_refraction.2)).symm

/--
For the horizontal ray entering the quarter-circular material at height `L`,
Snell's law at the curved and flat faces gives

`θ = arcsin (n * sin (arcsin (L / R) - arcsin (L / (n * R))))`,

which is answer choice C and formalizes
`thm:physics:phyx_mini_0018:target`.
-/
theorem problem_phyx_mini_0018
    (setup : QuarterCircleRefractionSetup)
    (h_parameters : HasPhysicalParameters setup)
    (h_angles : HasPhysicalRayAngles setup)
    (h_geometry : ObeysQuarterCircleGeometry setup)
    (h_snell : ∀ interface, SatisfiesSnellLawAt setup interface) :
    setup.emergenceAngleRad =
      Real.arcsin
        (setup.material.refractiveIndex *
          Real.sin
            (Real.arcsin
                (lengthInMeters setup.incomingHeightAboveBase /
                  lengthInMeters setup.radius) -
              Real.arcsin
                (lengthInMeters setup.incomingHeightAboveBase /
                  (setup.material.refractiveIndex *
                    lengthInMeters setup.radius)))) := by
  have h_refraction_eq :
      setup.curvedRefractionAngleRad =
        Real.arcsin
          (lengthInMeters setup.incomingHeightAboveBase /
            (setup.material.refractiveIndex *
              lengthInMeters setup.radius)) :=
    curvedRefractionAngle_eq_arcsin
      setup h_parameters h_angles h_geometry (h_snell .curvedEntry)
  rcases h_parameters with
    ⟨h_vacuum, _h_vacuum_lt_material, _h_radius_pos, _h_height_pos,
      _h_height_lt_radius⟩
  rcases h_angles with
    ⟨_h_incidence, _h_refraction, _h_internal, h_emergence⟩
  rcases h_geometry with
    ⟨_h_horizontal, h_incidence_eq, h_internal_eq⟩
  have h_exit_snell := h_snell .flatExit
  change
    setup.material.refractiveIndex *
        Real.sin setup.internalAngleBelowBaseRad =
      setup.vacuum.refractiveIndex *
        Real.sin setup.emergenceAngleRad
    at h_exit_snell
  rw [h_vacuum, one_mul] at h_exit_snell
  have h_emergence_lower :
      -(Real.pi / 2) ≤ setup.emergenceAngleRad := by
    calc
      -(Real.pi / 2) ≤ 0 :=
        neg_nonpos.mpr (div_nonneg (le_of_lt Real.pi_pos) (by norm_num))
      _ ≤ setup.emergenceAngleRad := le_of_lt h_emergence.1
  calc
    setup.emergenceAngleRad =
        Real.arcsin (Real.sin setup.emergenceAngleRad) :=
      (Real.arcsin_sin
        h_emergence_lower
        (le_of_lt h_emergence.2)).symm
    _ =
        Real.arcsin
          (setup.material.refractiveIndex *
            Real.sin setup.internalAngleBelowBaseRad) :=
      congrArg Real.arcsin h_exit_snell.symm
    _ =
        Real.arcsin
          (setup.material.refractiveIndex *
            Real.sin
              (Real.arcsin
                  (lengthInMeters setup.incomingHeightAboveBase /
                    lengthInMeters setup.radius) -
                Real.arcsin
                  (lengthInMeters setup.incomingHeightAboveBase /
                    (setup.material.refractiveIndex *
                      lengthInMeters setup.radius)))) := by
      rw [h_internal_eq, h_incidence_eq, h_refraction_eq]

end PhyXMiniProblems.ProblemPhyXMini0018
