import Mathlib
import Physlib.Units.WithDim.Basic
import Physlib.SpaceAndTime.Space.LengthUnit

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0030

/-!
# Overall magnification of a lens--mirror--lens optical path

The figure places an object, a converging thin lens, and a convex spherical
mirror on one horizontal optical axis. Light passes through the lens, reflects
at the mirror, and passes through the same lens a second time. Signed object
and image distances use the Gaussian convention at each encounter.
-/

/-- A signed physical length, independent of the unit used to read it. -/
abbrev OpticalLength : Type := Dimensionful (WithDim Dimension.L𝓭 ℝ)

/-- The physical length having the given scalar readout in `unit`. -/
def lengthIn (unit : LengthUnit) (magnitude : ℝ) : OpticalLength :=
  CarriesDimension.toDimensionful { UnitChoices.SI with length := unit } ⟨magnitude⟩

/-- The signed scalar readout of a physical length in meters. -/
def metersValue (length : OpticalLength) : ℝ :=
  (length UnitChoices.SI).val

/-- The two paraxial thin-lens types, distinguished by the sign of focal length. -/
inductive ThinLensKind where
  | converging
  | diverging
  deriving DecidableEq, Repr

/-- The two spherical-mirror types viewed from the incident-light side. -/
inductive SphericalMirrorKind where
  | concave
  | convex
  deriving DecidableEq, Repr

/--
The physical objects and labeled axial positions in the figure. The focal
lengths are signed physical lengths; the axial positions are signed
coordinates on the common horizontal optical axis.
-/
structure LensMirrorSetup where
  /-- Figure label `Object`. -/
  objectAxialPosition : OpticalLength
  /-- Figure label `Lens`. -/
  lensAxialPosition : OpticalLength
  /-- Figure label `Mirror`. -/
  mirrorAxialPosition : OpticalLength
  lensKind : ThinLensKind
  mirrorKind : SphericalMirrorKind
  lensFocalLength : OpticalLength
  mirrorFocalLength : OpticalLength

/-- The meter readout of the directed separation from `left` to `right`. -/
def axialSeparationMeters (left right : OpticalLength) : ℝ :=
  metersValue right - metersValue left

/--
The element types and numerical data read from the problem and its figure:
the biconvex lens is converging, the pictured mirror is convex, the object is
`1.00 m` left of the lens, the mirror is `1.00 m` right of it, and the signed
focal lengths are `+80.0 cm` and `-50.0 cm`, respectively.
-/
def MatchesFigureReadout (setup : LensMirrorSetup) : Prop :=
  setup.lensKind = .converging ∧
    setup.mirrorKind = .convex ∧
    axialSeparationMeters setup.objectAxialPosition setup.lensAxialPosition = 1 ∧
    axialSeparationMeters setup.lensAxialPosition setup.mirrorAxialPosition = 1 ∧
    setup.lensFocalLength = lengthIn LengthUnit.centimeters 80 ∧
    setup.mirrorFocalLength = lengthIn LengthUnit.centimeters (-50)

/--
The paraxial Gaussian imaging law `1/f = 1/p + 1/q`, written in the
division-free, dimensionally homogeneous form `f * (p + q) = p * q`.
It is required in every choice of units.
-/
def GaussianImagingLaw
    (focalLength objectDistance imageDistance : OpticalLength) : Prop :=
  ∀ units : UnitChoices,
    focalLength units * (objectDistance units + imageDistance units) =
      objectDistance units * imageDistance units

/--
The signed transverse-magnification law `m = -q/p`. The ratio is
dimensionless and therefore has the same value in every choice of units.
-/
def TransverseMagnificationLaw
    (objectDistance imageDistance : OpticalLength) (magnification : ℝ) : Prop :=
  ∀ units : UnitChoices,
    magnification = - (imageDistance units).val / (objectDistance units).val

/-- The overall magnification of three successive imaging encounters is their product. -/
def ThreeStageMagnificationLaw
    (outboundLens mirror returnLens overall : ℝ) : Prop :=
  overall = outboundLens * mirror * returnLens

/--
For the pictured system, applying the Gaussian imaging and signed
magnification laws to the outbound lens, convex mirror, and return pass
through the lens gives overall magnification `-0.800` (answer choice D).

The propagation equations connect the outbound lens image to the mirror's
signed object distance, and the mirror image to the return-pass lens object
distance. Thus none of the intermediate image locations or magnifications is
assumed numerically.

Blueprint: `thm:physics:phyx_mini_0030:target`.
-/
theorem problem_phyx_mini_0030
    (setup : LensMirrorSetup)
    (outboundLensObjectDistance outboundLensImageDistance : OpticalLength)
    (mirrorObjectDistance mirrorImageDistance : OpticalLength)
    (returnLensObjectDistance returnLensImageDistance : OpticalLength)
    (outboundLensMagnification mirrorMagnification returnLensMagnification : ℝ)
    (overallMagnification : ℝ)
    (h_figure : MatchesFigureReadout setup)
    (h_outbound_object_geometry :
      metersValue outboundLensObjectDistance =
        axialSeparationMeters setup.objectAxialPosition setup.lensAxialPosition)
    (h_outbound_imaging :
      GaussianImagingLaw setup.lensFocalLength
        outboundLensObjectDistance outboundLensImageDistance)
    (h_outbound_magnification :
      TransverseMagnificationLaw outboundLensObjectDistance outboundLensImageDistance
        outboundLensMagnification)
    (h_mirror_object_geometry :
      metersValue mirrorObjectDistance =
        axialSeparationMeters setup.lensAxialPosition setup.mirrorAxialPosition -
          metersValue outboundLensImageDistance)
    (h_mirror_imaging :
      GaussianImagingLaw setup.mirrorFocalLength mirrorObjectDistance mirrorImageDistance)
    (h_mirror_magnification :
      TransverseMagnificationLaw mirrorObjectDistance mirrorImageDistance
        mirrorMagnification)
    (h_return_object_geometry :
      metersValue returnLensObjectDistance =
        axialSeparationMeters setup.lensAxialPosition setup.mirrorAxialPosition -
          metersValue mirrorImageDistance)
    (h_return_imaging :
      GaussianImagingLaw setup.lensFocalLength
        returnLensObjectDistance returnLensImageDistance)
    (h_return_magnification :
      TransverseMagnificationLaw returnLensObjectDistance returnLensImageDistance
        returnLensMagnification)
    (h_composition :
      ThreeStageMagnificationLaw outboundLensMagnification mirrorMagnification
        returnLensMagnification overallMagnification) :
    overallMagnification = (-0.800 : ℝ) := by
  rcases h_figure with
    ⟨_, _, h_object_lens_separation, h_lens_mirror_separation,
      h_lens_focal_length, h_mirror_focal_length⟩

  have h_lens_focal_value : metersValue setup.lensFocalLength = (4 / 5 : ℝ) := by
    rw [h_lens_focal_length]
    change
      (((CarriesDimension.toDimensionful
        {UnitChoices.SI with length := LengthUnit.centimeters}
        (⟨80⟩ : WithDim Dimension.L𝓭 ℝ)).1 UnitChoices.SI).val = (4 / 5 : ℝ))
    rw [CarriesDimension.toDimensionful_apply_apply]
    simp only [WithDim.dim_apply, WithDim.smul_val, NNReal.smul_def]
    simp [UnitChoices.dimScale, Dimension.L𝓭]
    rw [LengthUnit.centimeters, LengthUnit.scale_div_self]
    change ((1 / 10 : ℝ) ^ 2) * 80 = 4 / 5
    norm_num

  have h_mirror_focal_value : metersValue setup.mirrorFocalLength = (-1 / 2 : ℝ) := by
    rw [h_mirror_focal_length]
    change
      (((CarriesDimension.toDimensionful
        {UnitChoices.SI with length := LengthUnit.centimeters}
        (⟨-50⟩ : WithDim Dimension.L𝓭 ℝ)).1 UnitChoices.SI).val = (-1 / 2 : ℝ))
    rw [CarriesDimension.toDimensionful_apply_apply]
    simp only [WithDim.dim_apply, WithDim.smul_val, NNReal.smul_def]
    simp [UnitChoices.dimScale, Dimension.L𝓭]
    change
      -(((LengthUnit.centimeters / LengthUnit.meters : NNReal) : ℝ) * 50) = -1 / 2
    rw [LengthUnit.centimeters, LengthUnit.scale_div_self]
    change -(((1 / 10 : ℝ) ^ 2) * 50) = -1 / 2
    norm_num

  have h_outbound_object_value :
      metersValue outboundLensObjectDistance = (1 : ℝ) := by
    calc
      metersValue outboundLensObjectDistance =
          axialSeparationMeters setup.objectAxialPosition setup.lensAxialPosition :=
        h_outbound_object_geometry
      _ = 1 := h_object_lens_separation

  have h_outbound_scalar :
      metersValue setup.lensFocalLength *
          (metersValue outboundLensObjectDistance +
            metersValue outboundLensImageDistance) =
        metersValue outboundLensObjectDistance *
          metersValue outboundLensImageDistance := by
    have h :=
      congrArg WithDim.val (h_outbound_imaging UnitChoices.SI)
    simpa only [metersValue, WithDim.withDim_hMul_val, WithDim.val_add] using h

  have h_outbound_image_value :
      metersValue outboundLensImageDistance = (4 : ℝ) := by
    nlinarith [h_outbound_scalar, h_lens_focal_value, h_outbound_object_value]

  have h_mirror_object_value :
      metersValue mirrorObjectDistance = (-3 : ℝ) := by
    rw [h_mirror_object_geometry, h_lens_mirror_separation, h_outbound_image_value]
    norm_num

  have h_mirror_scalar :
      metersValue setup.mirrorFocalLength *
          (metersValue mirrorObjectDistance + metersValue mirrorImageDistance) =
        metersValue mirrorObjectDistance * metersValue mirrorImageDistance := by
    have h :=
      congrArg WithDim.val (h_mirror_imaging UnitChoices.SI)
    simpa only [metersValue, WithDim.withDim_hMul_val, WithDim.val_add] using h

  have h_mirror_image_value :
      metersValue mirrorImageDistance = (-3 / 5 : ℝ) := by
    nlinarith [h_mirror_scalar, h_mirror_focal_value, h_mirror_object_value]

  have h_return_object_value :
      metersValue returnLensObjectDistance = (8 / 5 : ℝ) := by
    rw [h_return_object_geometry, h_lens_mirror_separation, h_mirror_image_value]
    norm_num

  have h_return_scalar :
      metersValue setup.lensFocalLength *
          (metersValue returnLensObjectDistance + metersValue returnLensImageDistance) =
        metersValue returnLensObjectDistance * metersValue returnLensImageDistance := by
    have h :=
      congrArg WithDim.val (h_return_imaging UnitChoices.SI)
    simpa only [metersValue, WithDim.withDim_hMul_val, WithDim.val_add] using h

  have h_return_image_value :
      metersValue returnLensImageDistance = (8 / 5 : ℝ) := by
    nlinarith [h_return_scalar, h_lens_focal_value, h_return_object_value]

  have h_outbound_magnification_value :
      outboundLensMagnification = (-4 : ℝ) := by
    calc
      outboundLensMagnification =
          -metersValue outboundLensImageDistance /
            metersValue outboundLensObjectDistance := by
        simpa only [metersValue] using
          h_outbound_magnification UnitChoices.SI
      _ = -4 := by
        rw [h_outbound_image_value, h_outbound_object_value]
        norm_num

  have h_mirror_magnification_value :
      mirrorMagnification = (-1 / 5 : ℝ) := by
    calc
      mirrorMagnification =
          -metersValue mirrorImageDistance / metersValue mirrorObjectDistance := by
        simpa only [metersValue] using
          h_mirror_magnification UnitChoices.SI
      _ = -1 / 5 := by
        rw [h_mirror_image_value, h_mirror_object_value]
        norm_num

  have h_return_magnification_value :
      returnLensMagnification = (-1 : ℝ) := by
    calc
      returnLensMagnification =
          -metersValue returnLensImageDistance /
            metersValue returnLensObjectDistance := by
        simpa only [metersValue] using
          h_return_magnification UnitChoices.SI
      _ = -1 := by
        rw [h_return_image_value, h_return_object_value]
        norm_num

  calc
    overallMagnification =
        outboundLensMagnification * mirrorMagnification * returnLensMagnification :=
      h_composition
    _ = (-0.800 : ℝ) := by
      rw [h_outbound_magnification_value, h_mirror_magnification_value,
        h_return_magnification_value]
      norm_num

end PhyXMiniProblems.ProblemPhyXMini0030
