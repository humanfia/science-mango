import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Projection
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0163

open Dimension

/-!
# Irradiance increase produced by a plane mirror

The textual problem places an isotropic point source `S` midway between a
plane mirror `M` and the observation point `P` on a viewing screen `A`.  Both
marked separations are the physical length `d`.  In geometrical optics, the
reflected contribution at `P` is computed from the virtual image of `S` behind
the mirror.  That image is `3d` from `P`, whereas the real source is `d` from
`P`.

Positions are points of a two-dimensional Euclidean cross-section whose
coordinates are SI-metre readouts.  Length, radiant power, and irradiance are
represented by Physlib dimensionful quantities.  Real numbers occur only for
coordinate readouts, dimensionless reflectance and intensity multipliers, and
explicit SI readouts.

The source file's referenced image is inconsistent with the textual problem:
it shows a lens, stamp, focal point, and virtual image rather than `M`, `S`,
`P`, and `A`.  Consequently `MatchesTextualMirrorScreenDiagram` formalizes the
unambiguous diagram relations stated in the chapter text, not the unrelated
bitmap.
-/

/-- The Euclidean cross-section containing the mirror, source, and screen. -/
abbrev OpticalPlane : Type := EuclideanSpace ℝ (Fin 2)

/-- A nonnegative physical length, independent of the chosen unit readout. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative radiant power, with physical dimension `mass * length² / time³`. -/
abbrev RadiantPowerQuantity : Type :=
  Dimensionful
    (WithDim
      (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹)
      NNReal)

/-- A nonnegative optical irradiance (power per area). -/
abbrev IrradianceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical length as a scalar number of SI metres. -/
def lengthInMetres (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a radiant power as a scalar number of SI watts. -/
def radiantPowerInWatts (power : RadiantPowerQuantity) : ℝ :=
  ((power UnitChoices.SI).val : ℝ)

/-- Read an irradiance as a scalar number of SI watts per square metre. -/
def irradianceInWattsPerSquareMetre (irradiance : IrradianceQuantity) : ℝ :=
  ((irradiance UnitChoices.SI).val : ℝ)

/-- The isotropic point source `S`, including its position and radiant power. -/
structure IsotropicPointLightSource where
  position : OpticalPlane
  radiantPower : RadiantPowerQuantity

/-!
An idealized plane mirror in the two-dimensional cross-section.  Its affine
line is the complete carrier used by the method of images.  The reference
point is the point on `M` level with `S` in the textual diagram.
-/
structure PlaneMirror where
  surface : AffineSubspace ℝ OpticalPlane
  surfaceNonempty : Nonempty surface
  surface_is_line : Module.finrank ℝ surface.direction = 1
  referencePoint : OpticalPlane
  referencePoint_mem : referencePoint ∈ surface
  reflectance : ℝ

namespace PlaneMirror

/-- The virtual image of a point under reflection in the mirror carrier. -/
def virtualImage (mirror : PlaneMirror) (point : OpticalPlane) : OpticalPlane :=
  letI : Nonempty mirror.surface := mirror.surfaceNonempty
  EuclideanGeometry.reflection mirror.surface point

end PlaneMirror

/-- The viewing screen `A` and its marked observation point `P`. -/
structure ViewingScreen where
  surface : AffineSubspace ℝ OpticalPlane
  surfaceNonempty : Nonempty surface
  pointP : OpticalPlane
  pointP_mem : pointP ∈ surface

/-!
All named quantities in the mirror/source/screen experiment.  `directAtP` is
the measured baseline irradiance before the mirror is installed;
`reflectedAtP` is the mirror contribution; and `totalWithMirrorAtP` is the
irradiance after installation.  No field contains their requested ratio.
-/
structure MirrorIntensitySetup where
  sourceS : IsotropicPointLightSource
  mirrorM : PlaneMirror
  screenA : ViewingScreen
  opticalAxis : OpticalPlane
  distanceD : LengthQuantity
  directAtP : IrradianceQuantity
  reflectedAtP : IrradianceQuantity
  totalWithMirrorAtP : IrradianceQuantity

/-!
The two distance labels and the horizontal alignment stated by the textual
diagram.  The unit optical-axis vector points from the mirror through `S`
toward `P`; hence `M`--`S` and `S`--`P` each have length `d`.
-/
structure MatchesTextualMirrorScreenDiagram
    (setup : MirrorIntensitySetup) : Prop where
  opticalAxis_unit : ‖setup.opticalAxis‖ = 1
  source_position :
    setup.sourceS.position =
      setup.mirrorM.referencePoint +
        lengthInMetres setup.distanceD • setup.opticalAxis
  point_P_position :
    setup.screenA.pointP =
      setup.sourceS.position +
        lengthInMetres setup.distanceD • setup.opticalAxis

/-!
Strictly positive distance, emitted power, and measured baseline irradiance.
These exclude the degenerate cases in which an intensity multiplier is not
defined.
-/
structure HasPhysicalMirrorIntensityParameters
    (setup : MirrorIntensitySetup) : Prop where
  distance_positive : 0 < lengthInMetres setup.distanceD
  radiantPower_positive : 0 < radiantPowerInWatts setup.sourceS.radiantPower
  directIrradiance_positive :
    0 < irradianceInWattsPerSquareMetre setup.directAtP

/-!
The ideal plane-mirror image law along the normal optical axis.  It is stated
for every signed axial displacement, independently of the displayed value
`d` and of any irradiance.  Thus it specifies the mirror geometry without
assuming the requested multiplier.
-/
structure SatisfiesIdealPlaneMirrorGeometry
    (setup : MirrorIntensitySetup) : Prop where
  reflects_normal_axis : ∀ axialDisplacementMetres : ℝ,
    setup.mirrorM.virtualImage
        (setup.mirrorM.referencePoint +
          axialDisplacementMetres • setup.opticalAxis) =
      setup.mirrorM.referencePoint -
        axialDisplacementMetres • setup.opticalAxis

/-!
The inverse-square relation for one isotropic point emitter.  `powerFraction`
is dimensionless; it is `1` for the direct source and the mirror reflectance
for the virtual source.  This governing law contains no source/mirror distance
ratio and no answer-choice value.
-/
def SatisfiesInverseSquareIrradiance
    (power : RadiantPowerQuantity)
    (powerFraction : ℝ)
    (emitter observer : OpticalPlane)
    (irradiance : IrradianceQuantity) : Prop :=
  irradianceInWattsPerSquareMetre irradiance * dist emitter observer ^ 2 =
    powerFraction * radiantPowerInWatts power / (4 * Real.pi)

/-!
The physical laws used in the computation: the installed mirror is perfectly
reflecting; the direct and virtual-image contributions obey the inverse-square
law; and geometrical-optics irradiances add incoherently at `P`.
-/
structure SatisfiesIdealPointSourceMirrorLaws
    (setup : MirrorIntensitySetup) : Prop where
  mirror_is_perfect : setup.mirrorM.reflectance = 1
  direct_inverse_square :
    SatisfiesInverseSquareIrradiance
      setup.sourceS.radiantPower 1 setup.sourceS.position
      setup.screenA.pointP setup.directAtP
  reflected_inverse_square :
    SatisfiesInverseSquareIrradiance
      setup.sourceS.radiantPower setup.mirrorM.reflectance
      (setup.mirrorM.virtualImage setup.sourceS.position)
      setup.screenA.pointP setup.reflectedAtP
  incoherent_superposition :
    irradianceInWattsPerSquareMetre setup.totalWithMirrorAtP =
      irradianceInWattsPerSquareMetre setup.directAtP +
        irradianceInWattsPerSquareMetre setup.reflectedAtP

/-- The mirror image of `S` is three marked distances from `P`. -/
lemma virtualImage_to_P_distance_eq_three_d
    (setup : MirrorIntensitySetup)
    (h_physical : HasPhysicalMirrorIntensityParameters setup)
    (h_figure : MatchesTextualMirrorScreenDiagram setup)
    (h_geometry : SatisfiesIdealPlaneMirrorGeometry setup) :
    dist (setup.mirrorM.virtualImage setup.sourceS.position)
        setup.screenA.pointP =
      3 * lengthInMetres setup.distanceD := by
  have hd : 0 < lengthInMetres setup.distanceD :=
    h_physical.distance_positive
  rw [dist_comm, h_figure.point_P_position, h_figure.source_position,
    h_geometry.reflects_normal_axis, dist_eq_norm]
  rw [show setup.mirrorM.referencePoint +
        lengthInMetres setup.distanceD • setup.opticalAxis +
        lengthInMetres setup.distanceD • setup.opticalAxis -
          (setup.mirrorM.referencePoint -
            lengthInMetres setup.distanceD • setup.opticalAxis) =
      (3 * lengthInMetres setup.distanceD) • setup.opticalAxis by
    module]
  simp only [norm_smul, h_figure.opticalAxis_unit, mul_one, Real.norm_eq_abs]
  rw [abs_of_pos]
  positivity

/-- By the inverse-square law, the reflected contribution is `1/9` of baseline. -/
lemma reflected_irradiance_eq_one_ninth_direct
    (setup : MirrorIntensitySetup)
    (h_physical : HasPhysicalMirrorIntensityParameters setup)
    (h_figure : MatchesTextualMirrorScreenDiagram setup)
    (h_geometry : SatisfiesIdealPlaneMirrorGeometry setup)
    (h_laws : SatisfiesIdealPointSourceMirrorLaws setup) :
    irradianceInWattsPerSquareMetre setup.reflectedAtP =
      irradianceInWattsPerSquareMetre setup.directAtP / 9 := by
  have hd : 0 < lengthInMetres setup.distanceD :=
    h_physical.distance_positive
  have h_direct_distance :
      dist setup.sourceS.position setup.screenA.pointP =
        lengthInMetres setup.distanceD := by
    rw [dist_comm, h_figure.point_P_position, dist_eq_norm]
    rw [show setup.sourceS.position +
          lengthInMetres setup.distanceD • setup.opticalAxis -
            setup.sourceS.position =
        lengthInMetres setup.distanceD • setup.opticalAxis by
      module]
    simp only [norm_smul, h_figure.opticalAxis_unit, mul_one,
      Real.norm_eq_abs]
    exact abs_of_pos hd
  have h_reflected_distance :=
    virtualImage_to_P_distance_eq_three_d setup h_physical h_figure h_geometry
  have h_direct := h_laws.direct_inverse_square
  have h_reflected := h_laws.reflected_inverse_square
  unfold SatisfiesInverseSquareIrradiance at h_direct h_reflected
  rw [h_direct_distance] at h_direct
  rw [h_laws.mirror_is_perfect, h_reflected_distance] at h_reflected
  norm_num at h_direct h_reflected
  have h_same :
      irradianceInWattsPerSquareMetre setup.reflectedAtP *
          (3 * lengthInMetres setup.distanceD) ^ 2 =
        irradianceInWattsPerSquareMetre setup.directAtP *
          lengthInMetres setup.distanceD ^ 2 :=
    h_reflected.trans h_direct.symm
  have h_ratio :
      9 * irradianceInWattsPerSquareMetre setup.reflectedAtP =
        irradianceInWattsPerSquareMetre setup.directAtP := by
    apply mul_right_cancel₀ (pow_ne_zero 2 hd.ne')
    calc
      (9 * irradianceInWattsPerSquareMetre setup.reflectedAtP) *
            lengthInMetres setup.distanceD ^ 2 =
          irradianceInWattsPerSquareMetre setup.reflectedAtP *
            (3 * lengthInMetres setup.distanceD) ^ 2 := by ring
      _ = irradianceInWattsPerSquareMetre setup.directAtP *
            lengthInMetres setup.distanceD ^ 2 := h_same
  linarith

/-- Labels of the four displayed multiple-choice multipliers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The decimal multiplier printed beside each answer label. -/
def displayedMultiplier : AnswerChoice → ℝ
  | .A => 95 / 100
  | .B => 1
  | .C => 105 / 100
  | .D => 111 / 100

/-- The dataset's recorded label, retained as metadata rather than a premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
A choice matches the physical multiplier when its displayed two-decimal value
is within half of `0.01` of the exact intensity ratio.
-/
def MatchesDisplayedMultiplier
    (setup : MirrorIntensitySetup) (choice : AnswerChoice) : Prop :=
  |irradianceInWattsPerSquareMetre setup.totalWithMirrorAtP /
        irradianceInWattsPerSquareMetre setup.directAtP -
      displayedMultiplier choice| ≤ (1 / 200 : ℝ)

/-- A displayed choice is the unique two-decimal match to the physical ratio. -/
def IsUniqueMatchingDisplayedMultiplier
    (setup : MirrorIntensitySetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedMultiplier setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedMultiplier setup other → other = choice

/-!
The mirror adds the virtual-source contribution `1/9` of the baseline, so the
total irradiance is multiplied by `1 + 1/9 = 10/9`.  This exact factor rounds
to `1.11`, uniquely selecting answer D.

Blueprint label: `thm:physics:phyx_mini_0163:target`.
-/
theorem problem_phyx_mini_0163
    (setup : MirrorIntensitySetup)
    (h_physical : HasPhysicalMirrorIntensityParameters setup)
    (h_figure : MatchesTextualMirrorScreenDiagram setup)
    (h_geometry : SatisfiesIdealPlaneMirrorGeometry setup)
    (h_laws : SatisfiesIdealPointSourceMirrorLaws setup) :
    irradianceInWattsPerSquareMetre setup.totalWithMirrorAtP =
        (10 / 9 : ℝ) *
          irradianceInWattsPerSquareMetre setup.directAtP ∧
      IsUniqueMatchingDisplayedMultiplier setup .D := by
  have h_reflected :=
    reflected_irradiance_eq_one_ninth_direct setup h_physical h_figure h_geometry
      h_laws
  have h_total :
      irradianceInWattsPerSquareMetre setup.totalWithMirrorAtP =
        (10 / 9 : ℝ) *
          irradianceInWattsPerSquareMetre setup.directAtP := by
    rw [h_laws.incoherent_superposition, h_reflected]
    ring
  have h_direct_pos := h_physical.directIrradiance_positive
  constructor
  · exact h_total
  · unfold IsUniqueMatchingDisplayedMultiplier
    constructor
    · unfold MatchesDisplayedMultiplier
      rw [h_total, mul_div_cancel_right₀ _ h_direct_pos.ne']
      norm_num [displayedMultiplier, abs_of_nonneg, abs_of_nonpos]
    · intro other h_other
      unfold MatchesDisplayedMultiplier at h_other
      rw [h_total, mul_div_cancel_right₀ _ h_direct_pos.ne'] at h_other
      cases other with
      | A =>
          norm_num [displayedMultiplier, abs_of_nonneg, abs_of_nonpos] at h_other
      | B =>
          norm_num [displayedMultiplier, abs_of_nonneg, abs_of_nonpos] at h_other
      | C =>
          norm_num [displayedMultiplier, abs_of_nonneg, abs_of_nonpos] at h_other
      | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0163
