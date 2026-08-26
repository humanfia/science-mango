import FamilyStickyGrounding.FamilyStickyHierarchyWZ2TranslatedCollisionCellPopularFloorUnionV1
import Submission.Kakeya.ConvexFactoring.FrameBoxCoordinateWindowEquiv

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace FamilyStickyHierarchyWZ2TranslatedSharedHundredHullVolumeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2TranslatedShadingUnionCovarianceV1
open FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1
open FamilyStickyWZ2ShearParameterPackingV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyWZ2SharedHundredSourceConstantEndpointV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellCanonicalRowScaleFloorV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Explicit volume of the finite-shear shared `100T` hull

The WZ2 shear copy with parameter `d` acts by
`(x,y,z) ↦ (x, y + d*z, z)`.  A radius-`r` unit tube lies, in every standard
coordinate, within `1+r` of its axis base.  On the finite shear grid,
`|d| ≤ siteCount * |spacing|`.  Consequently every shear image lies in one
explicit standard-coordinate `FrameBox` centered at the source axis base:

* the `x` and `z` half-widths are `L = 1+r`;
* the `y` half-width is `L + D * (|base_z| + L)`, where
  `D = siteCount * |spacing|`.

The box is convex and closed, so it contains the closed convex hull of all
copies.  Its volume is exactly
`8 * L^2 * (L + D * (|base_z| + L))`.

For the hierarchy application `r = 100*delta`.  The remaining dependence on
the absolute source height is honest: the current `UniformTubeFamily` and
fixed-vertical-chart APIs constrain directions but contain no absolute
`z`-position normalization, while the ambient shear displacement is `d*z`.
No hull-volume estimate is accepted as a premise.
-/

/-- Coordinate reach of a unit tube of radius `radius` from its axis base. -/
def tubeReach (radius : NNReal) : NNReal := 1 + radius

/-- Maximum absolute shear parameter on the declared finite grid. -/
def shearGridMagnitude (spacing : Real) (siteCount : Nat) : NNReal :=
  ⟨(siteCount : Real) * |spacing|,
    mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)⟩

/-- Absolute vertical coordinate of the source axis base. -/
def sourceBaseZAbs {radius : NNReal} (T : Tube radius) : NNReal :=
  ⟨|T.axis.base 2|, abs_nonneg _⟩

/-- A point of a radius-`radius` unit tube is within `1+radius` of the axis
base in every standard coordinate. -/
theorem abs_tube_coord_sub_base_le_tubeReach
    {radius : NNReal} (T : Tube radius) {p : Space}
    (hp : p ∈ T.carrier) (i : Fin 3) :
    |p i - T.axis.base i| ≤ (tubeReach radius : Real) := by
  rw [Tube.carrier,
    T.axis.isCompact_carrier.cthickening_eq_biUnion_closedBall
      (show 0 ≤ (radius : Real) by positivity)] at hp
  simp only [Set.mem_iUnion, Metric.mem_closedBall] at hp
  obtain ⟨y, hyAxis, hpy⟩ := hp
  rw [T.axis.carrier_eq_image] at hyAxis
  obtain ⟨s, hs, rfl⟩ := hyAxis
  have hnear :
      |p i - (T.axis.base + s • T.axis.direction) i| ≤
        (radius : Real) := by
    simpa only [Real.dist_eq] using
      (PiLp.dist_apply_le p
        (T.axis.base + s • T.axis.direction) i).trans hpy
  have hsabs : |s| ≤ 1 := by
    rw [abs_of_nonneg hs.1]
    exact hs.2
  have hdir : |T.axis.direction i| ≤ 1 := by
    have h := PiLp.norm_apply_le T.axis.direction i
    rw [T.axis.norm_direction] at h
    simpa only [Real.norm_eq_abs] using h
  have haxis :
      |(T.axis.base + s • T.axis.direction) i - T.axis.base i| ≤ 1 := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      add_sub_cancel_left]
    rw [abs_mul]
    exact (mul_le_mul hsabs hdir (abs_nonneg _) (by positivity)).trans_eq
      (by ring)
  exact (abs_sub_le _ _ _).trans (add_le_add hnear haxis) |>.trans_eq
    (by simp [tubeReach]; ring)

/-- Half-widths of the explicit standard-coordinate shear-grid box. -/
def shearGridTubeHalf {radius : NNReal} (T : Tube radius)
    (spacing : Real) (siteCount : Nat) (i : Fin 3) : NNReal :=
  if i = 1 then
    tubeReach radius + shearGridMagnitude spacing siteCount *
      (sourceBaseZAbs T + tubeReach radius)
  else tubeReach radius

/-- The standard-coordinate box containing every finite-grid shear image. -/
def shearGridTubeFrameBox {radius : NNReal} (T : Tube radius)
    (spacing : Real) (siteCount : Nat) : FrameBox where
  center := T.axis.base
  frame := EuclideanSpace.basisFun (Fin 3) Real
  side := fun i => 2 * shearGridTubeHalf T spacing siteCount i

/-- Explicit volume of the shear-grid box. -/
def shearGridTubeVolumeBound {radius : NNReal} (T : Tube radius)
    (spacing : Real) (siteCount : Nat) : ENNReal :=
  8 * (tubeReach radius : ENNReal) ^ 2 *
    ((tubeReach radius + shearGridMagnitude spacing siteCount *
      (sourceBaseZAbs T + tubeReach radius) : NNReal) : ENNReal)

@[simp]
theorem inner_standardShearFrame (p : Space) (i : Fin 3) :
    ⟪(EuclideanSpace.basisFun (Fin 3) Real) i, p⟫_Real = p i := by
  rw [real_inner_comm]
  exact EuclideanSpace.inner_basisFun_real (Fin 3) p i

/-- Exact finite-grid bound for the actual shear parameter. -/
theorem abs_shearGridParameter_le
    {siteCount : Nat} (spacing : Real) (j : Fin siteCount) :
    |((j : Nat) : Real) * spacing| ≤
      (shearGridMagnitude spacing siteCount : Real) := by
  have hjNat : (j : Nat) ≤ siteCount := Nat.le_of_lt j.isLt
  have hjReal : ((j : Nat) : Real) ≤ siteCount := by
    exact_mod_cast hjNat
  rw [shearGridMagnitude, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg (j : Nat))]
  exact mul_le_mul_of_nonneg_right hjReal (abs_nonneg spacing)

/-- Every literal finite-grid shear image of the whole tube is contained in
the explicit box. -/
theorem shearGrid_image_tube_subset_frameBox
    {radius : NNReal} (T : Tube radius)
    (spacing : Real) {siteCount : Nat} (j : Fin siteCount) :
    ambientCinematicTranslation 0 0 (((j : Nat) : Real) * spacing) ''
        T.carrier ⊆
      (shearGridTubeFrameBox T spacing siteCount).carrier := by
  rintro q ⟨p, hp, rfl⟩
  have hcoord (i : Fin 3) :
      |p i - T.axis.base i| ≤ (tubeReach radius : Real) :=
    abs_tube_coord_sub_base_le_tubeReach T hp i
  have hpz : |p 2| ≤
      (sourceBaseZAbs T + tubeReach radius : NNReal) := by
    calc
      |p 2| ≤ |p 2 - T.axis.base 2| + |T.axis.base 2| := by
        simpa only [sub_add_cancel] using
          (abs_add_le (p 2 - T.axis.base 2) (T.axis.base 2))
      _ ≤ (tubeReach radius : Real) + |T.axis.base 2| :=
        add_le_add (hcoord 2) le_rfl
      _ = (sourceBaseZAbs T + tubeReach radius : NNReal) := by
        change (tubeReach radius : Real) + |T.axis.base 2| =
          |T.axis.base 2| + (tubeReach radius : Real)
        ring
  have hd := abs_shearGridParameter_le spacing j
  have hy :
      |(p 1 + (((j : Nat) : Real) * spacing) * p 2) -
          T.axis.base 1| ≤
        (tubeReach radius + shearGridMagnitude spacing siteCount *
          (sourceBaseZAbs T + tubeReach radius) : NNReal) := by
    calc
      |(p 1 + (((j : Nat) : Real) * spacing) * p 2) -
          T.axis.base 1| =
          |(p 1 - T.axis.base 1) +
            (((j : Nat) : Real) * spacing) * p 2| := by ring_nf
      _ ≤ |p 1 - T.axis.base 1| +
          |(((j : Nat) : Real) * spacing) * p 2| := abs_add_le _ _
      _ = |p 1 - T.axis.base 1| +
          |((j : Nat) : Real) * spacing| * |p 2| := by rw [abs_mul]
      _ ≤ (tubeReach radius : Real) +
          (shearGridMagnitude spacing siteCount : Real) *
            ((sourceBaseZAbs T + tubeReach radius : NNReal) : Real) := by
        exact add_le_add (hcoord 1)
          (mul_le_mul hd hpz (abs_nonneg _) (by positivity))
      _ = (tubeReach radius + shearGridMagnitude spacing siteCount *
          (sourceBaseZAbs T + tubeReach radius) : NNReal) := by
        norm_cast
  rw [FrameBox.carrier_eq_centeredCoordinateWindow,
    TransverseCoordinateOverlap.mem_centeredCoordinateWindow_iff]
  intro i
  change |⟪(EuclideanSpace.basisFun (Fin 3) Real) i,
      ambientCinematicTranslation 0 0 (((j : Nat) : Real) * spacing) p⟫_Real -
      ⟪(EuclideanSpace.basisFun (Fin 3) Real) i, T.axis.base⟫_Real| ≤
    (((2 * shearGridTubeHalf T spacing siteCount i) / 2 : NNReal) : Real)
  rw [inner_standardShearFrame, inner_standardShearFrame]
  rw [show (2 * shearGridTubeHalf T spacing siteCount i) / 2 =
    shearGridTubeHalf T spacing siteCount i by simp]
  fin_cases i
  · simpa [shearGridTubeHalf, ambientCinematicTranslation, point3] using hcoord 0
  · simpa [shearGridTubeHalf, ambientCinematicTranslation, point3] using hy
  · simpa [shearGridTubeHalf, ambientCinematicTranslation, point3] using hcoord 2

/-- Exact product computation for the explicit shear-grid box. -/
theorem volume_shearGridTubeFrameBox
    {radius : NNReal} (T : Tube radius)
    (spacing : Real) (siteCount : Nat) :
    volume (shearGridTubeFrameBox T spacing siteCount).carrier =
      shearGridTubeVolumeBound T spacing siteCount := by
  rw [FrameBox.volume_carrier, Fin.prod_univ_three]
  simp only [shearGridTubeFrameBox, shearGridTubeHalf]
  simp [shearGridTubeVolumeBound]
  ring

/-! ## The shared source `100T` specialization -/

/-- The explicit frame box for all shear copies of the shared source `100T`. -/
def translatedSharedHundredShearFrameBox
    {kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    (spacing : Real) (siteCount : Nat)
    (fine : UniformTubeFamily delta kappa)
    (shared : SharedHundredSourceContainer fine) : FrameBox :=
  shearGridTubeFrameBox (hundredTube shared.container) spacing siteCount

/-- Every affine shared-`100T` copy is contained in the explicit box. -/
theorem translatedSharedHundredBody_subset_shearFrameBox
    {kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    {siteCount : Nat} (spacing : Real)
    (fine : UniformTubeFamily delta kappa)
    (shared : SharedHundredSourceContainer fine) (j : Fin siteCount) :
    (translatedSharedHundredBodyFamily
        (shearReducedShift spacing (siteCount := siteCount)) fine shared j :
        Set Space) ⊆
      (translatedSharedHundredShearFrameBox
        spacing siteCount fine shared).carrier := by
  rw [coe_translatedSharedHundredBodyFamily]
  simpa [shearReducedShift, translatedSharedHundredShearFrameBox] using
    (shearGrid_image_tube_subset_frameBox
      (hundredTube shared.container) spacing j)

/-- The closed convex hull of all shared-`100T` shear copies is contained in
the same explicit convex frame box. -/
theorem translatedSharedHundredHullContainer_subset_shearFrameBox
    {kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    {siteCount : Nat} (hsiteCount : 0 < siteCount) (spacing : Real)
    (fine : UniformTubeFamily delta kappa)
    (shared : SharedHundredSourceContainer fine) :
    (translatedSharedHundredHullContainer
        (shearReducedShift spacing (siteCount := siteCount)) fine shared :
        Set Space) ⊆
      (translatedSharedHundredShearFrameBox
        spacing siteCount fine shared).carrier := by
  classical
  change
    (hullContainer
        (translatedSharedHundredBodyFamily
          (shearReducedShift spacing (siteCount := siteCount)) fine shared)
        Finset.univ : Set Space) ⊆
      ((translatedSharedHundredShearFrameBox
        spacing siteCount fine shared).body : Set Space)
  apply hullContainer_subset
    (translatedSharedHundredBodyFamily
      (shearReducedShift spacing (siteCount := siteCount)) fine shared)
    ⟨⟨0, hsiteCount⟩, Finset.mem_univ _⟩
  intro j _hj
  exact translatedSharedHundredBody_subset_shearFrameBox
    spacing fine shared j

/-- Fully explicit volume bound for the translated shared-`100T` hull. -/
theorem volume_translatedSharedHundredHullContainer_le_explicit
    {kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    {siteCount : Nat} (hsiteCount : 0 < siteCount) (spacing : Real)
    (fine : UniformTubeFamily delta kappa)
    (shared : SharedHundredSourceContainer fine) :
    volume
        (translatedSharedHundredHullContainer
          (shearReducedShift spacing (siteCount := siteCount)) fine shared :
          Set Space) ≤
      shearGridTubeVolumeBound
        (hundredTube shared.container) spacing siteCount := by
  calc
    volume
        (translatedSharedHundredHullContainer
          (shearReducedShift spacing (siteCount := siteCount)) fine shared :
          Set Space) ≤
        volume
          (translatedSharedHundredShearFrameBox
            spacing siteCount fine shared).carrier :=
      measure_mono
        (translatedSharedHundredHullContainer_subset_shearFrameBox
          hsiteCount spacing fine shared)
    _ = shearGridTubeVolumeBound
          (hundredTube shared.container) spacing siteCount :=
      volume_shearGridTubeFrameBox
        (hundredTube shared.container) spacing siteCount

/-- The radius occurring in the explicit bound is literally `1+100*delta`. -/
@[simp]
theorem tubeReach_hundredRadius (delta : NNReal) :
    tubeReach (hundredRadius delta) = 1 + 100 * delta :=
  rfl

#print axioms abs_tube_coord_sub_base_le_tubeReach
#print axioms shearGrid_image_tube_subset_frameBox
#print axioms volume_shearGridTubeFrameBox
#print axioms translatedSharedHundredBody_subset_shearFrameBox
#print axioms translatedSharedHundredHullContainer_subset_shearFrameBox
#print axioms volume_translatedSharedHundredHullContainer_le_explicit

end
end FamilyStickyHierarchyWZ2TranslatedSharedHundredHullVolumeV1
