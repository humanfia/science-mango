import Family8Grounding.Family8Family7NativeHighCriticalBallRestrictedSourceV1
import Family8Grounding.Family8SelectedParentPlankFineProxyCarrierV3
import Family8Grounding.Family8SelectedParentAffineShadingTransportV4
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7NativeHighCriticalBallAffineProxyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family6AffineConvexVolumeCoreV1
open Family8ContractedJohnActualTubeProxyV1
open Family8Family7NativeHighCriticalBallDatumV1
open Family8Family7NativeHighCriticalBallRestrictedSourceV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8SelectedParentPlankFineProxyDatumV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-!
# Honest affine image and tube proxy for a native-high critical ball

An arbitrary affine image of a round project tube is a convex body, not in
general another round project tube.  This file therefore keeps both honest
objects:

* the exact memberwise affine-image convex family and shading, on which mass,
  union volume, average multiplicity, and overlap essential distinctness are
  affine invariant;
* a genuine unit-axis tube proxy containing every affine image, under the two
  explicit longitudinal and transverse geometric inequalities.

No essential-distinctness claim is made for the enlarged proxy tubes.  That
is the remaining geometric adapter required by a recursive tube consumer.
-/

/-- Overlap essential distinctness for arbitrary convex bodies. -/
def ConvexOverlapEssentiallyDistinct (K L : ConvexBody Space) : Prop :=
  volume ((K : Set Space) ∩ (L : Set Space)) ≤
    (2 : ENNReal)⁻¹ *
      max (volume (K : Set Space)) (volume (L : Set Space))

/-- The overlap ratio is invariant under one common affine equivalence. -/
theorem convexOverlapEssentiallyDistinct_affineImage_of_tubes
    {radius : NNReal} (e : Space ≃ᵃ[Real] Space)
    (T U : Tube radius) (hTU : EssentiallyDistinct T U) :
    ConvexOverlapEssentiallyDistinct
      (affineImageConvexBody e T.body)
      (affineImageConvexBody e U.body) := by
  unfold ConvexOverlapEssentiallyDistinct
  change volume ((e '' T.carrier) ∩ (e '' U.carrier)) ≤
    (2 : ENNReal)⁻¹ *
      max (volume (e '' T.carrier)) (volume (e '' U.carrier))
  rw [← Set.image_inter e.injective]
  simp_rw [volume_image_affineEquiv]
  unfold EssentiallyDistinct at hTU
  let J := affineJacobian e
  calc
    J * volume (T.carrier ∩ U.carrier) ≤
        J * ((2 : ENNReal)⁻¹ *
          max (volume T.carrier) (volume U.carrier)) :=
      by gcongr
    _ = (2 : ENNReal)⁻¹ *
        max (J * volume T.carrier) (J * volume U.carrier) := by
      rcases le_total (volume T.carrier) (volume U.carrier) with h | h
      · have hJ : J * volume T.carrier ≤ J * volume U.carrier := by
          gcongr
        rw [max_eq_right h, max_eq_right hJ]
        ac_rfl
      · have hJ : J * volume U.carrier ≤ J * volume T.carrier := by
          gcongr
        rw [max_eq_left h, max_eq_left hJ]
        ac_rfl

/-- The exact affine-image convex family on the critical-ball subtype. -/
abbrev nativeHighCriticalBallAffineFamily
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (e : Space ≃ᵃ[Real] Space)
    (D : NativeBranchCore radius iota) (c : D.HighCenter) :
    ConvexFamily (NativeHighCriticalBallIndex D c) :=
  affineImageFamily e (nativeHighCriticalBallFamily D c).bodyFamily

/-- The literal affine image of the restricted source shading. -/
def nativeHighCriticalBallAffineShading
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (e : Space ≃ᵃ[Real] Space)
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (Y : Shading D.S.family.bodyFamily) :
    Shading (nativeHighCriticalBallAffineFamily e D c) :=
  affineImageShading e (nativeHighCriticalBallShading D c Y)

theorem nativeHighCriticalBallAffineShading_shadingMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (e : Space ≃ᵃ[Real] Space)
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (Y : Shading D.S.family.bodyFamily) :
    (nativeHighCriticalBallAffineShading e D c Y).shadingMass =
      affineJacobian e *
        (nativeHighCriticalBallShading D c Y).shadingMass :=
  affineImageShading_shadingMass e _

theorem nativeHighCriticalBallAffineShading_shadedUnion_volume
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (e : Space ≃ᵃ[Real] Space)
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (Y : Shading D.S.family.bodyFamily) :
    volume (nativeHighCriticalBallAffineShading e D c Y).shadedUnion =
      affineJacobian e *
        volume (nativeHighCriticalBallShading D c Y).shadedUnion :=
  affineImageShading_shadedUnion_volume e _

theorem nativeHighCriticalBallAffineShading_averageMultiplicity
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (e : Space ≃ᵃ[Real] Space)
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (Y : Shading D.S.family.bodyFamily) :
    (nativeHighCriticalBallAffineShading e D c Y).averageMultiplicity =
      (nativeHighCriticalBallShading D c Y).averageMultiplicity :=
  affineImageShading_averageMultiplicity e _

/-- Exact affine images retain overlap essential distinctness before any
tube-proxy enlargement. -/
theorem nativeHighCriticalBallAffineFamily_pairwise_overlapDistinct
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (e : Space ≃ᵃ[Real] Space)
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (datum : NativeHighCriticalBallDatum D c) :
    Set.Pairwise (Set.univ : Set (NativeHighCriticalBallIndex D c))
      (fun i j => ConvexOverlapEssentiallyDistinct
        (nativeHighCriticalBallAffineFamily e D c i)
        (nativeHighCriticalBallAffineFamily e D c j)) := by
  intro i _hi j _hj hij
  apply convexOverlapEssentiallyDistinct_affineImage_of_tubes
  exact datum.pairwise_essentiallyDistinct i.2 j.2
    (Subtype.coe_ne_coe.mpr hij)

/-- The genuine unit-axis tube proxy for the affine critical-ball family. -/
def nativeHighCriticalBallAffineProxyFamily
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (D : NativeBranchCore radius iota) (c : D.HighCenter) :
    UniformTubeFamily s (NativeHighCriticalBallIndex D c) where
  tubes i := affineAxisProxyTube s e (D.S.family.tubes i.1)
  refinement := UniformRefinement.ofFinset Finset.univ

@[simp] theorem nativeHighCriticalBallAffineProxyFamily_tubes
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (i : NativeHighCriticalBallIndex D c) :
    (nativeHighCriticalBallAffineProxyFamily s e D c).tubes i =
      affineAxisProxyTube s e (D.S.family.tubes i.1) :=
  rfl

/-- The two exact geometric inequalities needed to place every affine-image
shading carrier inside the genuine proxy tube, together with its `L_3` chart. -/
structure NativeHighCriticalBallAffineProxyGeometry
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (D : NativeBranchCore radius iota) (c : D.HighCenter) : Prop where
  axisLength : ∀ i : NativeHighCriticalBallIndex D c,
    ‖affineImageAxisVector e (D.S.family.tubes i.1)‖ ≤ 1
  transverseRadius :
    affineLinearOperatorNorm e * (radius : Real) ≤ (s : Real)
  chart : ∀ i : NativeHighCriticalBallIndex D c,
    (1 / 2 : Real) ≤
      |((nativeHighCriticalBallAffineProxyFamily s e D c).tubes i).axis.direction 2|

/-- The actual affine-image shading, viewed as a shading of the containing
genuine proxy tubes. -/
def nativeHighCriticalBallAffineProxyShading
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (Y : Shading D.S.family.bodyFamily)
    (G : NativeHighCriticalBallAffineProxyGeometry s e D c) :
    Shading (nativeHighCriticalBallAffineProxyFamily s e D c).bodyFamily where
  carrier i := e '' Y.carrier i.1
  measurable_carrier i :=
    e.toContinuousAffineEquiv.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr
      (Y.measurable_carrier i.1)
  carrier_subset i :=
    (Set.image_mono (Y.carrier_subset i.1)).trans
      (image_tubeCarrier_subset_affineAxisProxyTube e
        (D.S.family.tubes i.1) (G.axisLength i) G.transverseRadius)

@[simp] theorem nativeHighCriticalBallAffineProxyShading_carrier
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (Y : Shading D.S.family.bodyFamily)
    (G : NativeHighCriticalBallAffineProxyGeometry s e D c)
    (i : NativeHighCriticalBallIndex D c) :
    (nativeHighCriticalBallAffineProxyShading s e D c Y G).carrier i =
      e '' Y.carrier i.1 :=
  rfl

/-- The proxy enlargement does not alter the transported shading mass. -/
theorem nativeHighCriticalBallAffineProxyShading_shadingMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (Y : Shading D.S.family.bodyFamily)
    (G : NativeHighCriticalBallAffineProxyGeometry s e D c) :
    (nativeHighCriticalBallAffineProxyShading s e D c Y G).shadingMass =
      affineJacobian e *
        (nativeHighCriticalBallShading D c Y).shadingMass := by
  unfold Shading.shadingMass
  simp_rw [nativeHighCriticalBallAffineProxyShading_carrier,
    volume_image_affineEquiv]
  rw [Finset.mul_sum]
  simp only [nativeHighCriticalBallShading_carrier]

/-- The proxy shading union is exactly the affine image of the restricted
source shading union. -/
theorem nativeHighCriticalBallAffineProxyShading_shadedUnion
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (Y : Shading D.S.family.bodyFamily)
    (G : NativeHighCriticalBallAffineProxyGeometry s e D c) :
    (nativeHighCriticalBallAffineProxyShading s e D c Y G).shadedUnion =
      e '' (nativeHighCriticalBallShading D c Y).shadedUnion := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨i, y, hy, rfl⟩
    exact ⟨y, Set.mem_iUnion.mpr ⟨i, hy⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    change e y ∈ e '' Y.carrier i.1
    change y ∈ Y.carrier i.1 at hi
    exact ⟨y, hi, rfl⟩

theorem nativeHighCriticalBallAffineProxyShading_shadedUnion_volume
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (Y : Shading D.S.family.bodyFamily)
    (G : NativeHighCriticalBallAffineProxyGeometry s e D c) :
    volume (nativeHighCriticalBallAffineProxyShading s e D c Y G).shadedUnion =
      affineJacobian e *
        volume (nativeHighCriticalBallShading D c Y).shadedUnion := by
  rw [nativeHighCriticalBallAffineProxyShading_shadedUnion,
    volume_image_affineEquiv]

theorem nativeHighCriticalBallAffineProxyShading_averageMultiplicity
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (Y : Shading D.S.family.bodyFamily)
    (G : NativeHighCriticalBallAffineProxyGeometry s e D c) :
    (nativeHighCriticalBallAffineProxyShading s e D c Y G).averageMultiplicity =
      (nativeHighCriticalBallShading D c Y).averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [nativeHighCriticalBallAffineProxyShading_shadingMass,
    nativeHighCriticalBallAffineProxyShading_shadedUnion_volume]
  apply ENNReal.mul_div_mul_left
  · exact (affineJacobian_pos e).ne'
  · exact affineJacobian_ne_top e

/-- The genuine proxy family carries the certified post-rescaling `L_3`
chart. -/
def nativeHighCriticalBallAffineProxyWZL3Source
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (G : NativeHighCriticalBallAffineProxyGeometry s e D c) :
    WZL3UniformTubeSource s (NativeHighCriticalBallIndex D c) where
  family := nativeHighCriticalBallAffineProxyFamily s e D c
  source := Finset.univ
  source_direction_final_half := by
    intro i _hi
    exact G.chart i

/-- The mass-retaining actual proxy datum. -/
def nativeHighCriticalBallAffineProxyDatum
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (Y : Shading D.S.family.bodyFamily)
    (G : NativeHighCriticalBallAffineProxyGeometry s e D c) :
    ActualTubeDatum s (NativeHighCriticalBallIndex D c) where
  family := nativeHighCriticalBallAffineProxyFamily s e D c
  shading := nativeHighCriticalBallAffineProxyShading s e D c Y G

#print axioms convexOverlapEssentiallyDistinct_affineImage_of_tubes
#print axioms nativeHighCriticalBallAffineShading_shadingMass
#print axioms nativeHighCriticalBallAffineShading_shadedUnion_volume
#print axioms nativeHighCriticalBallAffineShading_averageMultiplicity
#print axioms nativeHighCriticalBallAffineFamily_pairwise_overlapDistinct
#print axioms nativeHighCriticalBallAffineProxyFamily
#print axioms nativeHighCriticalBallAffineProxyShading
#print axioms nativeHighCriticalBallAffineProxyShading_shadingMass
#print axioms nativeHighCriticalBallAffineProxyShading_shadedUnion
#print axioms nativeHighCriticalBallAffineProxyShading_shadedUnion_volume
#print axioms nativeHighCriticalBallAffineProxyShading_averageMultiplicity
#print axioms nativeHighCriticalBallAffineProxyWZL3Source
#print axioms nativeHighCriticalBallAffineProxyDatum

end

end Family8Family7NativeHighCriticalBallAffineProxyV1
