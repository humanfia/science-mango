import Family8Grounding.Family8FiniteRandomRigidMotionB2NormalizationCarrierV1
import Family8Grounding.Family8FiniteRandomRigidMotionB2DilationVolumeV1
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionB2NormalizedDatumV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2NormalizationCarrierV1
open Family8FiniteRandomRigidMotionB2DilationVolumeV1

noncomputable section

/-!
# The normalized actual family and shading

The normalized shading is the literal affine image of the source shading.
Consequently both its total mass and shaded-union volume acquire the same
factor `1/512`, and average multiplicity is unchanged exactly.
-/

def eighthNormalizedTubeFamily
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (F : UniformTubeFamily delta iota) :
    UniformTubeFamily (delta / 8) iota where
  tubes i := eighthNormalizedTube (F.tubes i)
  refinement := F.refinement

@[simp] theorem eighthNormalizedTubeFamily_tubes
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (F : UniformTubeFamily delta iota) (i : iota) :
    (eighthNormalizedTubeFamily F).tubes i =
      eighthNormalizedTube (F.tubes i) := rfl

def eighthNormalizedShading
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (F : UniformTubeFamily delta iota)
    (Y : Shading F.bodyFamily) :
    Shading (eighthNormalizedTubeFamily F).bodyFamily where
  carrier i := eighthDilationPoint '' Y.carrier i
  measurable_carrier i := by
    change MeasurableSet
      (eighthDilationLinearEquiv '' Y.carrier i)
    exact
      eighthDilationLinearEquiv.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr
        (Y.measurable_carrier i)
  carrier_subset i := by
    change eighthDilationPoint '' Y.carrier i ⊆
      (eighthNormalizedTube (F.tubes i)).carrier
    exact (Set.image_mono (Y.carrier_subset i)).trans
      (image_eighthDilation_tube_carrier_subset_normalizedTube (F.tubes i))

@[simp] theorem eighthNormalizedShading_carrier
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (F : UniformTubeFamily delta iota)
    (Y : Shading F.bodyFamily) (i : iota) :
    (eighthNormalizedShading F Y).carrier i =
      eighthDilationPoint '' Y.carrier i := rfl

/-- Total shaded mass has the exact three-dimensional dilation factor. -/
theorem eighthNormalizedShading_shadingMass
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (F : UniformTubeFamily delta iota)
    (Y : Shading F.bodyFamily) :
    (eighthNormalizedShading F Y).shadingMass =
      (1 / 512 : ENNReal) * Y.shadingMass := by
  unfold Shading.shadingMass
  simp_rw [eighthNormalizedShading_carrier,
    volume_image_eighthDilationPoint]
  rw [Finset.mul_sum]

/-- The normalized shaded union is the literal image of the source union. -/
theorem eighthNormalizedShading_shadedUnion
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (F : UniformTubeFamily delta iota)
    (Y : Shading F.bodyFamily) :
    (eighthNormalizedShading F Y).shadedUnion =
      eighthDilationPoint '' Y.shadedUnion := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨i, y, hy, rfl⟩
    exact ⟨y, Set.mem_iUnion.mpr ⟨i, hy⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, y, hi, rfl⟩

/-- Shaded-union volume has the same exact dilation factor. -/
theorem volume_eighthNormalizedShading_shadedUnion
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (F : UniformTubeFamily delta iota)
    (Y : Shading F.bodyFamily) :
    volume (eighthNormalizedShading F Y).shadedUnion =
      (1 / 512 : ENNReal) * volume Y.shadedUnion := by
  rw [eighthNormalizedShading_shadedUnion,
    volume_image_eighthDilationPoint]

/-- Average multiplicity is invariant under the common affine dilation. -/
theorem eighthNormalizedShading_averageMultiplicity
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (F : UniformTubeFamily delta iota)
    (Y : Shading F.bodyFamily) :
    (eighthNormalizedShading F Y).averageMultiplicity =
      Y.averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [eighthNormalizedShading_shadingMass,
    volume_eighthNormalizedShading_shadedUnion]
  apply ENNReal.mul_div_mul_left
  · norm_num
  · norm_num

/-- Package the normalized family and image shading at radius `delta/8`. -/
def eighthNormalizedDatum
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (D : ActualTubeDatum delta iota) :
    ActualTubeDatum (delta / 8) iota where
  family := eighthNormalizedTubeFamily D.family
  shading := eighthNormalizedShading D.family D.shading

@[simp] theorem eighthNormalizedDatum_family
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (D : ActualTubeDatum delta iota) :
    (eighthNormalizedDatum D).family =
      eighthNormalizedTubeFamily D.family := rfl

@[simp] theorem eighthNormalizedDatum_shading
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (D : ActualTubeDatum delta iota) :
    (eighthNormalizedDatum D).shading =
      eighthNormalizedShading D.family D.shading := rfl

theorem eighthNormalizedDatum_averageMultiplicity
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (D : ActualTubeDatum delta iota) :
    (eighthNormalizedDatum D).shading.averageMultiplicity =
      D.shading.averageMultiplicity :=
  eighthNormalizedShading_averageMultiplicity D.family D.shading

/-- The unit-ball field of admissibility is automatic from honest B2 input;
pairwise essential distinctness is intentionally left for a fresh greedy
refinement after the unit-axis extensions. -/
theorem eighthNormalizedDatum_contained_in_unit_ball
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (D : ActualTubeDatum delta iota)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hB2 : forall i,
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2) :
    forall i,
      ((eighthNormalizedDatum D).family.tubes i).carrier ⊆
        Metric.closedBall (0 : Space) 1 := by
  intro i
  exact eighthNormalizedTube_carrier_subset_unitBall
    (D.family.tubes i) hdeltaHalf (hB2 i)

#print axioms eighthNormalizedShading_shadingMass
#print axioms eighthNormalizedShading_shadedUnion
#print axioms volume_eighthNormalizedShading_shadedUnion
#print axioms eighthNormalizedShading_averageMultiplicity
#print axioms eighthNormalizedDatum_averageMultiplicity
#print axioms eighthNormalizedDatum_contained_in_unit_ball

end
end Family8FiniteRandomRigidMotionB2NormalizedDatumV1
