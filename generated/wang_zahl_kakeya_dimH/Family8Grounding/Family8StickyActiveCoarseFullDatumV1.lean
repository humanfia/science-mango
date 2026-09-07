import Family8Grounding.Family8KatzTaoNegativeExponentObstructionV1
import Family8Grounding.Family8FiniteRandomRigidMotionB2NormalizedDatumV1
import Family8Grounding.Family8FiniteRandomRigidMotionB2KatzTaoTransportV1
import Family8Grounding.Family8FrozenCoarseB2DensityTransportScaleOnlyV1
import FamilyStickyGrounding.FamilyStickyAtEveryScaleCoreV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8StickyActiveCoarseFullDatumV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8KatzTaoNegativeExponentObstructionV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2KatzTaoTransportV1
open Family8FrozenCoarseB2DensityTransportScaleOnlyV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Literal full-shaded datum on active sticky parents

The paper's coarse multiplicity `mu(T_rho)` uses the full carriers of the
actual active parent tubes.  This module packages precisely that object.
No admissibility is asserted: B2 support and fresh selection are handled
later.  The source density is exactly one, native Katz--Tao control is the
cover's existing at-scale certificate, and eighth-normalization preserves
average multiplicity exactly.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

def activeCoarseFullDatum (S : StickyScaleCover fine rho) :
    ActualTubeDatum rho {k // k ∈ S.activeCoarse} where
  family := S.coarse.restrictTo S.activeCoarse
  shading := fullShading S.activeCoarseFamily

@[simp]
theorem activeCoarseFullDatum_family_tubes
    (S : StickyScaleCover fine rho)
    (k : {k // k ∈ S.activeCoarse}) :
    (activeCoarseFullDatum S).family.tubes k = S.coarse.tubes k.1 :=
  rfl

@[simp]
theorem activeCoarseFullDatum_shading_carrier
    (S : StickyScaleCover fine rho)
    (k : {k // k ∈ S.activeCoarse}) :
    (activeCoarseFullDatum S).shading.carrier k =
      (S.coarse.tubes k.1).carrier :=
  rfl

theorem activeCoarseFullDatum_isKatzTao_of_isKatzTaoAtScale
    (S : StickyScaleCover fine rho) {C : ENNReal}
    (hKT : S.IsKatzTaoAtScale C) :
    IsKatzTao C (activeCoarseFullDatum S).family.bodyFamily := by
  have hfamily :
      (activeCoarseFullDatum S).family.bodyFamily =
        S.activeCoarseFamily := by
    funext k
    rfl
  apply isKatzTao_iff_concentration_le.mpr
  intro K
  rw [hfamily]
  exact hKT K

theorem activeCoarseFullDatum_shadingDensity_eq_one
    (S : StickyScaleCover fine rho)
    [Nonempty {k // k ∈ S.activeCoarse}]
    (hrho : 0 < rho) :
    (activeCoarseFullDatum S).shading.shadingDensity = 1 := by
  apply fullShading_shadingDensity_eq_one
  exact (actualDatum_familyVolume_pos_of_scale
    (activeCoarseFullDatum S) hrho).ne'

theorem eighthNormalized_activeCoarseFullDatum_density_lower
    (S : StickyScaleCover fine rho)
    [Nonempty {k // k ∈ S.activeCoarse}]
    (hrho : 0 < rho) (hrhoHalf : rho <= (2 : NNReal)⁻¹) :
    (1 / 128 : ENNReal) <=
      (eighthNormalizedDatum
        (activeCoarseFullDatum S)).shading.shadingDensity := by
  have htransport := source_shadingDensity_div_128_le_eighthNormalized_of_scale
    (activeCoarseFullDatum S) hrho hrhoHalf
  rw [activeCoarseFullDatum_shadingDensity_eq_one S hrho] at htransport
  simpa using htransport

theorem eighthNormalized_activeCoarseFullDatum_averageMultiplicity
    (S : StickyScaleCover fine rho) :
    (eighthNormalizedDatum
        (activeCoarseFullDatum S)).shading.averageMultiplicity =
      (activeCoarseFullDatum S).shading.averageMultiplicity :=
  eighthNormalizedDatum_averageMultiplicity _

theorem eighthNormalized_activeCoarseFullDatum_isKatzTao
    (S : StickyScaleCover fine rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    {C : ENNReal} (hKT : S.IsKatzTaoAtScale C) :
    IsKatzTao (128 * C)
      (eighthNormalizedDatum
        (activeCoarseFullDatum S)).family.bodyFamily := by
  exact eighthNormalizedDatum_isKatzTao
    (activeCoarseFullDatum S) hrhoHalf
      (activeCoarseFullDatum_isKatzTao_of_isKatzTaoAtScale S hKT)

#print axioms activeCoarseFullDatum
#print axioms activeCoarseFullDatum_family_tubes
#print axioms activeCoarseFullDatum_shading_carrier
#print axioms activeCoarseFullDatum_isKatzTao_of_isKatzTaoAtScale
#print axioms activeCoarseFullDatum_shadingDensity_eq_one
#print axioms eighthNormalized_activeCoarseFullDatum_density_lower
#print axioms eighthNormalized_activeCoarseFullDatum_averageMultiplicity
#print axioms eighthNormalized_activeCoarseFullDatum_isKatzTao

end
end Family8StickyActiveCoarseFullDatumV1
