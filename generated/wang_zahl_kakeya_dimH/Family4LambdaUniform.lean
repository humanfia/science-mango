import «Family4PublishedInputs»
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Family4LambdaUniform

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Submission.Kakeya.ConvexFactoring
open TubeSelectedFamilyRatioPrototype
open Family4FrozenDensityAdapter
open Family4MinimalJoint
open Family4FinalMaster
open Family4PublishedInputs

noncomputable section

set_option linter.unusedSectionVars false

variable {delta rho : NNReal} {ι κ : Type*}
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  {fineFamily : UniformTubeFamily delta ι}
  {coarseFamily : UniformTubeFamily rho κ}
  {P : CoarseTubePartition fineFamily coarseFamily}
  {Y : Shading fineFamily.bodyFamily}

/-- Paper-facing per-tube `lambda` uniformity on the source profile bucket.
The upper/lower asymmetry permits a dyadic density loss. -/
structure LambdaUniformShadingData
    (P : CoarseTubePartition fineFamily coarseFamily)
    (Y : Shading fineFamily.bodyFamily) where
  lambda : ℝ≥0∞
  densityLoss : ℕ
  support_profile : ∀ i ∉ fineFamily.refinement.profile.family,
    Y.carrier i = ∅
  source_upper : ∀ i ∈ fineFamily.refinement.profile.family,
    volume (Y.carrier i) ≤
      densityLoss • (lambda * volume (fineFamily.tubes i).carrier)
  refined_lower : ∀ i ∈ P.fineIndices,
    lambda * volume (fineFamily.tubes i).carrier ≤ volume (Y.carrier i)

namespace LambdaUniformShadingData

/-- Unit `delta`-tubes have volumes within factor 16, so lambda-uniformity
becomes the common shading-mass band used by cardinal pigeonholing. -/
def toActiveShadingBucketData
    (S : LambdaUniformShadingData P Y)
    (hdeltaHalf : delta ≤ (2 : ℝ≥0)⁻¹) :
    ActiveShadingBucketData P Y where
  massBase := S.lambda * ((delta : ℝ≥0∞) ^ 2 / 2)
  massLoss := 16 * S.densityLoss
  support_profile := S.support_profile
  source_upper := by
    intro i hi
    calc
      volume (Y.carrier i) ≤
          S.densityLoss • (S.lambda * volume (fineFamily.tubes i).carrier) :=
        S.source_upper i hi
      _ ≤ S.densityLoss •
          (S.lambda * (8 * (delta : ℝ≥0∞) ^ 2)) := by
        apply nsmul_le_nsmul_right
        exact mul_le_mul' le_rfl
          ((fineFamily.tubes i).volume_le_eight_mul_sq_of_le_half hdeltaHalf)
      _ = (16 * S.densityLoss) •
          (S.lambda * ((delta : ℝ≥0∞) ^ 2 / 2)) := by
        simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
        rw [ENNReal.div_eq_inv_mul]
        calc
          (S.densityLoss : ℝ≥0∞) *
              (S.lambda * (8 * (delta : ℝ≥0∞) ^ 2)) =
            (S.densityLoss : ℝ≥0∞) * S.lambda *
              ((16 * (2 : ℝ≥0∞)⁻¹) * (delta : ℝ≥0∞) ^ 2) := by
                rw [show (16 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ = 8 by
                  calc
                    (16 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ =
                        (8 * 2) * (2 : ℝ≥0∞)⁻¹ := by norm_num
                    _ = 8 * (2 * (2 : ℝ≥0∞)⁻¹) := by ac_rfl
                    _ = 8 := by rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]]
                ac_rfl
          _ = 16 * (S.densityLoss : ℝ≥0∞) *
              (S.lambda * ((2 : ℝ≥0∞)⁻¹ * (delta : ℝ≥0∞) ^ 2)) := by
                ac_rfl
  refined_lower := by
    intro i hi
    calc
      S.lambda * ((delta : ℝ≥0∞) ^ 2 / 2) ≤
          S.lambda * volume (fineFamily.tubes i).carrier :=
        mul_le_mul' le_rfl
          ((fineFamily.tubes i).half_sq_le_volume_of_le_half hdeltaHalf)
      _ ≤ volume (Y.carrier i) := S.refined_lower i hi

theorem withinFactor_active
    (S : LambdaUniformShadingData P Y)
    (hdeltaHalf : delta ≤ (2 : ℝ≥0)⁻¹) :
    WithinFactor
      (fineFamily.refinement.loss * (16 * S.densityLoss))
      Y.shadingMass
      (FrozenTubeDensityMasterPrototype.activeFineShading P Y).shadingMass :=
  (S.toActiveShadingBucketData hdeltaHalf).withinFactor_active

end LambdaUniformShadingData

/-- Fully published-data wrapper: per-tube lambda uniformity and the two-part
extremal scale certificate discharge both former naked inputs. -/
theorem family4_from_lambdaUniform_and_extremal {r : ℝ}
    (A : Submission.Kakeya.ConvexFactoring.FrozenNeighborhoodAssembly.Assembly
      P.asConvexFactorization Y r)
    (S : LambdaUniformShadingData P Y)
    (Q : ℝ≥0∞) (E : ExtremalScaleBranchingData A Q)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta ≤ (2 : ℝ≥0)⁻¹)
    (hrhoHalf : rho ≤ (2 : ℝ≥0)⁻¹) :
    Conclusion A
      (fineFamily.refinement.loss * (16 * S.densityLoss)) Q := by
  exact family4_from_published_step_data A
    (S.toActiveShadingBucketData hdeltaHalf) Q E hdeltaPos hrhoHalf

end
end Family4LambdaUniform

#print axioms Family4LambdaUniform.LambdaUniformShadingData.withinFactor_active
#print axioms Family4LambdaUniform.family4_from_lambdaUniform_and_extremal
