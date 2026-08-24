import «Family4FinalMaster»

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Family4PublishedInputs

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open TubeSelectedFamilyRatioPrototype
open Family4FrozenDensityAdapter
open Family4MinimalJoint
open Family4FinalMaster

noncomputable section

set_option linter.unusedSectionVars false

variable {delta rho : NNReal} {ι κ : Type*}
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  {fineFamily : UniformTubeFamily delta ι}
  {coarseFamily : UniformTubeFamily rho κ}
  {P : CoarseTubePartition fineFamily coarseFamily}
  {Y : Shading fineFamily.bodyFamily}

/-- Data produced by the paper's per-tube shading-density pigeonhole step.
The profile family is the source bucket, the refined family retains its
cardinality, and all source shading pieces lie in one common mass band. -/
structure ActiveShadingBucketData
    (P : CoarseTubePartition fineFamily coarseFamily)
    (Y : Shading fineFamily.bodyFamily) where
  massBase : ℝ≥0∞
  massLoss : ℕ
  support_profile : ∀ i ∉ fineFamily.refinement.profile.family,
    Y.carrier i = ∅
  source_upper : ∀ i ∈ fineFamily.refinement.profile.family,
    volume (Y.carrier i) ≤ massLoss • massBase
  refined_lower : ∀ i ∈ P.fineIndices,
    massBase ≤ volume (Y.carrier i)

namespace ActiveShadingBucketData

theorem sourceMass_eq_profileSum (S : ActiveShadingBucketData P Y) :
    Y.shadingMass = ∑ i ∈ fineFamily.refinement.profile.family,
      volume (Y.carrier i) := by
  unfold Shading.shadingMass
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _hiuniv hi
  rw [S.support_profile i hi]
  simp

theorem activeMass_eq_refinedSum (_S : ActiveShadingBucketData P Y) :
    (FrozenTubeDensityMasterPrototype.activeFineShading P Y).shadingMass =
      ∑ i ∈ fineFamily.refinement.refined, volume (Y.carrier i) := by
  unfold FrozenTubeDensityMasterPrototype.activeFineShading activeFineBodyFamily
  rw [selectedCoarseShading_mass, P.fineIndices_eq_refined]

/-- Cardinal retention plus a common per-tube shading-mass band produces the
actual source-to-active `WithinFactor`; inactive mass is handled by
`support_profile`, not discarded. -/
theorem withinFactor_active (S : ActiveShadingBucketData P Y) :
    WithinFactor (fineFamily.refinement.loss * S.massLoss)
      Y.shadingMass
      (FrozenTubeDensityMasterPrototype.activeFineShading P Y).shadingMass := by
  unfold WithinFactor
  rw [S.sourceMass_eq_profileSum, S.activeMass_eq_refinedSum]
  calc
    (∑ i ∈ fineFamily.refinement.profile.family, volume (Y.carrier i)) ≤
        ∑ _i ∈ fineFamily.refinement.profile.family,
          S.massLoss • S.massBase :=
      Finset.sum_le_sum fun i hi => S.source_upper i hi
    _ = fineFamily.refinement.profile.family.card •
        (S.massLoss • S.massBase) := by simp
    _ ≤ (fineFamily.refinement.loss * fineFamily.refinement.refined.card) •
        (S.massLoss • S.massBase) := by
      simp only [nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right ?_ bot_le
      exact_mod_cast fineFamily.refinement.card_le_loss_mul
    _ = (fineFamily.refinement.loss * S.massLoss) •
        (fineFamily.refinement.refined.card • S.massBase) := by
      simp only [nsmul_eq_mul, Nat.cast_mul]
      ring
    _ ≤ (fineFamily.refinement.loss * S.massLoss) •
        (∑ i ∈ fineFamily.refinement.refined, volume (Y.carrier i)) := by
      apply nsmul_le_nsmul_right
      calc
        fineFamily.refinement.refined.card • S.massBase =
            ∑ _i ∈ fineFamily.refinement.refined, S.massBase := by simp
        _ ≤ ∑ i ∈ fineFamily.refinement.refined, volume (Y.carrier i) :=
          Finset.sum_le_sum fun i hi => by
            apply S.refined_lower i
            simpa [P.fineIndices_eq_refined] using hi

end ActiveShadingBucketData

/-- The two outputs of the WZ extremal step: the chosen fiber bucket is
controlled by an intermediate extremal scale weight, and that weight is
controlled by branching at the fine scale. -/
structure ExtremalScaleBranchingData {r : ℝ}
    (A : Submission.Kakeya.ConvexFactoring.FrozenNeighborhoodAssembly.Assembly
      P.asConvexFactorization Y r) (Q : ℝ≥0∞) where
  extremalWeight : ℝ≥0∞
  fiber_scale_le :
    (rho : ℝ≥0∞) ^ 2 *
        ((2 * Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets.comparableBase
          A.fiberLabel : ℕ) : ℝ≥0∞) ≤ extremalWeight
  extremal_le_branching_scale : extremalWeight ≤
    Q * (P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2

namespace ExtremalScaleBranchingData

theorem wzJointNormalization {r : ℝ}
    {A : Submission.Kakeya.ConvexFactoring.FrozenNeighborhoodAssembly.Assembly
      P.asConvexFactorization Y r} {Q : ℝ≥0∞}
    (E : ExtremalScaleBranchingData A Q) : WZJointNormalization A Q :=
  E.fiber_scale_le.trans E.extremal_le_branching_scale

end ExtremalScaleBranchingData

/-- Published-step wrapper: neither a naked source-retention inequality nor a
naked joint-normalization inequality appears in the interface. -/
theorem family4_from_published_step_data {r : ℝ}
    (A : Submission.Kakeya.ConvexFactoring.FrozenNeighborhoodAssembly.Assembly
      P.asConvexFactorization Y r)
    (S : ActiveShadingBucketData P Y)
    (Q : ℝ≥0∞) (E : ExtremalScaleBranchingData A Q)
    (hdeltaPos : 0 < delta) (hrhoHalf : rho ≤ (2 : ℝ≥0)⁻¹) :
    Conclusion A (fineFamily.refinement.loss * S.massLoss) Q := by
  exact family4_items_one_to_six_same_object A
    (fineFamily.refinement.loss * S.massLoss) S.withinFactor_active Q
      hdeltaPos hrhoHalf E.wzJointNormalization

end
end Family4PublishedInputs

#print axioms Family4PublishedInputs.ActiveShadingBucketData.withinFactor_active
#print axioms Family4PublishedInputs.ExtremalScaleBranchingData.wzJointNormalization
#print axioms Family4PublishedInputs.family4_from_published_step_data
