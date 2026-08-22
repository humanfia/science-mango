import Family6Grounding.Family6CanonicalCertifiedPlankSlabIncidenceCoreV3

set_option autoImplicit false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family6PlankSlabUniformVolumeConcentrationGammaOneV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6PlankKatzTaoFrostmanActualAdaptersV1

noncomputable section

universe u

variable {index : Type u} [Fintype index] [DecidableEq index]
  {a b : NNReal} {D : ShadedConvexPlankFamily index a b}

/-- A finite positive common lower bound for the actual member volumes. -/
structure UniformMemberVolumeLower (D : ShadedConvexPlankFamily index a b)
    (v : ENNReal) : Prop where
  ne_zero : v ≠ 0
  ne_top : v ≠ ∞
  le_volume : ∀ i, v ≤ volume (D.family i : Set Space)

/-- Exact scalar budget for cancelling the common member-volume lower bound
and retaining one slab-thickness factor. -/
def UniformVolumeConcentrationGammaOneBudget
    (v : ENNReal) (eta : Real) : Prop :=
  maximalConcentration D.family ≤
    (a : ENNReal) ^ (-eta) * (Fintype.card index : ENNReal) * v

/-- Containment and a common member-volume lower bound turn cardinality into
contained mass.  Maximal concentration and the slab volume upper bound then
give the single factor of `theta`. -/
theorem members_card_mul_volumeLower_le
    (I : PlankSlabIncidence index D) {v : ENNReal}
    (hv : UniformMemberVolumeLower D v)
    (slabComparisonConstant theta : NNReal) (S : ConvexBody Space)
    (hS : IsSlab slabComparisonConstant theta S) :
    ((I.members theta S).card : ENNReal) * v ≤
      maximalConcentration D.family * (theta : ENNReal) := by
  classical
  have hsubset : I.members theta S ⊆
      Submission.Kakeya.ConvexGeometry.containedIndices D.family S := by
    intro i hi
    have hi' := I.members_contained theta S hi
    simpa [Family6AffinePlankAnalyticHypothesesStableV1.containedIndices,
      Submission.Kakeya.ConvexGeometry.containedIndices] using hi'
  have hKT : IsKatzTao (maximalConcentration D.family) D.family :=
    isKatzTao_iff_maximalConcentration_le.mpr le_rfl
  calc
    ((I.members theta S).card : ENNReal) * v =
      ∑ _i ∈ I.members theta S, v := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ I.members theta S,
        volume (D.family i : Set Space) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact hv.le_volume i
    _ ≤ ∑ i ∈
        Submission.Kakeya.ConvexGeometry.containedIndices D.family S,
          volume (D.family i : Set Space) := by
      exact Finset.sum_le_sum_of_subset hsubset
    _ = containedMass D.family S := rfl
    _ ≤ maximalConcentration D.family * volume (S : Set Space) := hKT S
    _ ≤ maximalConcentration D.family * (theta : ENNReal) := by
      gcongr
      exact hS.volume_upper_bound

/-- Arbitrary-uniform-volume `gamma = 1` count.  The theorem is agnostic
about how `v` was obtained, so exact FrameBox volumes incur no comparability
loss. -/
theorem count_gamma_one_of_uniformVolume_maximalConcentration
    (I : PlankSlabIncidence index D) {v : ENNReal}
    (hv : UniformMemberVolumeLower D v)
    (slabComparisonConstant : NNReal) (eta : Real)
    (hbudget : UniformVolumeConcentrationGammaOneBudget
      (D := D) v eta) :
    ∀ theta : NNReal, a / b ≤ theta → theta ≤ 1 →
      ∀ S : ConvexBody Space, IsSlab slabComparisonConstant theta S →
        ((I.members theta S).card : ENNReal) ≤
          (a : ENNReal) ^ (-eta) * (theta : ENNReal) ^ (1 : Real) *
            (Fintype.card index : ENNReal) := by
  intro theta _hthetaLower _hthetaUpper S hS
  have hmass := members_card_mul_volumeLower_le
    I hv slabComparisonConstant theta S hS
  have hcancel :
      ((I.members theta S).card : ENNReal) * v ≤
        ((a : ENNReal) ^ (-eta) * (theta : ENNReal) ^ (1 : Real) *
          (Fintype.card index : ENNReal)) * v := by
    calc
      ((I.members theta S).card : ENNReal) * v ≤
          maximalConcentration D.family * (theta : ENNReal) := hmass
      _ ≤ (((a : ENNReal) ^ (-eta) *
          (Fintype.card index : ENNReal)) * v) *
          (theta : ENNReal) := by
        gcongr
        exact hbudget
      _ = ((a : ENNReal) ^ (-eta) *
          (theta : ENNReal) ^ (1 : Real) *
          (Fintype.card index : ENNReal)) * v := by
        rw [ENNReal.rpow_one]
        ring
  exact (ENNReal.mul_le_mul_iff_left hv.ne_zero hv.ne_top).mp hcancel

theorem katzTaoControl_gamma_one_of_uniformVolume_maximalConcentration
    (I : PlankSlabIncidence index D) {v : ENNReal}
    (hv : UniformMemberVolumeLower D v)
    (slabComparisonConstant : NNReal) (eta : Real)
    (hbudget : UniformVolumeConcentrationGammaOneBudget
      (D := D) v eta) :
    KatzTaoSlabIncidenceControl D I slabComparisonConstant eta 1 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  exact count_gamma_one_of_uniformVolume_maximalConcentration
    I hv slabComparisonConstant eta hbudget

#print axioms members_card_mul_volumeLower_le
#print axioms count_gamma_one_of_uniformVolume_maximalConcentration
#print axioms katzTaoControl_gamma_one_of_uniformVolume_maximalConcentration

end
end Family6PlankSlabUniformVolumeConcentrationGammaOneV1
