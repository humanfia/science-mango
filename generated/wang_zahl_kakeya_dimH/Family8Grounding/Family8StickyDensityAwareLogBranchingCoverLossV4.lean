import Family8Grounding.Family8StickyJointExactUniformCoverCostV4
import Family8Grounding.Family8ParentAggregatedShadingActiveCoarseXUpperV3
import Submission.Kakeya.ConvexFactoring.AlmostCoverTubeFactoring
import Mathlib.Tactic

/-!
# Density-aware cover loss for a literal Sticky parent map

For the actual parent map of a `StickyScaleCover`, the occupied-parent
volume sum is exactly the active-coarse family volume.  Dividing that exact
cost by the positive active-fine mass gives an honest global loss for the
logarithmic `JointTubeFactoring` producer.  This avoids paying the artificial
`rho^2 / delta^2` ratio used by the uniform-volume fallback.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyDensityAwareLogBranchingCoverLossV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open Family8StickyJointExactUniformCoverCostV4
open Family8StickyParentAggregatedDensityTransportV3.StickyScaleCover
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The exact global cover cost per unit active-fine body mass. -/
def stickyDensityAwareCoverLoss
    (S : StickyScaleCover fine rho) (A : ENNReal) : ENNReal :=
  (A * familyVolume S.activeCoarseFamily) /
    bodyMassOn fine.bodyFamily S.activeFine

private theorem activeCoarseFamilyVolume_pos
    (S : StickyScaleCover fine rho)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty) :
    0 < familyVolume S.activeCoarseFamily := by
  obtain ⟨i, hi⟩ := hactive
  have hk : S.parent i ∈ S.activeCoarse := S.parent_mem i hi
  unfold familyVolume
    FamilyStickyAtEveryScaleCoreV1.StickyScaleCover.activeCoarseFamily
  rw [Finset.sum_pos_iff]
  exact ⟨⟨S.parent i, hk⟩, Finset.mem_univ _, by
    simpa only [UniformTubeFamily.bodyFamily, Tube.coe_body] using
      (S.coarse.tubes (S.parent i)).volume_pos hrho⟩

/-- The density-aware loss is nonzero on nonempty positive-scale data. -/
theorem stickyDensityAwareCoverLoss_ne_zero
    (S : StickyScaleCover fine rho) {A : ENNReal}
    (hA0 : A ≠ 0) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    stickyDensityAwareCoverLoss S A ≠ 0 := by
  unfold stickyDensityAwareCoverLoss
  apply ENNReal.div_ne_zero.mpr
  exact ⟨mul_ne_zero hA0
      (activeCoarseFamilyVolume_pos S hrho hactive).ne',
    bodyMassOn_ne_top fine.bodyFamily S.activeFine⟩

/-- The density-aware loss is finite on nonempty positive-scale data. -/
theorem stickyDensityAwareCoverLoss_ne_top
    (S : StickyScaleCover fine rho) {A : ENNReal}
    (hAtop : A ≠ ∞) (hdelta : 0 < delta)
    (hactive : S.activeFine.Nonempty) :
    stickyDensityAwareCoverLoss S A ≠ ∞ := by
  unfold stickyDensityAwareCoverLoss
  apply ENNReal.div_ne_top
  · exact ENNReal.mul_ne_top hAtop (familyVolume_ne_top S.activeCoarseFamily)
  · exact (bodyMassOn_pos_of_nonempty fine S.activeFine hdelta hactive).ne'

/-- The exact occupied-parent cost is paid by the density-aware loss. -/
theorem stickyDensityAwareCoverCost
    (S : StickyScaleCover fine rho) (A : ENNReal)
    (hdelta : 0 < delta) (hactive : S.activeFine.Nonempty) :
    A * (∑ k ∈ occupiedParents S.activeFine S.parent,
        volume (S.coarse.tubes k).carrier) ≤
      stickyDensityAwareCoverLoss S A *
        bodyMassOn fine.bodyFamily S.activeFine := by
  rw [sum_occupiedParentVolume_eq_activeCoarseFamilyVolume]
  unfold stickyDensityAwareCoverLoss
  rw [ENNReal.div_mul_cancel
    (bodyMassOn_pos_of_nonempty fine S.activeFine hdelta hactive).ne'
    (bodyMassOn_ne_top fine.bodyFamily S.activeFine)]

/-- Any scalar bound for the exact numerator turns directly into a bound for
the density-aware loss. -/
theorem stickyDensityAwareCoverLoss_le_of_scaled
    (S : StickyScaleCover fine rho) (A B : ENNReal)
    (hdelta : 0 < delta) (hactive : S.activeFine.Nonempty)
    (hscaled :
      A * familyVolume S.activeCoarseFamily ≤
        B * bodyMassOn fine.bodyFamily S.activeFine) :
    stickyDensityAwareCoverLoss S A ≤ B := by
  unfold stickyDensityAwareCoverLoss
  exact (ENNReal.div_le_iff_le_mul
    (Or.inl (bodyMassOn_pos_of_nonempty
      fine S.activeFine hdelta hactive).ne')
    (Or.inl (bodyMassOn_ne_top fine.bodyFamily S.activeFine))).2 hscaled

/-- It is enough to control the normalized parent cardinality
`X = |activeCoarse| rho^2`; the tube volume upper bound supplies the factor
eight. -/
theorem stickyDensityAwareCoverLoss_le_of_cardScaleMass
    (S : StickyScaleCover fine rho) (A B : ENNReal)
    (hdelta : 0 < delta) (hactive : S.activeFine.Nonempty)
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (hscaled :
      A * (8 * (activeCoarseCardScaleMass S : ENNReal)) ≤
        B * bodyMassOn fine.bodyFamily S.activeFine) :
    stickyDensityAwareCoverLoss S A ≤ B := by
  apply stickyDensityAwareCoverLoss_le_of_scaled S A B hdelta hactive
  calc
    A * familyVolume S.activeCoarseFamily ≤
        A * ((S.activeCoarse.card : ENNReal) *
          (8 * (rho : ENNReal) ^ 2)) :=
      mul_le_mul' le_rfl
        (activeCoarseFamilyVolume_le_card_mul_eight_sq S hrhoHalf)
    _ = A * (8 * ((S.activeCoarse.card : ENNReal) *
          (rho : ENNReal) ^ 2)) := by ac_rfl
    _ = A * (8 * (activeCoarseCardScaleMass S : ENNReal)) := by
      simp only [activeCoarseCardScaleMass, ENNReal.coe_mul,
        ENNReal.coe_natCast, ENNReal.coe_pow]
    _ ≤ B * bodyMassOn fine.bodyFamily S.activeFine := hscaled

#print axioms stickyDensityAwareCoverLoss
#print axioms stickyDensityAwareCoverLoss_ne_zero
#print axioms stickyDensityAwareCoverLoss_ne_top
#print axioms stickyDensityAwareCoverCost
#print axioms stickyDensityAwareCoverLoss_le_of_scaled
#print axioms stickyDensityAwareCoverLoss_le_of_cardScaleMass

end
end Family8StickyDensityAwareLogBranchingCoverLossV4
