import Family8Grounding.Family8SelectedParentJohnPlankQuantitativeLossV9
import Family8Grounding.Family8SelectedParentPlankStickyDirectionTransportV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped NNReal InnerProductSpace BigOperators

namespace Family8SelectedParentBucketMapDistortionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankStickyDirectionTransportV4
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8TubeJohnUnitRescalingV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The winning hull contains an actual coarse `rho`-tube, so every side of
its common John certificate is at least the tube's transverse diameter. -/
theorem selectedParentGreedyBlockJohnSide_two_mul_rho_le
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length) (j : Fin 3) :
    2 * rho ≤ (selectedParentGreedyBlockJohnFrame S hrho P k).side j := by
  let Q := blockAt S.activeCoarseFamily P k
  let p : ActiveParentIndex S := Classical.choose Q.fiber_nonempty
  have hp : p ∈ Q.fiber := Classical.choose_spec Q.fiber_nonempty
  have hTube : (S.coarse.tubes p.1).carrier ⊆ (Q.body : Set Space) := by
    simpa [Q, FamilyStickyAtEveryScaleCoreV1.StickyScaleCover.activeCoarseFamily,
      UniformTubeFamily.bodyFamily] using Q.contained p hp
  exact JohnSideLowerFinal.boxCertificate_side_lower_of_tube_subset
    (S.coarse.tubes p.1) hTube
    (selectedParentGreedyBlockJohnFrame S hrho P k).certificate j

/-- A lower bound `m` for all John sides gives a forward Lipschitz bound for
the John normalization. The factor three is the explicit three-coordinate
triangle estimate. -/
theorem PositiveJohnFrame.linear_norm_le_three_div_of_side_lower
    {H : ConvexBody Space} (J : PositiveJohnFrame H) (m : NNReal)
    (hm : 0 < m) (hside : ∀ j, m ≤ J.side j) (v : Space) :
    ‖J.affineEquiv.linear v‖ ≤ (3 / (m : Real)) * ‖v‖ := by
  change ‖axisEllipsoidNormalizationLinearEquiv
      J.certificate.box.frame J.radius J.radius_pos v‖ ≤ _
  rw [axisEllipsoidNormalizationLinearEquiv_apply]
  calc
    ‖∑ j, (⟪J.certificate.box.frame j, v⟫_Real /
        (3 * (J.radius j : Real))) • J.certificate.box.frame j‖ ≤
        ∑ j, ‖(⟪J.certificate.box.frame j, v⟫_Real /
          (3 * (J.radius j : Real))) •
            J.certificate.box.frame j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, ‖v‖ / (m : Real) := by
      apply Finset.sum_le_sum
      intro j _hj
      have hdenom : (3 : Real) * (J.radius j : Real) =
          (J.side j : Real) := by
        dsimp only [PositiveJohnFrame.radius]
        norm_num [NNReal.coe_div]
        ring
      rw [norm_smul, J.certificate.box.frame.norm_eq_one, mul_one,
        Real.norm_eq_abs, abs_div, hdenom,
        abs_of_pos (show (0 : Real) < (J.side j : Real) by
          exact_mod_cast J.side_pos j)]
      have hinner := abs_real_inner_le_norm
        (J.certificate.box.frame j) v
      rw [J.certificate.box.frame.norm_eq_one, one_mul] at hinner
      have hmReal : (0 : Real) < (m : Real) := by exact_mod_cast hm
      have hsideReal : (m : Real) ≤ (J.side j : Real) := by
        exact_mod_cast hside j
      exact div_le_div₀ (norm_nonneg v) hinner hmReal hsideReal
    _ = (3 / (m : Real)) * ‖v‖ := by
      rw [Fin.sum_univ_three]
      ring

#print axioms selectedParentGreedyBlockJohnSide_two_mul_rho_le
#print axioms PositiveJohnFrame.linear_norm_le_three_div_of_side_lower

end
end Family8SelectedParentBucketMapDistortionV1
