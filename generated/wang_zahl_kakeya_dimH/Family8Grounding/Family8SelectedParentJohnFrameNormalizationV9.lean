import Family8Grounding.Family8SelectedParentAffineShadingTransportV4
import FamilyStickyGrounding.JohnCapturedTubeCertificateCleanAdapterV1
import Family8Grounding.Family8TubeJohnUnitRescalingV2
import Submission.Kakeya.ConvexFactoring.FrameBoxCoordinateWindowEquiv
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentJohnFrameNormalizationV9

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8TubeJohnUnitRescalingV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

structure PositiveJohnFrame (H : ConvexBody Space) where
  side : Fin 3 → NNReal
  side_pos : ∀ i, 0 < side i
  certificate : BoxDimensionsCertificate 288 side H

noncomputable def selectedParentGreedyBlockJohnFrame
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length) :
    PositiveJohnFrame (blockAt S.activeCoarseFamily P k).body := by
  let Q := blockAt S.activeCoarseFamily P k
  let p : ActiveParentIndex S := Classical.choose Q.fiber_nonempty
  have hp : p ∈ Q.fiber := Classical.choose_spec Q.fiber_nonempty
  have hTube : (S.coarse.tubes p.1).carrier ⊆ (Q.body : Set Space) := by
    simpa [Q, FamilyStickyAtEveryScaleCoreV1.StickyScaleCover.activeCoarseFamily,
      UniformTubeFamily.bodyFamily] using Q.contained p hp
  let hex := exists_positive_boxDimensionsCertificate_288_of_tube_subset_clean
    Q.body (S.coarse.tubes p.1) hrho hTube
  let side : Fin 3 → NNReal := Classical.choose hex
  have hspec := Classical.choose_spec hex
  let cert : BoxDimensionsCertificate 288 side Q.body :=
    Classical.choice hspec.2
  exact ⟨side, hspec.1, cert⟩

def PositiveJohnFrame.radius {H : ConvexBody Space}
    (J : PositiveJohnFrame H) (i : Fin 3) : NNReal := J.side i / 3

theorem PositiveJohnFrame.radius_pos {H : ConvexBody Space}
    (J : PositiveJohnFrame H) (i : Fin 3) : 0 < J.radius i := by
  exact div_pos (J.side_pos i) (by norm_num)

def PositiveJohnFrame.affineEquiv {H : ConvexBody Space}
    (J : PositiveJohnFrame H) : Space ≃ᵃ[ℝ] Space :=
  axisEllipsoidNormalizationAffineEquiv J.certificate.box.center
    J.certificate.box.frame J.radius J.radius_pos

theorem PositiveJohnFrame.inner_affineEquiv_apply
    {H : ConvexBody Space} (J : PositiveJohnFrame H)
    (x : Space) (i : Fin 3) :
    ⟪J.certificate.box.frame i, J.affineEquiv x⟫_ℝ =
      (⟪J.certificate.box.frame i, x⟫_ℝ -
        ⟪J.certificate.box.frame i, J.certificate.box.center⟫_ℝ) /
          (J.side i : Real) := by
  rw [PositiveJohnFrame.affineEquiv,
    axisEllipsoidNormalizationAffineEquiv_apply]
  simp only [inner_sum, real_inner_smul_right]
  rw [Finset.sum_eq_single i]
  · simp only [J.certificate.box.frame.inner_eq_ite, if_pos, mul_one]
    have hdenom : (3 : Real) * (J.radius i : Real) = (J.side i : Real) := by
      dsimp [PositiveJohnFrame.radius]
      ring
    rw [hdenom, inner_sub_right]
  · intro j _hj hji
    have hij : i ≠ j := Ne.symm hji
    rw [J.certificate.box.frame.inner_eq_ite]
    simp [hij]
  · simp

#print axioms selectedParentGreedyBlockJohnFrame
#print axioms PositiveJohnFrame.inner_affineEquiv_apply

end
end Family8SelectedParentJohnFrameNormalizationV9
