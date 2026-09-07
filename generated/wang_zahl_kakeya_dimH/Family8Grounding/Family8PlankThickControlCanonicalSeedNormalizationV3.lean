import Family8Grounding.Family8PlankThickControlSeedwiseAffineCopyV1
import Family8Grounding.Family8SelectedParentCertifiedPlankCordobaConnectorV3
import Family8Grounding.Family8TubeJohnUnitRescalingV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8PlankThickControlCanonicalSeedNormalizationV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PlankThickControlActualClusterV1
open Family8PlankThickControlActualCopyFamilyV2
open Family8PlankThickControlSeedwiseAffineCopyV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8TubeJohnUnitRescalingV2

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

abbrev plankSeedCertificate
    (D : ShadedConvexPlankFamily iota a b) (i : iota) :=
  chosenPlankCertificate D.all_isPlank i

theorem plankSeedCertificate_side_pos
    (D : ShadedConvexPlankFamily iota a b) (i : iota) (k : Fin 3) :
    0 < (plankSeedCertificate D i).box.side k := by
  let cert := plankSeedCertificate D i
  rw [cert.side_eq]
  fin_cases k
  · simpa [plankSides] using cert.a_pos
  · have hb : 0 < b := cert.a_pos.trans_le cert.a_le_b
    simpa [plankSides] using hb
  · simp [plankSides]

def plankSeedRadius
    (D : ShadedConvexPlankFamily iota a b) (i : iota) (k : Fin 3) : NNReal :=
  (plankSeedCertificate D i).box.side k / 3

theorem plankSeedRadius_pos
    (D : ShadedConvexPlankFamily iota a b) (i : iota) (k : Fin 3) :
    0 < plankSeedRadius D i k :=
  div_pos (plankSeedCertificate_side_pos D i k) (by norm_num)

/-- The canonical seed map uses the actual box certificate selected from
`D.all_isPlank`; it is not an external affine-map premise. -/
def plankSeedAffineEquiv
    (D : ShadedConvexPlankFamily iota a b) (i : iota) :
    Space ≃ᵃ[Real] Space :=
  axisEllipsoidNormalizationAffineEquiv
    (plankSeedCertificate D i).box.center
    (plankSeedCertificate D i).box.frame
    (plankSeedRadius D i) (plankSeedRadius_pos D i)

theorem plankSeedAffineEquiv_inner_apply
    (D : ShadedConvexPlankFamily iota a b) (i : iota)
    (x : Space) (k : Fin 3) :
    ⟪(plankSeedCertificate D i).box.frame k,
      plankSeedAffineEquiv D i x⟫_Real =
      (⟪(plankSeedCertificate D i).box.frame k, x⟫_Real -
        ⟪(plankSeedCertificate D i).box.frame k,
          (plankSeedCertificate D i).box.center⟫_Real) /
        ((plankSeedCertificate D i).box.side k : Real) := by
  rw [plankSeedAffineEquiv,
    axisEllipsoidNormalizationAffineEquiv_apply]
  simp only [inner_sum, real_inner_smul_right]
  rw [Finset.sum_eq_single k]
  · simp only [(plankSeedCertificate D i).box.frame.inner_eq_ite,
      if_pos, mul_one]
    have hdenomNN :
        (3 : NNReal) * plankSeedRadius D i k =
          (plankSeedCertificate D i).box.side k := by
      rw [mul_comm]
      exact div_mul_cancel₀ _ (by norm_num)
    have hdenom :
        (3 : Real) * (plankSeedRadius D i k : Real) =
          ((plankSeedCertificate D i).box.side k : Real) := by
      exact_mod_cast hdenomNN
    rw [hdenom, inner_sub_right]
  · intro j _hj hjk
    have hkj : k ≠ j := Ne.symm hjk
    rw [(plankSeedCertificate D i).box.frame.inner_eq_ite]
    simp [hkj]
  · simp

/-- Each actual seed plank is sent into `B(0,1)` by the affine map chosen
from its own box certificate. -/
theorem image_seedBody_subset_closedBall_one
    (D : ShadedConvexPlankFamily iota a b) (i : iota) :
    plankSeedAffineEquiv D i '' (D.family i : Set Space) ⊆
      Metric.closedBall (0 : Space) 1 := by
  rintro _ ⟨x, hx, rfl⟩
  let cert := plankSeedCertificate D i
  let E := plankSeedAffineEquiv D i
  have hxbox : x ∈ cert.box.carrier := cert.outer_le hx
  have hcoord (k : Fin 3) :
      |⟪cert.box.frame k, E x⟫_Real| ≤ (1 / 2 : Real) := by
    rw [show ⟪cert.box.frame k, E x⟫_Real =
      (⟪cert.box.frame k, x⟫_Real -
        ⟪cert.box.frame k, cert.box.center⟫_Real) /
          (cert.box.side k : Real) by
      exact plankSeedAffineEquiv_inner_apply D i x k]
    have hsideNN : 0 < cert.box.side k := by
      simpa [cert] using plankSeedCertificate_side_pos D i k
    have hside : (0 : Real) < (cert.box.side k : Real) := by
      exact_mod_cast hsideNN
    rw [abs_div, abs_of_pos hside]
    apply (div_le_iff₀ hside).2
    have hs := cert.box.centeredCoordinate_abs_le_halfSide hxbox k
    nlinarith
  let c0 : Real := ⟪cert.box.frame 0, E x⟫_Real
  let c1 : Real := ⟪cert.box.frame 1, E x⟫_Real
  let c2 : Real := ⟪cert.box.frame 2, E x⟫_Real
  have hc0 : c0 ^ 2 ≤ (1 / 2 : Real) ^ 2 := by
    have hb := abs_le.mp (hcoord 0)
    nlinarith
  have hc1 : c1 ^ 2 ≤ (1 / 2 : Real) ^ 2 := by
    have hb := abs_le.mp (hcoord 1)
    nlinarith
  have hc2 : c2 ^ 2 ≤ (1 / 2 : Real) ^ 2 := by
    have hb := abs_le.mp (hcoord 2)
    nlinarith
  have hparseval := cert.box.frame.sum_sq_inner_right (E x)
  rw [Fin.sum_univ_three] at hparseval
  change c0 ^ 2 + c1 ^ 2 + c2 ^ 2 = ‖E x‖ ^ 2 at hparseval
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hn
  have hn' : (1 : Real) < ‖E x‖ := lt_of_not_ge hn
  nlinarith [norm_nonneg (E x)]

abbrev canonicalSeedwiseAffineThickenedPlankCopyFamily
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    ConvexFamily (ThickenedPlankOccurrence D theta) :=
  seedwiseAffineThickenedPlankCopyFamily (plankSeedAffineEquiv D) D theta

def canonicalSeedwiseAffineThickenedPlankCopyShading
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    Shading (canonicalSeedwiseAffineThickenedPlankCopyFamily D theta) :=
  seedwiseAffineThickenedPlankCopyShading (plankSeedAffineEquiv D) D theta

theorem canonicalSeedwiseAffine_diagonal_subset_closedBall_one
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    (canonicalSeedwiseAffineThickenedPlankCopyFamily D theta
      ⟨i, ⟨i, source_mem_thickenedPlankIndices D theta i⟩⟩ : Set Space) ⊆
        Metric.closedBall (0 : Space) 1 := by
  exact image_seedBody_subset_closedBall_one D i

theorem canonicalSeedwiseAffine_cluster_averageMultiplicity
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    (seedwiseAffineThickenedPlankClusterShading
      (plankSeedAffineEquiv D) D theta i).averageMultiplicity =
      (thickenedPlankCluster D theta i).shading.averageMultiplicity :=
  seedwiseAffineThickenedPlankCluster_averageMultiplicity
    (plankSeedAffineEquiv D) D theta i

theorem canonicalSeedwiseAffine_cluster_shadingDensity
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    (seedwiseAffineThickenedPlankClusterShading
      (plankSeedAffineEquiv D) D theta i).shadingDensity =
      (thickenedPlankCluster D theta i).shading.shadingDensity :=
  seedwiseAffineThickenedPlankCluster_shadingDensity
    (plankSeedAffineEquiv D) D theta i

#print axioms plankSeedCertificate_side_pos
#print axioms plankSeedRadius_pos
#print axioms plankSeedAffineEquiv_inner_apply
#print axioms image_seedBody_subset_closedBall_one
#print axioms canonicalSeedwiseAffine_diagonal_subset_closedBall_one
#print axioms canonicalSeedwiseAffine_cluster_averageMultiplicity
#print axioms canonicalSeedwiseAffine_cluster_shadingDensity

end
end Family8PlankThickControlCanonicalSeedNormalizationV3
