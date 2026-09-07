import Family8Grounding.Family8PlankThickControlLongTubeClusterDatumV2
import Submission.Kakeya.ConvexFactoring.BufferedHomotheticCore
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8PlankLongTubeAmbientB2SupportV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.BufferedHomotheticCore
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8CertifiedPlankPairOverlapV2
open Family8PlankCertificateLongTubeCoverV2
open Family8PlankThickControlCanonicalSeedNormalizationV3

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Universe-polymorphic common B2 support for the long-tube cover

V1 is SAFE but its index variable was accidentally fixed to `Type 0`.
V2 was a failed inner-product-notation draft. This successor repeats the
construction at an arbitrary universe and imports neither predecessor.
-/

def ambientPlankCertificate
    (D : ShadedConvexPlankFamily iota a b) :
    PlankDimensionsCertificate D.ambientComparisonConstant 1 1 D.ambient :=
  Classical.choice
    (IsPlank.nonempty_plankDimensionsCertificate D.ambient_is_unit_scale)

theorem plankSeedCertificate_center_mem_source
    (D : ShadedConvexPlankFamily iota a b) (i : iota) :
    (plankSeedCertificate D i).box.center ∈ (D.family i : Set Space) := by
  exact certificateCenter_mem_body
    (plankSeedCertificate D i).toBoxDimensionsCertificate

theorem dist_plankSeedCenter_ambientCenter_le_one
    (D : ShadedConvexPlankFamily iota a b) (i : iota) :
    dist (plankSeedCertificate D i).box.center
        (ambientPlankCertificate D).box.center ≤ 1 := by
  let A := ambientPlankCertificate D
  let p : Space := (plankSeedCertificate D i).box.center
  have hpAmbient : p ∈ (D.ambient : Set Space) :=
    D.contained_in_ambient i (plankSeedCertificate_center_mem_source D i)
  have hpBox : p ∈ A.box.carrier := A.outer_le hpAmbient
  have hcoord (k : Fin 3) :
      |⟪A.box.frame k, p⟫_Real -
        ⟪A.box.frame k, A.box.center⟫_Real| ≤ (1 / 2 : Real) := by
    have h := A.box.centeredCoordinate_abs_le_halfSide hpBox k
    rw [A.side_eq] at h
    fin_cases k <;> simpa [plankSides, NNReal.coe_div] using h
  let c0 : Real := ⟪A.box.frame 0, p - A.box.center⟫_Real
  let c1 : Real := ⟪A.box.frame 1, p - A.box.center⟫_Real
  let c2 : Real := ⟪A.box.frame 2, p - A.box.center⟫_Real
  have hsq (k : Fin 3) :
      ⟪A.box.frame k, p - A.box.center⟫_Real ^ 2 ≤
        (1 / 2 : Real) ^ 2 := by
    have habs :
        |⟪A.box.frame k, p - A.box.center⟫_Real| ≤ (1 / 2 : Real) := by
      simpa [inner_sub_right] using hcoord k
    have hsquare :=
      (sq_le_sq₀ (abs_nonneg
        ⟪A.box.frame k, p - A.box.center⟫_Real)
        (by norm_num : (0 : Real) ≤ 1 / 2)).2 habs
    simpa only [sq_abs] using hsquare
  have hc0 : c0 ^ 2 ≤ (1 / 2 : Real) ^ 2 := hsq 0
  have hc1 : c1 ^ 2 ≤ (1 / 2 : Real) ^ 2 := hsq 1
  have hc2 : c2 ^ 2 ≤ (1 / 2 : Real) ^ 2 := hsq 2
  have hparseval := A.box.frame.sum_sq_inner_right (p - A.box.center)
  rw [Fin.sum_univ_three] at hparseval
  change c0 ^ 2 + c1 ^ 2 + c2 ^ 2 = ‖p - A.box.center‖ ^ 2 at hparseval
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (p - A.box.center)]

/-- Every genuine long-tube cover member is contained in one common
radius-two ball determined solely by the actual ambient box certificate. -/
theorem longTubeCover_subset_closedBall_ambientCenter_two
    (D : ShadedConvexPlankFamily iota a b) (hb : b ≤ (2 : NNReal)⁻¹)
    (i : iota) :
    ((plankLongTubeCoverFamily D).tubes i).carrier ⊆
      Metric.closedBall (ambientPlankCertificate D).box.center 2 := by
  intro x hx
  let T := (plankLongTubeCoverFamily D).tubes i
  rw [Tube.carrier,
    T.axis.isCompact_carrier.cthickening_eq_biUnion_closedBall
      (show 0 ≤ (b : Real) by positivity)] at hx
  simp only [mem_iUnion, Metric.mem_closedBall] at hx
  obtain ⟨y, hyAxis, hxy⟩ := hx
  rw [T.axis.carrier_eq_image] at hyAxis
  obtain ⟨t, ht, rfl⟩ := hyAxis
  have htAbs : |t - (2 : Real)⁻¹| ≤ (2 : Real)⁻¹ := by
    rw [abs_le]
    constructor <;> norm_num at * <;> linarith [ht.1, ht.2]
  let cert := plankSeedCertificate D i
  have haxisVec :
      (T.axis.base + t • T.axis.direction) -
          (ambientPlankCertificate D).box.center =
        (cert.box.center - (ambientPlankCertificate D).box.center) +
          (t - (2 : Real)⁻¹) • cert.box.frame 2 := by
    simp only [T, plankLongTubeCoverFamily_tubes,
      plankCertificateLongTube, plankCertificateLongAxis, cert]
    module
  have hyAmbient :
      dist (T.axis.base + t • T.axis.direction)
        (ambientPlankCertificate D).box.center ≤ (3 / 2 : Real) := by
    rw [dist_eq_norm, haxisVec]
    calc
      ‖(cert.box.center - (ambientPlankCertificate D).box.center) +
          (t - (2 : Real)⁻¹) • cert.box.frame 2‖ ≤
          ‖cert.box.center - (ambientPlankCertificate D).box.center‖ +
            ‖(t - (2 : Real)⁻¹) • cert.box.frame 2‖ := norm_add_le _ _
      _ = dist cert.box.center (ambientPlankCertificate D).box.center +
          |t - (2 : Real)⁻¹| := by
        rw [dist_eq_norm]
        simp [norm_smul, cert.box.frame.norm_eq_one]
      _ ≤ 1 + (2 : Real)⁻¹ :=
        add_le_add (dist_plankSeedCenter_ambientCenter_le_one D i) htAbs
      _ = (3 / 2 : Real) := by norm_num
  rw [Metric.mem_closedBall]
  calc
    dist x (ambientPlankCertificate D).box.center ≤
        dist x (T.axis.base + t • T.axis.direction) +
          dist (T.axis.base + t • T.axis.direction)
            (ambientPlankCertificate D).box.center := dist_triangle _ _ _
    _ ≤ (b : Real) + (3 / 2 : Real) := add_le_add hxy hyAmbient
    _ ≤ 2 := by
      have hbR : (b : Real) ≤ (2 : Real)⁻¹ := by exact_mod_cast hb
      linarith

#print axioms plankSeedCertificate_center_mem_source
#print axioms dist_plankSeedCenter_ambientCenter_le_one
#print axioms longTubeCover_subset_closedBall_ambientCenter_two

end
end Family8PlankLongTubeAmbientB2SupportV3
