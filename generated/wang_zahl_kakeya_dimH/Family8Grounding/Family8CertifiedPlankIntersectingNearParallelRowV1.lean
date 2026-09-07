import Family8Grounding.Family8CertifiedPlankDyadicCordobaV2
import Family8Grounding.Family8FiniteRandomRigidMotionPaperTransverseCoordinateAngleV1
import Submission.Kakeya.ConvexFactoring.FrameBoxCoordinateWindowEquiv
import Submission.Kakeya.ConvexFactoring.FrameBoxVolume
import Mathlib.Tactic

/-!
# A sharp container for an intersecting near-parallel plank row

This is the geometric content of Appendix B, Lemma B.2, specialized to the
normalized `a x b x 1` plank coordinates used by Family 8.  The row contains
only bodies which actually meet the fixed body.  This restriction is
essential: it lets the short-normal offset be paid by the intersection point,
while the common unit-ball support pays only the two long coordinates.

The resulting test box has side vector `8 * theta, 4, 4`, hence volume exactly
`128 * theta`.  No lower bound on an individual shading carrier occurs.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace Matrix

namespace Family8CertifiedPlankIntersectingNearParallelRowV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.TransverseCoordinateOverlap
open Submission.Kakeya.ConvexFactoring
open Family8CertifiedPlankPairOverlapV2
open Family8CertifiedPlankDyadicCordobaV2
open Family8FiniteRandomRigidMotionPaperTransverseCoordinateAngleV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

variable {iota : Type u} [Fintype iota]
variable {F : ConvexFamily iota} {C a b : NNReal}

/-- The deterministic slab-shaped test box attached to row `i` and angular
scale `theta`.  Its normal and centre are those of the certified outer box of
`F i`; only its side vector changes. -/
def certifiedPlankNearParallelTestBox
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (i : iota) (theta : NNReal) : FrameBox where
  center := (cert i).box.center
  frame := (cert i).box.frame
  side := ![8 * theta, 4, 4]

omit [Fintype iota] in
/-- Exact volume of the normalized near-parallel test box. -/
theorem volume_certifiedPlankNearParallelTestBox
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (i : iota) (theta : NNReal) :
    volume
        ((certifiedPlankNearParallelTestBox cert i theta).body : Set Space) =
      128 * (theta : ENNReal) := by
  rw [FrameBox.volume_body, Fin.prod_univ_three]
  simp [certifiedPlankNearParallelTestBox]
  ring

omit [Fintype iota] in
/-- The centre of a certified outer box belongs to its convex body. -/
theorem certifiedPlank_center_mem_body
    {K : ConvexBody Space}
    (cert : PlankDimensionsCertificate C a b K) :
    cert.box.center ∈ (K : Set Space) := by
  apply cert.inner_le
  have h := (cert.box.rescale C⁻¹).center_mem_carrier
  change cert.box.center ∈ (cert.box.rescale C⁻¹).carrier
  exact h

omit [Fintype iota] in
/-- Two points of one certified plank differ by at most the full declared
side in each of its certified frame coordinates. -/
theorem certifiedPlank_abs_inner_sub_le_side
    {K : ConvexBody Space}
    (cert : PlankDimensionsCertificate C a b K)
    {x z : Space} (hx : x ∈ (K : Set Space)) (hz : z ∈ (K : Set Space))
    (k : Fin 3) :
    |⟪cert.box.frame k, x - z⟫_ℝ| ≤ (cert.box.side k : Real) := by
  have hx' := cert.box.centeredCoordinate_abs_le_halfSide
    (cert.outer_le hx) k
  have hz' := cert.box.centeredCoordinate_abs_le_halfSide
    (cert.outer_le hz) k
  rw [inner_sub_right]
  calc
    |⟪cert.box.frame k, x⟫_ℝ - ⟪cert.box.frame k, z⟫_ℝ| ≤
        |⟪cert.box.frame k, x⟫_ℝ -
            ⟪cert.box.frame k, cert.box.center⟫_ℝ| +
          |⟪cert.box.frame k, z⟫_ℝ -
            ⟪cert.box.frame k, cert.box.center⟫_ℝ| := by
      simpa only [abs_sub_comm
        ⟪cert.box.frame k, cert.box.center⟫_ℝ
        ⟪cert.box.frame k, z⟫_ℝ] using
        (abs_sub_le
          ⟪cert.box.frame k, x⟫_ℝ
          ⟪cert.box.frame k, cert.box.center⟫_ℝ
          ⟪cert.box.frame k, z⟫_ℝ)
    _ ≤ (cert.box.side k : Real) / 2 +
          (cert.box.side k : Real) / 2 := add_le_add hx' hz'
    _ = (cert.box.side k : Real) := by ring

/-- Coordinate-free version of the elementary Parseval observation used in
the near-parallel row: when coordinate `0` is `u`, both other coordinates of
a unit vector `v` are bounded by `sin (angle u v)`. -/
theorem abs_inner_frame_le_sin_angle_of_ne_zero
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (u v : Space)
    (hframe : frame 0 = u)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (k : Fin 3) (hk : k ≠ 0) :
    |inner Real (frame k) v| ≤
      Real.sin (InnerProductGeometry.angle u v) := by
  apply (sq_le_sq₀ (abs_nonneg _)
    (InnerProductGeometry.sin_angle_nonneg u v)).mp
  rw [sq_abs]
  have hparseval := frame.sum_sq_inner_right v
  rw [Fin.sum_univ_three, hv] at hparseval
  have hzero :
      inner Real (frame 0) v =
        Real.cos (InnerProductGeometry.angle u v) := by
    rw [hframe]
    exact InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one hu hv
  have htrig := Real.sin_sq_add_cos_sq
    (InnerProductGeometry.angle u v)
  rw [hzero] at hparseval
  norm_num at hparseval
  fin_cases k
  · exact (hk rfl).elim
  · change inner Real (frame 1) v ^ 2 ≤
      Real.sin (InnerProductGeometry.angle u v) ^ 2
    nlinarith [sq_nonneg (inner Real (frame 2) v)]
  · change inner Real (frame 2) v ^ 2 ≤
      Real.sin (InnerProductGeometry.angle u v) ^ 2
    nlinarith [sq_nonneg (inner Real (frame 1) v)]

omit [Fintype iota] in
/-- Projective sine control plus actual intersection controls the entire
short-normal displacement of the second plank from the first plank's middle
plane. -/
theorem abs_inner_short_sub_center_le
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (i j : iota) (theta : NNReal)
    (hsine : certifiedPlankPairSine cert i j ≤ (theta : Real))
    {x z : Space} (hx : x ∈ (F j : Set Space))
    (hzi : z ∈ (F i : Set Space)) (hzj : z ∈ (F j : Set Space)) :
    |inner Real ((cert i).box.frame 0) x -
        inner Real ((cert i).box.frame 0) (cert i).box.center| ≤
      (a : Real) * (3 / 2 : Real) + 2 * (theta : Real) := by
  let fi := (cert i).box.frame
  let fj := (cert j).box.frame
  let d := x - z
  have hd (k : Fin 3) :
      |inner Real (fj k) d| ≤ ((cert j).box.side k : Real) := by
    exact certifiedPlank_abs_inner_sub_le_side (cert j) hx hzj k
  have hside0 : ((cert j).box.side 0 : Real) = (a : Real) := by
    rw [(cert j).side_eq]
    rfl
  have hside1 : ((cert j).box.side 1 : Real) = (b : Real) := by
    rw [(cert j).side_eq]
    rfl
  have hside2 : ((cert j).box.side 2 : Real) = 1 := by
    rw [(cert j).side_eq]
    rfl
  have hcoeff0 : |inner Real (fj 0) (fi 0)| ≤ 1 := by
    simpa [fj, fi, (cert j).box.frame.norm_eq_one,
      (cert i).box.frame.norm_eq_one] using
      abs_real_inner_le_norm (fj 0) (fi 0)
  have hcoeff1 : |inner Real (fj 1) (fi 0)| ≤ (theta : Real) := by
    have h := abs_inner_frame_le_sin_angle_of_ne_zero
      fj (fj 0) (fi 0) rfl
      ((cert j).box.frame.norm_eq_one 0)
      ((cert i).box.frame.norm_eq_one 0) 1 (by decide)
    have hsine' :
        Real.sin (InnerProductGeometry.angle (fj 0) (fi 0)) ≤
          (theta : Real) := by
      simpa [fj, fi, certifiedPlankPairSine,
        InnerProductGeometry.angle_comm] using hsine
    exact h.trans hsine'
  have hcoeff2 : |inner Real (fj 2) (fi 0)| ≤ (theta : Real) := by
    have h := abs_inner_frame_le_sin_angle_of_ne_zero
      fj (fj 0) (fi 0) rfl
      ((cert j).box.frame.norm_eq_one 0)
      ((cert i).box.frame.norm_eq_one 0) 2 (by decide)
    have hsine' :
        Real.sin (InnerProductGeometry.angle (fj 0) (fi 0)) ≤
          (theta : Real) := by
      simpa [fj, fi, certifiedPlankPairSine,
        InnerProductGeometry.angle_comm] using hsine
    exact h.trans hsine'
  have hdecomp :
      inner Real (fi 0) d =
        ∑ k, inner Real (fj k) (fi 0) * inner Real (fj k) d := by
    have hrepr := fj.sum_repr' (fi 0)
    calc
      inner Real (fi 0) d =
          inner Real (∑ k, inner Real (fj k) (fi 0) • fj k) d := by rw [hrepr]
      _ = ∑ k, inner Real (fj k) (fi 0) * inner Real (fj k) d := by
        rw [sum_inner]
        apply Finset.sum_congr rfl
        intro k _hk
        rw [real_inner_smul_left]
  have hnormal : |inner Real (fi 0) d| ≤
      (a : Real) + 2 * (theta : Real) := by
    rw [hdecomp, Fin.sum_univ_three]
    calc
      |inner Real (fj 0) (fi 0) * inner Real (fj 0) d +
          inner Real (fj 1) (fi 0) * inner Real (fj 1) d +
          inner Real (fj 2) (fi 0) * inner Real (fj 2) d| ≤
          |inner Real (fj 0) (fi 0) * inner Real (fj 0) d| +
          |inner Real (fj 1) (fi 0) * inner Real (fj 1) d| +
          |inner Real (fj 2) (fi 0) * inner Real (fj 2) d| := by
        exact (abs_add_le _ _).trans <|
          add_le_add (abs_add_le _ _) le_rfl
      _ = |inner Real (fj 0) (fi 0)| * |inner Real (fj 0) d| +
          |inner Real (fj 1) (fi 0)| * |inner Real (fj 1) d| +
          |inner Real (fj 2) (fi 0)| * |inner Real (fj 2) d| := by
        simp only [abs_mul]
      _ ≤ 1 * (a : Real) + (theta : Real) * (b : Real) +
          (theta : Real) * 1 := by
        have h0 := mul_le_mul hcoeff0 (by simpa only [hside0] using hd 0)
          (abs_nonneg _) (by norm_num)
        have h1 := mul_le_mul hcoeff1 (by simpa only [hside1] using hd 1)
          (abs_nonneg _) (by positivity)
        have h2 := mul_le_mul hcoeff2 (by simpa only [hside2] using hd 2)
          (abs_nonneg _) (by positivity)
        exact add_le_add (add_le_add h0 h1) h2
      _ ≤ (a : Real) + 2 * (theta : Real) := by
        have hb : (b : Real) ≤ 1 := by exact_mod_cast (cert j).b_le_one
        have ht : (0 : Real) ≤ theta := by positivity
        nlinarith
  have hziCoord := (cert i).box.centeredCoordinate_abs_le_halfSide
    ((cert i).outer_le hzi) 0
  have hziCoord' :
      |inner Real (fi 0) z - inner Real (fi 0) (cert i).box.center| ≤
        (a : Real) / 2 := by
    simpa [fi, (cert i).side_eq, plankSides] using hziCoord
  calc
    |inner Real (fi 0) x - inner Real (fi 0) (cert i).box.center| ≤
        |inner Real (fi 0) x - inner Real (fi 0) z| +
          |inner Real (fi 0) z -
            inner Real (fi 0) (cert i).box.center| := by
      exact abs_sub_le _ _ _
    _ ≤ ((a : Real) + 2 * (theta : Real)) + (a : Real) / 2 := by
      gcongr
      simpa [d, fi, inner_sub_right] using hnormal
    _ = (a : Real) * (3 / 2 : Real) + 2 * (theta : Real) := by ring

omit [Fintype iota] in
/-- Appendix-B.2 containment in normalized coordinates.  The common
unit-ball support controls the two long coordinates, while actual
intersection and projective sine control give the sharp short coordinate. -/
theorem body_subset_certifiedPlankNearParallelTestBox
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (hunit : ∀ k, (F k : Set Space) ⊆ Metric.closedBall (0 : Space) 1)
    (i j : iota) (theta : NNReal)
    (haTheta : a ≤ theta)
    (hsine : certifiedPlankPairSine cert i j ≤ (theta : Real))
    (hinter : ((F i : Set Space) ∩ (F j : Set Space)).Nonempty) :
    (F j : Set Space) ⊆
      (certifiedPlankNearParallelTestBox cert i theta).carrier := by
  rintro x hx
  obtain ⟨z, hzi, hzj⟩ := hinter
  rw [FrameBox.carrier_eq_centeredCoordinateWindow,
    mem_centeredCoordinateWindow_iff]
  intro k
  simp only [FrameBox.coordinateCenter, FrameBox.coordinateHalf]
  fin_cases k
  · have hnormal := abs_inner_short_sub_center_le
      cert i j theta hsine hx hzi hzj
    change
      |inner Real ((cert i).box.frame 0) x -
          inner Real ((cert i).box.frame 0) (cert i).box.center| ≤
        ((((8 * theta : NNReal) / 2 : NNReal) : Real))
    have ha : (a : Real) ≤ theta := by exact_mod_cast haTheta
    norm_num [NNReal.coe_div]
    nlinarith
  · have hcenter : (cert i).box.center ∈ (F i : Set Space) :=
      certifiedPlank_center_mem_body (cert i)
    have hxBall := hunit j hx
    have hcBall := hunit i hcenter
    rw [Metric.mem_closedBall] at hxBall hcBall
    have hdist : dist x (cert i).box.center ≤ (2 : Real) := by
      calc
        dist x (cert i).box.center ≤ dist x 0 + dist 0 (cert i).box.center :=
          dist_triangle _ _ _
        _ ≤ 1 + 1 := add_le_add hxBall (by simpa [dist_comm] using hcBall)
        _ = 2 := by norm_num
    have hinner :
        |inner Real ((cert i).box.frame 1) x -
          inner Real ((cert i).box.frame 1) (cert i).box.center| ≤ 2 := by
      rw [← inner_sub_right]
      calc
        |inner Real ((cert i).box.frame 1) (x - (cert i).box.center)| ≤
            ‖(cert i).box.frame 1‖ * ‖x - (cert i).box.center‖ :=
          abs_real_inner_le_norm _ _
        _ = dist x (cert i).box.center := by
          rw [(cert i).box.frame.norm_eq_one, one_mul, dist_eq_norm]
        _ ≤ 2 := hdist
    change
      |inner Real ((cert i).box.frame 1) x -
          inner Real ((cert i).box.frame 1) (cert i).box.center| ≤
        ((((4 : NNReal) / 2 : NNReal) : Real))
    norm_num [NNReal.coe_div]
    exact hinner

  · have hcenter : (cert i).box.center ∈ (F i : Set Space) :=
      certifiedPlank_center_mem_body (cert i)
    have hxBall := hunit j hx
    have hcBall := hunit i hcenter
    rw [Metric.mem_closedBall] at hxBall hcBall
    have hdist : dist x (cert i).box.center ≤ (2 : Real) := by
      calc
        dist x (cert i).box.center ≤ dist x 0 + dist 0 (cert i).box.center :=
          dist_triangle _ _ _
        _ ≤ 1 + 1 := add_le_add hxBall (by simpa [dist_comm] using hcBall)
        _ = 2 := by norm_num
    have hinner :
        |inner Real ((cert i).box.frame 2) x -
          inner Real ((cert i).box.frame 2) (cert i).box.center| ≤ 2 := by
      rw [← inner_sub_right]
      calc
        |inner Real ((cert i).box.frame 2) (x - (cert i).box.center)| ≤
            ‖(cert i).box.frame 2‖ * ‖x - (cert i).box.center‖ :=
          abs_real_inner_le_norm _ _
        _ = dist x (cert i).box.center := by
          rw [(cert i).box.frame.norm_eq_one, one_mul, dist_eq_norm]
        _ ≤ 2 := hdist
    change
      |inner Real ((cert i).box.frame 2) x -
          inner Real ((cert i).box.frame 2) (cert i).box.center| ≤
        ((((4 : NNReal) / 2 : NNReal) : Real))
    norm_num [NNReal.coe_div]
    exact hinner

/-! ## The actual labelled interaction row -/

/-- The row used by the labelled slab estimate: unlike the older angle-only
row, it retains only bodies which actually meet the fixed body. -/
def certifiedPlankIntersectingNearParallelRow
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (i : iota) (theta : NNReal) : Finset iota := by
  classical
  exact Finset.univ.filter fun j ↦
    ((F i : Set Space) ∩ (F j : Set Space)).Nonempty ∧
      certifiedPlankPairSine cert i j ≤ (theta : Real)

@[simp] theorem mem_certifiedPlankIntersectingNearParallelRow
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (i j : iota) (theta : NNReal) :
    j ∈ certifiedPlankIntersectingNearParallelRow cert i theta ↔
      ((F i : Set Space) ∩ (F j : Set Space)).Nonempty ∧
        certifiedPlankPairSine cert i j ≤ (theta : Real) := by
  classical
  simp [certifiedPlankIntersectingNearParallelRow]

/-- Katz--Tao nonconcentration applied to the sharp B.2 test box gives the
labelled body-mass form of the intersecting near-parallel row estimate. -/
theorem sum_body_volume_intersectingNearParallelRow_le
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (hunit : ∀ k, (F k : Set Space) ⊆ Metric.closedBall (0 : Space) 1)
    (D : ENNReal) (hKT : IsKatzTao D F)
    (i : iota) (theta : NNReal) (haTheta : a ≤ theta) :
    (∑ j ∈ certifiedPlankIntersectingNearParallelRow cert i theta,
        volume (F j : Set Space)) ≤
      D * (128 * (theta : ENNReal)) := by
  let K : ConvexBody Space :=
    (certifiedPlankNearParallelTestBox cert i theta).body
  have hrow :
      (∑ j ∈ certifiedPlankIntersectingNearParallelRow cert i theta,
          volume (F j : Set Space)) ≤ containedMass F K := by
    unfold containedMass
    apply Finset.sum_le_sum_of_subset
    intro j hj
    rw [mem_containedIndices]
    have hj' :=
      (mem_certifiedPlankIntersectingNearParallelRow cert i j theta).1 hj
    exact body_subset_certifiedPlankNearParallelTestBox cert hunit i j theta
      haTheta hj'.2 hj'.1
  calc
    (∑ j ∈ certifiedPlankIntersectingNearParallelRow cert i theta,
        volume (F j : Set Space)) ≤ containedMass F K := hrow
    _ ≤ D * volume (K : Set Space) := by
      simpa [IsKatzTaoAt] using hKT K
    _ = D * (128 * (theta : ENNReal)) := by
      rw [volume_certifiedPlankNearParallelTestBox]

#print axioms volume_certifiedPlankNearParallelTestBox
#print axioms certifiedPlank_center_mem_body
#print axioms certifiedPlank_abs_inner_sub_le_side
#print axioms abs_inner_short_sub_center_le
#print axioms body_subset_certifiedPlankNearParallelTestBox
#print axioms sum_body_volume_intersectingNearParallelRow_le

end
end Family8CertifiedPlankIntersectingNearParallelRowV1
