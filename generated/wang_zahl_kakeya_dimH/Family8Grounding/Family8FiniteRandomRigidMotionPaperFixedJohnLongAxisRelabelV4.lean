import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnBoundedPackingMeanV5
import Submission.Kakeya.ConvexFactoring.FrameBoxCoordinateWindowEquiv
import Mathlib.Tactic

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRandomRigidMotionPaperFixedJohnLongAxisRelabelV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.TransverseCoordinateOverlap
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionPaperFixedJohnConflictGridV4
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperFixedJohnExactMeanSelectorV4
open Family8FiniteRandomRigidMotionPaperFixedJohnBoundedPackingMeanV5
open Family8PolynomialJohnFrameBoxTestNetV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

/-! Carrier-preserving relabeling which places a proved long John side in
coordinate `2`.  No ordering of the original John certificate is assumed. -/

def relabelFrameBox (B : FrameBox) (e : Equiv.Perm (Fin 3)) : FrameBox where
  center := B.center
  frame := B.frame.reindex e
  side := fun i => B.side (e.symm i)

@[simp] theorem relabelFrameBox_center
    (B : FrameBox) (e : Equiv.Perm (Fin 3)) :
    (relabelFrameBox B e).center = B.center := rfl

@[simp] theorem relabelFrameBox_frame_apply
    (B : FrameBox) (e : Equiv.Perm (Fin 3)) (i : Fin 3) :
    (relabelFrameBox B e).frame i = B.frame (e.symm i) := by
  exact B.frame.reindex_apply e i

@[simp] theorem relabelFrameBox_side
    (B : FrameBox) (e : Equiv.Perm (Fin 3)) (i : Fin 3) :
    (relabelFrameBox B e).side i = B.side (e.symm i) := rfl

theorem relabelFrameBox_carrier
    (B : FrameBox) (e : Equiv.Perm (Fin 3)) :
    (relabelFrameBox B e).carrier = B.carrier := by
  rw [FrameBox.carrier_eq_centeredCoordinateWindow,
    FrameBox.carrier_eq_centeredCoordinateWindow]
  ext x
  rw [mem_centeredCoordinateWindow_iff,
    mem_centeredCoordinateWindow_iff]
  constructor
  · intro hx i
    have h := hx (e i)
    simpa only [FrameBox.coordinateCenter, FrameBox.coordinateHalf,
      relabelFrameBox_center, relabelFrameBox_frame_apply,
      relabelFrameBox_side, e.symm_apply_apply] using h
  · intro hx i
    have h := hx (e.symm i)
    simpa only [FrameBox.coordinateCenter, FrameBox.coordinateHalf,
      relabelFrameBox_center, relabelFrameBox_frame_apply,
      relabelFrameBox_side, e.apply_symm_apply] using h

theorem relabelFrameBox_body
    (B : FrameBox) (e : Equiv.Perm (Fin 3)) :
    (relabelFrameBox B e).body = B.body := by
  apply ConvexBody.ext
  exact relabelFrameBox_carrier B e

theorem volume_relabelFrameBox
    (B : FrameBox) (e : Equiv.Perm (Fin 3)) :
    volume ((relabelFrameBox B e).body : Set Space) =
      volume (B.body : Set Space) := by
  rw [relabelFrameBox_body B e]

/-- The unit axis inside the outer John box forces a side of length at least
`1/2`; the rational constant follows directly from three-coordinate Parseval. -/
theorem exists_half_le_capturedJohnSide
    {rho : NNReal} (p : CapturedJohnParameter rho) :
    exists i : Fin 3, (1 / 2 : NNReal) <= p.side i := by
  let B := p.certificate.box
  let T := p.witnessTube
  have hbaseTube : T.axis.base ∈ T.carrier :=
    T.axis_subset_carrier T.axis.base_mem_carrier
  have hendTube : T.axis.endpoint ∈ T.carrier :=
    T.axis_subset_carrier T.axis.endpoint_mem_carrier
  have hbase : T.axis.base ∈ B.carrier :=
    p.certificate.outer_le (p.tube_subset_body hbaseTube)
  have hend : T.axis.endpoint ∈ B.carrier :=
    p.certificate.outer_le (p.tube_subset_body hendTube)
  have hcoord (i : Fin 3) :
      |inner Real (B.frame i) T.axis.direction| <= (p.side i : Real) := by
    have hb := B.centeredCoordinate_abs_le_halfSide hbase i
    have he := B.centeredCoordinate_abs_le_halfSide hend i
    rw [congrFun p.certificate.side_eq i] at hb he
    change
      |inner Real (B.frame i) T.axis.base -
        inner Real (B.frame i) B.center| <= (p.side i : Real) / 2 at hb
    change
      |inner Real (B.frame i) T.axis.endpoint -
        inner Real (B.frame i) B.center| <= (p.side i : Real) / 2 at he
    have htriangle :
        |inner Real (B.frame i) T.axis.endpoint -
            inner Real (B.frame i) T.axis.base| <=
          |inner Real (B.frame i) T.axis.endpoint -
              inner Real (B.frame i) B.center| +
            |inner Real (B.frame i) T.axis.base -
              inner Real (B.frame i) B.center| := by
      calc
        |inner Real (B.frame i) T.axis.endpoint -
            inner Real (B.frame i) T.axis.base| <=
          |inner Real (B.frame i) T.axis.endpoint -
              inner Real (B.frame i) B.center| +
            |inner Real (B.frame i) B.center -
              inner Real (B.frame i) T.axis.base| := abs_sub_le _ _ _
        _ = |inner Real (B.frame i) T.axis.endpoint -
              inner Real (B.frame i) B.center| +
            |inner Real (B.frame i) T.axis.base -
              inner Real (B.frame i) B.center| := by
          rw [abs_sub_comm
            (inner Real (B.frame i) B.center)
            (inner Real (B.frame i) T.axis.base)]
    calc
      |inner Real (B.frame i) T.axis.direction| =
          |inner Real (B.frame i) T.axis.endpoint -
            inner Real (B.frame i) T.axis.base| := by
        simp only [T, UnitSegment.endpoint, inner_add_right]
        ring
      _ <= |inner Real (B.frame i) T.axis.endpoint -
              inner Real (B.frame i) B.center| +
            |inner Real (B.frame i) T.axis.base -
              inner Real (B.frame i) B.center| := htriangle
      _ <= (p.side i : Real) / 2 + (p.side i : Real) / 2 :=
        add_le_add he hb
      _ = (p.side i : Real) := by ring
  by_contra hnone
  rw [not_exists] at hnone
  have hsmall (i : Fin 3) :
      |inner Real (B.frame i) T.axis.direction| < (1 / 2 : Real) := by
    have hside : p.side i < (1 / 2 : NNReal) :=
      lt_of_not_ge (hnone i)
    exact (hcoord i).trans_lt (by exact_mod_cast hside)
  have h0 := abs_lt.mp (hsmall 0)
  have h1 := abs_lt.mp (hsmall 1)
  have h2 := abs_lt.mp (hsmall 2)
  have hparseval := B.frame.sum_sq_inner_right T.axis.direction
  rw [Fin.sum_univ_three, T.axis.norm_direction] at hparseval
  norm_num at h0 h1 h2
  nlinarith [sq_nonneg (inner Real (B.frame 0) T.axis.direction),
    sq_nonneg (inner Real (B.frame 1) T.axis.direction),
    sq_nonneg (inner Real (B.frame 2) T.axis.direction)]

def capturedJohnLongIndex
    {rho : NNReal} (p : CapturedJohnParameter rho) : Fin 3 :=
  Classical.choose (exists_half_le_capturedJohnSide p)

theorem half_le_capturedJohnLongIndex_side
    {rho : NNReal} (p : CapturedJohnParameter rho) :
    (1 / 2 : NNReal) <= p.side (capturedJohnLongIndex p) :=
  Classical.choose_spec (exists_half_le_capturedJohnSide p)

def fixedJohnRepresentativeParameter
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) : CapturedJohnParameter (delta / 8) :=
  representativeParameter (delta / 8) (admissibleNormalizedRadiusPos hD)
    (normalizedJohnCatalogueOfIndex K)

def fixedJohnLongPermutation
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) : Equiv.Perm (Fin 3) :=
  Equiv.swap 2
    (capturedJohnLongIndex (fixedJohnRepresentativeParameter D hD K))

def fixedJohnLongTestBox
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) : FrameBox :=
  relabelFrameBox
    (representativeTestBox (delta / 8)
      (admissibleNormalizedRadiusPos hD)
      (normalizedJohnCatalogueOfIndex K))
    (fixedJohnLongPermutation D hD K)

def fixedJohnLongSide
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) : Fin 3 → NNReal :=
  (fixedJohnLongTestBox D hD K).side

theorem fixedJohnLongTestBox_body_eq
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) :
    (fixedJohnLongTestBox D hD K).body =
      fixedJohnCatalogueBody hD K := by
  unfold fixedJohnLongTestBox fixedJohnCatalogueBody
    normalizedJohnCatalogueBody representativeTestBody
  exact relabelFrameBox_body _ _

theorem one_le_fixedJohnLongSide_two
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) :
    1 <= fixedJohnLongSide D hD K 2 := by
  let p := fixedJohnRepresentativeParameter D hD K
  have hp := half_le_capturedJohnLongIndex_side p
  change 1 <= (relabelFrameBox (p.certificate.box.rescale 2)
    (Equiv.swap 2 (capturedJohnLongIndex p))).side 2
  simp only [relabelFrameBox_side, Equiv.symm_swap,
    Equiv.swap_apply_left, FrameBox.rescale_side]
  rw [congrFun p.certificate.side_eq (capturedJohnLongIndex p)]
  nlinarith

theorem normalizedRadius_le_fixedJohnLongSide
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) (j : Fin 3) :
    delta / 8 <= fixedJohnLongSide D hD K j := by
  let p := fixedJohnRepresentativeParameter D hD K
  let e : Equiv.Perm (Fin 3) :=
    Equiv.swap 2 (capturedJohnLongIndex p)
  have hp : 2 * (delta / 8) <= p.side (e.symm j) :=
    p.two_mul_delta_le_side (e.symm j)
  change delta / 8 <=
    (relabelFrameBox (p.certificate.box.rescale 2) e).side j
  simp only [relabelFrameBox_side, FrameBox.rescale_side,
    congrFun p.certificate.side_eq (e.symm j)]
  nlinarith

theorem fixedJohnCatalogueBody_hasLongBoxDimensions
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) :
    HasBoxDimensions 1 (fixedJohnLongSide D hD K)
      (fixedJohnCatalogueBody hD K) := by
  let B := fixedJohnLongTestBox D hD K
  refine ⟨by norm_num, B, rfl, ?_, ?_⟩
  · have hinv : (1 : NNReal)⁻¹ = 1 := by norm_num
    rw [hinv]
    have hrescale : B.rescale 1 = B := by
      cases B
      simp [FrameBox.rescale]
    rw [hrescale, fixedJohnLongTestBox_body_eq D hD K]
  · rw [fixedJohnLongTestBox_body_eq D hD K]

#print axioms relabelFrameBox_carrier
#print axioms relabelFrameBox_body
#print axioms exists_half_le_capturedJohnSide
#print axioms one_le_fixedJohnLongSide_two
#print axioms normalizedRadius_le_fixedJohnLongSide
#print axioms fixedJohnCatalogueBody_hasLongBoxDimensions

end
end Family8FiniteRandomRigidMotionPaperFixedJohnLongAxisRelabelV4
