import Family8Grounding.Family8FiniteRandomRigidMotionPaperTranslationBodyGridV1
import Submission.Kakeya.ConvexFactoring.TubeFrameBoxDimensions
import Submission.Kakeya.ConvexFactoring.FrameBoxVolume
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators Matrix

namespace Family8FiniteRandomRigidMotionPaperElongatedFrameTestV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.TransverseCoordinateOverlap
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1

noncomputable section

/-!
# Honest longitudinally enlarged paper tests

The repository's `hundredTube` keeps a unit axis and changes only its radius.
The test used in the paper must also absorb longitudinal displacement.  We
therefore use an aligned frame box with full side lengths
`200 rho, 200 rho, 6`.  Its body is compact and convex, contains its anchor
`rho`-tube, and has exact volume `240000 rho^2`; thus longitudinal enlargement
costs only an absolute constant and preserves the required tube-volume scale.
-/

/-- Side lengths of the honest elongated conflict test. -/
def paperElongatedSides (rho : NNReal) : Fin 3 -> NNReal :=
  ![200 * rho, 200 * rho, 6]

/-- The length-six aligned frame box centered at the tube-axis midpoint. -/
def paperElongatedFrameBox {rho : NNReal} (T : Tube rho)
    (frame : OrthonormalBasis (Fin 3) Real Space) : FrameBox where
  center := tubeAxisMidpoint T
  frame := frame
  side := paperElongatedSides rho

@[simp] theorem paperElongatedFrameBox_center
    {rho : NNReal} (T : Tube rho)
    (frame : OrthonormalBasis (Fin 3) Real Space) :
    (paperElongatedFrameBox T frame).center = tubeAxisMidpoint T := rfl

@[simp] theorem paperElongatedFrameBox_frame
    {rho : NNReal} (T : Tube rho)
    (frame : OrthonormalBasis (Fin 3) Real Space) :
    (paperElongatedFrameBox T frame).frame = frame := rfl

@[simp] theorem paperElongatedFrameBox_side
    {rho : NNReal} (T : Tube rho)
    (frame : OrthonormalBasis (Fin 3) Real Space) :
    (paperElongatedFrameBox T frame).side = paperElongatedSides rho := rfl

/-- The corresponding actual compact convex test body. -/
def paperElongatedBody {rho : NNReal} (T : Tube rho)
    (frame : OrthonormalBasis (Fin 3) Real Space) : ConvexBody Space :=
  (paperElongatedFrameBox T frame).body

@[simp] theorem coe_paperElongatedBody
    {rho : NNReal} (T : Tube rho)
    (frame : OrthonormalBasis (Fin 3) Real Space) :
    (paperElongatedBody T frame : Set Space) =
      (paperElongatedFrameBox T frame).carrier := rfl

/-- Same-center, same-frame boxes are monotone in their full side lengths. -/
theorem FrameBox.carrier_subset_of_center_frame_side_le
    (B C : FrameBox)
    (hcenter : B.center = C.center)
    (hframe : B.frame = C.frame)
    (hside : forall i, B.side i <= C.side i) :
    B.carrier ⊆ C.carrier := by
  rw [B.carrier_eq_centeredCoordinateWindow,
    C.carrier_eq_centeredCoordinateWindow]
  intro x hx
  rw [mem_centeredCoordinateWindow_iff] at hx ⊢
  intro i
  have hi := hx i
  simp only [FrameBox.coordinateCenter, FrameBox.coordinateHalf] at hi ⊢
  rw [<- hcenter, <- hframe]
  exact hi.trans (by
    norm_cast
    gcongr
    exact hside i)

/-- The natural outer box of a unit tube fits in the elongated test whenever
the radius is at most one. -/
theorem alignedFrameBox_carrier_subset_paperElongatedFrameBox
    {rho : NNReal} (T : Tube rho)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hrho : rho <= 1) :
    (T.alignedFrameBox frame).carrier ⊆
      (paperElongatedFrameBox T frame).carrier := by
  apply FrameBox.carrier_subset_of_center_frame_side_le
  · simp [paperElongatedFrameBox, tubeAxisMidpoint]
  · rfl
  · intro i
    fin_cases i <;>
      simp [Tube.alignedFrameBox, Tube.frameBoxSides,
        paperElongatedFrameBox, paperElongatedSides] <;>
      nlinarith [rho.2]

/-- In particular the anchor tube lies in its honest elongated test. -/
theorem carrier_subset_paperElongatedBody
    {rho : NNReal} (T : Tube rho)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hframe : frame 2 = T.axis.direction)
    (hrho : rho <= 1) :
    T.carrier ⊆ (paperElongatedBody T frame : Set Space) := by
  rw [coe_paperElongatedBody]
  exact (T.carrier_subset_alignedFrameBox frame hframe).trans
    (alignedFrameBox_carrier_subset_paperElongatedFrameBox T frame hrho)

/-- Exact test-body volume: longitudinal enlargement loses only an absolute
constant and retains the `rho^2` scale. -/
theorem volume_paperElongatedBody
    {rho : NNReal} (T : Tube rho)
    (frame : OrthonormalBasis (Fin 3) Real Space) :
    volume (paperElongatedBody T frame : Set Space) =
      (240000 : ENNReal) * (rho : ENNReal) ^ 2 := by
  rw [paperElongatedBody, FrameBox.volume_body]
  simp [paperElongatedFrameBox, paperElongatedSides,
    Fin.prod_univ_three]
  ring

#print axioms FrameBox.carrier_subset_of_center_frame_side_le
#print axioms carrier_subset_paperElongatedBody
#print axioms volume_paperElongatedBody

end
end Family8FiniteRandomRigidMotionPaperElongatedFrameTestV1
