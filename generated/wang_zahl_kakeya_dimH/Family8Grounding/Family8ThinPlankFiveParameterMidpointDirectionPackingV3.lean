import Family8Grounding.Family8ThinPlankFiveParameterUnorientedFrameBoxPackingV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped NNReal InnerProductSpace

namespace Family8ThinPlankFiveParameterMidpointDirectionPackingV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family4GlobalExtremalUpstream
open Family8CommonPointTubePackingV1
open Family8ThinPlankEssentialDistinctPackingV4
open Family8ThinPlankFiveParameterPackingV2
open Family8ThinPlankFiveParameterFrameBoxPackingV4
open Family8ThinPlankFiveParameterUnorientedFrameBoxPackingV2
open FamilyStickySameRadiusTubeContainmentCompatibleV1

noncomputable section

/-!
# Five-parameter packing from the literal scalar data used by the code

Contracted-John proxy axes are unit extensions of much shorter affine image
segments, so neither full proxy tubes nor their extended axes lie in the
parent image.  The finite packing code only needs the proxy midpoint and its
normalized direction.  This module consumes exactly those quantities.
-/

@[simp] theorem tubeAxisMidpoint_forwardOrientedTube
    {delta : NNReal} (frame : OrthonormalBasis (Fin 3) Real Space)
    (T : Tube delta) :
    tubeAxisMidpoint (forwardOrientedTube
      { center := 0, frame := frame, side := fun _ => 0 } T) =
      tubeAxisMidpoint T := by
  let B : FrameBox := { center := 0, frame := frame, side := fun _ => 0 }
  change tubeAxisMidpoint (forwardOrientedTube B T) = tubeAxisMidpoint T
  by_cases h : 0 ≤ ⟪B.frame 2, T.axis.direction⟫_Real
  · simp [forwardOrientedTube, h]
  · simp only [forwardOrientedTube, h, if_false, tubeAxisMidpoint,
      reversedTube, reversedUnitSegmentBase, reversedUnitSegmentDirection,
      UnitSegment.endpoint]
    module

theorem abs_inner_forwardOrientedTube_direction
    {delta : NNReal} (B : FrameBox) (T : Tube delta) (i : Fin 3) :
    |⟪B.frame i, (forwardOrientedTube B T).axis.direction⟫_Real| =
      |⟪B.frame i, T.axis.direction⟫_Real| := by
  by_cases h : 0 ≤ ⟪B.frame 2, T.axis.direction⟫_Real
  · simp [forwardOrientedTube, h]
  · simp [forwardOrientedTube, h, reversedTube,
      reversedUnitSegmentDirection, inner_neg_right]

@[simp] theorem tubeAxisMidpoint_forwardOrientedTube_frameBox
    {delta : NNReal} (B : FrameBox) (T : Tube delta) :
    tubeAxisMidpoint (forwardOrientedTube B T) = tubeAxisMidpoint T := by
  by_cases h : 0 ≤ ⟪B.frame 2, T.axis.direction⟫_Real
  · simp [forwardOrientedTube, h]
  · simp only [forwardOrientedTube, h, if_false, tubeAxisMidpoint,
      reversedTube, reversedUnitSegmentBase, reversedUnitSegmentDirection,
      UnitSegment.endpoint]
    module

/-- Two normalized short direction bounds recover the omitted long component
by Parseval. -/
theorem half_le_abs_inner_long_of_short_direction_bounds
    {delta : NNReal} (frame : OrthonormalBasis (Fin 3) Real Space)
    (T : Tube delta) (R : Real)
    (hdir0 : |⟪frame 0, T.axis.direction⟫_Real| ≤ (delta : Real))
    (hdir1 : |⟪frame 1, T.axis.direction⟫_Real| ≤ R * (delta : Real))
    (hthin :
      (delta : Real) ^ 2 + (R * (delta : Real)) ^ 2 ≤ (3 : Real) / 4) :
    (1 : Real) / 2 ≤ |⟪frame 2, T.axis.direction⟫_Real| := by
  let c0 : Real := ⟪frame 0, T.axis.direction⟫_Real
  let c1 : Real := ⟪frame 1, T.axis.direction⟫_Real
  let c2 : Real := ⟪frame 2, T.axis.direction⟫_Real
  let d : Real := (delta : Real)
  let w : Real := R * (delta : Real)
  have hc0Bounds := abs_le.mp hdir0
  have hc1Bounds := abs_le.mp hdir1
  have hc0Sq : c0 ^ 2 ≤ d ^ 2 := by
    have hp : 0 ≤ (d - c0) * (d + c0) :=
      mul_nonneg (by linarith [hc0Bounds.2]) (by linarith [hc0Bounds.1])
    nlinarith
  have hc1Sq : c1 ^ 2 ≤ w ^ 2 := by
    have hp : 0 ≤ (w - c1) * (w + c1) :=
      mul_nonneg (by linarith [hc1Bounds.2]) (by linarith [hc1Bounds.1])
    nlinarith
  have hparseval := frame.sum_sq_inner_right T.axis.direction
  rw [Fin.sum_univ_three, T.axis.norm_direction] at hparseval
  norm_num at hparseval
  change c0 ^ 2 + c1 ^ 2 + c2 ^ 2 = 1 at hparseval
  change d ^ 2 + w ^ 2 ≤ (3 : Real) / 4 at hthin
  by_contra hlong
  have hc2abs : |c2| < (1 : Real) / 2 := lt_of_not_ge hlong
  have hc2Bounds := abs_lt.mp hc2abs
  have hp2 : 0 < ((1 : Real) / 2 - c2) * ((1 : Real) / 2 + c2) :=
    mul_pos (by linarith [hc2Bounds.2]) (by linarith [hc2Bounds.1])
  have hc2Sq : c2 ^ 2 < (1 : Real) / 4 := by nlinarith
  nlinarith

/-- The transverse coordinate is controlled directly by midpoint and
direction coordinates. -/
theorem abs_inner_tubePointTransverse_le_midpoint_add_long_mul_direction
    {delta : NNReal} (frame : OrthonormalBasis (Fin 3) Real Space)
    (x : Space) (T : Tube delta) (i : Fin 3) :
    |⟪frame i, tubePointTransverse x T⟫_Real| ≤
      |⟪frame i, tubeAxisMidpoint T - x⟫_Real| +
        |tubePointLongitudinal x T| *
          |⟪frame i, T.axis.direction⟫_Real| := by
  rw [tubePointTransverse, inner_sub_right, real_inner_smul_right]
  exact (abs_sub _ _).trans_eq (by rw [abs_mul])

/-- Orientation-free five-parameter packing from actual midpoint and
normalized-direction bounds.  These are precisely the quantities that a
contracted affine image plus a quantitative image-vector lower bound must
produce. -/
theorem card_le_thinPlankFivePackingNatCap_of_midpoint_direction_bounds
    {delta : NNReal} {parameter : Type} [Fintype parameter]
    [DecidableEq parameter]
    (frame : OrthonormalBasis (Fin 3) Real Space) (x : Space)
    (tube : parameter → Tube delta) (R : Real)
    (hdeltaPos : 0 < delta) (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (hR : 0 ≤ R)
    (hmidNorm : ∀ p, ‖tubeAxisMidpoint (tube p) - x‖ ≤ 2)
    (hmid0 : ∀ p,
      |⟪frame 0, tubeAxisMidpoint (tube p) - x⟫_Real| ≤
        (delta : Real) / 2)
    (hmid1 : ∀ p,
      |⟪frame 1, tubeAxisMidpoint (tube p) - x⟫_Real| ≤
        (R * (delta : Real)) / 2)
    (hdir0 : ∀ p,
      |⟪frame 0, (tube p).axis.direction⟫_Real| ≤ (delta : Real))
    (hdir1 : ∀ p,
      |⟪frame 1, (tube p).axis.direction⟫_Real| ≤ R * (delta : Real))
    (hthin :
      (delta : Real) ^ 2 + (R * (delta : Real)) ^ 2 ≤ (3 : Real) / 4)
    (hpairwise : Set.Pairwise (Set.univ : Set parameter) fun p q =>
      EssentiallyDistinct (tube p) (tube q)) :
    Fintype.card parameter ≤ thinPlankFivePackingNatCap (3 * R) := by
  let B : FrameBox := { center := x, frame := frame, side := fun _ => 0 }
  let oriented : parameter → Tube delta := fun p =>
    forwardOrientedTube B (tube p)
  have hmidEq (p : parameter) :
      tubeAxisMidpoint (oriented p) = tubeAxisMidpoint (tube p) := by
    simpa only [oriented] using
      tubeAxisMidpoint_forwardOrientedTube_frameBox B (tube p)
  have hdirAbs (p : parameter) (i : Fin 3) :
      |⟪frame i, (oriented p).axis.direction⟫_Real| =
        |⟪frame i, (tube p).axis.direction⟫_Real| := by
    simpa only [B] using abs_inner_forwardOrientedTube_direction B (tube p) i
  have hlong (p : parameter) :
      |tubePointLongitudinal x (oriented p)| ≤ 2 := by
    change
      |⟪(oriented p).axis.direction,
        tubeAxisMidpoint (oriented p) - x⟫_Real| ≤ 2
    rw [hmidEq p]
    have hinner := abs_real_inner_le_norm (oriented p).axis.direction
      (tubeAxisMidpoint (tube p) - x)
    rw [(oriented p).axis.norm_direction, one_mul] at hinner
    exact hinner.trans (hmidNorm p)
  have htransverse (p : parameter) :
      ‖tubePointTransverse x (oriented p)‖ ≤ 2 := by
    exact (norm_tubePointTransverse_le_norm_midpoint_sub
      x (oriented p)).trans (by simpa only [hmidEq p] using hmidNorm p)
  have hfixed (p : parameter) (j : Fin 3) :
      |thinPlankFiveFixedCoordinates frame x (oriented p) j| ≤
        thinPlankPackingFixedBound := by
    have hdeltaReal : 0 < (delta : Real) := NNReal.coe_pos.mpr hdeltaPos
    fin_cases j
    · change |tubePointLongitudinal x (oriented p)| ≤ thinPlankPackingFixedBound
      simpa [thinPlankPackingFixedBound] using (hlong p).trans (by norm_num)
    · change
        |⟪frame 0, tubePointTransverse x (oriented p)⟫_Real /
          (delta : Real)| ≤ thinPlankPackingFixedBound
      rw [abs_div, abs_of_pos hdeltaReal]
      have hnum :=
        abs_inner_tubePointTransverse_le_midpoint_add_long_mul_direction
          frame x (oriented p) 0
      rw [hmidEq p, hdirAbs p 0] at hnum
      have hnum' :
          |⟪frame 0, tubePointTransverse x (oriented p)⟫_Real| ≤
            (5 : Real) / 2 * (delta : Real) := by
        calc
          _ ≤ |⟪frame 0, tubeAxisMidpoint (tube p) - x⟫_Real| +
              |tubePointLongitudinal x (oriented p)| *
                |⟪frame 0, (tube p).axis.direction⟫_Real| := hnum
          _ ≤ (delta : Real) / 2 + 2 * (delta : Real) := by
            exact add_le_add (hmid0 p)
              (mul_le_mul (hlong p) (hdir0 p) (abs_nonneg _) (by norm_num))
          _ = (5 : Real) / 2 * (delta : Real) := by ring
      unfold thinPlankPackingFixedBound
      apply (div_le_iff₀ hdeltaReal).2
      nlinarith
    · change
        |⟪frame 0, (oriented p).axis.direction⟫_Real /
          (delta : Real)| ≤ thinPlankPackingFixedBound
      rw [abs_div, abs_of_pos hdeltaReal, hdirAbs p 0]
      unfold thinPlankPackingFixedBound
      apply (div_le_iff₀ hdeltaReal).2
      exact (hdir0 p).trans (by nlinarith)
  have hwide (p : parameter) (j : Fin 2) :
      |thinPlankFiveWideCoordinates frame x (oriented p) j| ≤ 3 * R := by
    have hdeltaReal : 0 < (delta : Real) := NNReal.coe_pos.mpr hdeltaPos
    fin_cases j
    · change
        |⟪frame 1, tubePointTransverse x (oriented p)⟫_Real /
          (delta : Real)| ≤ 3 * R
      rw [abs_div, abs_of_pos hdeltaReal]
      have hnum :=
        abs_inner_tubePointTransverse_le_midpoint_add_long_mul_direction
          frame x (oriented p) 1
      rw [hmidEq p, hdirAbs p 1] at hnum
      have hnum' :
          |⟪frame 1, tubePointTransverse x (oriented p)⟫_Real| ≤
            (5 : Real) / 2 * (R * (delta : Real)) := by
        calc
          _ ≤ |⟪frame 1, tubeAxisMidpoint (tube p) - x⟫_Real| +
              |tubePointLongitudinal x (oriented p)| *
                |⟪frame 1, (tube p).axis.direction⟫_Real| := hnum
          _ ≤ (R * (delta : Real)) / 2 + 2 * (R * (delta : Real)) := by
            exact add_le_add (hmid1 p)
              (mul_le_mul (hlong p) (hdir1 p) (abs_nonneg _) (by norm_num))
          _ = (5 : Real) / 2 * (R * (delta : Real)) := by ring
      apply (div_le_iff₀ hdeltaReal).2
      nlinarith
    · change
        |⟪frame 1, (oriented p).axis.direction⟫_Real /
          (delta : Real)| ≤ 3 * R
      rw [abs_div, abs_of_pos hdeltaReal, hdirAbs p 1]
      apply (div_le_iff₀ hdeltaReal).2
      nlinarith [hdir1 p]
  have hforward (p : parameter) :
      (1 : Real) / 2 ≤ ⟪frame 2, (oriented p).axis.direction⟫_Real := by
    change (1 : Real) / 2 ≤ ⟪B.frame 2, (oriented p).axis.direction⟫_Real
    dsimp only [oriented]
    rw [inner_forwardOrientedTube_direction_eq_abs]
    exact half_le_abs_inner_long_of_short_direction_bounds
      frame (tube p) R (hdir0 p) (hdir1 p) hthin
  have hpairwiseOriented :
      Set.Pairwise (Set.univ : Set parameter) fun p q =>
        EssentiallyDistinct (oriented p) (oriented q) := by
    intro p _hp q _hq hpq
    unfold EssentiallyDistinct at *
    simpa only [oriented, forwardOrientedTube_carrier] using
      hpairwise (Set.mem_univ p) (Set.mem_univ q) hpq
  exact card_le_thinPlankFivePackingNatCap frame x oriented (3 * R)
    hdeltaPos hdeltaSmall hlong hforward htransverse hfixed hwide
      hpairwiseOriented

#print axioms tubeAxisMidpoint_forwardOrientedTube_frameBox
#print axioms abs_inner_forwardOrientedTube_direction
#print axioms half_le_abs_inner_long_of_short_direction_bounds
#print axioms abs_inner_tubePointTransverse_le_midpoint_add_long_mul_direction
#print axioms card_le_thinPlankFivePackingNatCap_of_midpoint_direction_bounds

end
end Family8ThinPlankFiveParameterMidpointDirectionPackingV3
