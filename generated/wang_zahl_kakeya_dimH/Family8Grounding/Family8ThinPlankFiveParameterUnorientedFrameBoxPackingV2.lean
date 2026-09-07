import Family8Grounding.Family8ThinPlankFiveParameterFrameBoxPackingV4
import FamilyStickyGrounding.FamilyStickySameRadiusTubeContainmentCompatibleV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped NNReal InnerProductSpace BigOperators

namespace Family8ThinPlankFiveParameterUnorientedFrameBoxPackingV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family4GlobalExtremalUpstream
open Family8ThinPlankFiveParameterPackingV2
open Family8ThinPlankFiveParameterFrameBoxPackingV4
open FamilyStickySameRadiusTubeContainmentCompatibleV1

noncomputable section

/-!
# Orientation-free five-parameter FrameBox packing

Tube carrier geometry is unoriented.  We reverse a parametrized axis whenever
its long-frame component is negative.  A scalar thinness condition and the two
short-side bounds force the absolute long-frame component to be at least one
half, so the oriented five-parameter kernel applies without a memberwise
orientation premise.
-/

def forwardOrientedTube
    {delta : NNReal} (B : FrameBox) (T : Tube delta) : Tube delta :=
  if 0 ≤ ⟪B.frame 2, T.axis.direction⟫_Real then T else reversedTube T

@[simp] theorem forwardOrientedTube_carrier
    {delta : NNReal} (B : FrameBox) (T : Tube delta) :
    (forwardOrientedTube B T).carrier = T.carrier := by
  by_cases h : 0 ≤ ⟪B.frame 2, T.axis.direction⟫_Real
  · simp [forwardOrientedTube, h]
  · simp [forwardOrientedTube, h, reversedTubeCarrier]

theorem inner_forwardOrientedTube_direction_eq_abs
    {delta : NNReal} (B : FrameBox) (T : Tube delta) :
    ⟪B.frame 2, (forwardOrientedTube B T).axis.direction⟫_Real =
      |⟪B.frame 2, T.axis.direction⟫_Real| := by
  by_cases h : 0 ≤ ⟪B.frame 2, T.axis.direction⟫_Real
  · simp [forwardOrientedTube, h, abs_of_nonneg h]
  · have hle : ⟪B.frame 2, T.axis.direction⟫_Real ≤ 0 := le_of_not_ge h
    simp [forwardOrientedTube, h, reversedTube, reversedUnitSegmentDirection,
      inner_neg_right, abs_of_nonpos hle]

/-- The two short coordinate bounds and the unit direction identity force a
large absolute component in the omitted long direction. -/
theorem half_le_abs_inner_long_of_frameBox_short_sides
    {delta : NNReal} (B : FrameBox) (T : Tube delta) (R : Real)
    (hdeltaNonneg : 0 ≤ (delta : Real)) (hR : 0 ≤ R)
    (hside0 : (B.side 0 : Real) ≤ (delta : Real))
    (hside1 : (B.side 1 : Real) ≤ R * (delta : Real))
    (hTB : T.carrier ⊆ B.carrier)
    (hthin :
      (delta : Real) ^ 2 + (R * (delta : Real)) ^ 2 ≤ (3 : Real) / 4) :
    (1 : Real) / 2 ≤ |⟪B.frame 2, T.axis.direction⟫_Real| := by
  let c0 : Real := ⟪B.frame 0, T.axis.direction⟫_Real
  let c1 : Real := ⟪B.frame 1, T.axis.direction⟫_Real
  let c2 : Real := ⟪B.frame 2, T.axis.direction⟫_Real
  let d : Real := (delta : Real)
  let w : Real := R * (delta : Real)
  have hc0 : |c0| ≤ d := by
    exact (abs_inner_direction_le_frameBox_side B T hTB 0).trans hside0
  have hc1 : |c1| ≤ w := by
    exact (abs_inner_direction_le_frameBox_side B T hTB 1).trans hside1
  have hd : 0 ≤ d := hdeltaNonneg
  have hw : 0 ≤ w := mul_nonneg hR hdeltaNonneg
  have hc0Bounds := abs_le.mp hc0
  have hc1Bounds := abs_le.mp hc1
  have hc0Sq : c0 ^ 2 ≤ d ^ 2 := by
    have hp : 0 ≤ (d - c0) * (d + c0) :=
      mul_nonneg (by linarith [hc0Bounds.2]) (by linarith [hc0Bounds.1])
    nlinarith
  have hc1Sq : c1 ^ 2 ≤ w ^ 2 := by
    have hp : 0 ≤ (w - c1) * (w + c1) :=
      mul_nonneg (by linarith [hc1Bounds.2]) (by linarith [hc1Bounds.1])
    nlinarith
  have hparseval := B.frame.sum_sq_inner_right T.axis.direction
  rw [Fin.sum_univ_three, T.axis.norm_direction] at hparseval
  norm_num at hparseval
  change c0 ^ 2 + c1 ^ 2 + c2 ^ 2 = 1 at hparseval
  change d ^ 2 + w ^ 2 ≤ (3 : Real) / 4 at hthin
  by_contra hlong
  have hc2abs : |c2| < (1 : Real) / 2 := lt_of_not_ge hlong
  have hc2Bounds := abs_lt.mp hc2abs
  have hp2 : 0 < ((1 : Real) / 2 - c2) * ((1 : Real) / 2 + c2) :=
    mul_pos (by linarith [hc2Bounds.2]) (by linarith [hc2Bounds.1])
  have hc2Sq : c2 ^ 2 < (1 : Real) / 4 := by
    nlinarith
  nlinarith

theorem card_le_thinPlankFivePackingNatCap_of_frameBox_unoriented
    {delta : NNReal} {parameter : Type} [Fintype parameter]
    [DecidableEq parameter]
    (B : FrameBox) (tube : parameter → Tube delta) (R : Real)
    (hdeltaPos : 0 < delta) (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (hR : 0 ≤ R)
    (hsum : (∑ i, B.side i : NNReal) ≤ 4)
    (hside0 : (B.side 0 : Real) ≤ (delta : Real))
    (hside1 : (B.side 1 : Real) ≤ R * (delta : Real))
    (hthin :
      (delta : Real) ^ 2 + (R * (delta : Real)) ^ 2 ≤ (3 : Real) / 4)
    (hcontain : ∀ p, (tube p).carrier ⊆ B.carrier)
    (hpairwise : Set.Pairwise (Set.univ : Set parameter) fun p q =>
      EssentiallyDistinct (tube p) (tube q)) :
    Fintype.card parameter ≤ thinPlankFivePackingNatCap (3 * R) := by
  let oriented : parameter → Tube delta := fun p =>
    forwardOrientedTube B (tube p)
  have hcontainOriented (p : parameter) :
      (oriented p).carrier ⊆ B.carrier := by
    simpa only [oriented, forwardOrientedTube_carrier] using hcontain p
  have hforwardOriented (p : parameter) :
      (1 : Real) / 2 ≤
        ⟪B.frame 2, (oriented p).axis.direction⟫_Real := by
    dsimp only [oriented]
    rw [inner_forwardOrientedTube_direction_eq_abs]
    exact half_le_abs_inner_long_of_frameBox_short_sides
      B (tube p) R NNReal.zero_le_coe hR hside0 hside1 (hcontain p) hthin
  have hpairwiseOriented :
      Set.Pairwise (Set.univ : Set parameter) fun p q =>
        EssentiallyDistinct (oriented p) (oriented q) := by
    intro p _hp q _hq hpq
    unfold EssentiallyDistinct at *
    simpa only [oriented, forwardOrientedTube_carrier] using
      hpairwise (Set.mem_univ p) (Set.mem_univ q) hpq
  exact card_le_thinPlankFivePackingNatCap_of_frameBox
    B oriented R hdeltaPos hdeltaSmall hR hsum hside0 hside1
      hcontainOriented hforwardOriented hpairwiseOriented

#print axioms forwardOrientedTube_carrier
#print axioms inner_forwardOrientedTube_direction_eq_abs
#print axioms half_le_abs_inner_long_of_frameBox_short_sides
#print axioms card_le_thinPlankFivePackingNatCap_of_frameBox_unoriented

end
end Family8ThinPlankFiveParameterUnorientedFrameBoxPackingV2
