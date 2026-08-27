import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32ThinReferenceCompactDomainSlopeWindowV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55CenteredRectangleDilationV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CurvilinearRectangleCardinalityBoundV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

set_option maxHeartbeats 1000000
open Set
open scoped Interval

namespace FamilyStickyCinematicL32Lemma312PivotCenteredContainerV1

open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32CurvilinearRectangleSlopeSeparationV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainSlopeWindowV1
open FamilyStickyCinematicL32RectangleScaleNormalizationV1
open FamilyStickyCinematicL32CurvilinearRectangleCardinalityBoundV1
open FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1
open FamilyStickyCinematicL32Lemma55CenteredRectangleDilationV1

noncomputable section

/-!
# Explicit pivot-centred form of PYZ Lemma 3.12

Two compact-C2 `lambda`-comparable fine rectangles are placed in a literal
dilation of the first rectangle.  The explicit enlargement
`(4 * (lambda + 1))^2` is intentionally generous: it absorbs the base drift,
the slope estimate from the common container, and the quadratic C2 error.
-/

/-- Explicit enlargement used by the formal Lemma 3.12. -/
def pyzLemma312PackingLambda (lambda : Real) : Real :=
  (4 * (lambda + 1)) ^ 2

theorem pyzLemma312PackingLambda_ge_hundred
    {lambda : Real} (hlambda : 100 <= lambda) :
    100 <= pyzLemma312PackingLambda lambda := by
  dsimp [pyzLemma312PackingLambda]
  nlinarith [sq_nonneg (4 * (lambda + 1))]

/-- A compact-C2 comparability witness gives containment in an explicit
pivot-centred dilation.  `hsegmentDomain` is the paper's fact that all fine
bases lie in one interval (`J/4`); it is exactly what lets Taylor's theorem
travel between the two bases. -/
theorem carrier_subset_centeredDilation_of_compactC2Comparable
    {domain : Set Real} {center R S : C2GraphRectangle}
    {delta t lambda : Real}
    (hdelta : 0 < delta) (ht : 0 < t) (hlambda : 1 <= lambda)
    (hlengthR : R.rectangle.right - R.rectangle.left =
      Real.sqrt (delta / t))
    (hbaseR : R.rectangle.base ⊆ domain)
    (hballR : InPointwiseC2BallOn domain center R (3 * t))
    (hsegmentDomain : forall x, x ∈ R.rectangle.base ->
      forall y, y ∈ S.rectangle.base -> [[x, y]] ⊆ domain)
    (hcomparable : compactC2SymmetricGraphLambdaComparableOn
      domain center R S delta t lambda) :
    S.carrier delta ⊆
      (centeredC2GraphRectangleDilation R delta t
        (pyzLemma312PackingLambda lambda)).carrier
          (pyzLemma312PackingLambda lambda * delta) := by
  rcases hcomparable with
    ⟨container, hcontainerLength, hcontain, hballContainer⟩
  let L := Real.sqrt (delta / t)
  let theta0 := graphRectangleCenter R.rectangle
  have hLpos : 0 < L := rectangleBaseScale_pos hdelta ht
  have hlambda0 : 0 <= lambda := (by linarith : 0 <= lambda)
  have htheta0R : theta0 ∈ R.rectangle.base := by
    dsimp [theta0, graphRectangleCenter, GraphRectangle.base]
    constructor <;> linarith [R.rectangle.left_le_right]
  have htheta0Container : theta0 ∈ container.rectangle.base := by
    have hpoint : (R.rectangle.graph theta0, theta0) ∈ R.carrier delta := by
      refine ⟨htheta0R, ?_⟩
      simpa using hdelta.le
    exact (hcontain (Or.inl hpoint)).1
  have hsecondRContainer : forall z, z ∈ R.rectangle.base ->
      |R.second z - container.second z| <= 6 * t := by
    intro z hz
    exact abs_second_sub_le_six_mul_t_of_mem_common_c2BallOn
      hballR hballContainer (hbaseR hz)
  have hslopeProduct :
      |R.first theta0 - container.first theta0| * (L / 2) <=
        (2 * lambda + 6) * delta := by
    have hslope := abs_slope_sub_reference_mul_halfLength_le_on_base
      R.rectangle R.first R.second container.rectangle.graph
        container.first container.second container.rectangle.base
      (delta := delta) (V := lambda * delta) (L := L) (M := 6 * t)
      (theta0 := theta0) hdelta.le (by positivity) htheta0R
      (by simpa [L] using hlengthR)
      (fun q hq => hcontain (Or.inl hq))
      R.graph_hasDeriv container.graph_hasDeriv
      R.first_hasDeriv container.first_hasDeriv hsecondRContainer
    calc
      |R.first theta0 - container.first theta0| * (L / 2) <=
          2 * (lambda * delta) + (6 * t) * L ^ 2 := hslope
      _ = (2 * lambda + 6) * delta := by
        have htL := t_mul_baseScale_sq hdelta ht
        dsimp [L] at htL ⊢
        nlinarith
  intro q hq
  have hqContainer := hcontain (Or.inr hq)
  have hthetaS : q.2 ∈ S.rectangle.base := hq.1
  have hthetaContainer : q.2 ∈ container.rectangle.base := hqContainer.1
  have hdistanceRaw := abs_sub_le_base_length container.rectangle
    hthetaContainer htheta0Container
  have hsqrtLambdaSq : (Real.sqrt lambda) ^ 2 = lambda :=
    Real.sq_sqrt hlambda0
  have hsqrtLambdaLe : Real.sqrt lambda <= lambda := by
    nlinarith [Real.sqrt_nonneg lambda]
  have hcontainerScale : Real.sqrt (lambda * delta / t) <= lambda * L := by
    rw [enlargedBaseScale_eq_sqrtLambda_mul hlambda0]
    exact mul_le_mul_of_nonneg_right hsqrtLambdaLe hLpos.le
  have hdistance : |q.2 - theta0| <= lambda * L := by
    exact hdistanceRaw.trans (by
      rw [hcontainerLength]
      exact hcontainerScale)
  have hanchorPoint :
      (R.rectangle.graph theta0, theta0) ∈ R.carrier delta := by
    refine ⟨htheta0R, ?_⟩
    simpa using hdelta.le
  have hanchorContainer := (hcontain (Or.inl hanchorPoint)).2
  have hsegment : [[theta0, q.2]] ⊆ domain :=
    hsegmentDomain theta0 htheta0R q.2 hthetaS
  have hTaylor := abs_value_le_anchor_add_linear_quadratic
    (fun z => R.rectangle.graph z - container.rectangle.graph z)
    (fun z => R.first z - container.first z)
    (fun z => R.second z - container.second z)
    (theta0 := theta0) (theta := q.2) (M := 6 * t)
    (by positivity)
    (fun z _hz => (R.graph_hasDeriv z).sub (container.graph_hasDeriv z))
    (fun z _hz => (R.first_hasDeriv z).sub (container.first_hasDeriv z))
    (fun z hz => abs_second_sub_le_six_mul_t_of_mem_common_c2BallOn
      hballR hballContainer (hsegment hz))
  have hlinearDistance :
      |R.first theta0 - container.first theta0| * |q.2 - theta0| <=
        2 * lambda * ((2 * lambda + 6) * delta) := by
    have hdistHalf : |q.2 - theta0| <= 2 * lambda * (L / 2) := by
      nlinarith
    calc
      |R.first theta0 - container.first theta0| * |q.2 - theta0| <=
          |R.first theta0 - container.first theta0| *
            (2 * lambda * (L / 2)) :=
        mul_le_mul_of_nonneg_left hdistHalf (abs_nonneg _)
      _ = 2 * lambda *
          (|R.first theta0 - container.first theta0| * (L / 2)) := by ring
      _ <= 2 * lambda * ((2 * lambda + 6) * delta) :=
        mul_le_mul_of_nonneg_left hslopeProduct (by positivity)
  have hdistanceSq : |q.2 - theta0| ^ 2 <= (lambda * L) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg hlambda0 hLpos.le)).2 hdistance
  have hquadratic :
      (6 * t) * |q.2 - theta0| ^ 2 <=
        6 * lambda ^ 2 * delta := by
    calc
      (6 * t) * |q.2 - theta0| ^ 2 <=
          (6 * t) * (lambda * L) ^ 2 :=
        mul_le_mul_of_nonneg_left hdistanceSq (by positivity)
      _ = 6 * lambda ^ 2 * delta := by
        have htL := t_mul_baseScale_sq hdelta ht
        dsimp [L] at htL ⊢
        nlinarith
  have hgraphDifference :
      |R.rectangle.graph q.2 - container.rectangle.graph q.2| <=
        (10 * lambda ^ 2 + 13 * lambda) * delta := by
    calc
      |R.rectangle.graph q.2 - container.rectangle.graph q.2| <=
          |R.rectangle.graph theta0 - container.rectangle.graph theta0| +
            (|R.first theta0 - container.first theta0| +
              (6 * t) * |q.2 - theta0|) * |q.2 - theta0| := hTaylor
      _ <= lambda * delta +
          2 * lambda * ((2 * lambda + 6) * delta) +
            6 * lambda ^ 2 * delta := by
        have hanchor :
            |R.rectangle.graph theta0 - container.rectangle.graph theta0| <=
              lambda * delta := by
          simpa only [abs_sub_comm] using hanchorContainer
        nlinarith [hlinearDistance, hquadratic]
      _ <= (10 * lambda ^ 2 + 13 * lambda) * delta := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hlambda) hdelta.le]
  have hvertical :
      |q.1 - R.rectangle.graph q.2| <=
        pyzLemma312PackingLambda lambda * delta := by
    have htriangle : |q.1 - R.rectangle.graph q.2| <=
        |q.1 - container.rectangle.graph q.2| +
          |R.rectangle.graph q.2 - container.rectangle.graph q.2| := by
      calc
        |q.1 - R.rectangle.graph q.2| =
            |(q.1 - container.rectangle.graph q.2) -
              (R.rectangle.graph q.2 - container.rectangle.graph q.2)| := by
                congr 1
                ring
        _ <= |q.1 - container.rectangle.graph q.2| +
            |R.rectangle.graph q.2 - container.rectangle.graph q.2| :=
          abs_sub _ _
    have hcoefficient :
        lambda + (10 * lambda ^ 2 + 13 * lambda) <=
          pyzLemma312PackingLambda lambda := by
      dsimp [pyzLemma312PackingLambda]
      nlinarith [sq_nonneg (lambda - 1)]
    calc
      |q.1 - R.rectangle.graph q.2| <=
          |q.1 - container.rectangle.graph q.2| +
            |R.rectangle.graph q.2 - container.rectangle.graph q.2| := htriangle
      _ <= lambda * delta +
          (10 * lambda ^ 2 + 13 * lambda) * delta :=
        add_le_add hqContainer.2 hgraphDifference
      _ = (lambda + (10 * lambda ^ 2 + 13 * lambda)) * delta := by ring
      _ <= pyzLemma312PackingLambda lambda * delta :=
        mul_le_mul_of_nonneg_right hcoefficient hdelta.le
  refine ⟨?_, ?_⟩
  · change q.2 ∈ Icc
      (graphRectangleCenter R.rectangle -
        Real.sqrt (pyzLemma312PackingLambda lambda * delta / t) / 2)
      (graphRectangleCenter R.rectangle +
        Real.sqrt (pyzLemma312PackingLambda lambda * delta / t) / 2)
    have hpacking0 : 0 <= pyzLemma312PackingLambda lambda := by
      dsimp [pyzLemma312PackingLambda]
      positivity
    have hsqrtPacking :
        Real.sqrt (pyzLemma312PackingLambda lambda) =
          4 * (lambda + 1) := by
      dsimp [pyzLemma312PackingLambda]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
      nlinarith
    have hhalf : lambda * L <=
        Real.sqrt (pyzLemma312PackingLambda lambda * delta / t) / 2 := by
      rw [enlargedBaseScale_eq_sqrtLambda_mul hpacking0,
        hsqrtPacking]
      have hL0 := hLpos.le
      nlinarith
    dsimp [theta0] at hdistance
    have hdistanceBounds := (abs_le.mp hdistance)
    constructor
    · linarith [hdistanceBounds.1, hhalf]
    · linarith [hdistanceBounds.2, hhalf]
  · simpa [centeredC2GraphRectangleDilation] using hvertical

#print axioms pyzLemma312PackingLambda
#print axioms pyzLemma312PackingLambda_ge_hundred
#print axioms carrier_subset_centeredDilation_of_compactC2Comparable

end

end FamilyStickyCinematicL32Lemma312PivotCenteredContainerV1
