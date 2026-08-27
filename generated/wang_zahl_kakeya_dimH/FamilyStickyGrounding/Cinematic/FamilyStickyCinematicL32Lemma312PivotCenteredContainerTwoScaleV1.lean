import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma312PivotCenteredContainerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41TwoScaleComparabilityCoreV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set
open scoped Interval

namespace FamilyStickyCinematicL32Lemma312PivotCenteredContainerTwoScaleV1

open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32CurvilinearRectangleSlopeSeparationV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainSlopeWindowV1
open FamilyStickyCinematicL32RectangleScaleNormalizationV1
open FamilyStickyCinematicL32CurvilinearRectangleCardinalityBoundV1
open FamilyStickyCinematicL32Lemma55CenteredRectangleDilationV1
open FamilyStickyCinematicL32Prop41TwoScaleComparabilityCoreV1

noncomputable section

/-!
# Two-scale pivot-centred form of PYZ Lemma 3.12

The local scale fixes the base length, while an independent reference scale
controls the C2 ball containing the comparison witness.  The resulting loss
is recorded by a dimensionless `curvatureRatio` satisfying
`3 * (localScale + referenceScale) <= curvatureRatio * localScale`.
-/

/-- Explicit two-scale enlargement.  At equal scales one may take
`curvatureRatio = 6`; the formula is deliberately polynomial so it can also
absorb a larger independent reference scale without hidden division. -/
def pyzLemma312TwoScalePackingLambda
    (lambda curvatureRatio : Real) : Real :=
  (curvatureRatio + 4) * lambda ^ 2 +
    (2 * curvatureRatio + 2) * lambda + 1

theorem pyzLemma312TwoScalePackingLambda_ge_hundred
    {lambda curvatureRatio : Real}
    (hlambda : 100 <= lambda) (hratio : 0 <= curvatureRatio) :
    100 <= pyzLemma312TwoScalePackingLambda lambda curvatureRatio := by
  unfold pyzLemma312TwoScalePackingLambda
  nlinarith [sq_nonneg lambda,
    mul_nonneg hratio (sq_nonneg lambda),
    mul_nonneg hratio (show 0 <= lambda by linarith)]

theorem pyzLemma312TwoScalePackingLambda_nonneg
    {lambda curvatureRatio : Real}
    (hlambda : 1 <= lambda) (hratio : 0 <= curvatureRatio) :
    0 <= pyzLemma312TwoScalePackingLambda lambda curvatureRatio := by
  unfold pyzLemma312TwoScalePackingLambda
  nlinarith [sq_nonneg lambda,
    mul_nonneg hratio (sq_nonneg lambda),
    mul_nonneg hratio (show 0 <= lambda by linarith)]

/-- A two-scale compact-C2 comparison witness fits in a literal dilation of
the first rectangle.  The only scale loss is the displayed curvature-ratio
budget; no order between `referenceScale` and `localScale` is assumed. -/
theorem carrier_subset_centeredDilation_of_compactC2ComparableAtScales
    {domain : Set Real} {center R S : C2GraphRectangle}
    {delta localScale referenceScale lambda curvatureRatio : Real}
    (hdelta : 0 < delta) (hlocal : 0 < localScale)
    (hlambda : 1 <= lambda) (hratio : 0 <= curvatureRatio)
    (hscaleRatio :
      3 * (localScale + referenceScale) <=
        curvatureRatio * localScale)
    (hlengthR : R.rectangle.right - R.rectangle.left =
      Real.sqrt (delta / localScale))
    (hbaseR : R.rectangle.base ⊆ domain)
    (hballR : InPointwiseC2BallOn domain center R (3 * localScale))
    (hsegmentDomain : forall x, x ∈ R.rectangle.base ->
      forall y, y ∈ S.rectangle.base -> [[x, y]] ⊆ domain)
    (hcomparable : compactC2SymmetricGraphLambdaComparableOnAtScales
      domain center R S delta localScale referenceScale lambda) :
    S.carrier delta ⊆
      (centeredC2GraphRectangleDilation R delta localScale
        (pyzLemma312TwoScalePackingLambda lambda curvatureRatio)).carrier
          (pyzLemma312TwoScalePackingLambda lambda curvatureRatio * delta) := by
  rcases hcomparable with
    ⟨container, hcontainerLength, hcontain, hballContainer⟩
  let L := Real.sqrt (delta / localScale)
  let theta0 := graphRectangleCenter R.rectangle
  have hLpos : 0 < L := rectangleBaseScale_pos hdelta hlocal
  have hlambda0 : 0 <= lambda := by linarith
  have hratioLocal : 0 <= curvatureRatio * localScale :=
    mul_nonneg hratio hlocal.le
  have htheta0R : theta0 ∈ R.rectangle.base := by
    dsimp [theta0, graphRectangleCenter, GraphRectangle.base]
    constructor <;> linarith [R.rectangle.left_le_right]
  have htheta0Container : theta0 ∈ container.rectangle.base := by
    have hpoint : (R.rectangle.graph theta0, theta0) ∈ R.carrier delta := by
      refine ⟨htheta0R, ?_⟩
      simpa using hdelta.le
    exact (hcontain (Or.inl hpoint)).1
  have hsecondOnDomain : forall z, z ∈ domain ->
      |R.second z - container.second z| <= curvatureRatio * localScale := by
    intro z hz
    have htriangle : |R.second z - container.second z| <=
        |R.second z - center.second z| +
          |container.second z - center.second z| := by
      calc
        |R.second z - container.second z| =
            |(R.second z - center.second z) -
              (container.second z - center.second z)| := by ring_nf
        _ <= |R.second z - center.second z| +
            |container.second z - center.second z| := abs_sub _ _
    exact htriangle.trans (by
      have hR := (hballR z hz).2.2
      have hC := (hballContainer z hz).2.2
      linarith)
  have hsecondRContainer : forall z, z ∈ R.rectangle.base ->
      |R.second z - container.second z| <= curvatureRatio * localScale := by
    intro z hz
    exact hsecondOnDomain z (hbaseR hz)
  have htL : localScale * L ^ 2 = delta := by
    dsimp only [L]
    exact t_mul_baseScale_sq hdelta hlocal
  have hslopeProduct :
      |R.first theta0 - container.first theta0| * (L / 2) <=
        (2 * lambda + curvatureRatio) * delta := by
    have hslope := abs_slope_sub_reference_mul_halfLength_le_on_base
      R.rectangle R.first R.second container.rectangle.graph
        container.first container.second container.rectangle.base
      (delta := delta) (V := lambda * delta) (L := L)
      (M := curvatureRatio * localScale) (theta0 := theta0)
      hdelta.le hratioLocal htheta0R
      (by simpa [L] using hlengthR)
      (fun q hq => hcontain (Or.inl hq))
      R.graph_hasDeriv container.graph_hasDeriv
      R.first_hasDeriv container.first_hasDeriv hsecondRContainer
    calc
      |R.first theta0 - container.first theta0| * (L / 2) <=
          2 * (lambda * delta) +
            (curvatureRatio * localScale) * L ^ 2 := hslope
      _ = (2 * lambda + curvatureRatio) * delta := by
        nlinarith
  have hsqrtLambdaSq : (Real.sqrt lambda) ^ 2 = lambda :=
    Real.sq_sqrt hlambda0
  have hsqrtLambdaLe : Real.sqrt lambda <= lambda := by
    nlinarith [Real.sqrt_nonneg lambda]
  have hcontainerScale :
      Real.sqrt (lambda * delta / localScale) <= lambda * L := by
    rw [enlargedBaseScale_eq_sqrtLambda_mul hlambda0]
    exact mul_le_mul_of_nonneg_right hsqrtLambdaLe hLpos.le
  intro q hq
  have hqContainer := hcontain (Or.inr hq)
  have hthetaS : q.2 ∈ S.rectangle.base := hq.1
  have hthetaContainer : q.2 ∈ container.rectangle.base := hqContainer.1
  have hdistanceRaw := abs_sub_le_base_length container.rectangle
    hthetaContainer htheta0Container
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
    (theta0 := theta0) (theta := q.2)
    (M := curvatureRatio * localScale)
    hratioLocal
    (fun z _hz => (R.graph_hasDeriv z).sub (container.graph_hasDeriv z))
    (fun z _hz => (R.first_hasDeriv z).sub (container.first_hasDeriv z))
    (fun z hz => hsecondOnDomain z (hsegment hz))
  have hlinearDistance :
      |R.first theta0 - container.first theta0| * |q.2 - theta0| <=
        2 * lambda * ((2 * lambda + curvatureRatio) * delta) := by
    have hdistHalf : |q.2 - theta0| <= 2 * lambda * (L / 2) := by
      nlinarith
    calc
      |R.first theta0 - container.first theta0| * |q.2 - theta0| <=
          |R.first theta0 - container.first theta0| *
            (2 * lambda * (L / 2)) :=
        mul_le_mul_of_nonneg_left hdistHalf (abs_nonneg _)
      _ = 2 * lambda *
          (|R.first theta0 - container.first theta0| * (L / 2)) := by ring
      _ <= 2 * lambda * ((2 * lambda + curvatureRatio) * delta) :=
        mul_le_mul_of_nonneg_left hslopeProduct (by positivity)
  have hdistanceSq : |q.2 - theta0| ^ 2 <= (lambda * L) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg hlambda0 hLpos.le)).2 hdistance
  have hquadratic :
      (curvatureRatio * localScale) * |q.2 - theta0| ^ 2 <=
        curvatureRatio * lambda ^ 2 * delta := by
    calc
      (curvatureRatio * localScale) * |q.2 - theta0| ^ 2 <=
          (curvatureRatio * localScale) * (lambda * L) ^ 2 :=
        mul_le_mul_of_nonneg_left hdistanceSq hratioLocal
      _ = curvatureRatio * lambda ^ 2 * (localScale * L ^ 2) := by ring
      _ = curvatureRatio * lambda ^ 2 * delta := by rw [htL]
  have hgraphDifference :
      |R.rectangle.graph q.2 - container.rectangle.graph q.2| <=
        ((curvatureRatio + 4) * lambda ^ 2 +
          (2 * curvatureRatio + 1) * lambda) * delta := by
    calc
      |R.rectangle.graph q.2 - container.rectangle.graph q.2| <=
          |R.rectangle.graph theta0 - container.rectangle.graph theta0| +
            (|R.first theta0 - container.first theta0| +
              (curvatureRatio * localScale) * |q.2 - theta0|) *
                |q.2 - theta0| := hTaylor
      _ <= lambda * delta +
          2 * lambda * ((2 * lambda + curvatureRatio) * delta) +
            curvatureRatio * lambda ^ 2 * delta := by
        have hanchor :
            |R.rectangle.graph theta0 - container.rectangle.graph theta0| <=
              lambda * delta := by
          simpa only [abs_sub_comm] using hanchorContainer
        nlinarith [hlinearDistance, hquadratic]
      _ = ((curvatureRatio + 4) * lambda ^ 2 +
          (2 * curvatureRatio + 1) * lambda) * delta := by ring
  have hvertical :
      |q.1 - R.rectangle.graph q.2| <=
        pyzLemma312TwoScalePackingLambda lambda curvatureRatio * delta := by
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
    calc
      |q.1 - R.rectangle.graph q.2| <=
          |q.1 - container.rectangle.graph q.2| +
            |R.rectangle.graph q.2 - container.rectangle.graph q.2| := htriangle
      _ <= lambda * delta +
          (((curvatureRatio + 4) * lambda ^ 2 +
            (2 * curvatureRatio + 1) * lambda) * delta) :=
        add_le_add hqContainer.2 hgraphDifference
      _ <= pyzLemma312TwoScalePackingLambda lambda curvatureRatio * delta := by
        unfold pyzLemma312TwoScalePackingLambda
        nlinarith [hdelta.le]
  refine ⟨?_, ?_⟩
  · change q.2 ∈ Icc
      (graphRectangleCenter R.rectangle -
        Real.sqrt
          (pyzLemma312TwoScalePackingLambda lambda curvatureRatio *
            delta / localScale) / 2)
      (graphRectangleCenter R.rectangle +
        Real.sqrt
          (pyzLemma312TwoScalePackingLambda lambda curvatureRatio *
            delta / localScale) / 2)
    let packing := pyzLemma312TwoScalePackingLambda lambda curvatureRatio
    have hpacking0 : 0 <= packing := by
      exact pyzLemma312TwoScalePackingLambda_nonneg hlambda hratio
    have hfourLambdaSq : (2 * lambda) ^ 2 <= packing := by
      dsimp only [packing, pyzLemma312TwoScalePackingLambda]
      nlinarith [mul_nonneg hratio (sq_nonneg lambda),
        mul_nonneg hratio hlambda0]
    have htwoLambdaSqrt : 2 * lambda <= Real.sqrt packing := by
      exact Real.le_sqrt_of_sq_le hfourLambdaSq
    have hsqrtPacking :
        Real.sqrt (packing * delta / localScale) =
          Real.sqrt packing * L := by
      exact enlargedBaseScale_eq_sqrtLambda_mul hpacking0
    have hhalf : lambda * L <=
        Real.sqrt (packing * delta / localScale) / 2 := by
      rw [hsqrtPacking]
      have hL0 := hLpos.le
      nlinarith
    dsimp only [theta0] at hdistance
    have hdistanceBounds := abs_le.mp hdistance
    constructor
    · linarith [hdistanceBounds.1, hhalf]
    · linarith [hdistanceBounds.2, hhalf]
  · simpa [centeredC2GraphRectangleDilation] using hvertical

#print axioms pyzLemma312TwoScalePackingLambda
#print axioms pyzLemma312TwoScalePackingLambda_ge_hundred
#print axioms carrier_subset_centeredDilation_of_compactC2ComparableAtScales

end

end FamilyStickyCinematicL32Lemma312PivotCenteredContainerTwoScaleV1
