import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55SymmetricRectangleComparabilityV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Lemma55CenteredRectangleDilationV1

open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1

noncomputable section

/-! # Literal centered dilation of a C2 graph rectangle -/

/-- The interval center used by PYZ Definition 3.11. -/
def graphRectangleCenter (R : GraphRectangle) : Real :=
  (R.left + R.right) / 2

/-- The literal `lambda`-dilation: same graph and jets, centered base of
length `sqrt (lambda * delta / t)`.  Domain clipping is handled separately
by an explicit base-subset hypothesis at the analytic boundary. -/
def centeredC2GraphRectangleDilation
    (R : C2GraphRectangle) (delta t lambda : Real) : C2GraphRectangle where
  rectangle :=
    { graph := R.rectangle.graph
      left := graphRectangleCenter R.rectangle -
        Real.sqrt (lambda * delta / t) / 2
      right := graphRectangleCenter R.rectangle +
        Real.sqrt (lambda * delta / t) / 2
      left_le_right := by
        nlinarith [Real.sqrt_nonneg (lambda * delta / t)] }
  first := R.first
  second := R.second
  graph_hasDeriv := R.graph_hasDeriv
  first_hasDeriv := R.first_hasDeriv

@[simp]
theorem centeredC2GraphRectangleDilation_length
    (R : C2GraphRectangle) (delta t lambda : Real) :
    (centeredC2GraphRectangleDilation R delta t lambda).rectangle.right -
      (centeredC2GraphRectangleDilation R delta t lambda).rectangle.left =
        Real.sqrt (lambda * delta / t) := by
  simp [centeredC2GraphRectangleDilation]

/-- Centered dilation preserves membership in every local pointwise C2
ball because it changes only the base endpoints. -/
theorem centeredC2GraphRectangleDilation_mem_c2BallOn
    {domain : Set Real} {center R : C2GraphRectangle}
    {radius delta t lambda : Real}
    (hR : InPointwiseC2BallOn domain center R radius) :
    InPointwiseC2BallOn domain center
      (centeredC2GraphRectangleDilation R delta t lambda) radius := by
  intro z hz
  simpa [centeredC2GraphRectangleDilation] using hR z hz

/-- An exact-scale base lies in every centered dilation with
`lambda >= 1`. -/
theorem base_subset_centeredC2GraphRectangleDilation
    (R : C2GraphRectangle) {delta t lambda : Real}
    (hdelta : 0 <= delta) (ht : 0 < t) (hlambda : 1 <= lambda)
    (hlength : R.rectangle.right - R.rectangle.left =
      Real.sqrt (delta / t)) :
    R.rectangle.base ⊆
      (centeredC2GraphRectangleDilation R delta t lambda).rectangle.base := by
  have hdeltaLambda : delta <= lambda * delta := by
    calc
      delta = 1 * delta := by ring
      _ <= lambda * delta := mul_le_mul_of_nonneg_right hlambda hdelta
  have hratio : delta / t <= lambda * delta / t :=
    (div_le_div_iff_of_pos_right ht).2 hdeltaLambda
  have hsqrt : Real.sqrt (delta / t) <=
      Real.sqrt (lambda * delta / t) := Real.sqrt_le_sqrt hratio
  intro theta htheta
  change theta ∈ Icc
    (graphRectangleCenter R.rectangle -
      Real.sqrt (lambda * delta / t) / 2)
    (graphRectangleCenter R.rectangle +
      Real.sqrt (lambda * delta / t) / 2)
  rw [← hlength] at hsqrt
  simp only [graphRectangleCenter]
  constructor <;> linarith [htheta.1, htheta.2]

/-- The actual carrier is contained in its literal centered dilation. -/
theorem carrier_subset_centeredC2GraphRectangleDilation
    (R : C2GraphRectangle) {delta t lambda : Real}
    (hdelta : 0 <= delta) (ht : 0 < t) (hlambda : 1 <= lambda)
    (hlength : R.rectangle.right - R.rectangle.left =
      Real.sqrt (delta / t)) :
    R.carrier delta ⊆
      (centeredC2GraphRectangleDilation R delta t lambda).carrier
        (lambda * delta) := by
  intro q hq
  refine ⟨base_subset_centeredC2GraphRectangleDilation
    R hdelta ht hlambda hlength hq.1, ?_⟩
  have hdeltaLambda : delta <= lambda * delta := by
    calc
      delta = 1 * delta := by ring
      _ <= lambda * delta := mul_le_mul_of_nonneg_right hlambda hdelta
  simpa [centeredC2GraphRectangleDilation] using hq.2.trans hdeltaLambda

/-- Monotonicity of the literal centered dilations in the enlargement
factor. -/
theorem centeredC2GraphRectangleDilation_carrier_mono
    (R : C2GraphRectangle) {delta t lambda Lambda : Real}
    (hdelta : 0 <= delta) (ht : 0 < t)
    (hlambda : 0 <= lambda) (hLambda : lambda <= Lambda) :
    (centeredC2GraphRectangleDilation R delta t lambda).carrier
        (lambda * delta) ⊆
      (centeredC2GraphRectangleDilation R delta t Lambda).carrier
        (Lambda * delta) := by
  have hLambdaNonneg : 0 <= Lambda := hlambda.trans hLambda
  have hscale : lambda * delta <= Lambda * delta :=
    mul_le_mul_of_nonneg_right hLambda hdelta
  have hratio : lambda * delta / t <= Lambda * delta / t :=
    (div_le_div_iff_of_pos_right ht).2 hscale
  have hsqrt : Real.sqrt (lambda * delta / t) <=
      Real.sqrt (Lambda * delta / t) := Real.sqrt_le_sqrt hratio
  intro q hq
  change (q.2 ∈ Icc
      (graphRectangleCenter R.rectangle -
        Real.sqrt (lambda * delta / t) / 2)
      (graphRectangleCenter R.rectangle +
        Real.sqrt (lambda * delta / t) / 2) ∧
      |q.1 - R.rectangle.graph q.2| <= lambda * delta) at hq
  refine ⟨?_, ?_⟩
  · change q.2 ∈ Icc
      (graphRectangleCenter R.rectangle -
        Real.sqrt (Lambda * delta / t) / 2)
      (graphRectangleCenter R.rectangle +
        Real.sqrt (Lambda * delta / t) / 2)
    constructor <;> linarith [hq.1.1, hq.1.2]
  · simpa [centeredC2GraphRectangleDilation] using hq.2.trans hscale

#print axioms graphRectangleCenter
#print axioms centeredC2GraphRectangleDilation
#print axioms centeredC2GraphRectangleDilation_length
#print axioms centeredC2GraphRectangleDilation_mem_c2BallOn
#print axioms base_subset_centeredC2GraphRectangleDilation
#print axioms carrier_subset_centeredC2GraphRectangleDilation
#print axioms centeredC2GraphRectangleDilation_carrier_mono

end

end FamilyStickyCinematicL32Lemma55CenteredRectangleDilationV1
