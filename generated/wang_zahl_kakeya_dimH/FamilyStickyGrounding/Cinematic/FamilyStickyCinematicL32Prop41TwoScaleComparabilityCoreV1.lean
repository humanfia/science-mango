import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41CommonReferenceComparabilityV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41TwoScaleComparabilityCoreV1

open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1
open FamilyStickyCinematicL32Prop41LensOverlapBaseDiameterV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainFiniteContainerV1

noncomputable section

/-! Minimal analytic core for independent local and common-C2 scales. -/

def compactC2SymmetricGraphLambdaComparableOnAtScales
    (domain : Set Real) (center R S : C2GraphRectangle)
    (delta localScale referenceScale lambda : Real) : Prop :=
  exists container : C2GraphRectangle,
    container.rectangle.right - container.rectangle.left =
      Real.sqrt (lambda * delta / localScale) ∧
    R.carrier delta ∪ S.carrier delta ⊆
      container.carrier (lambda * delta) ∧
    InPointwiseC2BallOn domain center container (3 * referenceScale)

theorem compactC2SymmetricGraphLambdaComparableOnAtScales_same
    {domain : Set Real} {center R S : C2GraphRectangle}
    {delta t lambda : Real} :
    compactC2SymmetricGraphLambdaComparableOnAtScales
      domain center R S delta t t lambda ↔
    compactC2SymmetricGraphLambdaComparableOn
      domain center R S delta t lambda := by
  rfl

theorem compactC2SymmetricGraphLambdaComparableOnAtScales_symm
    {domain : Set Real} {center R S : C2GraphRectangle}
    {delta localScale referenceScale lambda : Real}
    (h : compactC2SymmetricGraphLambdaComparableOnAtScales
      domain center R S delta localScale referenceScale lambda) :
    compactC2SymmetricGraphLambdaComparableOnAtScales
      domain center S R delta localScale referenceScale lambda := by
  rcases h with ⟨container, hlength, hcontain, hball⟩
  refine ⟨container, hlength, ?_, hball⟩
  simpa [union_comm] using hcontain

theorem inPointwiseC2BallOn_mono_radius
    {domain : Set Real} {center R : C2GraphRectangle} {r s : Real}
    (hrs : r ≤ s) (hR : InPointwiseC2BallOn domain center R r) :
    InPointwiseC2BallOn domain center R s := by
  intro z hz
  exact ⟨(hR z hz).1.trans hrs,
    (hR z hz).2.1.trans hrs,
    (hR z hz).2.2.trans hrs⟩

theorem compactC2SymmetricGraphLambdaComparableOnAtScales_mono_reference
    {domain : Set Real} {center R S : C2GraphRectangle}
    {delta localScale referenceScale₁ referenceScale₂ lambda : Real}
    (hscale : referenceScale₁ ≤ referenceScale₂)
    (h : compactC2SymmetricGraphLambdaComparableOnAtScales
      domain center R S delta localScale referenceScale₁ lambda) :
    compactC2SymmetricGraphLambdaComparableOnAtScales
      domain center R S delta localScale referenceScale₂ lambda := by
  rcases h with ⟨container, hlength, hcontain, hball⟩
  refine ⟨container, hlength, hcontain, ?_⟩
  apply inPointwiseC2BallOn_mono_radius (r := 3 * referenceScale₁)
    (s := 3 * referenceScale₂)
  · gcongr
  · exact hball

theorem compactC2ComparableAtScales_of_commonReference_and_baseUnionDiameter
    {domain piece : Set Real} {center reference R S : C2GraphRectangle}
    {delta localScale referenceScale lambda : Real}
    (hbaseR : R.rectangle.base ⊆ piece)
    (hbaseS : S.rectangle.base ⊆ piece)
    (hpieceDiameter : forall x, x ∈ piece -> forall y, y ∈ piece ->
      dist x y <= Real.sqrt (lambda * delta / localScale))
    (htangentR : R.carrier delta ⊆
      cinematicVerticalNeighborhood reference.rectangle.graph
        R.rectangle.base (lambda * delta))
    (htangentS : S.carrier delta ⊆
      cinematicVerticalNeighborhood reference.rectangle.graph
        S.rectangle.base (lambda * delta))
    (hreference : InPointwiseC2BallOn domain center reference
      (3 * referenceScale)) :
    compactC2SymmetricGraphLambdaComparableOnAtScales
      domain center R S delta localScale referenceScale lambda := by
  classical
  let pairRectangles : Bool -> C2GraphRectangle := fun b =>
    if b then R else S
  have hbasePair : forall b, b ∈ (Finset.univ : Finset Bool) ->
      (pairRectangles b).rectangle.base ⊆ piece := by
    intro b _hb
    cases b <;> simp [pairRectangles, hbaseR, hbaseS]
  have htangentPair : forall b, b ∈ (Finset.univ : Finset Bool) ->
      (pairRectangles b).carrier delta ⊆
        cinematicVerticalNeighborhood reference.rectangle.graph
          (pairRectangles b).rectangle.base (lambda * delta) := by
    intro b _hb
    cases b <;> simp [pairRectangles, htangentR, htangentS]
  rcases exists_rebased_container_of_bases_in_diameter_piece_on
      (Finset.univ : Finset Bool) pairRectangles reference piece domain
      (length := Real.sqrt (lambda * delta / localScale))
      (delta := delta) (V := lambda * delta)
      (Real.sqrt_nonneg _) hbasePair hpieceDiameter htangentPair with
    ⟨container, hlength, hball, hcontain⟩
  refine ⟨container, hlength, ?_,
    hball center (3 * referenceScale) hreference⟩
  intro q hq
  rcases hq with hqR | hqS
  · exact hcontain true (Finset.mem_univ _) (by
      simpa [pairRectangles] using hqR)
  · exact hcontain false (Finset.mem_univ _) (by
      simpa [pairRectangles] using hqS)

theorem compactC2ComparableAtScales_of_lensSupport_overlap
    {domain : Set Real} {center reference R S : C2GraphRectangle}
    {lensSupportR lensSupportS : Set Real}
    {criticalR criticalS radius delta localScale referenceScale lambda : Real}
    (hradius : 0 <= radius)
    (hbaseR : forall x, x ∈ R.rectangle.base ->
      dist x criticalR <= radius)
    (hbaseS : forall x, x ∈ S.rectangle.base ->
      dist x criticalS <= radius)
    (hlensR : forall x, x ∈ lensSupportR ->
      dist x criticalR <= radius)
    (hlensS : forall x, x ∈ lensSupportS ->
      dist x criticalS <= radius)
    (hoverlap : (lensSupportR ∩ lensSupportS).Nonempty)
    (hscale : 4 * radius <= Real.sqrt (lambda * delta / localScale))
    (htangentR : R.carrier delta ⊆
      cinematicVerticalNeighborhood reference.rectangle.graph
        R.rectangle.base (lambda * delta))
    (htangentS : S.carrier delta ⊆
      cinematicVerticalNeighborhood reference.rectangle.graph
        S.rectangle.base (lambda * delta))
    (hreference : InPointwiseC2BallOn domain center reference
      (3 * referenceScale)) :
    compactC2SymmetricGraphLambdaComparableOnAtScales
      domain center R S delta localScale referenceScale lambda := by
  have hdiameter :=
    base_union_diameter_le_four_mul_of_lensSupport_overlap
      R.rectangle.base S.rectangle.base lensSupportR lensSupportS
      criticalR criticalS radius hradius hbaseR hbaseS hlensR hlensS hoverlap
  apply compactC2ComparableAtScales_of_commonReference_and_baseUnionDiameter
    (piece := R.rectangle.base ∪ S.rectangle.base)
    (center := center) (reference := reference)
  · exact subset_union_left
  · exact subset_union_right
  · intro x hx y hy
    exact (hdiameter x hx y hy).trans hscale
  · exact htangentR
  · exact htangentS
  · exact hreference

#print axioms compactC2SymmetricGraphLambdaComparableOnAtScales
#print axioms compactC2SymmetricGraphLambdaComparableOnAtScales_same
#print axioms compactC2SymmetricGraphLambdaComparableOnAtScales_symm
#print axioms inPointwiseC2BallOn_mono_radius
#print axioms compactC2SymmetricGraphLambdaComparableOnAtScales_mono_reference
#print axioms compactC2ComparableAtScales_of_commonReference_and_baseUnionDiameter
#print axioms compactC2ComparableAtScales_of_lensSupport_overlap

end

end FamilyStickyCinematicL32Prop41TwoScaleComparabilityCoreV1
