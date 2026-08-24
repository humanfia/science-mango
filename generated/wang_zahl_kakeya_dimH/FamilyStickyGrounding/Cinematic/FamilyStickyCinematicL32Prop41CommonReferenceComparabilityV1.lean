import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41LensOverlapBaseDiameterV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32ThinReferenceCompactDomainFiniteContainerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41CommonReferenceComparabilityV1

open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainFiniteContainerV1
open FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1
open FamilyStickyCinematicL32Prop41LensOverlapBaseDiameterV1

noncomputable section

/-!
# PYZ Lemma 4.7: common-reference comparability from lens localization

Once the two fine bases fit in one interval of the enlarged scale and both
rectangles are tangent to the same actual cinematic graph, an exact rebased
C2 rectangle is constructed around that graph.  The second theorem obtains
the needed base-diameter bound from the proved lens-support overlap core.

Thus the only remaining analytic input is the Lemma 3.8 localization of
each actual lens support and rectangle base near its critical parameter.
No comparability, common-container, or lens-counting conclusion is assumed.
-/

/-- A diameter-controlled pair of bases tangent to one actual reference
curve produces the literal compact-C2 common-container comparability. -/
theorem compactC2Comparable_of_commonReference_and_baseUnionDiameter
    {domain piece : Set Real} {center reference R S : C2GraphRectangle}
    {delta t lambda : Real}
    (hbaseR : R.rectangle.base ⊆ piece)
    (hbaseS : S.rectangle.base ⊆ piece)
    (hpieceDiameter : forall x, x ∈ piece -> forall y, y ∈ piece ->
      dist x y <= Real.sqrt (lambda * delta / t))
    (htangentR : R.carrier delta ⊆
      cinematicVerticalNeighborhood reference.rectangle.graph
        R.rectangle.base (lambda * delta))
    (htangentS : S.carrier delta ⊆
      cinematicVerticalNeighborhood reference.rectangle.graph
        S.rectangle.base (lambda * delta))
    (hreference : InPointwiseC2BallOn domain center reference (3 * t)) :
    compactC2SymmetricGraphLambdaComparableOn
      domain center R S delta t lambda := by
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
      (length := Real.sqrt (lambda * delta / t))
      (delta := delta) (V := lambda * delta)
      (Real.sqrt_nonneg _) hbasePair hpieceDiameter htangentPair with
    ⟨container, hlength, hball, hcontain⟩
  refine ⟨container, hlength, ?_, hball center (3 * t) hreference⟩
  intro q hq
  rcases hq with hqR | hqS
  · exact hcontain true (Finset.mem_univ _) (by
      simpa [pairRectangles] using hqR)
  · exact hcontain false (Finset.mem_univ _) (by
      simpa [pairRectangles] using hqS)

/-- Lens-support overlap plus the four honest critical-parameter
localizations automatically produces compact-C2 rectangle comparability. -/
theorem compactC2Comparable_of_lensSupport_overlap
    {domain : Set Real} {center reference R S : C2GraphRectangle}
    {lensSupportR lensSupportS : Set Real}
    {criticalR criticalS radius delta t lambda : Real}
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
    (hscale : 4 * radius <= Real.sqrt (lambda * delta / t))
    (htangentR : R.carrier delta ⊆
      cinematicVerticalNeighborhood reference.rectangle.graph
        R.rectangle.base (lambda * delta))
    (htangentS : S.carrier delta ⊆
      cinematicVerticalNeighborhood reference.rectangle.graph
        S.rectangle.base (lambda * delta))
    (hreference : InPointwiseC2BallOn domain center reference (3 * t)) :
    compactC2SymmetricGraphLambdaComparableOn
      domain center R S delta t lambda := by
  have hdiameter :=
    base_union_diameter_le_four_mul_of_lensSupport_overlap
      R.rectangle.base S.rectangle.base lensSupportR lensSupportS
      criticalR criticalS radius hradius hbaseR hbaseS hlensR hlensS hoverlap
  apply compactC2Comparable_of_commonReference_and_baseUnionDiameter
    (piece := R.rectangle.base ∪ S.rectangle.base)
    (center := center) (reference := reference)
  · exact subset_union_left
  · exact subset_union_right
  · intro x hx y hy
    exact (hdiameter x hx y hy).trans hscale
  · exact htangentR
  · exact htangentS
  · exact hreference

#print axioms compactC2Comparable_of_commonReference_and_baseUnionDiameter
#print axioms compactC2Comparable_of_lensSupport_overlap

end


end FamilyStickyCinematicL32Prop41CommonReferenceComparabilityV1
