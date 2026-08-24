import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55CenteredRectangleDilationV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1

open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32Lemma55SymmetricRectangleComparabilityV1
open FamilyStickyCinematicL32Lemma55CenteredRectangleDilationV1

noncomputable section

/-!
# Compact-C2 symmetric comparability without a spurious enlarged-domain field

The common enlarged rectangle must carry a graph from the same compact C2
family.  Its base, however, need not lie wholly in the compact parameter
domain: the calculus only travels between points of the two fine bases.
Keeping that distinction is essential when comparability is composed.
-/

/-- Honest PYZ common-container comparability with a C2-family witness.
Fine-base containment in the compact domain is supplied where the witness is
used, rather than imposed on the enlarged base. -/
def compactC2SymmetricGraphLambdaComparableOn
    (domain : Set Real) (center R S : C2GraphRectangle)
    (delta t lambda : Real) : Prop :=
  exists container : C2GraphRectangle,
    container.rectangle.right - container.rectangle.left =
      Real.sqrt (lambda * delta / t) ∧
    R.carrier delta ∪ S.carrier delta ⊆
      container.carrier (lambda * delta) ∧
    InPointwiseC2BallOn domain center container (3 * t)

theorem compactC2SymmetricGraphLambdaComparableOn_symm
    {domain : Set Real} {center R S : C2GraphRectangle}
    {delta t lambda : Real}
    (h : compactC2SymmetricGraphLambdaComparableOn
      domain center R S delta t lambda) :
    compactC2SymmetricGraphLambdaComparableOn
      domain center S R delta t lambda := by
  rcases h with ⟨container, hlength, hcontain, hball⟩
  refine ⟨container, hlength, ?_, hball⟩
  simpa [union_comm] using hcontain

theorem symmetricGraphLambdaComparable_of_compactC2On
    {domain : Set Real} {center R S : C2GraphRectangle}
    {delta t lambda : Real}
    (h : compactC2SymmetricGraphLambdaComparableOn
      domain center R S delta t lambda) :
    symmetricGraphLambdaComparable
      R.rectangle S.rectangle delta t lambda := by
  rcases h with ⟨container, hlength, hcontain, _hball⟩
  exact ⟨container.rectangle, hlength, hcontain⟩

theorem compactC2SymmetricGraphLambdaComparableOn_refl
    {domain : Set Real} {center R : C2GraphRectangle}
    {delta t lambda : Real}
    (hdelta : 0 <= delta) (ht : 0 < t) (hlambda : 1 <= lambda)
    (hlength : R.rectangle.right - R.rectangle.left =
      Real.sqrt (delta / t))
    (hR : InPointwiseC2BallOn domain center R (3 * t)) :
    compactC2SymmetricGraphLambdaComparableOn
      domain center R R delta t lambda := by
  let container := centeredC2GraphRectangleDilation R delta t lambda
  refine ⟨container,
    centeredC2GraphRectangleDilation_length R delta t lambda, ?_, ?_⟩
  · simpa [container] using
      (carrier_subset_centeredC2GraphRectangleDilation
        R hdelta ht hlambda hlength)
  · exact centeredC2GraphRectangleDilation_mem_c2BallOn hR

#print axioms compactC2SymmetricGraphLambdaComparableOn
#print axioms compactC2SymmetricGraphLambdaComparableOn_symm
#print axioms symmetricGraphLambdaComparable_of_compactC2On
#print axioms compactC2SymmetricGraphLambdaComparableOn_refl

end

end FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1
