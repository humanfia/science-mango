import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41EndpointOrderedSkirtDepthV1

open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1

noncomputable section

/-!
# A canonical skirt depth ordered by the left endpoint

Adding `M + 1` to the left endpoint value makes every depth positive under
the existing graph bound.  It preserves strict order exactly, so endpoint
injectivity automatically gives depth injectivity.  This is the finite
ordering needed by the asymmetric exterior-intersection calculation.
-/

def endpointOrderedSkirtDepth
    {curve : Type*} [DecidableEq curve] {curves : Finset curve}
    (graph : curve -> Real -> Real) (A M : Real)
    (c : FirstGenerationCurve curves) : Real :=
  M + 1 + graph c.1 A

theorem endpointOrderedSkirtDepth_pos
    {curve : Type*} [DecidableEq curve] {curves : Finset curve}
    (graph : curve -> Real -> Real) (A M : Real)
    (hbound : forall c, c ∈ curves -> |graph c A| <= M)
    (c : FirstGenerationCurve curves) :
    0 < endpointOrderedSkirtDepth graph A M c := by
  have hlower : -M <= graph c.1 A :=
    neg_le_of_abs_le (hbound c.1 c.2)
  unfold endpointOrderedSkirtDepth
  linarith

theorem endpointOrderedSkirtDepth_lt_iff
    {curve : Type*} [DecidableEq curve] {curves : Finset curve}
    (graph : curve -> Real -> Real) (A M : Real)
    (c d : FirstGenerationCurve curves) :
    endpointOrderedSkirtDepth graph A M c <
        endpointOrderedSkirtDepth graph A M d ↔
      graph c.1 A < graph d.1 A := by
  constructor <;> intro h
  · unfold endpointOrderedSkirtDepth at h
    linarith
  · unfold endpointOrderedSkirtDepth
    linarith

theorem endpointOrderedSkirtDepth_injective
    {curve : Type*} [DecidableEq curve] {curves : Finset curve}
    (graph : curve -> Real -> Real) (A B M : Real)
    (hendpoint : EndpointValuesDistinct curves graph A B) :
    Function.Injective
      (endpointOrderedSkirtDepth (curves := curves) graph A M) := by
  intro c d hcd
  apply Subtype.ext
  apply hendpoint.1 c.2 d.2
  unfold endpointOrderedSkirtDepth at hcd
  linarith

#print axioms endpointOrderedSkirtDepth_pos
#print axioms endpointOrderedSkirtDepth_lt_iff
#print axioms endpointOrderedSkirtDepth_injective

end

end FamilyStickyCinematicL32Prop41EndpointOrderedSkirtDepthV1
