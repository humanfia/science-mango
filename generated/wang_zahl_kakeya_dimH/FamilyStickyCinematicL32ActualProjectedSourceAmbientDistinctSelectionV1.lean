import FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
import FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32ActualProjectedSourceAmbientDistinctSelectionV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1

noncomputable section

/-!
# Ambient distinctness producer for actual projected critical selection

Every active family is a literal filter of the fixed finite ambient family.
Thus the paper's global essentially-distinct tube hypothesis restricts to
every projected fibre automatically; no pointwise distinctness callback is
needed.
-/

universe u v

/-- Any pairwise relation on the ambient family restricts to every literal
active incidence fibre. -/
theorem pairwise_activeAtPoint_of_pairwise_ambient
    {point : Type v} [MeasurableSpace point]
    {iota : Type u} [DecidableEq iota]
    (Z : FiniteProjectedShading point iota)
    {relation : iota -> iota -> Prop}
    (hambient : Set.Pairwise (Z.ambient : Set iota) relation) :
    forall x, Set.Pairwise (Z.activeAtPoint x : Set iota) relation := by
  intro x i hi j hj hij
  exact hambient ((Z.mem_activeAtPoint x i).mp hi).1
    ((Z.mem_activeAtPoint x j).mp hj).1 hij

/-- In particular, global essential distinctness supplies the pointwise
geometric input used by the selected critical-family nonemptiness theorem. -/
theorem essentiallyDistinct_activeAtPoint_of_ambient
    {point : Type v} [MeasurableSpace point]
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (Z : FiniteProjectedShading point iota)
    (hambient : Set.Pairwise (Z.ambient : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j)) :
    forall x, Set.Pairwise (Z.activeAtPoint x : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j) :=
  pairwise_activeAtPoint_of_pairwise_ambient Z hambient

#print axioms pairwise_activeAtPoint_of_pairwise_ambient
#print axioms essentiallyDistinct_activeAtPoint_of_ambient

end

end FamilyStickyCinematicL32ActualProjectedSourceAmbientDistinctSelectionV1
