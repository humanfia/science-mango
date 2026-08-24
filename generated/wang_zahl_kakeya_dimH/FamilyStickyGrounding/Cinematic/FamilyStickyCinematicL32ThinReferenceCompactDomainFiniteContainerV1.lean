import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
import Mathlib.Data.Finset.Max

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32ThinReferenceCompactDomainFiniteContainerV1

open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1

noncomputable section

/-! # Exact rebased containers preserving compact-domain C2 control -/

/-- A finite family of intervals with bounded cross-endpoint differences
fits into one interval of the prescribed exact length. -/
theorem exists_exact_length_interval_cover_finset
    {index : Type*} (indices : Finset index)
    (left right : index -> Real) {length : Real}
    (hcross : forall i, i ∈ indices -> forall j, j ∈ indices ->
      right i - left j <= length) :
    exists containerLeft containerRight,
      containerRight - containerLeft = length ∧
      forall i, i ∈ indices ->
        Icc (left i) (right i) ⊆ Icc containerLeft containerRight := by
  classical
  by_cases hindices : indices.Nonempty
  · let leftValues := indices.image left
    have hleftValues : leftValues.Nonempty := hindices.image left
    let containerLeft := leftValues.min' hleftValues
    let containerRight := containerLeft + length
    have hleftMem : containerLeft ∈ leftValues :=
      Finset.min'_mem leftValues hleftValues
    rcases Finset.mem_image.mp hleftMem with ⟨j, hj, hjLeft⟩
    refine ⟨containerLeft, containerRight, by simp [containerRight], ?_⟩
    intro i hi theta htheta
    constructor
    · have hleftIn : left i ∈ leftValues :=
        Finset.mem_image.mpr ⟨i, hi, rfl⟩
      exact (Finset.min'_le leftValues (left i) hleftIn).trans htheta.1
    · have hbound := hcross i hi j hj
      rw [hjLeft] at hbound
      dsimp only [containerRight]
      linarith [htheta.2]
  · refine ⟨0, length, by ring, ?_⟩
    intro i hi
    exact (hindices ⟨i, hi⟩).elim

/-- Rebase one actual C2 graph without altering any jet. -/
def rebaseC2GraphRectangle
    (reference : C2GraphRectangle) (left length : Real)
    (hlengthNonneg : 0 <= length) : C2GraphRectangle where
  rectangle :=
    { graph := reference.rectangle.graph
      left := left
      right := left + length
      left_le_right := by linarith }
  first := reference.first
  second := reference.second
  graph_hasDeriv := reference.graph_hasDeriv
  first_hasDeriv := reference.first_hasDeriv

@[simp]
theorem rebaseC2GraphRectangle_length
    (reference : C2GraphRectangle) (left length : Real)
    (hlengthNonneg : 0 <= length) :
    (rebaseC2GraphRectangle reference left length hlengthNonneg).rectangle.right -
        (rebaseC2GraphRectangle reference left length hlengthNonneg).rectangle.left =
      length := by
  simp [rebaseC2GraphRectangle]

/-- Rebasing preserves membership in a C2 ball on exactly the same compact
domain; no statement outside the domain is needed. -/
theorem rebaseC2GraphRectangle_mem_c2BallOn
    {domain : Set Real} {center reference : C2GraphRectangle}
    {radius left length : Real}
    (hlengthNonneg : 0 <= length)
    (hreference : InPointwiseC2BallOn domain center reference radius) :
    InPointwiseC2BallOn domain center
      (rebaseC2GraphRectangle reference left length hlengthNonneg)
      radius := by
  intro z hz
  simpa [rebaseC2GraphRectangle] using hreference z hz

/-- Promote literal reference tangency to the rebased container after
covering the fine base. -/
theorem carrier_subset_rebase_of_base_subset_and_reference_tangent
    (R reference : C2GraphRectangle) {left length delta V : Real}
    (hlengthNonneg : 0 <= length)
    (hbase : R.rectangle.base ⊆ Icc left (left + length))
    (htangent : R.carrier delta ⊆
      cinematicVerticalNeighborhood reference.rectangle.graph
        R.rectangle.base V) :
    R.carrier delta ⊆
      (rebaseC2GraphRectangle reference left length hlengthNonneg).carrier V := by
  intro q hq
  have hqTangent := htangent hq
  exact ⟨hbase hqTangent.1, hqTangent.2⟩

/-- Diameter-bounded fine bases produce an exact-length literal graph
container, and compact-domain C2 membership of its reference graph is
transported to the container. -/
theorem exists_rebased_container_of_bases_in_diameter_piece_on
    {index : Type*} (indices : Finset index)
    (rectangles : index -> C2GraphRectangle)
    (reference : C2GraphRectangle) (piece domain : Set Real)
    {length delta V : Real} (hlengthNonneg : 0 <= length)
    (hbaseInPiece : forall i, i ∈ indices ->
      (rectangles i).rectangle.base ⊆ piece)
    (hpieceDiameter : forall x, x ∈ piece -> forall y, y ∈ piece ->
      dist x y <= length)
    (htangent : forall i, i ∈ indices ->
      (rectangles i).carrier delta ⊆
        cinematicVerticalNeighborhood reference.rectangle.graph
          (rectangles i).rectangle.base V) :
    exists container : C2GraphRectangle,
      container.rectangle.right - container.rectangle.left = length ∧
      (forall center radius,
        InPointwiseC2BallOn domain center reference radius ->
          InPointwiseC2BallOn domain center container radius) ∧
      forall i, i ∈ indices ->
        (rectangles i).carrier delta ⊆ container.carrier V := by
  have hcross : forall i, i ∈ indices -> forall j, j ∈ indices ->
      (rectangles i).rectangle.right -
        (rectangles j).rectangle.left <= length := by
    intro i hi j hj
    have hrightBase : (rectangles i).rectangle.right ∈
        (rectangles i).rectangle.base :=
      ⟨(rectangles i).rectangle.left_le_right, le_rfl⟩
    have hleftBase : (rectangles j).rectangle.left ∈
        (rectangles j).rectangle.base :=
      ⟨le_rfl, (rectangles j).rectangle.left_le_right⟩
    have hdist := hpieceDiameter
      (rectangles i).rectangle.right (hbaseInPiece i hi hrightBase)
      (rectangles j).rectangle.left (hbaseInPiece j hj hleftBase)
    rw [Real.dist_eq] at hdist
    exact (le_abs_self
      ((rectangles i).rectangle.right -
        (rectangles j).rectangle.left)).trans hdist
  rcases exists_exact_length_interval_cover_finset indices
      (fun i => (rectangles i).rectangle.left)
      (fun i => (rectangles i).rectangle.right) hcross with
    ⟨containerLeft, containerRight, hcontainerLength, hbaseCover⟩
  have hright : containerRight = containerLeft + length := by linarith
  let container := rebaseC2GraphRectangle
    reference containerLeft length hlengthNonneg
  refine ⟨container, ?_, ?_, ?_⟩
  · exact rebaseC2GraphRectangle_length
      reference containerLeft length hlengthNonneg
  · intro center radius hreference
    exact rebaseC2GraphRectangle_mem_c2BallOn hlengthNonneg hreference
  · intro i hi
    apply carrier_subset_rebase_of_base_subset_and_reference_tangent
      (rectangles i) reference hlengthNonneg
    · simpa [GraphRectangle.base, hright] using hbaseCover i hi
    · exact htangent i hi

#print axioms exists_exact_length_interval_cover_finset
#print axioms rebaseC2GraphRectangle
#print axioms rebaseC2GraphRectangle_length
#print axioms rebaseC2GraphRectangle_mem_c2BallOn
#print axioms carrier_subset_rebase_of_base_subset_and_reference_tangent
#print axioms exists_rebased_container_of_bases_in_diameter_piece_on

end

end FamilyStickyCinematicL32ThinReferenceCompactDomainFiniteContainerV1
