import Family6Grounding.Family6AffinePlankAnalyticHypothesesStableV1
import Submission.Kakeya.ConvexFactoring.CertifiedSlabOverlap

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace Family6FaithfulPlankSlabIncidenceCoreV9

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1

noncomputable section

universe u v

/-- A data-bearing frame for one `a × b × 1` plank. -/
structure FramedPlank (C a b : NNReal) (K : ConvexBody Space) : Type
    extends BoxDimensionsCertificate C (plankSides a b) K

/-- A data-bearing frame for one `theta × 1 × 1` test slab. -/
structure CertifiedSlab (C theta : NNReal) (S : ConvexBody Space) : Type
    extends SlabDimensionsCertificate C theta S

/-- Sine of the angle between the two certified short normals.  In three
dimensions these normals determine the two long-direction planes. -/
def planeSine
    {Cp a b Cs theta : NNReal} {K S : ConvexBody Space}
    (P : FramedPlank Cp a b K) (Q : CertifiedSlab Cs theta S) : Real :=
  Real.sin (InnerProductGeometry.angle (P.box.frame 0) (Q.box.frame 0))

/-- Fixed, frame-grounded form of the manuscript condition: the plank lies
inside the slab and the two long-direction planes have angle at most a
constant times theta.  The comparison constant is explicit scalar data. -/
def FrameTangent
    (tangentComparisonConstant : NNReal)
    {Cp a b Cs theta : NNReal} {K S : ConvexBody Space}
    (P : FramedPlank Cp a b K) (Q : CertifiedSlab Cs theta S) : Prop :=
  (K : Set Space) ⊆ (S : Set Space) ∧
    planeSine P Q ≤ (tangentComparisonConstant : Real) * (theta : Real)

/-- Definitional semantic grounding in the two certified short normals. -/
theorem frameTangent_iff_plane_sine
    (tangentComparisonConstant : NNReal)
    {Cp a b Cs theta : NNReal} {K S : ConvexBody Space}
    (P : FramedPlank Cp a b K) (Q : CertifiedSlab Cs theta S) :
    FrameTangent tangentComparisonConstant P Q ↔
      (K : Set Space) ⊆ (S : Set Space) ∧
        Real.sin (InnerProductGeometry.angle
          (P.box.frame 0) (Q.box.frame 0)) ≤
            (tangentComparisonConstant : Real) * (theta : Real) := Iff.rfl

/-- Canonical union over every certified frame carried by the same legacy
test-slab body.  This is the conservative semantics available when the old
query type contains only `(theta, S)` and no chosen slab frame. -/
noncomputable def membersOfFrames
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} (D : ShadedConvexPlankFamily index a b)
    (slabComparisonConstant tangentComparisonConstant : NNReal)
    (plank : ∀ i, FramedPlank D.comparisonConstant a b (D.family i))
    (theta : NNReal) (S : ConvexBody Space) : Finset index := by
  classical
  exact Finset.univ.filter fun i =>
    ∃ cert : CertifiedSlab slabComparisonConstant theta S,
      FrameTangent tangentComparisonConstant (plank i) cert

@[simp] theorem mem_membersOfFrames
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} (D : ShadedConvexPlankFamily index a b)
    (slabComparisonConstant tangentComparisonConstant : NNReal)
    (plank : ∀ i, FramedPlank D.comparisonConstant a b (D.family i))
    (theta : NNReal) (S : ConvexBody Space) (i : index) :
    i ∈ membersOfFrames D slabComparisonConstant
      tangentComparisonConstant plank theta S ↔
      ∃ cert : CertifiedSlab slabComparisonConstant theta S,
        FrameTangent tangentComparisonConstant (plank i) cert := by
  classical
  simp [membersOfFrames]

/-- Faithful semantic refinement of the legacy `PlankSlabIncidence`.
The production-side and analytic index types are related by genuine inverse
maps.  On every certified slab, membership is sound and complete for the
fixed frame-level `FrameTangent` predicate. -/
structure FaithfulPlankSlabIncidence
    (sourceIndex : Type v) [Fintype sourceIndex] [DecidableEq sourceIndex]
    (index : Type u) [Fintype index] [DecidableEq index]
    {a b : NNReal} (D : ShadedConvexPlankFamily index a b)
    (slabComparisonConstant tangentComparisonConstant : NNReal) where
  one_le_tangentComparisonConstant : 1 ≤ tangentComparisonConstant
  index_nonempty : Nonempty index
  sourceToIndex : sourceIndex → index
  indexToSource : index → sourceIndex
  source_leftInverse : ∀ s, indexToSource (sourceToIndex s) = s
  index_rightInverse : ∀ i, sourceToIndex (indexToSource i) = i
  plank : ∀ i, FramedPlank D.comparisonConstant a b (D.family i)
  members : NNReal → ConvexBody Space → Finset index
  members_contained : ∀ theta S,
    members theta S ⊆ containedIndices D (S : Set Space)
  mem_iff_frame_tangent : ∀ {theta : NNReal} {S : ConvexBody Space}
    (i : index), i ∈ members theta S ↔
      ∃ cert : CertifiedSlab slabComparisonConstant theta S,
        FrameTangent tangentComparisonConstant (plank i) cert
  tangent_coverage : ∀ i, ∃ (theta : NNReal) (S : ConvexBody Space)
    (cert : CertifiedSlab slabComparisonConstant theta S),
      a / b ≤ theta ∧ theta ≤ 1 ∧
        FrameTangent tangentComparisonConstant (plank i) cert

/-- Generic constructor proving the grounded contract is an actual data type,
not an empty shell.  It still requires genuine frames and tangent coverage;
it is not an actual-production constructor. -/
noncomputable def FaithfulPlankSlabIncidence.ofFrames
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} (D : ShadedConvexPlankFamily index a b)
    (slabComparisonConstant tangentComparisonConstant : NNReal)
    (one_le_tangentComparisonConstant : 1 ≤ tangentComparisonConstant)
    (index_nonempty : Nonempty index)
    (sourceToIndex : sourceIndex → index)
    (indexToSource : index → sourceIndex)
    (source_leftInverse : ∀ s, indexToSource (sourceToIndex s) = s)
    (index_rightInverse : ∀ i, sourceToIndex (indexToSource i) = i)
    (plank : ∀ i, FramedPlank D.comparisonConstant a b (D.family i))
    (tangent_coverage : ∀ i, ∃ (theta : NNReal) (S : ConvexBody Space)
      (cert : CertifiedSlab slabComparisonConstant theta S),
        a / b ≤ theta ∧ theta ≤ 1 ∧
          FrameTangent tangentComparisonConstant (plank i) cert) :
    FaithfulPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant where
  one_le_tangentComparisonConstant := one_le_tangentComparisonConstant
  index_nonempty := index_nonempty
  sourceToIndex := sourceToIndex
  indexToSource := indexToSource
  source_leftInverse := source_leftInverse
  index_rightInverse := index_rightInverse
  plank := plank
  members := membersOfFrames D slabComparisonConstant
    tangentComparisonConstant plank
  members_contained := by
    classical
    intro theta S i hi
    obtain ⟨_cert, htangent⟩ :=
      (mem_membersOfFrames D slabComparisonConstant
        tangentComparisonConstant plank theta S i).mp hi
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ i, htangent.1⟩
  mem_iff_frame_tangent := by
    intro theta S i
    exact mem_membersOfFrames D slabComparisonConstant
      tangentComparisonConstant plank theta S i
  tangent_coverage := tangent_coverage

/-- Every production-side index is covered by the analytic reindex. -/
theorem FaithfulPlankSlabIncidence.source_coverage
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : FaithfulPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant) (s : sourceIndex) :
    ∃ i, R.indexToSource i = s := by
  exact ⟨R.sourceToIndex s, R.source_leftInverse s⟩

/-- Every analytic index is covered by the production-side reindex. -/
theorem FaithfulPlankSlabIncidence.index_coverage
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : FaithfulPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant) (i : index) :
    ∃ s, R.sourceToIndex s = i := by
  exact ⟨R.indexToSource i, R.index_rightInverse i⟩

/-- Forget only the semantic grounding, retaining the exact legacy data. -/
def FaithfulPlankSlabIncidence.toPlankSlabIncidence
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : FaithfulPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant) :
    PlankSlabIncidence index D where
  members := R.members
  members_contained := R.members_contained

/-- Every analytic index has a certified, admissible-scale, genuine member. -/
theorem FaithfulPlankSlabIncidence.member_coverage
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : FaithfulPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant) (i : index) :
    ∃ (theta : NNReal) (S : ConvexBody Space)
      (_cert : CertifiedSlab slabComparisonConstant theta S),
        a / b ≤ theta ∧ theta ≤ 1 ∧ i ∈ R.members theta S := by
  obtain ⟨theta, S, cert, hthetaLower, hthetaUpper, htangent⟩ :=
    R.tangent_coverage i
  exact ⟨theta, S, cert, hthetaLower, hthetaUpper,
    (R.mem_iff_frame_tangent i).2 ⟨cert, htangent⟩⟩

/-- Unconditional negative vacuity test.  Nonempty analytic indexing plus
per-index geometric coverage rules out the everywhere-empty implementation. -/
theorem FaithfulPlankSlabIncidence.not_all_members_empty
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : FaithfulPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant) :
    ¬ (∀ theta S, R.members theta S = ∅) := by
  rintro hall
  let i : index := Classical.choice R.index_nonempty
  obtain ⟨theta, S, _cert, _hthetaLower, _hthetaUpper, hmem⟩ :=
    R.member_coverage i
  rw [hall theta S] at hmem
  simp at hmem

/-- Negative vacuity test: a frame-grounded tangent witness forces a genuine
member, so the everywhere-empty legacy implementation cannot arise. -/
theorem FaithfulPlankSlabIncidence.not_all_members_empty_of_frameTangent
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : FaithfulPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    (h : ∃ (theta : NNReal) (S : ConvexBody Space)
      (cert : CertifiedSlab slabComparisonConstant theta S) (i : index),
        FrameTangent tangentComparisonConstant (R.plank i) cert) :
    ¬ (∀ theta S, R.members theta S = ∅) := by
  rintro hall
  obtain ⟨theta, S, cert, i, htangent⟩ := h
  have hmem : i ∈ R.members theta S :=
    (R.mem_iff_frame_tangent i).2 ⟨cert, htangent⟩
  rw [hall theta S] at hmem
  simp at hmem

/-- Thin adapter from faithful incidence plus the actual numerical count to
the legacy Katz--Tao control consumed by the analytic theorem. -/
theorem FaithfulPlankSlabIncidence.katzTaoControl
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : FaithfulPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    (eta gamma : Real) (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hcount : ∀ theta : NNReal, a / b ≤ theta → theta ≤ 1 →
      ∀ S : ConvexBody Space,
        IsSlab slabComparisonConstant theta S →
          ((R.members theta S).card : ENNReal) ≤
            (a : ENNReal) ^ (-eta) *
              (theta : ENNReal) ^ gamma *
                (Fintype.card index : ENNReal)) :
    KatzTaoSlabIncidenceControl D R.toPlankSlabIncidence
      slabComparisonConstant eta gamma := by
  exact ⟨hgamma0, hgamma1, hcount⟩

#print axioms frameTangent_iff_plane_sine
#print axioms mem_membersOfFrames
#print axioms FaithfulPlankSlabIncidence.ofFrames
#print axioms FaithfulPlankSlabIncidence.source_coverage
#print axioms FaithfulPlankSlabIncidence.index_coverage
#print axioms FaithfulPlankSlabIncidence.toPlankSlabIncidence
#print axioms FaithfulPlankSlabIncidence.member_coverage
#print axioms FaithfulPlankSlabIncidence.not_all_members_empty
#print axioms FaithfulPlankSlabIncidence.not_all_members_empty_of_frameTangent
#print axioms FaithfulPlankSlabIncidence.katzTaoControl

end
end Family6FaithfulPlankSlabIncidenceCoreV9
