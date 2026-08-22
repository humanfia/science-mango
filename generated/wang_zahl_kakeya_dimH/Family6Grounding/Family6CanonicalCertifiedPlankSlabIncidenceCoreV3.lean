import Family6Grounding.Family6FaithfulSameCertifiedSlabFineAngleV2

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace Family6CanonicalCertifiedPlankSlabIncidenceCoreV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6FaithfulPlankSlabIncidenceCoreV9
open Family6ProjectiveSineTriangleV1

noncomputable section

universe u v

/-- A fixed certificate selected from one valid legacy slab query.  The word
`chosen` means one proof-irrelevant choice per `(theta,S)`; it does not assert
geometric uniqueness of slab frames. -/
noncomputable def chosenCertifiedSlab
    {C theta : NNReal} {S : ConvexBody Space}
    (hS : IsSlab C theta S) : CertifiedSlab C theta S where
  toSlabDimensionsCertificate :=
    Classical.choice hS.nonempty_slabDimensionsCertificate

/-- A selector fixes exactly one certified frame for every valid legacy
query.  Supplying a different selector is useful when production geometry
already carries preferred frames. -/
structure SlabCertificateSelector (C : NNReal) where
  select : ∀ {theta : NNReal} {S : ConvexBody Space},
    IsSlab C theta S → CertifiedSlab C theta S

/-- Classical choice always supplies a selector, but by itself does not say
that the selected frames are tangent to any particular plank. -/
noncomputable def classicalChoiceSlabCertificateSelector (C : NNReal) :
    SlabCertificateSelector C where
  select := chosenCertifiedSlab

/-- Faithful incidence with one fixed certified frame at each valid legacy
query.  Membership is derived below and is not an arbitrary callback.
The final field is the exact compatibility needed to retain genuine,
non-vacuous tangent coverage after selecting one certificate per query. -/
structure CanonicalCertifiedPlankSlabIncidence
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
  selector : SlabCertificateSelector slabComparisonConstant
  selected_tangent_coverage : ∀ i, ∃ (theta : NNReal)
    (S : ConvexBody Space) (hS : IsSlab slabComparisonConstant theta S),
      a / b ≤ theta ∧ theta ≤ 1 ∧
        FrameTangent tangentComparisonConstant (plank i)
          (selector.select hS)

/-- The legacy member set is the finite set tangent to the one selected
frame.  Invalid slab queries have no members. -/
noncomputable def CanonicalCertifiedPlankSlabIncidence.members
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : CanonicalCertifiedPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    (theta : NNReal) (S : ConvexBody Space) : Finset index := by
  classical
  exact if hS : IsSlab slabComparisonConstant theta S then
    Finset.univ.filter fun i =>
      FrameTangent tangentComparisonConstant (R.plank i)
        (R.selector.select hS)
  else ∅

@[simp] theorem CanonicalCertifiedPlankSlabIncidence.mem_members_of_isSlab
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : CanonicalCertifiedPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    {theta : NNReal} {S : ConvexBody Space}
    (hS : IsSlab slabComparisonConstant theta S) (i : index) :
    i ∈ R.members theta S ↔
      FrameTangent tangentComparisonConstant (R.plank i)
        (R.selector.select hS) := by
  classical
  simp [CanonicalCertifiedPlankSlabIncidence.members, hS]

@[simp] theorem CanonicalCertifiedPlankSlabIncidence.members_eq_empty_of_not_isSlab
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : CanonicalCertifiedPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    {theta : NNReal} {S : ConvexBody Space}
    (hS : ¬ IsSlab slabComparisonConstant theta S) :
    R.members theta S = ∅ := by
  classical
  simp [CanonicalCertifiedPlankSlabIncidence.members, hS]

/-- Forget the selected frame while retaining exactly the derived member
sets consumed by the legacy analytic endpoint. -/
noncomputable def CanonicalCertifiedPlankSlabIncidence.toPlankSlabIncidence
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : CanonicalCertifiedPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant) :
    PlankSlabIncidence index D where
  members := R.members
  members_contained := by
    classical
    intro theta S i hi
    by_cases hS : IsSlab slabComparisonConstant theta S
    · have htangent := (R.mem_members_of_isSlab hS i).mp hi
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ i, htangent.1⟩
    · rw [R.members_eq_empty_of_not_isSlab hS] at hi
      simp at hi

/-- Selected tangent coverage produces an actual member at an admissible
valid slab query. -/
theorem CanonicalCertifiedPlankSlabIncidence.member_coverage
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : CanonicalCertifiedPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant) (i : index) :
    ∃ (theta : NNReal) (S : ConvexBody Space)
      (_hS : IsSlab slabComparisonConstant theta S),
        a / b ≤ theta ∧ theta ≤ 1 ∧ i ∈ R.members theta S := by
  obtain ⟨theta, S, hS, hthetaLower, hthetaUpper, htangent⟩ :=
    R.selected_tangent_coverage i
  exact ⟨theta, S, hS, hthetaLower, hthetaUpper,
    (R.mem_members_of_isSlab hS i).2 htangent⟩

/-- Nonempty indexing plus selected geometric coverage forbids the
everywhere-empty legacy incidence. -/
theorem CanonicalCertifiedPlankSlabIncidence.not_all_members_empty
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : CanonicalCertifiedPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant) :
    ¬ (∀ theta S, R.members theta S = ∅) := by
  rintro hall
  let i : index := Classical.choice R.index_nonempty
  obtain ⟨theta, S, _hS, _hthetaLower, _hthetaUpper, hi⟩ :=
    R.member_coverage i
  rw [hall theta S] at hi
  simp at hi

/-- Because one query uses one certificate, any two of its members satisfy
the fine pair-angle bound with constant exactly twice the tangent constant.
No cross-certificate coherence or spread premise is needed. -/
theorem CanonicalCertifiedPlankSlabIncidence.pair_sine_le_two_mul
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : CanonicalCertifiedPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    {theta : NNReal} {S : ConvexBody Space}
    (hS : IsSlab slabComparisonConstant theta S)
    {i j : index} (hi : i ∈ R.members theta S)
    (hj : j ∈ R.members theta S) :
    Real.sin (InnerProductGeometry.angle
      ((R.plank i).box.frame 0) ((R.plank j).box.frame 0)) ≤
        (2 : Real) * (tangentComparisonConstant : Real) *
          (theta : Real) := by
  have hti := (R.mem_members_of_isSlab hS i).mp hi
  have htj := (R.mem_members_of_isSlab hS j).mp hj
  have htri := sin_angle_triangle_projective
    ((R.plank i).box.frame 0) ((R.selector.select hS).box.frame 0)
    ((R.plank j).box.frame 0)
  have hi' :
      Real.sin (InnerProductGeometry.angle
        ((R.plank i).box.frame 0) ((R.selector.select hS).box.frame 0)) ≤
        (tangentComparisonConstant : Real) * (theta : Real) := hti.2
  have hj' :
      Real.sin (InnerProductGeometry.angle
        ((R.selector.select hS).box.frame 0) ((R.plank j).box.frame 0)) ≤
        (tangentComparisonConstant : Real) * (theta : Real) := by
    rw [InnerProductGeometry.angle_comm]
    exact htj.2
  linarith

/-- Thin numerical adapter to the unchanged legacy Katz--Tao control. -/
theorem CanonicalCertifiedPlankSlabIncidence.katzTaoControl
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : CanonicalCertifiedPlankSlabIncidence sourceIndex index D
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

#print axioms chosenCertifiedSlab
#print axioms classicalChoiceSlabCertificateSelector
#print axioms CanonicalCertifiedPlankSlabIncidence.mem_members_of_isSlab
#print axioms CanonicalCertifiedPlankSlabIncidence.toPlankSlabIncidence
#print axioms CanonicalCertifiedPlankSlabIncidence.member_coverage
#print axioms CanonicalCertifiedPlankSlabIncidence.not_all_members_empty
#print axioms CanonicalCertifiedPlankSlabIncidence.pair_sine_le_two_mul
#print axioms CanonicalCertifiedPlankSlabIncidence.katzTaoControl

end
end Family6CanonicalCertifiedPlankSlabIncidenceCoreV3
