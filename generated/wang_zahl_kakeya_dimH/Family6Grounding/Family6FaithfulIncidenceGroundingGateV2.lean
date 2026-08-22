import Family6Grounding.Family6FaithfulPlankSlabIncidenceCoreV9

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace Family6FaithfulIncidenceGroundingGateV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6FaithfulPlankSlabIncidenceCoreV9

noncomputable section

universe u v

/-- The legacy everywhere-empty incidence. -/
def emptyPlankSlabIncidence
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} (D : ShadedConvexPlankFamily index a b) :
    PlankSlabIncidence index D where
  members := fun _ _ => ∅
  members_contained := by
    intro theta S
    exact Finset.empty_subset _

/-- Machine grounding requires faithful V9 semantics and exact preservation
of the production body and its complete orthonormal frame. -/
structure GroundedIncidenceGate
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    (slabComparisonConstant tangentComparisonConstant : NNReal)
    (I : PlankSlabIncidence index D)
    (sourceBody : sourceIndex → ConvexBody Space)
    (sourceFrame : sourceIndex → OrthonormalBasis (Fin 3) ℝ Space) :
    Type (max u v) where
  faithful : FaithfulPlankSlabIncidence sourceIndex index D
    slabComparisonConstant tangentComparisonConstant
  incidence_eq : I = faithful.toPlankSlabIncidence
  body_preserved : ∀ s,
    D.family (faithful.sourceToIndex s) = sourceBody s
  frame_preserved : ∀ s,
    (faithful.plank (faithful.sourceToIndex s)).box.frame = sourceFrame s

/-- A machine status is conditional unless a complete grounding gate is
present.  No legacy incidence datum alone can construct `grounded`. -/
inductive GroundingStatus
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    (slabComparisonConstant tangentComparisonConstant : NNReal)
    (I : PlankSlabIncidence index D)
    (sourceBody : sourceIndex → ConvexBody Space)
    (sourceFrame : sourceIndex → OrthonormalBasis (Fin 3) ℝ Space) :
    Type (max u v) where
  | conditional
  | grounded
      (gate : GroundedIncidenceGate slabComparisonConstant
        tangentComparisonConstant I sourceBody sourceFrame)

def GroundingStatus.IsGrounded
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    {I : PlankSlabIncidence index D}
    {sourceBody : sourceIndex → ConvexBody Space}
    {sourceFrame : sourceIndex → OrthonormalBasis (Fin 3) ℝ Space} :
    GroundingStatus slabComparisonConstant tangentComparisonConstant I
      sourceBody sourceFrame → Prop
  | .conditional => False
  | .grounded _ => True

/-- V9 tangent coverage rules out the everywhere-empty legacy datum. -/
theorem faithful_toPlankSlabIncidence_ne_empty
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : FaithfulPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant) :
    R.toPlankSlabIncidence ≠ emptyPlankSlabIncidence D := by
  intro hEq
  apply R.not_all_members_empty
  intro theta S
  have hmembers := congrArg
    (fun J : PlankSlabIncidence index D => J.members theta S) hEq
  simpa [FaithfulPlankSlabIncidence.toPlankSlabIncidence,
    emptyPlankSlabIncidence] using hmembers

theorem emptyPlankSlabIncidence_has_no_grounded_gate
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    (slabComparisonConstant tangentComparisonConstant : NNReal)
    (sourceBody : sourceIndex → ConvexBody Space)
    (sourceFrame : sourceIndex → OrthonormalBasis (Fin 3) ℝ Space) :
    ¬ Nonempty (GroundedIncidenceGate slabComparisonConstant
      tangentComparisonConstant (emptyPlankSlabIncidence D)
        sourceBody sourceFrame) := by
  rintro ⟨G⟩
  exact faithful_toPlankSlabIncidence_ne_empty G.faithful
    G.incidence_eq.symm

theorem emptyPlankSlabIncidence_status_not_grounded
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    (slabComparisonConstant tangentComparisonConstant : NNReal)
    (sourceBody : sourceIndex → ConvexBody Space)
    (sourceFrame : sourceIndex → OrthonormalBasis (Fin 3) ℝ Space)
    (status : GroundingStatus slabComparisonConstant
      tangentComparisonConstant (emptyPlankSlabIncidence D)
        sourceBody sourceFrame) :
    ¬ status.IsGrounded := by
  cases status with
  | conditional => simp [GroundingStatus.IsGrounded]
  | grounded G =>
      intro _hgrounded
      exact (emptyPlankSlabIncidence_has_no_grounded_gate
        slabComparisonConstant tangentComparisonConstant
          sourceBody sourceFrame) ⟨G⟩

theorem GroundedIncidenceGate.one_le_tangentComparisonConstant
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    {I : PlankSlabIncidence index D}
    {sourceBody : sourceIndex → ConvexBody Space}
    {sourceFrame : sourceIndex → OrthonormalBasis (Fin 3) ℝ Space}
    (G : GroundedIncidenceGate slabComparisonConstant
      tangentComparisonConstant I sourceBody sourceFrame) :
    1 ≤ tangentComparisonConstant :=
  G.faithful.one_le_tangentComparisonConstant

theorem GroundedIncidenceGate.reindex_inverses
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    {I : PlankSlabIncidence index D}
    {sourceBody : sourceIndex → ConvexBody Space}
    {sourceFrame : sourceIndex → OrthonormalBasis (Fin 3) ℝ Space}
    (G : GroundedIncidenceGate slabComparisonConstant
      tangentComparisonConstant I sourceBody sourceFrame) :
    (∀ s, G.faithful.indexToSource (G.faithful.sourceToIndex s) = s) ∧
      (∀ i, G.faithful.sourceToIndex (G.faithful.indexToSource i) = i) :=
  ⟨G.faithful.source_leftInverse, G.faithful.index_rightInverse⟩

theorem GroundedIncidenceGate.mem_iff_certified_frameTangent
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    {I : PlankSlabIncidence index D}
    {sourceBody : sourceIndex → ConvexBody Space}
    {sourceFrame : sourceIndex → OrthonormalBasis (Fin 3) ℝ Space}
    (G : GroundedIncidenceGate slabComparisonConstant
      tangentComparisonConstant I sourceBody sourceFrame)
    {theta : NNReal} {S : ConvexBody Space} (i : index) :
    i ∈ I.members theta S ↔
      ∃ cert : CertifiedSlab slabComparisonConstant theta S,
        FrameTangent tangentComparisonConstant (G.faithful.plank i) cert := by
  have hmembers : I.members theta S =
      G.faithful.toPlankSlabIncidence.members theta S :=
    congrArg (fun J : PlankSlabIncidence index D => J.members theta S)
      G.incidence_eq
  rw [hmembers]
  exact G.faithful.mem_iff_frame_tangent i

theorem GroundedIncidenceGate.index_has_admissible_frameTangent
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    {I : PlankSlabIncidence index D}
    {sourceBody : sourceIndex → ConvexBody Space}
    {sourceFrame : sourceIndex → OrthonormalBasis (Fin 3) ℝ Space}
    (G : GroundedIncidenceGate slabComparisonConstant
      tangentComparisonConstant I sourceBody sourceFrame) (i : index) :
    ∃ (theta : NNReal) (S : ConvexBody Space)
      (cert : CertifiedSlab slabComparisonConstant theta S),
        a / b ≤ theta ∧ theta ≤ 1 ∧
          FrameTangent tangentComparisonConstant (G.faithful.plank i) cert :=
  G.faithful.tangent_coverage i

#print axioms faithful_toPlankSlabIncidence_ne_empty
#print axioms emptyPlankSlabIncidence_has_no_grounded_gate
#print axioms emptyPlankSlabIncidence_status_not_grounded
#print axioms GroundedIncidenceGate.one_le_tangentComparisonConstant
#print axioms GroundedIncidenceGate.reindex_inverses
#print axioms GroundedIncidenceGate.mem_iff_certified_frameTangent
#print axioms GroundedIncidenceGate.index_has_admissible_frameTangent

end
end Family6FaithfulIncidenceGroundingGateV2
