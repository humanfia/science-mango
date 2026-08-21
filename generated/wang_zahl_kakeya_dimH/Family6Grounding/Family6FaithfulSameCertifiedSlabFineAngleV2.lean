import Family6Grounding.Family6FineFiberCanonicalAngleSchemeCoreV2
import Family6Grounding.Family6ProjectiveSineTriangleV1

set_option autoImplicit false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace BigOperators

namespace Family6FaithfulSameCertifiedSlabFineAngleV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6FaithfulPlankSlabIncidenceCoreV9
open Family6FineFiberCanonicalAngleSchemeCoreV2
open Family6ProjectiveSineTriangleV1

noncomputable section

universe u v

/-- Two planks tangent to the very same certified slab have projective
pair-sine at most twice the individual tangent threshold. -/
theorem faithfulFinePairSine_le_two_mul_of_sameCertifiedSlab
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant theta : NNReal}
    (R : FaithfulPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    {S : ConvexBody Space}
    (cert : CertifiedSlab slabComparisonConstant theta S)
    (i j : index)
    (hi : FrameTangent tangentComparisonConstant (R.plank i) cert)
    (hj : FrameTangent tangentComparisonConstant (R.plank j) cert) :
    faithfulFinePairSine R i j ≤
      (2 * tangentComparisonConstant) * theta := by
  have htri := sin_angle_triangle_projective
    ((R.plank i).box.frame 0) (cert.box.frame 0)
    ((R.plank j).box.frame 0)
  have hi' :
      Real.sin (InnerProductGeometry.angle
        ((R.plank i).box.frame 0) (cert.box.frame 0)) ≤
        (tangentComparisonConstant : Real) * (theta : Real) := by
    exact hi.2
  have hj' :
      Real.sin (InnerProductGeometry.angle
        (cert.box.frame 0) ((R.plank j).box.frame 0)) ≤
        (tangentComparisonConstant : Real) * (theta : Real) := by
    rw [InnerProductGeometry.angle_comm]
    exact hj.2
  have hreal :
      Real.sin (InnerProductGeometry.angle
        ((R.plank i).box.frame 0) ((R.plank j).box.frame 0)) ≤
        (2 : Real) * (tangentComparisonConstant : Real) * (theta : Real) := by
    linarith
  change Real.toNNReal (Real.sin (InnerProductGeometry.angle
    ((R.plank i).box.frame 0) ((R.plank j).box.frame 0))) ≤
      (2 * tangentComparisonConstant) * theta
  rw [Real.toNNReal_le_iff_le_coe]
  simpa using hreal

/-- Exact coherence gate missing from V9's existential union semantics:
for each pair of members, one certified frame witnesses both tangencies. -/
def FaithfulMemberCommonCertificateCoherence
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : FaithfulPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant) : Prop :=
  ∀ (theta : NNReal) (S : ConvexBody Space) (i j : index),
    i ∈ R.members theta S → j ∈ R.members theta S →
      ∃ cert : CertifiedSlab slabComparisonConstant theta S,
        FrameTangent tangentComparisonConstant (R.plank i) cert ∧
          FrameTangent tangentComparisonConstant (R.plank j) cert

/-- Common-certificate coherence automatically supplies the fine-angle
coverage gate with the honest constant `2 * tangentComparisonConstant`. -/
theorem faithfulCommonTangentFineAngleCoverage_of_commonCertificate
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : FaithfulPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    (hcoherent : FaithfulMemberCommonCertificateCoherence R) :
    FaithfulCommonTangentFineAngleCoverage R
      (2 * tangentComparisonConstant) := by
  intro theta S i hi j hj
  obtain ⟨cert, hti, htj⟩ := hcoherent theta S i j hi hj
  exact faithfulFinePairSine_le_two_mul_of_sameCertifiedSlab
    R cert i j hti htj

#print axioms faithfulFinePairSine_le_two_mul_of_sameCertifiedSlab
#print axioms faithfulCommonTangentFineAngleCoverage_of_commonCertificate

end
end Family6FaithfulSameCertifiedSlabFineAngleV2
