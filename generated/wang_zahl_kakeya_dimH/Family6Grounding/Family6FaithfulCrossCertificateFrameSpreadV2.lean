import Family6Grounding.Family6FaithfulSameCertifiedSlabFineAngleV2

set_option autoImplicit false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace BigOperators

namespace Family6FaithfulCrossCertificateFrameSpreadV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6FaithfulPlankSlabIncidenceCoreV9
open Family6FineFiberCanonicalAngleSchemeCoreV2
open Family6ProjectiveSineTriangleV1
open Family6FaithfulSameCertifiedSlabFineAngleV2

noncomputable section

universe u v

/-- Quantitative replacement for nonexistent certificate uniqueness: any
two slab certificates for the same body and scale have projective short-axis
sine at most `spreadConstant * theta`. -/
def CertifiedSlabShortFrameSpread
    (slabComparisonConstant spreadConstant : NNReal) : Prop :=
  ∀ (theta : NNReal) (S : ConvexBody Space)
    (cert cert' : CertifiedSlab slabComparisonConstant theta S),
      Real.sin (InnerProductGeometry.angle
        (cert.box.frame 0) (cert'.box.frame 0)) ≤
          (spreadConstant : Real) * (theta : Real)

/-- With cross-certificate frame spread `q`, two members of the existential
V9 union lie in one fine-angle row with exact constant `2*c+q`. -/
theorem faithfulCommonTangentFineAngleCoverage_of_certificateFrameSpread
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant spreadConstant : NNReal}
    (R : FaithfulPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    (hspread : CertifiedSlabShortFrameSpread
      slabComparisonConstant spreadConstant) :
    FaithfulCommonTangentFineAngleCoverage R
      (2 * tangentComparisonConstant + spreadConstant) := by
  intro theta S i hi j hj
  obtain ⟨certi, hti⟩ := (R.mem_iff_frame_tangent i).mp hi
  obtain ⟨certj, htj⟩ := (R.mem_iff_frame_tangent j).mp hj
  have htriOuter := sin_angle_triangle_projective
    ((R.plank i).box.frame 0) (certi.box.frame 0)
    ((R.plank j).box.frame 0)
  have htriInner := sin_angle_triangle_projective
    (certi.box.frame 0) (certj.box.frame 0)
    ((R.plank j).box.frame 0)
  have hi' :
      Real.sin (InnerProductGeometry.angle
        ((R.plank i).box.frame 0) (certi.box.frame 0)) ≤
        (tangentComparisonConstant : Real) * (theta : Real) := hti.2
  have hj' :
      Real.sin (InnerProductGeometry.angle
        (certj.box.frame 0) ((R.plank j).box.frame 0)) ≤
        (tangentComparisonConstant : Real) * (theta : Real) := by
    rw [InnerProductGeometry.angle_comm]
    exact htj.2
  have hcert :
      Real.sin (InnerProductGeometry.angle
        (certi.box.frame 0) (certj.box.frame 0)) ≤
        (spreadConstant : Real) * (theta : Real) :=
    hspread theta S certi certj
  have hreal :
      Real.sin (InnerProductGeometry.angle
        ((R.plank i).box.frame 0) ((R.plank j).box.frame 0)) ≤
        ((2 : Real) * (tangentComparisonConstant : Real) +
          (spreadConstant : Real)) * (theta : Real) := by
    linarith
  change Real.toNNReal (Real.sin (InnerProductGeometry.angle
    ((R.plank i).box.frame 0) ((R.plank j).box.frame 0))) ≤
      (2 * tangentComparisonConstant + spreadConstant) * theta
  rw [Real.toNNReal_le_iff_le_coe]
  simpa using hreal

/-- Projective uniqueness is the zero-spread special case.  It is explicit
because `SlabDimensionsCertificate` itself does not provide uniqueness. -/
def CertifiedSlabShortFrameProjectivelyUnique
    (slabComparisonConstant : NNReal) : Prop :=
  ∀ (theta : NNReal) (S : ConvexBody Space)
    (cert cert' : CertifiedSlab slabComparisonConstant theta S),
      Real.sin (InnerProductGeometry.angle
        (cert.box.frame 0) (cert'.box.frame 0)) = 0

theorem certifiedSlabShortFrameSpread_zero_of_projectivelyUnique
    {slabComparisonConstant : NNReal}
    (hunique : CertifiedSlabShortFrameProjectivelyUnique
      slabComparisonConstant) :
    CertifiedSlabShortFrameSpread slabComparisonConstant 0 := by
  intro theta S cert cert'
  simpa using (hunique theta S cert cert').le

/-- Zero spread lets either existential witness serve both planks, thereby
recovering literal pairwise common-certificate coherence. -/
theorem commonCertificateCoherence_of_projectivelyUnique
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : FaithfulPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    (hunique : CertifiedSlabShortFrameProjectivelyUnique
      slabComparisonConstant) :
    FaithfulMemberCommonCertificateCoherence R := by
  intro theta S i j hi hj
  obtain ⟨certi, hti⟩ := (R.mem_iff_frame_tangent i).mp hi
  obtain ⟨certj, htj⟩ := (R.mem_iff_frame_tangent j).mp hj
  refine ⟨certi, hti, htj.1, ?_⟩
  have htri := sin_angle_triangle_projective
    ((R.plank j).box.frame 0) (certj.box.frame 0) (certi.box.frame 0)
  have hj' :
      Real.sin (InnerProductGeometry.angle
        ((R.plank j).box.frame 0) (certj.box.frame 0)) ≤
        (tangentComparisonConstant : Real) * (theta : Real) := htj.2
  have hzero :
      Real.sin (InnerProductGeometry.angle
        (certj.box.frame 0) (certi.box.frame 0)) = 0 :=
    hunique theta S certj certi
  change Real.sin (InnerProductGeometry.angle
    ((R.plank j).box.frame 0) (certi.box.frame 0)) ≤
      (tangentComparisonConstant : Real) * (theta : Real)
  linarith

#print axioms faithfulCommonTangentFineAngleCoverage_of_certificateFrameSpread
#print axioms commonCertificateCoherence_of_projectivelyUnique

end
end Family6FaithfulCrossCertificateFrameSpreadV2
