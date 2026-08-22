import Family6Grounding.Family6FaithfulCrossCertificateFrameSpreadV2
import Submission.Kakeya.ConvexFactoring.BoxDimensionsMeasure
import Submission.Kakeya.ConvexFactoring.TransverseUnit
import Submission.Kakeya.ConvexFactoring.CertifiedSlabDyadicAngle

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace Family6CertifiedSlabFrameSpreadOneV6

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6FaithfulPlankSlabIncidenceCoreV9
open Family6FaithfulCrossCertificateFrameSpreadV2

noncomputable section

/-- Two exact-comparison (`C=1`) slab certificates for the same body and
scale have projective short-frame sine at most `2*theta`.  This follows from
the body's slab-volume lower bound and the transverse intersection upper
bound; no certificate uniqueness is assumed. -/
theorem certifiedSlabShortFrameSpread_one_two :
    CertifiedSlabShortFrameSpread 1 2 := by
  intro theta S cert₀ cert₁
  let s : Real := Real.sin (InnerProductGeometry.angle
    (cert₀.box.frame 0) (cert₁.box.frame 0))
  by_cases hs0 : s = 0
  · simp [s, hs0]
  have hspos : 0 < s :=
    lt_of_le_of_ne
      (InnerProductGeometry.sin_angle_nonneg
        (cert₀.box.frame 0) (cert₁.box.frame 0))
      (Ne.symm hs0)
  have hupper :=
    cert₀.toSlabDimensionsCertificate.volume_inter_body_le_sin_angle_auto
      cert₁.toSlabDimensionsCertificate hspos
  rw [Set.inter_self] at hupper
  have hslab : IsSlab 1 theta S :=
    slabDimensionsCertificate_isSlab cert₀.toSlabDimensionsCertificate
  have hlower := hslab.volume_lower_bound
  norm_num at hlower
  have hchain :
      (theta : ENNReal) ≤
        ENNReal.ofReal (s⁻¹) * 2 * (theta : ENNReal) *
          (theta : ENNReal) := by
    exact hlower.trans hupper
  have hchainReal :=
    (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr hchain
  have hsInvPos : 0 < s⁻¹ := inv_pos.mpr hspos
  norm_num only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal hsInvPos.le, ENNReal.coe_toReal] at hchainReal
  have hthetaPos : 0 < (theta : Real) := by exact_mod_cast cert₀.theta_pos
  have hdiv : (1 : Real) ≤ s⁻¹ * 2 * (theta : Real) := by
    apply le_of_mul_le_mul_right _ hthetaPos
    simpa only [one_mul, mul_one, mul_assoc, mul_left_comm, mul_comm] using
      hchainReal
  change s ≤ (2 : Real) * (theta : Real)
  calc
    s = s * 1 := by ring
    _ ≤ s * (s⁻¹ * 2 * (theta : Real)) :=
      mul_le_mul_of_nonneg_left hdiv hspos.le
    _ = 2 * (theta : Real) := by
      field_simp [ne_of_gt hspos]

#print axioms certifiedSlabShortFrameSpread_one_two

end
end Family6CertifiedSlabFrameSpreadOneV6
