import Submission.Kakeya.ConvexFactoring.CertifiedSlabOverlap
import Submission.Kakeya.ConvexFactoring.FrameBoxCoordinateWindowEquiv
import Submission.Kakeya.ConvexGeometry.Tube

set_option autoImplicit false

open scoped NNReal ENNReal InnerProductSpace
open Set

namespace JohnSideLowerFinal

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

/-- A tube's transverse closed ball forces every side of any containing
frame-box certificate to have width at least twice the tube radius. -/
theorem boxCertificate_side_lower_of_tube_subset
    {K : ConvexBody Space} {delta : NNReal} (T : Tube delta)
    (hTK : T.carrier ⊆ (K : Set Space))
    {side : Fin 3 -> NNReal}
    (cert : BoxDimensionsCertificate 288 side K) (i : Fin 3) :
    2 * delta <= side i := by
  let p : Space := T.axis.base + (delta : Real) • cert.box.frame i
  let q : Space := T.axis.base - (delta : Real) • cert.box.frame i
  have hpball : p ∈ Metric.closedBall T.axis.base (delta : Real) := by
    rw [Metric.mem_closedBall]
    simp [p, dist_eq_norm, norm_smul]
  have hqball : q ∈ Metric.closedBall T.axis.base (delta : Real) := by
    rw [Metric.mem_closedBall]
    simp [q, norm_smul]
  have hpTube : p ∈ T.carrier :=
    Metric.closedBall_subset_cthickening T.axis.base_mem_carrier
      (delta : Real) hpball
  have hqTube : q ∈ T.carrier :=
    Metric.closedBall_subset_cthickening T.axis.base_mem_carrier
      (delta : Real) hqball
  have hpBox : p ∈ cert.box.carrier := cert.outer_le (hTK hpTube)
  have hqBox : q ∈ cert.box.carrier := cert.outer_le (hTK hqTube)
  have hpcoord := cert.box.centeredCoordinate_abs_le_halfSide hpBox i
  have hqcoord := cert.box.centeredCoordinate_abs_le_halfSide hqBox i
  have hside : cert.box.side i = side i := congrFun cert.side_eq i
  simp [p, q, inner_add_right, inner_sub_right, real_inner_smul_right,
    hside] at hpcoord hqcoord
  rw [abs_le] at hpcoord hqcoord
  apply NNReal.coe_le_coe.mp
  norm_num
  nlinarith [hpcoord.1, hpcoord.2, hqcoord.1, hqcoord.2]

#print axioms boxCertificate_side_lower_of_tube_subset

end
end JohnSideLowerFinal
