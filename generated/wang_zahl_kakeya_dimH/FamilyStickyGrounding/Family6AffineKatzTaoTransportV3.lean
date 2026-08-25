import FamilyStickyGrounding.Family6AffineConvexVolumeCoreV1
import Submission.Kakeya.ConvexFactoring.NonConcentration

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family6AffineKatzTaoTransportV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffineConvexVolumeCoreV1

noncomputable section

universe u

theorem containedIndices_affineImageFamily
    {iota : Type u} [Fintype iota]
    (e : Space ≃ᵃ[ℝ] Space) (F : ConvexFamily iota)
    (K : ConvexBody Space) :
    containedIndices (affineImageFamily e F) K =
      containedIndices F (affinePreimageConvexBody e K) := by
  classical
  ext i
  rw [mem_containedIndices, mem_containedIndices]
  exact affineImage_subset_iff_subset_preimage e _ _

/-- Every contained member volume acquires the same affine Jacobian. -/
theorem containedMass_affineImageFamily
    {iota : Type u} [Fintype iota]
    (e : Space ≃ᵃ[ℝ] Space) (F : ConvexFamily iota)
    (K : ConvexBody Space) :
    containedMass (affineImageFamily e F) K =
      affineJacobian e * containedMass F (affinePreimageConvexBody e K) := by
  classical
  unfold containedMass
  rw [containedIndices_affineImageFamily]
  simp_rw [affineImageFamily, volume_affineImageConvexBody]
  exact (Finset.mul_sum _ _ _).symm

/-- Katz--Tao non-concentration is invariant under a common affine
equivalence; no determinant loss remains. -/
theorem isKatzTao_affineImageFamily
    {iota : Type u} [Fintype iota]
    {C : ENNReal} (e : Space ≃ᵃ[ℝ] Space) (F : ConvexFamily iota)
    (hKT : IsKatzTao C F) :
    IsKatzTao C (affineImageFamily e F) := by
  intro K
  unfold IsKatzTaoAt
  rw [containedMass_affineImageFamily,
    volume_eq_affineJacobian_mul_preimage]
  calc
    affineJacobian e *
        containedMass F (affinePreimageConvexBody e K) ≤
      affineJacobian e *
        (C * volume (affinePreimageConvexBody e K : Set Space)) := by
      gcongr
      simpa [IsKatzTaoAt] using hKT (affinePreimageConvexBody e K)
    _ = C * (affineJacobian e *
        volume (affinePreimageConvexBody e K : Set Space)) := by
      ac_rfl

#print axioms containedIndices_affineImageFamily
#print axioms containedMass_affineImageFamily
#print axioms isKatzTao_affineImageFamily

end
end Family6AffineKatzTaoTransportV3
