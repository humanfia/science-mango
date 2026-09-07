import Family8Grounding.Family8Family7CoordinateToVerticalSelectedSubtypeFrostmanV3
import FamilyStickyGrounding.Family6AffineKatzTaoTransportV3

/-!
# Inverse Katz--Tao transport for a selected vertical-coordinate subtype, V2

V1 is frozen with a namespace typo.  Katz--Tao control is affine invariant,
so applying the inverse rigid affine equivalence returns control to the
identical selected source indices used by the contracted-John proxy.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7CoordinateToVerticalSelectedSubtypeKatzTaoInverseV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family6AffineKatzTaoTransportV3
open Family8Family7CoordinateToVerticalFamilyV1
open Family8Family7CoordinateToVerticalSelectedSubtypeFrostmanV3
open Family8Family7CoordinateToVerticalTubeTransportV1
open Family8NormalizedLongIntervalFrostmanInheritanceV1

noncomputable section

universe u

/-- Applying an affine equivalence and then its inverse returns the literal
convex family, with the original index type unchanged. -/
theorem affineImageFamily_symm_affineImageFamily
    {iota : Type u} (e : Space ≃ᵃ[Real] Space)
    (F : ConvexFamily iota) :
    affineImageFamily e.symm (affineImageFamily e F) = F := by
  funext i
  apply ConvexBody.ext
  change e.symm '' (e '' (F i : Set Space)) = (F i : Set Space)
  exact e.toEquiv.symm_image_image (F i : Set Space)

/-- Katz--Tao control on the coordinate image of one literal selected subtype
pulls back to the same selected indices of the original family. -/
theorem isKatzTao_activeSubtypeFamily_of_coordinateToVertical
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {C : ENNReal} (axis : Fin 3)
    (F : UniformTubeFamily radius iota) (active : Finset iota)
    (hKT : IsKatzTao C
      (activeSubtypeFamily
        (coordinateToVerticalFamily axis F).bodyFamily active)) :
    IsKatzTao C (activeSubtypeFamily F.bodyFamily active) := by
  rw [coordinateToVertical_activeSubtypeFamily_eq_affineImageFamily] at hKT
  have hback := isKatzTao_affineImageFamily
    (coordinateToVerticalRigidMotion axis).toAffineEquiv.symm
    (affineImageFamily
      (coordinateToVerticalRigidMotion axis).toAffineEquiv
      (activeSubtypeFamily F.bodyFamily active)) hKT
  rw [affineImageFamily_symm_affineImageFamily] at hback
  exact hback

#print axioms affineImageFamily_symm_affineImageFamily
#print axioms isKatzTao_activeSubtypeFamily_of_coordinateToVertical

end
end Family8Family7CoordinateToVerticalSelectedSubtypeKatzTaoInverseV2
