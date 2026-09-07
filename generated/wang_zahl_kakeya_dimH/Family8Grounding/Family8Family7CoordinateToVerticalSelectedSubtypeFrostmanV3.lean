import Family8Grounding.Family8Family7CoordinateToVerticalSelectedSubtypeDensityV3
import Family8Grounding.Family8GeneralizedFrostmanMultiplicityV1
import Family8Grounding.Family8NormalizedLongIntervalFrostmanInheritanceV1
import Family8Grounding.Family8SelectedOccurrenceMaxOwnerHullCommonScaleDatumV1
import Family8Grounding.Family8SelectedParentAffineShadingTransportV4
import FamilyStickyGrounding.Family6AffineConvexVolumeCoreV1

/-!
# Frostman transport for a selected subtype under the vertical coordinate map, V3

V1 imported a failed density draft.  V2 repaired that dependency but omitted
the namespaces containing the memberwise affine image and rigid-motion
carrier lemmas.  This clean successor declares every direct dependency while
keeping the same literal subtype and exact Frostman transport statement.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7CoordinateToVerticalSelectedSubtypeFrostmanV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8Family7CoordinateToVerticalFamilyV1
open Family8Family7CoordinateToVerticalTubeTransportV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8SelectedOccurrenceMaxOwnerHullCommonScaleDatumV1
open Family8SelectedParentAffineShadingTransportV4

noncomputable section

universe u

/-- The selected coordinate-image tube family is literally the affine image
of the selected original tube family. -/
theorem coordinateToVertical_activeSubtypeFamily_eq_affineImageFamily
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (axis : Fin 3) (F : UniformTubeFamily radius iota)
    (active : Finset iota) :
    activeSubtypeFamily
        (coordinateToVerticalFamily axis F).bodyFamily active =
      affineImageFamily
        (coordinateToVerticalRigidMotion axis).toAffineEquiv
        (activeSubtypeFamily F.bodyFamily active) := by
  funext i
  apply ConvexBody.ext
  simp only [activeSubtypeFamily, affineImageFamily,
    coe_affineImageConvexBody, UniformTubeFamily.bodyFamily_apply,
    Tube.coe_body, coordinateToVerticalFamily_tubes, rigidTube_carrier]
  rfl

/-- `IsFrostmanOn` is unchanged when one literal active subtype and its
ambient body are moved by the same vertical-coordinate rigid motion. -/
theorem IsFrostmanOn.coordinateToVertical
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {C : ENNReal} (axis : Fin 3)
    (F : UniformTubeFamily radius iota) (active : Finset iota)
    (K : ConvexBody Space)
    (hF : IsFrostmanOn C F.bodyFamily active K) :
    IsFrostmanOn C
      (coordinateToVerticalFamily axis F).bodyFamily active
      (affineImageConvexBody
        (coordinateToVerticalRigidMotion axis).toAffineEquiv K) := by
  apply (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
    (coordinateToVerticalFamily axis F).bodyFamily active
    (affineImageConvexBody
      (coordinateToVerticalRigidMotion axis).toAffineEquiv K)).2
  rw [coordinateToVertical_activeSubtypeFamily_eq_affineImageFamily]
  exact IsFrostmanIn.affineImage
    (coordinateToVerticalRigidMotion axis).toAffineEquiv
    ((isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
      F.bodyFamily active K).1 hF)

#print axioms coordinateToVertical_activeSubtypeFamily_eq_affineImageFamily
#print axioms IsFrostmanOn.coordinateToVertical

end
end Family8Family7CoordinateToVerticalSelectedSubtypeFrostmanV3
