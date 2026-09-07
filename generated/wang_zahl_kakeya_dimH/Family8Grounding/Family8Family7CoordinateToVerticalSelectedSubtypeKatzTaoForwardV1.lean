import Family8Grounding.Family8Family7CoordinateToVerticalSelectedSubtypeFrostmanV3
import FamilyStickyGrounding.Family6AffineKatzTaoTransportV3

/-!
# Forward Katz--Tao transport to one vertical-coordinate subtype

The existing inverse adapter pulls a vertical-coordinate certificate back
to the original tube family.  The full-coefficient critical-scale argument
needs the forward direction: it acts on the genuinely vertical source.
Affine invariance gives that direction on the identical active subtype with
no loss.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7CoordinateToVerticalSelectedSubtypeKatzTaoForwardV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineKatzTaoTransportV3
open Family8Family7CoordinateToVerticalFamilyV1
open Family8Family7CoordinateToVerticalSelectedSubtypeFrostmanV3
open Family8Family7CoordinateToVerticalTubeTransportV1
open Family8NormalizedLongIntervalFrostmanInheritanceV1

noncomputable section

universe u

/-- Katz--Tao control on one literal active subtype is preserved by the
common rigid coordinate map that makes the source vertical. -/
theorem isKatzTao_coordinateToVertical_activeSubtypeFamily
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {C : ENNReal} (axis : Fin 3)
    (F : UniformTubeFamily radius iota) (active : Finset iota)
    (hKT : IsKatzTao C (activeSubtypeFamily F.bodyFamily active)) :
    IsKatzTao C
      (activeSubtypeFamily
        (coordinateToVerticalFamily axis F).bodyFamily active) := by
  rw [coordinateToVertical_activeSubtypeFamily_eq_affineImageFamily]
  exact isKatzTao_affineImageFamily
    (coordinateToVerticalRigidMotion axis).toAffineEquiv
    (activeSubtypeFamily F.bodyFamily active) hKT

#print axioms isKatzTao_coordinateToVertical_activeSubtypeFamily

end
end Family8Family7CoordinateToVerticalSelectedSubtypeKatzTaoForwardV1
