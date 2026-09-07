import Family8Grounding.Family8AmbientFamilyVolumeDensityV2
import Family8Grounding.Family8Family7CoordinateToVerticalSelectedSubtypeKatzTaoInverseV2
import Family8Grounding.Family8NormalizedLongIntervalFrostmanInheritanceV1

/-!
# Katz--Tao control for a coordinate graph in an arbitrary ambient body

The coordinate graph and the convex body containing it need not have the
same tube radius.  This general-ambient bridge therefore takes the two exact
volume hypotheses used by the Frostman-to-Katz--Tao conversion instead of
artificially packaging the ambient body as a tube at the graph scale.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7CoordinateGraphGeneralAmbientKatzTaoV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8AmbientFamilyVolumeDensityV2
open Family8Family7CoordinateToVerticalFamilyV1
open Family8Family7CoordinateToVerticalSelectedSubtypeKatzTaoInverseV2
open Family8NormalizedLongIntervalFrostmanInheritanceV1

noncomputable section

universe u

/-- The exact ambient-density coefficient for a coordinate graph in an
arbitrary convex ambient body. -/
def coordinateGraphGeneralAmbientKatzTaoConstant
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (axis : Fin 3) (F : UniformTubeFamily radius iota)
    (graph : Finset iota) (K : ConvexBody Space) (CF : ENNReal) : ENNReal :=
  CF * ambientFamilyVolumeDensity
    (activeSubtypeFamily
      (coordinateToVerticalFamily axis F).bodyFamily graph) K

/-- A coordinate-image Frostman graph yields Katz--Tao control on the
identical selected source subtype whenever the exact ambient body has
positive finite volume. -/
theorem sourceGraph_isKatzTao_of_coordinate_isFrostmanOn_generalAmbient
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (axis : Fin 3) (F : UniformTubeFamily radius iota)
    (graph : Finset iota) (K : ConvexBody Space) {CF : ENNReal}
    (hK0 : volume (K : Set Space) ≠ 0)
    (hKTop : volume (K : Set Space) ≠ ∞)
    (hF : IsFrostmanOn CF
      (coordinateToVerticalFamily axis F).bodyFamily graph K) :
    IsKatzTao
      (coordinateGraphGeneralAmbientKatzTaoConstant axis F graph K CF)
      (activeSubtypeFamily F.bodyFamily graph) := by
  apply isKatzTao_activeSubtypeFamily_of_coordinateToVertical axis F graph
  unfold coordinateGraphGeneralAmbientKatzTaoConstant
  exact isKatzTao_of_isFrostmanIn_familyVolumeDensity
    ((isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
      (coordinateToVerticalFamily axis F).bodyFamily graph K).1 hF)
    hK0 hKTop

/-- The general-ambient coordinate graph coefficient is finite whenever the
Frostman coefficient is finite and the ambient volume is nonzero. -/
theorem coordinateGraphGeneralAmbientKatzTaoConstant_ne_top
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (axis : Fin 3) (F : UniformTubeFamily radius iota)
    (graph : Finset iota) (K : ConvexBody Space) {CF : ENNReal}
    (hCF : CF ≠ ∞) (hK0 : volume (K : Set Space) ≠ 0) :
    coordinateGraphGeneralAmbientKatzTaoConstant
      axis F graph K CF ≠ ∞ := by
  unfold coordinateGraphGeneralAmbientKatzTaoConstant
  exact ENNReal.mul_ne_top hCF
    (ambientFamilyVolumeDensity_ne_top
      (activeSubtypeFamily
        (coordinateToVerticalFamily axis F).bodyFamily graph) K hK0)

#print axioms coordinateGraphGeneralAmbientKatzTaoConstant
#print axioms
  sourceGraph_isKatzTao_of_coordinate_isFrostmanOn_generalAmbient
#print axioms coordinateGraphGeneralAmbientKatzTaoConstant_ne_top

end
end Family8Family7CoordinateGraphGeneralAmbientKatzTaoV1
