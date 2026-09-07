import Family8Grounding.Family8TubeJohnWitnessPositiveRadiiV4

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal InnerProductSpace

namespace Family8TubeJohnUnitRescalingGeometryV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8TubeJohnAxisWitnessV1
open Family8TubeJohnUnitRescalingV2
open Family8TubeJohnOuterEllipsoidUnitBallV3
open Family8TubeJohnWitnessPositiveRadiiV4

noncomputable section

/-!
# Automatic John unit-rescaling geometry for a positive tube cover

For each occupied coarse tube, choose the explicit John witness from V1.
V4 makes positivity of every chosen semiaxis intrinsic, V2 supplies the
diagonal affine equivalence, and V3 supplies its exact outer-ellipsoid image.
-/

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- A canonical chosen John witness for one active parent tube. -/
noncomputable def StickyScaleCover.tubeJohnWitness
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (k : {k // k ∈ S.activeCoarse}) :
    JohnAxisWitness (S.coarse.tubes k.1).body :=
  Classical.choice
    (Family8TubeJohnAxisWitnessV1.Tube.johnAxisWitness_of_pos_le_half
      (S.coarse.tubes k.1) hrho hrhoHalf)

/-- Every semiaxis of the chosen active-parent witness is positive. -/
theorem StickyScaleCover.tubeJohnWitness_radius_pos
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (k : {k // k ∈ S.activeCoarse}) (i : Fin 3) :
    0 < (StickyScaleCover.tubeJohnWitness S hrho hrhoHalf k).radius i :=
  JohnAxisWitness.radius_pos_of_tube
    (S.coarse.tubes k.1) hrho (StickyScaleCover.tubeJohnWitness S hrho hrhoHalf k) i

/-- Every positive-radius sticky scale cover with radius at most `1/2`
automatically carries the genuine Definition 2.12 John unit-rescaling data. -/
noncomputable def StickyScaleCover.tubeJohnUnitRescalingGeometry
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹) :
    ScaleCover.UnitRescalingGeometry S where
  johnWitness := fun k => StickyScaleCover.tubeJohnWitness S hrho hrhoHalf k
  unitRescaling := fun k =>
    axisEllipsoidNormalizationAffineEquiv
      (StickyScaleCover.tubeJohnWitness S hrho hrhoHalf k).center
      (StickyScaleCover.tubeJohnWitness S hrho hrhoHalf k).frame
      (StickyScaleCover.tubeJohnWitness S hrho hrhoHalf k).radius
      (StickyScaleCover.tubeJohnWitness_radius_pos S hrho hrhoHalf k)
  johnOuter_image_eq_unitBall := by
    intro k
    exact image_axisEllipsoid_three_eq_closedBall
      (StickyScaleCover.tubeJohnWitness S hrho hrhoHalf k).center
      (StickyScaleCover.tubeJohnWitness S hrho hrhoHalf k).frame
      (StickyScaleCover.tubeJohnWitness S hrho hrhoHalf k).radius
      (StickyScaleCover.tubeJohnWitness_radius_pos S hrho hrhoHalf k)

#print axioms StickyScaleCover.tubeJohnWitness_radius_pos
#print axioms StickyScaleCover.tubeJohnUnitRescalingGeometry

end
end Family8TubeJohnUnitRescalingGeometryV5
