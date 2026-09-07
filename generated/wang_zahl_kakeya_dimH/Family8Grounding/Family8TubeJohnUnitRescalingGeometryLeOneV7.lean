import Family8Grounding.Family8TubeJohnAxisWitnessLeOneV6

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal InnerProductSpace

namespace Family8TubeJohnUnitRescalingGeometryLeOneV7

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8TubeJohnUnitRescalingV2
open Family8TubeJohnOuterEllipsoidUnitBallV3

noncomputable section

/-!
# John unit rescaling throughout the complete Definition 2.12 scale window

The assumptions `0 < rho` and `rho <= 1` are exactly the geometric window
used here.  No John-existence or image-normalization callback remains.
-/

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The explicit V6 John witness chosen for one active parent tube. -/
noncomputable def StickyScaleCover.tubeJohnWitnessLeOne
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (k : {k // k ∈ S.activeCoarse}) :
    JohnAxisWitness (S.coarse.tubes k.1).body :=
  Classical.choice
    (Family8TubeJohnAxisWitnessLeOneV6.Tube.johnAxisWitness_of_pos_le_one
      (S.coarse.tubes k.1) hrho hrhoOne)

/-- Every semiaxis of the full-window chosen witness is positive. -/
theorem StickyScaleCover.tubeJohnWitnessLeOne_radius_pos
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (k : {k // k ∈ S.activeCoarse})
    (i : Fin 3) :
    0 < (StickyScaleCover.tubeJohnWitnessLeOne S hrho hrhoOne k).radius i :=
  Family8TubeJohnWitnessPositiveRadiiV4.JohnAxisWitness.radius_pos_of_tube
    (S.coarse.tubes k.1) hrho
    (StickyScaleCover.tubeJohnWitnessLeOne S hrho hrhoOne k) i

/-- A positive-radius sticky scale cover at any radius at most one carries
the genuine John normalization geometry required by Definition 2.12. -/
noncomputable def StickyScaleCover.tubeJohnUnitRescalingGeometry_of_le_one
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) :
    ScaleCover.UnitRescalingGeometry S where
  johnWitness := fun k =>
    StickyScaleCover.tubeJohnWitnessLeOne S hrho hrhoOne k
  unitRescaling := fun k =>
    axisEllipsoidNormalizationAffineEquiv
      (StickyScaleCover.tubeJohnWitnessLeOne S hrho hrhoOne k).center
      (StickyScaleCover.tubeJohnWitnessLeOne S hrho hrhoOne k).frame
      (StickyScaleCover.tubeJohnWitnessLeOne S hrho hrhoOne k).radius
      (StickyScaleCover.tubeJohnWitnessLeOne_radius_pos S hrho hrhoOne k)
  johnOuter_image_eq_unitBall := by
    intro k
    exact image_axisEllipsoid_three_eq_closedBall
      (StickyScaleCover.tubeJohnWitnessLeOne S hrho hrhoOne k).center
      (StickyScaleCover.tubeJohnWitnessLeOne S hrho hrhoOne k).frame
      (StickyScaleCover.tubeJohnWitnessLeOne S hrho hrhoOne k).radius
      (StickyScaleCover.tubeJohnWitnessLeOne_radius_pos S hrho hrhoOne k)

#print axioms StickyScaleCover.tubeJohnWitnessLeOne_radius_pos
#print axioms StickyScaleCover.tubeJohnUnitRescalingGeometry_of_le_one

end
end Family8TubeJohnUnitRescalingGeometryLeOneV7
