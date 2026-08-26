import FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
import FamilyStickyCinematicL32FiniteMetricMaximalCoverV1

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41SeparatedCoefficientBallPairV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1

noncomputable section

/-!
# Cross-separation of two finite metric balls

The unreduced PYZ Proposition 4.1 asks only for separation between its white
and black families.  Once those families have been selected inside two
coefficient balls, this module supplies that geometric step directly from
the distance between the two centres.  It makes no claim that the two rich
balls, or their required tangency multiplicities, already exist.
-/

variable {alpha : Type*}

/-- Two finite families are cross-separated when every point of the first is
separated from every point of the second.  No within-family separation is
required. -/
def FiniteFamiliesCrossSeparated
    (distance : alpha -> alpha -> Real) (separation : Real)
    (white black : Finset alpha) : Prop :=
  forall w, w ∈ white -> forall b, b ∈ black ->
    separation <= distance w b

/-- Subfamilies of two radius-`r` balls are cross-separated at scale `s`
whenever the two centres are at least `s + 2r` apart. -/
theorem finiteFamilyMetricBalls_crossSeparated
    (family : Finset alpha) (distance : alpha -> alpha -> Real)
    (hsymm : forall x y, distance x y = distance y x)
    (htriangle : forall x center y,
      distance x y <= distance x center + distance center y)
    {ballRadius separation : Real} {whiteCenter blackCenter : alpha}
    (hcenters : separation + 2 * ballRadius <=
      distance whiteCenter blackCenter) :
    FiniteFamiliesCrossSeparated distance separation
      (finiteFamilyMetricBall family distance ballRadius whiteCenter)
      (finiteFamilyMetricBall family distance ballRadius blackCenter) := by
  intro w hw b hb
  have hwRadius : distance w whiteCenter <= ballRadius :=
    (Finset.mem_filter.mp hw).2
  have hbRadius : distance b blackCenter <= ballRadius :=
    (Finset.mem_filter.mp hb).2
  have hwhiteToW : distance whiteCenter w <= ballRadius := by
    rw [hsymm whiteCenter w]
    exact hwRadius
  have hwhiteBlack : distance whiteCenter blackCenter <=
      distance whiteCenter w +
        (distance w b + distance b blackCenter) := by
    calc
      distance whiteCenter blackCenter <=
          distance whiteCenter w + distance w blackCenter :=
        htriangle whiteCenter w blackCenter
      _ <= distance whiteCenter w +
          (distance w b + distance b blackCenter) := by
        gcongr
        exact htriangle w b blackCenter
  linarith

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-- Literal projected-coefficient specialization for actual tubes. -/
theorem projectedTubeCoefficientBalls_crossSeparated
    {radius : NNReal} (curves : Finset (Tube radius))
    {ballRadius separation : Real}
    {whiteCenter blackCenter : Tube radius}
    (hcenters : separation + 2 * ballRadius <=
      projectedTubePairCoefficientDistance whiteCenter blackCenter) :
    FiniteFamiliesCrossSeparated projectedTubePairCoefficientDistance
      separation
      (finiteFamilyMetricBall curves projectedTubePairCoefficientDistance
        ballRadius whiteCenter)
      (finiteFamilyMetricBall curves projectedTubePairCoefficientDistance
        ballRadius blackCenter) := by
  apply finiteFamilyMetricBalls_crossSeparated curves
    projectedTubePairCoefficientDistance
    projectedTubePairCoefficientDistance_comm
  · intro T center U
    exact projectedTubePairCoefficientDistance_triangle T center U
  · exact hcenters

/-- The constants used in the paper's separated-ball selection leave the
stronger margin `8r` between any white and black members. -/
theorem projectedTubeCoefficientBalls_crossSeparated_of_ten_mul
    {radius : NNReal} (curves : Finset (Tube radius))
    {ballRadius : Real}
    {whiteCenter blackCenter : Tube radius}
    (hcenters : 10 * ballRadius <=
      projectedTubePairCoefficientDistance whiteCenter blackCenter) :
    FiniteFamiliesCrossSeparated projectedTubePairCoefficientDistance
      (8 * ballRadius)
      (finiteFamilyMetricBall curves projectedTubePairCoefficientDistance
        ballRadius whiteCenter)
      (finiteFamilyMetricBall curves projectedTubePairCoefficientDistance
        ballRadius blackCenter) := by
  apply projectedTubeCoefficientBalls_crossSeparated curves
  nlinarith [hcenters]

#print axioms FiniteFamiliesCrossSeparated
#print axioms finiteFamilyMetricBalls_crossSeparated
#print axioms projectedTubeCoefficientBalls_crossSeparated
#print axioms projectedTubeCoefficientBalls_crossSeparated_of_ten_mul

end

end FamilyStickyCinematicL32Prop41SeparatedCoefficientBallPairV1
