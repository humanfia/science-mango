import FamilyStickyCinematicL32PyzActualUnitBallVerticalCoefficientCeilingV1
import FamilyStickyCinematicL32FiniteNormCriticalBallV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32PyzActualUnitBallVerticalNormRetentionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32PyzActualUnitBallVerticalCoefficientCeilingV1

noncomputable section

/-!
# Automatic norm critical-scale retention in the fixed vertical chart

For actual unit-ball tubes in the selected vertical chart, the comparison
ceiling is the fixed paper-uniform constant `16`.  Thus the finite norm
maximizer retains the exact weighted cardinality without a free `hfull`
input or a family-dependent maximum.
-/

theorem ambientCriticalFamily_weighted_card_retention_sixteen
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (ambient active : Finset iota)
    (hfamily : (actualProjectedAmbientCriticalFamily fine ambient active).Nonempty)
    (hunit : ∀ i, i ∈ ambient →
      (fine.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (hvertical : ∀ i, i ∈ ambient →
      (1 / 2 : Real) ≤ |(fine.tubes i).axis.direction 2|)
    (hradius : 0 < radius) (hradiusSixteen : (radius : Real) ≤ 16)
    (exponent : Real) (hexponent : 0 ≤ exponent)
    (testCenter : Tube radius)
    (htestCenter : testCenter ∈
      actualProjectedAmbientCriticalFamily fine ambient active) :
    let family := actualProjectedAmbientCriticalFamily fine ambient active
    (family.card : Real) * (16 : Real) ^ (-exponent) ≤
      ((finiteNormCriticalBall family projectedTubePairCoefficientDistance
        (radius : Real) 16 exponent hfamily).card : Real) *
      (finiteCriticalMaximizerScale family
        projectedTubePairCoefficientDistance (radius : Real) 16 exponent
        hfamily) ^ (-exponent) := by
  dsimp only
  apply finiteNormCriticalBall_weighted_card_retention
    (actualProjectedAmbientCriticalFamily fine ambient active)
    projectedTubePairCoefficientDistance hfamily (testCenter := testCenter)
  · intro center _hcenter
    rw [projectedTubePairCoefficientDistance_self]
    exact_mod_cast hradius.le
  · exact_mod_cast hradius
  · exact hradiusSixteen
  · exact hexponent
  · exact htestCenter
  · exact ambientCriticalFamily_full_coefficientCeiling_sixteen
      fine ambient active hunit hvertical testCenter htestCenter

end
end FamilyStickyCinematicL32PyzActualUnitBallVerticalNormRetentionV1
