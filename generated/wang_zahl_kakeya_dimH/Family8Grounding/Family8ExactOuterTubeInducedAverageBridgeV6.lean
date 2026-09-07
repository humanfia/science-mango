import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import Family8Grounding.Family8TubeInducedAverageMultiplicityLowerV4
import Submission.Kakeya.ConvexFactoring.CoarseTubePartition
import Mathlib.Tactic

/-!
# Exact outer average versus the recomputed tube neighborhood, V6

V1--V4 are frozen drafts and V5 is the safe radius-matched form.  This clean
generalization observes that the factor-432 argument uses the assembly's
exact outer/refinement fields but not its auxiliary real radius.  The
recomputed neighborhood still has the literal coarse tube radius `rho`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ExactOuterTubeInducedAverageBridgeV6

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ComparableMultiplicityBucketsV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8TubeInducedAverageMultiplicityLowerV4

noncomputable section

variable {delta rho : NNReal} {iota kappa : Type*}
  [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho kappa}

/-- The factor-432 exact-outer comparison is independent of the assembly's
auxiliary real neighborhood parameter. -/
theorem frozenCoarse_averageMultiplicity_le_432_mul_neighborhood
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {r : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      P.asConvexFactorization Y r)
    (hrho : 0 < rho)
    (hmass : A.refinement.shading.shadingMass ≠ 0)
    (hfrozen : A.frozenCoarse =
      P.asConvexFactorization.inducedShading A.refinement.shading) :
    A.frozenCoarse.averageMultiplicity <=
      432 *
        (P.asConvexFactorization.neighborhoodInducedShading
          A.refinement.shading (rho : Real)).averageMultiplicity := by
  let m := comparableBase A.outerLabel
  have hactive : A.refinement.shading.shadedUnion ⊆
      P.asConvexFactorization.activeFineShadedUnion
        A.refinement.shading := by
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    have hi : i ∈ A.refinement.indices := by
      by_contra hni
      rw [A.refinement.carrier_eq_empty_of_not_mem i hni] at hxi
      exact hxi
    exact Set.mem_iUnion.mpr
      ⟨⟨i, A.indices_subset_fine hi⟩, hxi⟩
  have houter : ∀ x ∈ A.refinement.shading.shadedUnion,
      m <= P.asConvexFactorization.outerMultiplicity
        A.refinement.shading x := by
    intro x hx
    have hxfrozen : x ∈ A.frozenCoarse.shadedUnion :=
      A.shadedUnion_subset_frozenCoarse hx
    calc
      m <= A.frozenCoarse.pointMultiplicity x :=
        frozenCoarse_pointMultiplicity_lower A x hxfrozen
      _ = (P.asConvexFactorization.inducedShading
          A.refinement.shading).pointMultiplicity x := by
        rw [← hfrozen]
      _ = P.asConvexFactorization.outerMultiplicity
          A.refinement.shading x :=
        P.asConvexFactorization.pointMultiplicity_inducedShading_eq_outer
          A.refinement.shading x
  have hmNeighborhood : (m : ENNReal) <=
      216 *
        (P.asConvexFactorization.neighborhoodInducedShading
          A.refinement.shading (rho : Real)).averageMultiplicity :=
    natCast_le_twoHundredSixteen_mul_inducedAverage
      P.asConvexFactorization A.refinement.shading m hrho
      hmass hactive houter
  calc
    A.frozenCoarse.averageMultiplicity <=
        ((2 * m : Nat) : ENNReal) :=
      frozenCoarse_averageMultiplicity_upper A
    _ = 2 * (m : ENNReal) := by
      push_cast
      rfl
    _ <= 2 *
        (216 *
          (P.asConvexFactorization.neighborhoodInducedShading
            A.refinement.shading (rho : Real)).averageMultiplicity) :=
      mul_le_mul' le_rfl hmNeighborhood
    _ = 432 *
        (P.asConvexFactorization.neighborhoodInducedShading
          A.refinement.shading (rho : Real)).averageMultiplicity := by
      ring

#print axioms frozenCoarse_averageMultiplicity_le_432_mul_neighborhood

end
end Family8ExactOuterTubeInducedAverageBridgeV6
