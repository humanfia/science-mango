import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import Submission.Kakeya.ConvexFactoring.CoarseTubePartition
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FrozenCoarseSameDataMassTransportV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Submission.Kakeya.Uniformity
open Family8FrozenNeighborhoodAssemblyV1
open Family8FrozenComparableActualAverageMassDensityV1

noncomputable section

/-!
# Same-data mass transport into a frozen coarse shading

The frozen comparable assembly stores the coarse shading selected before its
final spatial restriction; it is deliberately not defined by recomputing the
induced shading of the final refinement.  Nevertheless, `Assembly.covers`
and the genuine branching bound in a `CoarseTubePartition` give the exact
one-sided mass transport needed downstream.  This file proves that transport
on the literal same assembly.  No density, mass-retention, or target estimate
is supplied by a caller.
-/

variable {delta rho : NNReal} {iota kappa : Type*}
  [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho kappa}

namespace Assembly

variable {P : CoarseTubePartition fine coarse}
  {Y : Shading fine.bodyFamily} {r : Real}

/-- Every final fine fibre is covered by its literal frozen parent, so the
final refinement mass is at most the actual upper branching factor times the
frozen coarse mass. -/
theorem actualRefinementShading_mass_le_branching_mul_frozenCoarse
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      P.asConvexFactorization Y r) :
    (Family8FrozenComparableActualAverageMassDensityV1.Assembly.actualRefinementShading
        A).shadingMass <=
      ((P.branchingLoss * P.branching : Nat) : ENNReal) *
        A.frozenCoarse.shadingMass := by
  rw [Family8FrozenComparableActualAverageMassDensityV1.Assembly.actualRefinementShading_shadingMass]
  rw [refinement_shadingMass_eq_sum_fiberShadingMass
    P.asConvexFactorization A.refinement A.indices_subset_fine]
  calc
    (∑ k ∈ P.index.coarse,
        fiberShadingMass P.asConvexFactorization A.refinement.shading k) <=
        ∑ k ∈ P.index.coarse,
          ((P.branchingLoss * P.branching : Nat) : ENNReal) *
            volume (A.frozenCoarse.carrier k) := by
      apply Finset.sum_le_sum
      intro k hk
      unfold fiberShadingMass
      calc
        (∑ i ∈ P.index.fiber k,
            volume (A.refinement.shading.carrier i)) <=
            ∑ _i ∈ P.index.fiber k,
              volume (A.frozenCoarse.carrier k) := by
          apply Finset.sum_le_sum
          intro i hi
          apply measure_mono
          intro x hx
          have hparent : P.index.parent i = k :=
            (P.index.mem_fiber i k).1 hi |>.2
          simpa only [CoarseTubePartition.asConvexFactorization, hparent] using
            A.covers i x hx
        _ = ((P.index.fiber k).card : ENNReal) *
            volume (A.frozenCoarse.carrier k) := by simp
        _ <= ((P.branchingLoss * P.branching : Nat) : ENNReal) *
            volume (A.frozenCoarse.carrier k) := by
          apply mul_le_mul' _ le_rfl
          exact_mod_cast P.fiber_card_le_loss_mul_branching k hk
    _ = ((P.branchingLoss * P.branching : Nat) : ENNReal) *
        (∑ k ∈ P.index.coarse,
          volume (A.frozenCoarse.carrier k)) := by
      rw [Finset.mul_sum]
    _ <= ((P.branchingLoss * P.branching : Nat) : ENNReal) *
        A.frozenCoarse.shadingMass := by
      apply mul_le_mul' le_rfl
      unfold Shading.shadingMass
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- The automatic dyadic retention and the actual partition branching bound
combine into a source-to-frozen mass comparison on the same assembly. -/
theorem sourceActiveFineShading_mass_le_loss_mul_branching_mul_frozenCoarse
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      P.asConvexFactorization Y r) :
    (Family8FrozenComparableActualAverageMassDensityV1.Assembly.sourceActiveFineShading
        P.asConvexFactorization Y).shadingMass <=
      ((A.loss : ENNReal) *
          ((P.branchingLoss * P.branching : Nat) : ENNReal)) *
        A.frozenCoarse.shadingMass := by
  calc
    (Family8FrozenComparableActualAverageMassDensityV1.Assembly.sourceActiveFineShading
        P.asConvexFactorization Y).shadingMass <=
        (A.loss : ENNReal) *
          (Family8FrozenComparableActualAverageMassDensityV1.Assembly.actualRefinementShading
            A).shadingMass :=
      Family8FrozenComparableActualAverageMassDensityV1.Assembly.sourceActiveFineShading_mass_le_loss_mul_actualRefinementShading
        A
    _ <= (A.loss : ENNReal) *
        (((P.branchingLoss * P.branching : Nat) : ENNReal) *
          A.frozenCoarse.shadingMass) :=
      mul_le_mul' le_rfl
        (actualRefinementShading_mass_le_branching_mul_frozenCoarse A)
    _ = ((A.loss : ENNReal) *
          ((P.branchingLoss * P.branching : Nat) : ENNReal)) *
        A.frozenCoarse.shadingMass := by ac_rfl

/-- Division-free density transport on the literal source and frozen coarse
families.  The remaining downstream task is purely quantitative: lower-bound
the left-hand density-volume product and upper-bound the displayed finite
loss times the coarse family volume. -/
theorem sourceDensity_mul_sourceVolume_le_loss_mul_branching_mul_frozenDensityVolume
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      P.asConvexFactorization Y r) :
    (Family8FrozenComparableActualAverageMassDensityV1.Assembly.sourceActiveFineShading
        P.asConvexFactorization Y).shadingDensity *
        familyVolume
          (Family8FrozenComparableActualAverageMassDensityV1.Assembly.sourceActiveFineFamily
            P.asConvexFactorization) <=
      ((A.loss : ENNReal) *
          ((P.branchingLoss * P.branching : Nat) : ENNReal)) *
        (A.frozenCoarse.shadingDensity * familyVolume coarse.bodyFamily) := by
  rw [shadingDensity_mul_familyVolume, shadingDensity_mul_familyVolume]
  exact sourceActiveFineShading_mass_le_loss_mul_branching_mul_frozenCoarse A

#print axioms actualRefinementShading_mass_le_branching_mul_frozenCoarse
#print axioms
  sourceActiveFineShading_mass_le_loss_mul_branching_mul_frozenCoarse
#print axioms
  sourceDensity_mul_sourceVolume_le_loss_mul_branching_mul_frozenDensityVolume

end Assembly
end
end Family8FrozenCoarseSameDataMassTransportV3
