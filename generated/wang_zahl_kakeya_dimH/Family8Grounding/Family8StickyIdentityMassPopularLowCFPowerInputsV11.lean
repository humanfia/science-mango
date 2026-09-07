import Family8Grounding.Family8IdentityMassPopularNoKTPowerEnvelopeV3
import Family8Grounding.Family8StickyBoundedMassPopularLowCFPowerInputsNoKTV5
import Family8Grounding.Family8StickyCardAreaSourceMassLowerV7
import Family8Grounding.Family8StickyFiberContractedJohnProxyDatumV1
import Family8Grounding.Family8StickyScaleCoverFrostmanInheritanceV1
import Mathlib.Tactic

/-!
# Identity-fibre mass-popular low-CF inputs
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyIdentityMassPopularLowCFPowerInputsV11

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8IdentityMassPopularNoKTPowerEnvelopeV3
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyBoundedMassPopularLowCFPowerInputsNoKTV5
open Family8StickyCardAreaSourceMassLowerV7
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8StickySelectedFineAssemblyFiberBridgeV1
open Family8StickySelectedFineSubtypeScaleCoverV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- For a literal singleton-fibre assembly, a source density floor and the
two reduced scalar budgets supply all four same-parent low-CF inputs. -/
theorem exists_boundedAssembly_massPopular_sameProduct_fourPowerInputs_noKT_of_density
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) (r : Real)
    (hscale : delta ≤ rho) (hcoarse : S.activeCoarse.Nonempty)
    (hM : ∀ k, k ∈ S.activeCoarse → (S.fiber k).card ≤ 1)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (boundedFiberCoarseTubePartition S hscale hcoarse 1 hM
        ).asConvexFactorization Y r)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y
        S.activeFine).shading.shadingMass ≠ 0)
    {densityFloor densityTarget baseTarget baseScale baseUnit
      proxyCardBound relativeCardBound : ENNReal}
    (hdensityFloor : densityFloor ≤
      (sourceActiveFineShading
        (toConvexFactorization S) Y).shadingDensity)
    (hdensityBudget :
      16 * (A.loss : ENNReal) *
          ((densityTarget * 93312) * 128) ≤ densityFloor)
    (hbaseBudget :
      16 * (A.loss : ENNReal) * baseTarget ≤
        baseScale * baseUnit * densityFloor)
    (hcardAndCount :
      ∀ q : {q // q ∈
          (selectedFineScaleCover S A.refinement.indices
            (assembly_indices_subset_activeFine S Y r A)).activeCoarse},
        (Fintype.card {i // i ∈
            (selectedFineScaleCover S A.refinement.indices
              (assembly_indices_subset_activeFine S Y r A)).fiber q.1} :
            ENNReal) ≤ proxyCardBound ∧
        (Fintype.card {i // i ∈
            (selectedFineScaleCover S A.refinement.indices
              (assembly_indices_subset_activeFine S Y r A)).fiber q.1} :
            ENNReal) ≤ relativeCardBound) :
    ∃ q : {q // q ∈
        (selectedFineScaleCover S A.refinement.indices
          (assembly_indices_subset_activeFine S Y r A)).activeCoarse},
      let T := selectedFineScaleCover S A.refinement.indices
        (assembly_indices_subset_activeFine S Y r A)
      let Z := selectedFineShading S A.refinement.indices
        A.refinement.shading
      (actualRefinementShading A).averageMultiplicity ≤
          4 * (A.frozenCoarse.averageMultiplicity *
            (stickyFiberSourceShading T Z q.1).averageMultiplicity) ∧
      densityTarget ≤
        (stickyFiberSourceShading T Z q.1).shadingDensity / 93312 / 128 ∧
      baseTarget ≤ baseScale *
        ((Fintype.card {i // i ∈ T.fiber q.1} : ENNReal) * baseUnit) ∧
      (Fintype.card {i // i ∈ T.fiber q.1} : ENNReal) ≤
        proxyCardBound ∧
      (Fintype.card {i // i ∈ T.fiber q.1} : ENNReal) ≤
        relativeCardBound := by
  have hsourceLower : densityFloor *
      ((S.activeCoarse.card : ENNReal) *
        ((delta : ENNReal) ^ 2 / 2)) ≤
      (sourceActiveFineShading
        (toConvexFactorization S) Y).shadingMass :=
    densityFloor_mul_activeCoarse_half_sq_le_sourceMass
      S Y hdelta hdeltaHalf hdensityFloor
  have htau0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have htauTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  obtain ⟨hdensityScalar, hbaseScalar⟩ :=
    identityCardArea_massPopular_scalar_cancellation
      htau0 htauTop hsourceLower hdensityBudget hbaseBudget
  refine
    exists_boundedAssembly_massPopular_sameProduct_fourPowerInputs_noKT
      S Y r hscale hcoarse 1 hM A hdeltaHalf hsource ?_ hbaseScalar
        hcardAndCount
  simpa only [Nat.cast_one] using hdensityScalar

#print axioms
  exists_boundedAssembly_massPopular_sameProduct_fourPowerInputs_noKT_of_density

end
end Family8StickyIdentityMassPopularLowCFPowerInputsV11
