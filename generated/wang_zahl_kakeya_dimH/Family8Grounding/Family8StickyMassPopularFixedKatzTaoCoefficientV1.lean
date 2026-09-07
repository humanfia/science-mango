import Family8Grounding.Family8LocalFiberCapRelativeSquareCancellationV1
import Family8Grounding.Family8StickyMassPopularRelativeScaleCoefficientV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyMassPopularFixedKatzTaoCoefficientV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8ContractedJohnActualTubeProxyV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8StickyFiberContractedJohnSourcePowerEndpointV1
open Family8StickySelectedFineSubtypeScaleCoverV1
open Family8StickySelectedFineAssemblyFiberBridgeV1
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyBoundedMassPopularRelativePowerFactorV1
open Family8StickyMassPopularRelativeScaleCoefficientV1
open Family8LocalFiberCapRelativeSquareCancellationV1
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Fixed Katz--Tao envelope for the mass-popular density coefficient

The local doubled-fibre cap is never estimated separately.  Its full
`(delta/rho)^{-2}` incidence scale cancels against the exact parent-card
factor `(delta/rho)^2`, leaving only the fixed constant `960000 * C`.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- A generic coefficient lemma: any cap which cancels against the relative
square may be inserted after the exact active-parent mass identity. -/
theorem densityCoefficient_le_of_fiberCap_relativeSquare
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (M A_loss : Nat) (lossBound XUpper capBound : ENNReal)
    (hloss : (A_loss : ENNReal) <= lossBound)
    (hX : (activeCoarseCardScaleMass S : ENNReal) <= XUpper)
    (hcap : (M : ENNReal) *
      (((delta : ENNReal) / (rho : ENNReal)) ^ 2) <= capBound) :
    (((A_loss : ENNReal) * (S.activeCoarse.card : ENNReal)) *
        ((M : ENNReal) * (8 * (delta : ENNReal) ^ 2))) <=
      lossBound * (8 * (XUpper * capBound)) := by
  have hidentity :=
    activeCoarse_card_mul_delta_sq_eq_cardScaleMass_mul_ratio_sq S hrho
  calc
    (((A_loss : ENNReal) * (S.activeCoarse.card : ENNReal)) *
        ((M : ENNReal) * (8 * (delta : ENNReal) ^ 2))) =
      (A_loss : ENNReal) *
        (8 * (((S.activeCoarse.card : ENNReal) *
          (delta : ENNReal) ^ 2) * (M : ENNReal))) := by ring
    _ = (A_loss : ENNReal) *
        (8 * (((activeCoarseCardScaleMass S : ENNReal) *
          (((delta : ENNReal) / (rho : ENNReal)) ^ 2)) *
          (M : ENNReal))) := by rw [hidentity]
    _ = (A_loss : ENNReal) *
        (8 * ((activeCoarseCardScaleMass S : ENNReal) *
          ((M : ENNReal) *
            (((delta : ENNReal) / (rho : ENNReal)) ^ 2)))) := by ring
    _ <= lossBound * (8 * (XUpper * capBound)) := by
      exact mul_le_mul' hloss
        (mul_le_mul' le_rfl (mul_le_mul' hX hcap))

/-- Specialization to the actual Katz--Tao doubled-fibre natural cap.  The
right side contains no local scale and no local multiplicity. -/
theorem densityCoefficient_le_fixedKatzTaoEnvelope
    (S : StickyScaleCover fine rho)
    (hdelta : 0 < delta) (hdeltaRho : delta <= rho)
    {C : ENNReal} (hCone : 1 <= C) (hCfinite : C ≠ ∞)
    (A_loss : Nat) (lossBound XUpper : ENNReal)
    (hloss : (A_loss : ENNReal) <= lossBound)
    (hX : (activeCoarseCardScaleMass S : ENNReal) <= XUpper) :
    (((A_loss : ENNReal) * (S.activeCoarse.card : ENNReal)) *
        ((katzTaoDoubledFiberNatCap delta rho C : ENNReal) *
          (8 * (delta : ENNReal) ^ 2))) <=
      lossBound *
        (8 * (XUpper * (ordinaryFiberNatCapFixedConstant * C))) := by
  apply densityCoefficient_le_of_fiberCap_relativeSquare
    S (hdelta.trans_le hdeltaRho) (katzTaoDoubledFiberNatCap delta rho C)
      A_loss lossBound XUpper (ordinaryFiberNatCapFixedConstant * C)
      hloss hX
  exact katzTaoDoubledFiberNatCap_mul_relativeSquare_le_fixed
    hdelta hdeltaRho hCone hCfinite

/-- First-factor wrapper with the sharp local Katz--Tao cancellation already
performed.  The density budget no longer mentions the local cap `M`; the
base budget retains the genuine relative square but has no cap at all. -/
theorem exists_boundedAssembly_massPopular_relativePower_factorized_of_fixedKatzTaoEnvelope
    {beta epsilon eta p a : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) (r : Real)
    (hscale : delta <= rho) (hcoarse : S.activeCoarse.Nonempty)
    {C : ENNReal}
    (hM : forall k, k ∈ S.activeCoarse ->
      (S.fiber k).card <= katzTaoDoubledFiberNatCap delta rho C)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (boundedFiberCoarseTubePartition S hscale hcoarse
        (katzTaoDoubledFiberNatCap delta rho C) hM
        ).asConvexFactorization Y r)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hdeltaRho : delta <= rho)
    (hKT : IsKatzTao C fine.bodyFamily)
    (hCone : 1 <= C) (hCfinite : C ≠ ∞)
    (hp : 0 < p) (ha : 0 < a)
    (hgap : 0 <= eta - (p + a))
    (hdelta0 : contractedJohnProxyRadius delta rho / 8 <= delta0)
    (hsmallRatio : delta / rho <=
      contractedJohnSourcePowerEndpointThreshold a)
    (hCratio : C <=
      (((delta : ENNReal) / (rho : ENNReal)) ^ (-p)))
    (hsource :
      (IndexedShadingRefinement.restrictTo Y S.activeFine).shading.shadingMass
        ≠ 0)
    {lossBound XUpper : ENNReal}
    (hloss : (A.loss : ENNReal) <= lossBound)
    (hX : (activeCoarseCardScaleMass S : ENNReal) <= XUpper)
    (hdensityEnvelope :
      (lossBound *
          (8 * (XUpper *
            (ordinaryFiberNatCapFixedConstant * C)))) *
        (((((delta : ENNReal) / (rho : ENNReal)) ^
            (eta - (p + a))) * 93312) * 128) <=
      (sourceActiveFineShading (toConvexFactorization S) Y).shadingMass)
    (hbaseEnvelope :
      (lossBound *
          (8 * (XUpper *
            (((delta : ENNReal) / (rho : ENNReal)) ^ 2)))) *
        ((3 / 64 : ENNReal) ^ (-(2 * p + a)) *
          (((delta : ENNReal) / (rho : ENNReal)) ^ (-(2 * p + a)))) <=
      (((3 / 64 : ENNReal) ^ (-eta) *
          (((delta : ENNReal) / (rho : ENNReal)) ^ (-eta)) *
        (((3 / 64 : ENNReal) ^ 2 *
          (((delta : ENNReal) / (rho : ENNReal)) ^ 2)) / 2)) *
        (sourceActiveFineShading (toConvexFactorization S) Y).shadingMass)) :
    exists q : {q // q ∈
        (selectedFineScaleCover S A.refinement.indices
          (assembly_indices_subset_activeFine S Y r A)).activeCoarse},
      exists selected : Finset {i // i ∈
          (selectedFineScaleCover S A.refinement.indices
            (assembly_indices_subset_activeFine S Y r A)).fiber q.1},
        selected.Nonempty ∧
        (actualRefinementShading A).averageMultiplicity <=
          4 * (A.frozenCoarse.averageMultiplicity *
            (stickyFiberContractedJohnSourceClosedLoss C *
              frostmanMultiplicityRHS
                (contractedJohnProxyRadius delta rho / 8)
                (restrictActualTubeDatum
                  (eighthNormalizedDatum
                    (stickyFiberContractedJohnProxyDatum
                      (selectedFineScaleCover S A.refinement.indices
                        (assembly_indices_subset_activeFine S Y r A))
                      (selectedFineShading S A.refinement.indices
                        A.refinement.shading)
                      hrho hrhoOne q)) selected).actualFamilyVolume
                epsilon beta)) := by
  have hdensityCoefficient := densityCoefficient_le_fixedKatzTaoEnvelope
    S hdelta hdeltaRho hCone hCfinite A.loss lossBound XUpper hloss hX
  have hbaseCoefficient := baseCoefficient_le_relativeScaleEnvelope
    S hrho lossBound XUpper A.loss hloss hX
  apply exists_boundedAssembly_massPopular_relativePower_factorized
    hF S Y r hscale hcoarse (katzTaoDoubledFiberNatCap delta rho C) hM A
      hdelta hdeltaHalf hrho hrhoOne hdeltaRho hKT hp ha hgap hdelta0
      hsmallRatio hCratio hsource
  · exact (mul_le_mul' hdensityCoefficient le_rfl).trans hdensityEnvelope
  · exact (mul_le_mul' hbaseCoefficient le_rfl).trans hbaseEnvelope

#print axioms densityCoefficient_le_of_fiberCap_relativeSquare
#print axioms densityCoefficient_le_fixedKatzTaoEnvelope
#print axioms
  exists_boundedAssembly_massPopular_relativePower_factorized_of_fixedKatzTaoEnvelope

end
end Family8StickyMassPopularFixedKatzTaoCoefficientV1
