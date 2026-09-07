import Family8Grounding.Family8StickySelectedFineAssemblyDenseProductV1
import Family8Grounding.Family8StickyFiberContractedJohnRelativePowerEndpointV1
import Family8Grounding.Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickySelectedFineRelativePowerFactorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8FrozenComparableActualAverageMassDensityV1
open Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8ContractedJohnActualTubeProxyV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8StickyFiberContractedJohnSourcePowerEndpointV1
open Family8StickyFiberContractedJohnRelativePowerEndpointV1
open Family8StickySelectedFineSubtypeScaleCoverV1
open Family8StickySelectedFineAssemblyFiberBridgeV1
open Family8StickySelectedFineAssemblyDenseProductV1
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Relative-power Frostman factor on the same assembly parent

The exact same-parent assembly product is combined with the genuine
contracted-John relative-power endpoint.  The dense-fibre step transports a
single global density budget on the literal selected refinement to the
chosen source fibre.  Consequently the only fibre-dependent scalar input
left here is the explicit base/cardinality comparison.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Native Katz--Tao nonconcentration is inherited by every literal selected
fine subtype without changing the constant. -/
theorem selectedFineFamily_isKatzTao
    (S : StickyScaleCover fine rho) (selected : Finset index)
    {C : ENNReal} (hKT : IsKatzTao C fine.bodyFamily) :
    IsKatzTao C (selectedFineFamily S selected).bodyFamily := by
  change IsKatzTao C (selectedCoarseFamily fine.bodyFamily selected)
  exact isKatzTao_selectedCoarseFamily_of_isKatzTaoOn
    (hKT.on selected)

/-- The first genuine relative-power Frostman factor and the exact assembly
product are realized on one selected parent.  The source-density premise is
global on the literal selected refinement; density selection transports it
to the endpoint fibre at no extra loss. -/
theorem exists_selectedFine_sameAssembly_relativePower_factorized
    {beta epsilon eta p a : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) (r : Real)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (toConvexFactorization S) Y r)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
    {C : ENNReal} (hKT : IsKatzTao C fine.bodyFamily)
    (hp : 0 < p) (ha : 0 < a)
    (hgap : 0 ≤ eta - (p + a))
    (hdelta0 : contractedJohnProxyRadius delta rho / 8 ≤ delta0)
    (hsmallRatio : delta / rho ≤
      contractedJohnSourcePowerEndpointThreshold a)
    (hCratio : C ≤
      (((delta : ENNReal) / (rho : ENNReal)) ^ (-p)))
    (hsource :
      (IndexedShadingRefinement.restrictTo Y S.activeFine).shading.shadingMass
        ≠ 0)
    (hselectedDensityRatio :
      (((delta : ENNReal) / (rho : ENNReal)) ^ (eta - (p + a))) ≤
        (selectedFineShading S A.refinement.indices
          A.refinement.shading).shadingDensity / 93312 / 128)
    (hbaseRatio : ∀ q : {q // q ∈
        (selectedFineScaleCover S A.refinement.indices
          (assembly_indices_subset_activeFine S Y r A)).activeCoarse},
      (3 / 64 : ENNReal) ^ (-(2 * p + a)) *
          (((delta : ENNReal) / (rho : ENNReal)) ^ (-(2 * p + a))) ≤
        ((3 / 64 : ENNReal) ^ (-eta) *
            (((delta : ENNReal) / (rho : ENNReal)) ^ (-eta))) *
          ((Fintype.card {i // i ∈
              (selectedFineScaleCover S A.refinement.indices
                (assembly_indices_subset_activeFine S Y r A)).fiber q.1} :
              ENNReal) *
            (((3 / 64 : ENNReal) ^ 2 *
                (((delta : ENNReal) / (rho : ENNReal)) ^ 2)) / 2))) :
    ∃ q : {q // q ∈
        (selectedFineScaleCover S A.refinement.indices
          (assembly_indices_subset_activeFine S Y r A)).activeCoarse},
      ∃ selected : Finset {i // i ∈
          (selectedFineScaleCover S A.refinement.indices
            (assembly_indices_subset_activeFine S Y r A)).fiber q.1},
        selected.Nonempty ∧
        (actualRefinementShading A).averageMultiplicity ≤
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
  classical
  let hselected := assembly_indices_subset_activeFine S Y r A
  let T := selectedFineScaleCover S A.refinement.indices hselected
  let Z := selectedFineShading S A.refinement.indices A.refinement.shading
  obtain ⟨q, hdensity, _hvolume, hproduct⟩ :=
    exists_selectedFine_dense_sameAssemblyFiber_product
      S Y r A hdelta hsource
  have hsourceDensityRatio :
      (((delta : ENNReal) / (rho : ENNReal)) ^ (eta - (p + a))) ≤
        (stickyFiberSourceShading T Z q.1).shadingDensity / 93312 / 128 := by
    apply hselectedDensityRatio.trans
    exact ENNReal.div_le_div_right
      (ENNReal.div_le_div_right
        (by simpa only [T, Z, hselected] using hdensity) 93312) 128
  have hKTSelected : IsKatzTao C (selectedFineFamily S
      A.refinement.indices).bodyFamily :=
    selectedFineFamily_isKatzTao S A.refinement.indices hKT
  obtain ⟨selected, hselectedNonempty, hfirst⟩ :=
    exists_stickyFiberContractedJohn_global_average_le_relativePower_frostmanRHS
      hF T Z hdelta hdeltaHalf hrho hrhoOne hdeltaRho q hKTSelected
        hp ha hgap hdelta0 hsmallRatio hCratio hsourceDensityRatio
        (by simpa only [T, hselected] using hbaseRatio q)
  refine ⟨q, selected, hselectedNonempty, hproduct.trans ?_⟩
  exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hfirst)

#print axioms selectedFineFamily_isKatzTao
#print axioms exists_selectedFine_sameAssembly_relativePower_factorized

end
end Family8StickySelectedFineRelativePowerFactorV1
