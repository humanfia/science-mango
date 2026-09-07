import Family8Grounding.Family8CoarseTubePartitionExactUniformStickyFiberV8
import Family8Grounding.Family8StickyFiberContractedJohnRelativePowerEndpointV1
import Mathlib.Tactic

/-!
# Contracted-John control of the exact Joint source fine level

The exact assembly's honest `sourceFineLevelShading` is fed directly to the
literal Sticky-fibre contracted-John endpoint through the exact partition
adapter.  Exact uniformity rewrites the subtype fibre cardinality to
`P.branching`; the resulting average is rewritten back to the same source
fine-level shading.  No final Prop. 6.6 inner bound is assumed here.

V1 is a failed namespace draft and is not imported.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8JointExactUniformSourceFineContractedJohnV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8ContractedJohnActualTubeProxyV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8StickyFiberContractedJohnSourcePowerEndpointV1
open Family8StickyFiberContractedJohnRelativePowerEndpointV1
open Family8CoarseTubePartitionExactUniformStickyFiberV4
open Family8CoarseTubePartitionExactUniformStickyFiberV8
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

variable {delta rho : NNReal} {iota : Type} {coarseCard : Nat}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho (Fin coarseCard)}

/-- The actual source fine-level statistic of an exact-uniform Joint
partition satisfies the genuine contracted-John relative-power Frostman
endpoint.  The base budget is stated with the exact common count
`P.branching`, not a separate fibre-card callback. -/
theorem exists_exactUniform_sourceFineLevel_average_le_relativePower_frostmanRHS
    {beta epsilon eta p absorb : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {loss : Nat}
    (A : ExactAssembly P.asConvexFactorization Y loss)
    (hloss : P.branchingLoss = 1)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
    (k : {k // k ∈ P.coarseIndices})
    {C : ENNReal} (hKT : IsKatzTao C fine.bodyFamily)
    (hp : 0 < p) (habsorb : 0 < absorb)
    (hgap : 0 ≤ eta - (p + absorb))
    (hdelta0 : contractedJohnProxyRadius delta rho / 8 ≤ delta0)
    (hsmallRatio : delta / rho ≤
      contractedJohnSourcePowerEndpointThreshold absorb)
    (hCratio : C ≤
      (((delta : ENNReal) / (rho : ENNReal)) ^ (-p)))
    (hsourceDensityRatio :
      (((delta : ENNReal) / (rho : ENNReal)) ^
          (eta - (p + absorb))) ≤
        (stickyFiberSourceShading (exactPartitionStickyCover P)
          (sourceFineLevelShading A k.1) k.1).shadingDensity / 93312 / 128)
    (hbaseRatio :
      (3 / 64 : ENNReal) ^ (-(2 * p + absorb)) *
          (((delta : ENNReal) / (rho : ENNReal)) ^
            (-(2 * p + absorb))) ≤
        ((3 / 64 : ENNReal) ^ (-eta) *
            (((delta : ENNReal) / (rho : ENNReal)) ^ (-eta))) *
          ((P.branching : ENNReal) *
            (((3 / 64 : ENNReal) ^ 2 *
                (((delta : ENNReal) / (rho : ENNReal)) ^ 2)) / 2))) :
    ∃ selected : Finset
        {i // i ∈ (exactPartitionStickyCover P).fiber k.1},
      selected.Nonempty ∧
      (sourceFineLevelShading A k.1).averageMultiplicity ≤
        stickyFiberContractedJohnSourceClosedLoss C *
          frostmanMultiplicityRHS
            (contractedJohnProxyRadius delta rho / 8)
            (restrictActualTubeDatum
              (eighthNormalizedDatum
                (stickyFiberContractedJohnProxyDatum
                  (exactPartitionStickyCover P)
                  (sourceFineLevelShading A k.1)
                  hrho hrhoOne k)) selected).actualFamilyVolume
            epsilon beta := by
  have hbaseRatio' :
      (3 / 64 : ENNReal) ^ (-(2 * p + absorb)) *
          (((delta : ENNReal) / (rho : ENNReal)) ^
            (-(2 * p + absorb))) ≤
        ((3 / 64 : ENNReal) ^ (-eta) *
            (((delta : ENNReal) / (rho : ENNReal)) ^ (-eta))) *
          ((Fintype.card
              {i // i ∈ (exactPartitionStickyCover P).fiber k.1} : ENNReal) *
            (((3 / 64 : ENNReal) ^ 2 *
                (((delta : ENNReal) / (rho : ENNReal)) ^ 2)) / 2)) := by
    rw [exactPartitionStickyCover_fiber_fintypeCard_eq_branching
      P hloss k.1 k.2]
    exact hbaseRatio
  obtain ⟨selected, hselected, hbound⟩ :=
    exists_stickyFiberContractedJohn_global_average_le_relativePower_frostmanRHS
      hF (exactPartitionStickyCover P) (sourceFineLevelShading A k.1)
        hdelta hdeltaHalf hrho hrhoOne hdeltaRho k hKT hp habsorb hgap
        hdelta0 hsmallRatio hCratio hsourceDensityRatio hbaseRatio'
  refine ⟨selected, hselected, ?_⟩
  rw [stickyFiber_exactPartition_sourceFineLevel_averageMultiplicity_eq
    P Y A k.1] at hbound
  exact hbound

#print axioms
  exists_exactUniform_sourceFineLevel_average_le_relativePower_frostmanRHS

end
end Family8JointExactUniformSourceFineContractedJohnV2
