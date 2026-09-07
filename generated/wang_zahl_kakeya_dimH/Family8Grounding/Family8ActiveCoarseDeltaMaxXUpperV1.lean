import Family8Grounding.Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4
import FamilyStickyGrounding.FamilyStickyDeltaMaxFiniteChainV2

/-!
# The genuine coarse-Delta-max upper bound for X

For any literal sticky scale cover, the paper quantity
`X = rho^2 * |active coarse|` is controlled by the actual maximal
concentration of that same active coarse family.  This is only an upper
bound for a supplied cover; it does not construct the required nonidentity
maximal-density cover.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8ActiveCoarseDeltaMaxXUpperV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4.StickyScaleCover

noncomputable section

/-- Literal paper-shaped upper bound, up to the fixed dimensional constant
already present in the tube-volume implementation. -/
theorem activeCoarseCardScaleMass_le_1024_mul_coarseDeltaMax
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹) :
    (activeCoarseCardScaleMass S : ENNReal) <=
      1024 * coarseDeltaMax S := by
  apply activeCoarseCardScaleMass_le_1024_mul_of_isKatzTaoAtScale
    D hD S hrhoHalf
  exact (isKatzTaoAtScale_iff_coarseDeltaMax_le S
    (coarseDeltaMax S)).2 le_rfl

#print axioms activeCoarseCardScaleMass_le_1024_mul_coarseDeltaMax

end
end Family8ActiveCoarseDeltaMaxXUpperV1
