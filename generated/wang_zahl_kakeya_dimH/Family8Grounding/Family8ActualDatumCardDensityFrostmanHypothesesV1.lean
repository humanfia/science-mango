import Family8Grounding.Family8ActualDatumCardRetentionFrostmanV2
import Family8Grounding.Family8RestrictedActualDatumDensityRetentionV1

/-!
# Frostman hypotheses for a cardinality- and density-retained subtype

The fresh greedy producer supplies literal cardinality and density retention
for one restricted `ActualTubeDatum`.  This adapter combines those fields
with a source `IsFrostmanIn` certificate.  The only remaining inputs are the
two displayed scalar absorptions at the unchanged tube radius.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ActualDatumCardDensityFrostmanHypothesesV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ActualDatumCardRetentionFrostmanV2
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

/-- Cardinality retention transports the Frostman certificate, density
retention transports the lower density bound, and the two explicit scalar
comparisons turn them into the exact `FrostmanHypotheses` required by the
paper-level property. -/
theorem restrictActualTubeDatum_frostmanHypotheses_of_card_density_retention
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (selected : Finset iota)
    {C L : ENNReal} {eta : Real}
    (hF : IsFrostmanIn C D.family.bodyFamily unitBallBody)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hcard : (Fintype.card iota : ENNReal) ≤
      L * (selected.card : ENNReal))
    (hdensityBudget : (delta : ENNReal) ^ eta ≤
      D.shading.shadingDensity / L)
    (hdensityRetention : D.shading.shadingDensity / L ≤
      (restrictActualTubeDatum D selected).shading.shadingDensity)
    (hconstantBudget : C * (16 * L) ≤
      (delta : ENNReal) ^ (-eta)) :
    FrostmanHypotheses (restrictActualTubeDatum D selected) eta := by
  have hselectedDensity : (delta : ENNReal) ^ eta ≤
      (restrictActualTubeDatum D selected).shading.shadingDensity :=
    hdensityBudget.trans hdensityRetention
  have hselectedFrostman0 : IsFrostmanIn (C * (16 * L))
      (restrictActualTubeDatum D selected).family.bodyFamily
      unitBallBody :=
    restrictActualTubeDatum_isFrostmanIn_of_card_retention
      D selected unitBallBody hF hdeltaHalf hcard
  have hselectedFrostman : IsFrostmanIn
      ((delta : ENNReal) ^ (-eta))
      (restrictActualTubeDatum D selected).family.bodyFamily
      unitBallBody :=
    hselectedFrostman0.mono hconstantBudget
  exact ⟨hselectedDensity, hselectedFrostman⟩

#print axioms
  restrictActualTubeDatum_frostmanHypotheses_of_card_density_retention

end
end Family8ActualDatumCardDensityFrostmanHypothesesV1
