import Family8Grounding.Family8FiniteRandomRigidMotionB2NormalizedDatumV1
import Family8Grounding.Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3
import Family8Grounding.Family8StickyActiveCoarseB2SupportV5

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set
open scoped NNReal

namespace Family8IdentifiedDividingWitnessTauActiveCoarseB2NormalizationV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3

noncomputable section

/-!
# Honest B2 support and eighth-normalization for the identified tau datum

The active `tau_m` parents are automatically supported in `B(0,2)` at
`tau_m <= 1/16`.  Eighth-normalization therefore supplies the unit-ball
containment field without any parent-support callback.  Pairwise essential
distinctness is deliberately not asserted: extending the shrunken axes is a
separate selection problem.
-/

namespace Witness

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}

/-- The literal eighth-normalization of the active `tau_m` coarse datum. -/
def eighthNormalizedTauActiveCoarseDatum
    (D : ActualTubeDatum delta iota)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness D.family C N epsilon eta S) :
    ActualTubeDatum (S.tau W.m / 8)
      {k // k ∈
        (Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness.tauScaleCover
          D C S W).activeCoarse} :=
  eighthNormalizedDatum
    (Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness.tauActiveCoarseDatum
      D C S W)

/-- The raw active parent datum has honest radius-two support. -/
theorem tauActiveCoarseDatum_carrier_subset_closedBall_two
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness D.family C N epsilon eta S)
    (htauSixteenth : S.tau W.m <= (1 / 16 : NNReal)) :
    forall k,
      ((Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness.tauActiveCoarseDatum
          D C S W).family.tubes k).carrier ⊆
        Metric.closedBall (0 : Space) 2 := by
  intro k
  simpa only [
      Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness.tauActiveCoarseDatum_family_tubes,
      StickyScaleCover.activeCoarseFamily,
      UniformTubeFamily.bodyFamily_apply,
      Tube.coe_body] using
    (Family8StickyActiveCoarseB2SupportV5.activeCoarseFamily_body_subset_closedBall_two
      D hD
      (Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness.tauScaleCover
        D C S W)
      htauSixteenth k)

/-- Eighth-normalization turns the automatic radius-two support into the
unit-ball containment field required downstream. -/
theorem eighthNormalizedTauActiveCoarseDatum_contained_in_unit_ball
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness D.family C N epsilon eta S)
    (htauSixteenth : S.tau W.m <= (1 / 16 : NNReal)) :
    forall k,
      ((eighthNormalizedTauActiveCoarseDatum D C S W).family.tubes k).carrier ⊆
        Metric.closedBall (0 : Space) 1 := by
  have htauHalf : S.tau W.m <= (2 : NNReal)⁻¹ :=
    htauSixteenth.trans (by
      simpa only [one_div] using
        (inv_anti₀ (show (0 : NNReal) < 2 by norm_num)
          (show (2 : NNReal) <= 16 by norm_num)))
  exact eighthNormalizedDatum_contained_in_unit_ball
    (Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness.tauActiveCoarseDatum
      D C S W)
    htauHalf
    (tauActiveCoarseDatum_carrier_subset_closedBall_two
      D hD C S W htauSixteenth)

/-- Average multiplicity is unchanged exactly by this normalization. -/
theorem eighthNormalizedTauActiveCoarseDatum_averageMultiplicity
    (D : ActualTubeDatum delta iota)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness D.family C N epsilon eta S) :
    (eighthNormalizedTauActiveCoarseDatum D C S W).shading.averageMultiplicity =
      (Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness.tauActiveCoarseDatum
        D C S W).shading.averageMultiplicity :=
  eighthNormalizedDatum_averageMultiplicity _

#print axioms eighthNormalizedTauActiveCoarseDatum
#print axioms tauActiveCoarseDatum_carrier_subset_closedBall_two
#print axioms eighthNormalizedTauActiveCoarseDatum_contained_in_unit_ball
#print axioms eighthNormalizedTauActiveCoarseDatum_averageMultiplicity

end Witness

end
end Family8IdentifiedDividingWitnessTauActiveCoarseB2NormalizationV4
