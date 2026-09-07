import Family8Grounding.Family8ActiveCoarseCanonicalFrostmanXLowerV3
import Family8Grounding.Family8FrostmanInOnUnivBridgeV2

/-!
# Canonical full active-coarse Frostman producer

This proof-valued adapter converts the existing canonical `IsFrostmanIn`
certificate to the literal `activeCoarseFamily`/`univ` form consumed by the
max-witness canonical input.  Its result type is inferred to avoid unfolding
the certificate in downstream elaboration.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ActiveCoarseCanonicalFrostmanOnUnivV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ActiveCoarseCanonicalFrostmanXLowerV3.StickyScaleCover
open Family8KatzTaoFrostmanPropertiesV1
open Family8StickyParentHullVolumeBoundV1
open Family8FrostmanInOnUnivBridgeV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option linter.defProp false

noncomputable def activeCoarseFamilyCanonicalFrostmanOnUniv
    {delta rho : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hcoarse : S.activeCoarse.Nonempty) :=
  (isFrostmanOn_univ_iff_isFrostmanIn
    S.activeCoarseFamily closedBallFourBody).2
      (activeCoarseFamily_isFrostmanIn_canonical
        D hD S hrho hrhoOne hcoarse)

#print axioms activeCoarseFamilyCanonicalFrostmanOnUniv

end
end Family8ActiveCoarseCanonicalFrostmanOnUnivV3
