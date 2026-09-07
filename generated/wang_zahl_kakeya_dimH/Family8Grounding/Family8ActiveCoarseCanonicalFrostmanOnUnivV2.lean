import Family8Grounding.Family8ActiveCoarseCanonicalFrostmanXLowerV3
import Mathlib.Tactic

/-!
# Canonical active-coarse Frostman certificate on `univ`, V2

Fresh-build-safe successor of V1.  The required actual-datum and canonical
radius-four namespaces are imported explicitly.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ActiveCoarseCanonicalFrostmanOnUnivV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8ActiveCoarseCanonicalFrostmanXLowerV3
open Family8ActiveCoarseCanonicalFrostmanXLowerV3.StickyScaleCover
open Family8KatzTaoFrostmanPropertiesV1
open Family8StickyParentHullVolumeBoundV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

theorem isFrostmanOn_univ_iff_isFrostmanIn
    {index : Type*} [Fintype index] [DecidableEq index]
    {C : ENNReal} (F : ConvexFamily index) (K : ConvexBody Space) :
    IsFrostmanOn C F Finset.univ K ↔ IsFrostmanIn C F K := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      exact h.1 i (Finset.mem_univ i)
    · intro K' hK'
      simpa only [containedMassOn_univ] using h.2 K' hK'
  · intro h
    refine ⟨?_, ?_⟩
    · intro i _hi
      exact h.1 i
    · intro K' hK'
      simpa only [containedMassOn_univ] using h.2 K' hK'

theorem StickyScaleCover.activeCoarseFamily_isFrostmanOn_univ_canonical
    {delta rho : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hcoarse : S.activeCoarse.Nonempty) :
    IsFrostmanOn
      (canonicalFrostmanConstant S.activeCoarseFamily closedBallFourBody)
      S.activeCoarseFamily Finset.univ closedBallFourBody := by
  exact (isFrostmanOn_univ_iff_isFrostmanIn
    S.activeCoarseFamily closedBallFourBody).2
      (activeCoarseFamily_isFrostmanIn_canonical
        D hD S hrho hrhoOne hcoarse)

#print axioms isFrostmanOn_univ_iff_isFrostmanIn
#print axioms
  StickyScaleCover.activeCoarseFamily_isFrostmanOn_univ_canonical

end
end Family8ActiveCoarseCanonicalFrostmanOnUnivV2
