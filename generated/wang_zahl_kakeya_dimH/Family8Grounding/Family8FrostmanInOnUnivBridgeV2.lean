import Submission.Kakeya.ConvexFactoring.ActiveNonConcentration

/-!
# Full-family Frostman certificates as active-univ certificates

The full-family and active-family definitions differ only by
`containedMassOn F univ = containedMass F`.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8FrostmanInOnUnivBridgeV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

theorem isFrostmanOn_univ_iff_isFrostmanIn
    {index : Type*} [Fintype index] [DecidableEq index]
    {C : ENNReal} (F : ConvexFamily index) (K : ConvexBody Space) :
    IsFrostmanOn C F Finset.univ K ↔ IsFrostmanIn C F K := by
  constructor
  · intro h
    refine ⟨fun i ↦ h.1 i (Finset.mem_univ i), ?_⟩
    intro K' hK'
    simpa only [containedMassOn_univ] using h.2 K' hK'
  · intro h
    refine ⟨fun i _hi ↦ h.1 i, ?_⟩
    intro K' hK'
    simpa only [containedMassOn_univ] using h.2 K' hK'

#print axioms isFrostmanOn_univ_iff_isFrostmanIn

end Family8FrostmanInOnUnivBridgeV2
