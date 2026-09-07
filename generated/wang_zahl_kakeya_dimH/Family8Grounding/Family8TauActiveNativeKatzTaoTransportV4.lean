import Family8Grounding.Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8TauActiveNativeKatzTaoTransportV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness

noncomputable section

/-!
# Native Katz--Tao control on the literal tau-active datum

The datum is the restriction of the tau cover's coarse family to its active
indices. The cover predicate uses quotient concentration, whereas native
`IsKatzTao` is cross-multiplied; the standard equivalence and the literal
pointwise family identity provide the exact transport.

V1--V3 are failed unfolding/predicate/namespace drafts and are not imported.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}

theorem tauActiveCoarseDatum_isKatzTao_of_tauScaleCover
    (D : ActualTubeDatum delta index)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti N epsilon eta Sseq)
    {CKT : ENNReal}
    (hKT : (tauScaleCover D Cmulti Sseq W).IsKatzTaoAtScale CKT) :
    IsKatzTao CKT
      (tauActiveCoarseDatum D Cmulti Sseq W).family.bodyFamily := by
  have hfamily :
      (tauActiveCoarseDatum D Cmulti Sseq W).family.bodyFamily =
        (tauScaleCover D Cmulti Sseq W).activeCoarseFamily := by
    funext k
    rfl
  apply isKatzTao_iff_concentration_le.mpr
  intro K
  rw [hfamily]
  exact hKT K

#print axioms tauActiveCoarseDatum_isKatzTao_of_tauScaleCover

end Witness
end
end Family8TauActiveNativeKatzTaoTransportV4
