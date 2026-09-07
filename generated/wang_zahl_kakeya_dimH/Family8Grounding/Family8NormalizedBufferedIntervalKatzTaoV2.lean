import Family8Grounding.Family8NormalizedCrossingFrozenComparableAdapterV3
import FamilyStickyGrounding.FamilyStickyAtEveryScaleCoreV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8NormalizedBufferedIntervalKatzTaoV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCrossingFrozenComparableAdapterV3

noncomputable section

/-!
# Katz--Tao data on the literal normalized buffered interval

The interval cover and the ambient multiscale cover use the same actual
`rho`-coarse family and active parent set.  We unfold the interval cover at
the test body so the identity is literal and no transport loss is introduced.
-/

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat}

theorem bufferedIntervalCover_isKatzTaoAtScale
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (m : Fin depth) (rho : NNReal)
    (hbuffered : S.IsBuffered epsilon m rho)
    {KT : ENNReal} (hKT : C.base.IsKatzTaoAtEveryScale KT) :
    (bufferedIntervalCover D hD C S epsilon hepsilon m rho
      hbuffered).IsKatzTaoAtScale KT := by
  intro K
  change concentration
    (C.base.cover rho
      ((S.delta_le_tau m).trans
        (actualDatum_tau_le_of_isBuffered
          D hD S hepsilon m rho hbuffered))
      (buffered_le_one S hepsilon m rho hbuffered)).activeCoarseFamily K <= KT
  exact hKT rho
    ((S.delta_le_tau m).trans
      (actualDatum_tau_le_of_isBuffered
        D hD S hepsilon m rho hbuffered))
    (buffered_le_one S hepsilon m rho hbuffered) K

#print axioms bufferedIntervalCover_isKatzTaoAtScale

end
end Family8NormalizedBufferedIntervalKatzTaoV2
