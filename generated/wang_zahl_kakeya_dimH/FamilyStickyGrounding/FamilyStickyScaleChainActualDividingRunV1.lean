import FamilyStickyGrounding.FamilyStickyScaleChainFiniteDeltaMaxBridgeV1
import FamilyStickyGrounding.FamilyStickyScaleChainActualValuesV1

set_option autoImplicit false

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainActualDividingRunV1

open Submission.Kakeya.ConvexFactoring
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyDividingScalesChainAtEveryAdapterV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainBufferedHierarchyProducerV1.MultiscaleTubeHierarchy
open FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy
open FamilyStickyScaleChainFiniteDeltaMaxBridgeV1.MultiscaleTubeHierarchy.BufferedTestBodyChain

noncomputable section

/-!
# Sticky Kakeya: actual buffered chains in the dividing-scales run

Each terminal interval may carry its own buffered tube hierarchy and honest
test-body chain.  Their normalized telescopes produce the literal finite
`Delta_max` chains used by the frozen Katz--Tao dividing-scales adapter.
Adjacent and middle values come from `ActualIntervalCovers`, so no opaque
scalar-valued slots remain.
-/

/-- A finite family of honest buffered chains, one for every terminal scale
interval. -/
structure BufferedChainFamily (outerDepth chainDepth : Nat) where
  nominalRadius : Fin outerDepth -> Nat -> NNReal
  card : Fin outerDepth -> Nat -> Nat
  hierarchy : (m : Fin outerDepth) ->
    MultiscaleTubeHierarchy chainDepth (nominalRadius m)
      (fun l => Fin (card m l))
  datum : (m : Fin outerDepth) ->
    FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy.BufferedTestBodyChain
      (hierarchy m)

namespace BufferedChainFamily

variable {outerDepth chainDepth : Nat}

/-- The actual finite Delta-max chain on terminal interval `m`. -/
def finiteChain (B : BufferedChainFamily outerDepth chainDepth)
    (m : Fin outerDepth) : FiniteDeltaMaxChain chainDepth :=
  FamilyStickyScaleChainFiniteDeltaMaxBridgeV1.MultiscaleTubeHierarchy.BufferedTestBodyChain.toFiniteDeltaMaxChain
    (B.datum m)

/-- The global value in the generated chain is the literal bottom
concentration of the buffered hierarchy. -/
@[simp] theorem finiteChain_deltaMax
    (B : BufferedChainFamily outerDepth chainDepth)
    (m : Fin outerDepth) (l : Nat) :
    (B.finiteChain m).deltaMax l =
      Submission.Kakeya.ConvexGeometry.concentration
        (effectiveActiveFamily (B.hierarchy m) l)
        ((B.datum m).testBody l) := by
  rfl

/-- Actual local-factor and endpoint budgets generate all finite-chain
product budgets at once. -/
theorem productBudget_of_actual
    (B : BufferedChainFamily outerDepth chainDepth)
    (target : Fin outerDepth -> ENNReal)
    (hbudget : forall m,
      (∏ l ∈ Finset.range chainDepth,
        FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy.BufferedTestBodyChain.localFactor
          (B.hierarchy m) (B.datum m) l) *
        ((MeasureTheory.volume ((B.datum m).testBody chainDepth : Set
            LeanEval.Analysis.WangZahlKakeya.Space) /
          MeasureTheory.volume ((B.datum m).testBody 0 : Set
            LeanEval.Analysis.WangZahlKakeya.Space)) *
          ((B.datum m).tubeVolume 0 /
            (B.datum m).tubeVolume chainDepth)) <= target m) :
    forall m,
      (B.finiteChain m).dimensionalLoss ^ chainDepth *
          (∏ l ∈ Finset.range chainDepth,
            (B.finiteChain m).localDeltaMax l) <= target m := by
  intro m
  exact productBudget_of_local_endpoint_le (B.datum m) (target m)
    (hbudget m)

end BufferedChainFamily

variable {delta : NNReal} {outerDepth chainDepth N : Nat}
  {epsilon : Real} {eta : Nat -> Real}
  {S : FiniteScaleSequence delta outerDepth}

/-- End-to-end producer for the chain-backed Katz--Tao no-split run.  Every
scalar in the output is tied either to an honest buffered hierarchy or to an
actual interval cover. -/
def toActualKatzTaoChainNoSplitRun
    (A : ActualIntervalCovers S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (eta_monotone : Monotone eta)
    (eta_stage_le_epsilon : eta stage <= epsilon)
    (actualProductBudget : forall m,
      (∏ l ∈ Finset.range chainDepth,
        FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy.BufferedTestBodyChain.localFactor
          (B.hierarchy m) (B.datum m) l) *
        ((MeasureTheory.volume ((B.datum m).testBody chainDepth : Set
            LeanEval.Analysis.WangZahlKakeya.Space) /
          MeasureTheory.volume ((B.datum m).testBody 0 : Set
            LeanEval.Analysis.WangZahlKakeya.Space)) *
          ((B.datum m).tubeVolume 0 /
            (B.datum m).tubeVolume chainDepth)) <=
        (S.theta m : ENNReal) ^ (-eta (stage - 1)))
    (adjacent_upper : forall m,
      A.adjacentCoarseValue m <=
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (stage - 1)))
    (terminal_noSplit : forall m, ¬ S.IsLarge epsilon m ->
      ¬ (exists rho, S.IsBuffered epsilon m rho ∧
        A.coarseValueAt m rho <
          (((S.theta m / rho : NNReal) : ENNReal) ^ eta stage))) :
    KatzTaoChainNoSplitRun delta outerDepth chainDepth N epsilon eta S :=
  A.toKatzTaoChainNoSplitRun stage stage_pos stage_le eta_monotone
    eta_stage_le_epsilon B.finiteChain
    (B.productBudget_of_actual
      (fun m => (S.theta m : ENNReal) ^ (-eta (stage - 1)))
      actualProductBudget)
    adjacent_upper terminal_noSplit

/-- The actual buffered/interval data therefore yields the frozen all-large
versus dividing-witness dichotomy. -/
theorem allLarge_or_witness
    (A : ActualIntervalCovers S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (eta_monotone : Monotone eta)
    (eta_stage_le_epsilon : eta stage <= epsilon)
    (actualProductBudget : forall m,
      (∏ l ∈ Finset.range chainDepth,
        FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy.BufferedTestBodyChain.localFactor
          (B.hierarchy m) (B.datum m) l) *
        ((MeasureTheory.volume ((B.datum m).testBody chainDepth : Set
            LeanEval.Analysis.WangZahlKakeya.Space) /
          MeasureTheory.volume ((B.datum m).testBody 0 : Set
            LeanEval.Analysis.WangZahlKakeya.Space)) *
          ((B.datum m).tubeVolume 0 /
            (B.datum m).tubeVolume chainDepth)) <=
        (S.theta m : ENNReal) ^ (-eta (stage - 1)))
    (adjacent_upper : forall m,
      A.adjacentCoarseValue m <=
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (stage - 1)))
    (terminal_noSplit : forall m, ¬ S.IsLarge epsilon m ->
      ¬ (exists rho, S.IsBuffered epsilon m rho ∧
        A.coarseValueAt m rho <
          (((S.theta m / rho : NNReal) : ENNReal) ^ eta stage))) :
    S.AllStepsLarge epsilon ∨
      Nonempty (KatzTaoDividingWitness delta N epsilon eta) := by
  exact (toActualKatzTaoChainNoSplitRun A B stage stage_pos stage_le
    eta_monotone eta_stage_le_epsilon actualProductBudget adjacent_upper
    terminal_noSplit).allLarge_or_witness

#print axioms BufferedChainFamily.finiteChain
#print axioms BufferedChainFamily.finiteChain_deltaMax
#print axioms BufferedChainFamily.productBudget_of_actual
#print axioms toActualKatzTaoChainNoSplitRun
#print axioms allLarge_or_witness

end
end FamilyStickyScaleChainActualDividingRunV1
