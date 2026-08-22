import FamilyStickyGrounding.FamilyStickyDividingScalesNoSplitV2

set_option autoImplicit false

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyDividingScalesChainAtEveryAdapterV1

open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyDividingScalesNoSplitV2
open Submission.Kakeya.Uniformity

noncomputable section

/-!
# Sticky dividing scales: finite-chain and at-every-scale adapters

This module connects the pure no-split stopping skeleton to the two frozen
Sticky APIs already available in the workspace:

* the global Katz--Tao value is produced from an actual
  `FiniteDeltaMaxChain` and its product budget;
* an all-large terminal chain is converted to the literal
  `StickyMultiscaleCover` predicates from pointwise scale bounds.

No geometric interpolation, adjacent-scale comparison, or random-motion
claim is introduced here.
-/

namespace StickyMultiscaleCover

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- Pointwise actual Frostman bounds are exactly the producer needed by the
at-every-scale Frostman API. -/
theorem isFrostmanAtEveryScale_of_atScale
    (M : StickyMultiscaleCover fine) (error : ENNReal)
    (hscale : forall rho (hdelta : delta <= rho) (hrho : rho <= 1),
      (M.cover rho hdelta hrho).IsFrostmanAtScale error) :
    M.IsFrostmanAtEveryScale error := by
  exact hscale

/-- Pointwise bounds on the actual coarse `Delta_max` produce the literal
Katz--Tao-at-every-scale statement. -/
theorem isKatzTaoAtEveryScale_of_coarseDeltaMax_le
    (M : StickyMultiscaleCover fine) (error : ENNReal)
    (hscale : forall rho (hdelta : delta <= rho) (hrho : rho <= 1),
      FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover.coarseDeltaMax
        (M.cover rho hdelta hrho) <= error) :
    M.IsKatzTaoAtEveryScale error := by
  intro rho hdelta hrho
  exact (FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover.isKatzTaoAtScale_iff_coarseDeltaMax_le
      (M.cover rho hdelta hrho) error).2
      (hscale rho hdelta hrho)

end StickyMultiscaleCover

namespace FrostmanNoSplitRun

variable {delta : NNReal} {depth N : Nat} {epsilon : Real}
  {eta : Nat -> Real} {S : FiniteScaleSequence delta depth}

/-- Composable all-large adapter whose residual input is pointwise in the
actual covers, rather than an opaque at-every-scale callback. -/
theorem frostmanAtEveryScale_or_witness_of_allLargeAtScale
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (M : StickyMultiscaleCover fine) (error : ENNReal)
    (R : FrostmanNoSplitRun delta depth N epsilon eta S)
    (hscale : S.AllStepsLarge epsilon ->
      forall rho (hdelta : delta <= rho) (hrho : rho <= 1),
        (M.cover rho hdelta hrho).IsFrostmanAtScale error) :
    M.IsFrostmanAtEveryScale error ∨
      Nonempty (FrostmanDividingWitness delta N epsilon eta) := by
  exact R.frostmanAtEveryScale_or_witness M error fun hlarge =>
    StickyMultiscaleCover.isFrostmanAtEveryScale_of_atScale M error (hscale hlarge)

end FrostmanNoSplitRun

/-- Katz--Tao no-split data in which every global value is the bottom value
of an actual frozen finite `Delta_max` chain.  The displayed product budget,
not a separately supplied global upper inequality, produces the source
global exponent bound. -/
structure KatzTaoChainNoSplitRun
    (delta : NNReal) (depth chainDepth N : Nat) (epsilon : Real)
    (eta : Nat -> Real)
    (S : FiniteScaleSequence delta depth) where
  stage : Nat
  stage_pos : 1 <= stage
  stage_le : stage <= N
  eta_monotone : Monotone eta
  eta_stage_le_epsilon : eta stage <= epsilon
  chain : Fin depth -> FiniteDeltaMaxChain chainDepth
  productBudget : forall m,
    (chain m).dimensionalLoss ^ chainDepth *
          (∏ k ∈ Finset.range chainDepth, (chain m).localDeltaMax k) <=
      (S.theta m : ENNReal) ^ (-eta (stage - 1))
  adjacentValue : Fin depth -> ENNReal
  middleValue : Fin depth -> NNReal -> ENNReal
  adjacent_upper : forall m,
    adjacentValue m <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (stage - 1))
  terminal_noSplit : forall m, ¬ S.IsLarge epsilon m ->
    ¬ exists rho, S.IsBuffered epsilon m rho ∧
      middleValue m rho <
        (((S.theta m / rho : NNReal) : ENNReal) ^ eta stage)

namespace KatzTaoChainNoSplitRun

variable {delta : NNReal} {depth chainDepth N : Nat} {epsilon : Real}
  {eta : Nat -> Real} {S : FiniteScaleSequence delta depth}

/-- The frozen finite-chain theorem automatically discharges every global
upper field of the generic no-split run. -/
def toNoSplitRun
    (R : KatzTaoChainNoSplitRun delta depth chainDepth N epsilon eta S) :
    KatzTaoNoSplitRun delta depth N epsilon eta S where
  stage := R.stage
  stage_pos := R.stage_pos
  stage_le := R.stage_le
  eta_monotone := R.eta_monotone
  eta_stage_le_epsilon := R.eta_stage_le_epsilon
  globalValue := fun m => (R.chain m).deltaMax 0
  adjacentValue := R.adjacentValue
  middleValue := R.middleValue
  global_upper := by
    intro m
    exact FamilyStickyDividingScalesFiniteStoppingV1.FiniteDeltaMaxChain.global_le_exponent_of_productBudget
        (R.chain m) (S.theta m) (eta (R.stage - 1))
        (R.productBudget m)
  adjacent_upper := R.adjacent_upper
  terminal_noSplit := R.terminal_noSplit

/-- Delta-max-chain-backed Part (B) dividing-scales dichotomy. -/
theorem allLarge_or_witness
    (R : KatzTaoChainNoSplitRun delta depth chainDepth N epsilon eta S) :
    S.AllStepsLarge epsilon ∨
      Nonempty (KatzTaoDividingWitness delta N epsilon eta) :=
  R.toNoSplitRun.allLarge_or_witness

/-- End-to-end thin combinatorial adapter.  The only residual input is the
actual pointwise coarse `Delta_max` interpolation for an all-large chain. -/
theorem katzTaoAtEveryScale_or_witness_of_allLargeCoarseDeltaMax
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (M : StickyMultiscaleCover fine) (error : ENNReal)
    (R : KatzTaoChainNoSplitRun delta depth chainDepth N epsilon eta S)
    (hscale : S.AllStepsLarge epsilon ->
      forall rho (hdelta : delta <= rho) (hrho : rho <= 1),
        FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover.coarseDeltaMax
        (M.cover rho hdelta hrho) <= error) :
    M.IsKatzTaoAtEveryScale error ∨
      Nonempty (KatzTaoDividingWitness delta N epsilon eta) := by
  exact R.toNoSplitRun.katzTaoAtEveryScale_or_witness M error fun hlarge =>
    StickyMultiscaleCover.isKatzTaoAtEveryScale_of_coarseDeltaMax_le M error (hscale hlarge)

end KatzTaoChainNoSplitRun

#print axioms StickyMultiscaleCover.isFrostmanAtEveryScale_of_atScale
#print axioms StickyMultiscaleCover.isKatzTaoAtEveryScale_of_coarseDeltaMax_le
#print axioms FrostmanNoSplitRun.frostmanAtEveryScale_or_witness_of_allLargeAtScale
#print axioms KatzTaoChainNoSplitRun.allLarge_or_witness
#print axioms KatzTaoChainNoSplitRun.katzTaoAtEveryScale_or_witness_of_allLargeCoarseDeltaMax

end

end FamilyStickyDividingScalesChainAtEveryAdapterV1
