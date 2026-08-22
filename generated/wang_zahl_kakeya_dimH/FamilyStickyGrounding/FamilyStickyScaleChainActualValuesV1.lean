import FamilyStickyGrounding.FamilyStickyScaleChainNormalizedIntegrationV1

set_option autoImplicit false

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainActualValuesV1

open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyDividingScalesNoSplitV2
open FamilyStickyDividingScalesChainAtEveryAdapterV1
open Submission.Kakeya.Uniformity

noncomputable section

/-!
# Sticky Kakeya: actual values for finite scale intervals

This module removes the abstract `adjacentValue` and `middleValue` slots from
the dividing-scales interface.  It totalizes the genuine fiber and coarse
`Delta_max` values of a `StickyMultiscaleCover`, then packages one such cover
on every finite interval `[tau_m, theta_m]`.

The defaults outside the legal scale interval are only there to give a total
function on `NNReal`; the evaluation lemmas show that every in-range value is
definitionally the actual supplied cover.  No adjacent cross estimate or
all-large interpolation theorem is assumed here.
-/

namespace StickyMultiscaleCover

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The genuine worst fiber concentration at scale `rho`, totalized by zero
outside the interval on which the multiscale cover is supplied. -/
def actualFiberDeltaMaxAt (M : StickyMultiscaleCover fine)
    (rho : NNReal) : ENNReal :=
  if hdelta : delta <= rho then
    if hrho : rho <= 1 then
      StickyScaleCover.fiberDeltaMax (M.cover rho hdelta hrho)
    else 0
  else 0

/-- The genuine coarse-family concentration at scale `rho`, totalized by
zero outside the legal scale interval. -/
def actualCoarseDeltaMaxAt (M : StickyMultiscaleCover fine)
    (rho : NNReal) : ENNReal :=
  if hdelta : delta <= rho then
    if hrho : rho <= 1 then
      StickyScaleCover.coarseDeltaMax (M.cover rho hdelta hrho)
    else 0
  else 0

@[simp] theorem actualFiberDeltaMaxAt_eq
    (M : StickyMultiscaleCover fine) (rho : NNReal)
    (hdelta : delta <= rho) (hrho : rho <= 1) :
    actualFiberDeltaMaxAt M rho =
      StickyScaleCover.fiberDeltaMax (M.cover rho hdelta hrho) := by
  simp [actualFiberDeltaMaxAt, hdelta, hrho]

@[simp] theorem actualCoarseDeltaMaxAt_eq
    (M : StickyMultiscaleCover fine) (rho : NNReal)
    (hdelta : delta <= rho) (hrho : rho <= 1) :
    actualCoarseDeltaMaxAt M rho =
      StickyScaleCover.coarseDeltaMax (M.cover rho hdelta hrho) := by
  simp [actualCoarseDeltaMaxAt, hdelta, hrho]

/-- An all-scale upper bound on the totalized actual coarse values is exactly
the pointwise producer needed by the frozen Katz--Tao-at-every-scale API. -/
theorem isKatzTaoAtEveryScale_iff_actualCoarseDeltaMaxAt_le
    (M : StickyMultiscaleCover fine) (error : ENNReal) :
    M.IsKatzTaoAtEveryScale error <->
      forall rho (_hdelta : delta <= rho) (_hrho : rho <= 1),
        actualCoarseDeltaMaxAt M rho <= error := by
  constructor
  · intro h rho hdelta hrho
    rw [actualCoarseDeltaMaxAt_eq M rho hdelta hrho]
    exact (StickyScaleCover.isKatzTaoAtScale_iff_coarseDeltaMax_le
      (M.cover rho hdelta hrho) error).1 (h rho hdelta hrho)
  · intro h rho hdelta hrho
    apply (StickyScaleCover.isKatzTaoAtScale_iff_coarseDeltaMax_le
      (M.cover rho hdelta hrho) error).2
    have hactual := h rho hdelta hrho
    rw [actualCoarseDeltaMaxAt_eq M rho hdelta hrho] at hactual
    exact hactual

end StickyMultiscaleCover

/-- Actual multiscale data on every terminal interval.  The fine family on
interval `m` has radius `tau_m`; its supplied covers therefore define honest
values at `theta_m` and at every intermediate legal scale. -/
structure ActualIntervalCovers
    {delta : NNReal} {depth : Nat}
    (S : FiniteScaleSequence delta depth) where
  fineCard : Fin depth -> Nat
  fine : (m : Fin depth) ->
    UniformTubeFamily (S.tau m) (Fin (fineCard m))
  multiscale : (m : Fin depth) -> StickyMultiscaleCover (fine m)

namespace ActualIntervalCovers

variable {delta : NNReal} {depth : Nat}
  {S : FiniteScaleSequence delta depth}

/-- Actual fiber `Delta_max` on interval `m` at scale `rho`. -/
def fiberValueAt (A : ActualIntervalCovers S)
    (m : Fin depth) (rho : NNReal) : ENNReal :=
  StickyMultiscaleCover.actualFiberDeltaMaxAt (A.multiscale m) rho

/-- Actual coarse `Delta_max` on interval `m` at scale `rho`. -/
def coarseValueAt (A : ActualIntervalCovers S)
    (m : Fin depth) (rho : NNReal) : ENNReal :=
  StickyMultiscaleCover.actualCoarseDeltaMaxAt (A.multiscale m) rho

/-- The actual adjacent Frostman value, evaluated at the upper endpoint. -/
def adjacentFiberValue (A : ActualIntervalCovers S)
    (m : Fin depth) : ENNReal :=
  A.fiberValueAt m (S.theta m)

/-- The actual adjacent Katz--Tao value, evaluated at the upper endpoint. -/
def adjacentCoarseValue (A : ActualIntervalCovers S)
    (m : Fin depth) : ENNReal :=
  A.coarseValueAt m (S.theta m)

theorem fiberValueAt_eq (A : ActualIntervalCovers S)
    (m : Fin depth) (rho : NNReal)
    (htau : S.tau m <= rho) (hrho : rho <= 1) :
    A.fiberValueAt m rho =
      StickyScaleCover.fiberDeltaMax
        ((A.multiscale m).cover rho htau hrho) := by
  exact StickyMultiscaleCover.actualFiberDeltaMaxAt_eq
    (A.multiscale m) rho htau hrho

theorem coarseValueAt_eq (A : ActualIntervalCovers S)
    (m : Fin depth) (rho : NNReal)
    (htau : S.tau m <= rho) (hrho : rho <= 1) :
    A.coarseValueAt m rho =
      StickyScaleCover.coarseDeltaMax
        ((A.multiscale m).cover rho htau hrho) := by
  exact StickyMultiscaleCover.actualCoarseDeltaMaxAt_eq
    (A.multiscale m) rho htau hrho

theorem adjacentFiberValue_eq (A : ActualIntervalCovers S)
    (m : Fin depth) :
    A.adjacentFiberValue m =
      StickyScaleCover.fiberDeltaMax
        ((A.multiscale m).cover (S.theta m)
          (S.tau_le_theta m) (S.theta_le_one m)) := by
  exact A.fiberValueAt_eq m (S.theta m)
    (S.tau_le_theta m) (S.theta_le_one m)

theorem adjacentCoarseValue_eq (A : ActualIntervalCovers S)
    (m : Fin depth) :
    A.adjacentCoarseValue m =
      StickyScaleCover.coarseDeltaMax
        ((A.multiscale m).cover (S.theta m)
          (S.tau_le_theta m) (S.theta_le_one m)) := by
  exact A.coarseValueAt_eq m (S.theta m)
    (S.tau_le_theta m) (S.theta_le_one m)

/-- Build the frozen Frostman no-split run with literal fiber `Delta_max`
values in both the adjacent and middle slots. -/
def toFrostmanNoSplitRun
    {N : Nat} {epsilon : Real} {eta : Nat -> Real}
    (A : ActualIntervalCovers S)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (eta_monotone : Monotone eta)
    (eta_stage_le_epsilon : eta stage <= epsilon)
    (fineFiberValue : Fin depth -> ENNReal)
    (fineFiber_upper : forall m,
      fineFiberValue m <=
        (((S.tau m / delta : NNReal) : ENNReal) ^ eta (stage - 1)))
    (adjacent_upper : forall m,
      A.adjacentFiberValue m <=
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (stage - 1)))
    (terminal_noSplit : forall m, ¬ S.IsLarge epsilon m ->
      ¬ (exists rho, S.IsBuffered epsilon m rho ∧
        A.fiberValueAt m rho <
          (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage))) :
    FrostmanNoSplitRun delta depth N epsilon eta S where
  stage := stage
  stage_pos := stage_pos
  stage_le := stage_le
  eta_monotone := eta_monotone
  eta_stage_le_epsilon := eta_stage_le_epsilon
  fineFiberValue := fineFiberValue
  adjacentValue := A.adjacentFiberValue
  middleValue := A.fiberValueAt
  fineFiber_upper := fineFiber_upper
  adjacent_upper := adjacent_upper
  terminal_noSplit := terminal_noSplit

/-- Build the chain-backed Katz--Tao no-split run with literal coarse
`Delta_max` values in both the adjacent and middle slots. -/
def toKatzTaoChainNoSplitRun
    {chainDepth N : Nat} {epsilon : Real} {eta : Nat -> Real}
    (A : ActualIntervalCovers S)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (eta_monotone : Monotone eta)
    (eta_stage_le_epsilon : eta stage <= epsilon)
    (chain : Fin depth -> FiniteDeltaMaxChain chainDepth)
    (productBudget : forall m,
      (chain m).dimensionalLoss ^ chainDepth *
          (∏ k ∈ Finset.range chainDepth, (chain m).localDeltaMax k) <=
        (S.theta m : ENNReal) ^ (-eta (stage - 1)))
    (adjacent_upper : forall m,
      A.adjacentCoarseValue m <=
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (stage - 1)))
    (terminal_noSplit : forall m, ¬ S.IsLarge epsilon m ->
      ¬ (exists rho, S.IsBuffered epsilon m rho ∧
        A.coarseValueAt m rho <
          (((S.theta m / rho : NNReal) : ENNReal) ^ eta stage))) :
    KatzTaoChainNoSplitRun delta depth chainDepth N epsilon eta S where
  stage := stage
  stage_pos := stage_pos
  stage_le := stage_le
  eta_monotone := eta_monotone
  eta_stage_le_epsilon := eta_stage_le_epsilon
  chain := chain
  productBudget := productBudget
  adjacentValue := A.adjacentCoarseValue
  middleValue := A.coarseValueAt
  adjacent_upper := adjacent_upper
  terminal_noSplit := terminal_noSplit

end ActualIntervalCovers

#print axioms StickyMultiscaleCover.actualFiberDeltaMaxAt_eq
#print axioms StickyMultiscaleCover.actualCoarseDeltaMaxAt_eq
#print axioms StickyMultiscaleCover.isKatzTaoAtEveryScale_iff_actualCoarseDeltaMaxAt_le
#print axioms ActualIntervalCovers.adjacentFiberValue_eq
#print axioms ActualIntervalCovers.adjacentCoarseValue_eq
#print axioms ActualIntervalCovers.toFrostmanNoSplitRun
#print axioms ActualIntervalCovers.toKatzTaoChainNoSplitRun

end
end FamilyStickyScaleChainActualValuesV1
