import FamilyStickyGrounding.FamilyStickyScaleChainActualValuesV1

set_option autoImplicit false

open Set
open scoped ENNReal NNReal

namespace FamilyStickyScaleChainCoherentIntervalProducerV1

open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open Submission.Kakeya.Uniformity

noncomputable section

/-!
# Sticky Kakeya: coherent interval-cover producer

The frozen `StickyMultiscaleCover` chooses a cover of the original fine
family independently at every scale.  To restart the same construction on a
terminal interval `[tau, rho]`, one needs actual parent maps between the
chosen `tau`- and `rho`-families.  This module records exactly those maps,
their active-index surjectivity, and their geometric carrier containment.

These are finite geometric data, not a concentration or interpolation
callback.  From them we construct literal `StickyScaleCover`s on every
subinterval and hence the `ActualIntervalCovers` consumed by dividing scales.
-/

/-- Cross-scale coherence for the actual covers chosen by one multiscale
cover.  At `tau <= rho`, every active `tau`-tube has an active `rho` parent,
every active `rho` parent is used, and the carrier containment is literal. -/
structure CoherentStickyMultiscaleCover
    {delta : NNReal} {iota : Type*} [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) where
  base : StickyMultiscaleCover fine
  parent : forall (tau rho : NNReal)
      (hdeltaTau : delta <= tau) (hTauRho : tau <= rho)
      (hRhoOne : rho <= 1),
    Fin ((base.cover tau hdeltaTau (hTauRho.trans hRhoOne)).coarseCard) ->
      Fin ((base.cover rho (hdeltaTau.trans hTauRho) hRhoOne).coarseCard)
  parent_mem : forall (tau rho : NNReal)
      (hdeltaTau : delta <= tau) (hTauRho : tau <= rho)
      (hRhoOne : rho <= 1) k,
    k ∈ (base.cover tau hdeltaTau (hTauRho.trans hRhoOne)).activeCoarse ->
      parent tau rho hdeltaTau hTauRho hRhoOne k ∈
        (base.cover rho (hdeltaTau.trans hTauRho) hRhoOne).activeCoarse
  parent_surjective : forall (tau rho : NNReal)
      (hdeltaTau : delta <= tau) (hTauRho : tau <= rho)
      (hRhoOne : rho <= 1) k,
    k ∈ (base.cover rho (hdeltaTau.trans hTauRho) hRhoOne).activeCoarse ->
      exists i,
        i ∈ (base.cover tau hdeltaTau
          (hTauRho.trans hRhoOne)).activeCoarse ∧
        parent tau rho hdeltaTau hTauRho hRhoOne i = k
  carrier_subset : forall (tau rho : NNReal)
      (hdeltaTau : delta <= tau) (hTauRho : tau <= rho)
      (hRhoOne : rho <= 1) i,
    i ∈ (base.cover tau hdeltaTau (hTauRho.trans hRhoOne)).activeCoarse ->
      ((base.cover tau hdeltaTau (hTauRho.trans hRhoOne)).coarse.tubes i).carrier ⊆
        ((base.cover rho (hdeltaTau.trans hTauRho) hRhoOne).coarse.tubes
          (parent tau rho hdeltaTau hTauRho hRhoOne i)).carrier

namespace CoherentStickyMultiscaleCover

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The actual cover of the chosen `tau`-family by the chosen `rho`-family. -/
def intervalScaleCover (C : CoherentStickyMultiscaleCover fine)
    (tau rho : NNReal) (hdeltaTau : delta <= tau)
    (hTauRho : tau <= rho) (hRhoOne : rho <= 1) :
    StickyScaleCover
      (C.base.cover tau hdeltaTau (hTauRho.trans hRhoOne)).coarse rho where
  coarseCard :=
    (C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne).coarseCard
  coarse := (C.base.cover rho
    (hdeltaTau.trans hTauRho) hRhoOne).coarse
  activeFine := (C.base.cover tau hdeltaTau
    (hTauRho.trans hRhoOne)).activeCoarse
  activeCoarse := (C.base.cover rho
    (hdeltaTau.trans hTauRho) hRhoOne).activeCoarse
  parent := C.parent tau rho hdeltaTau hTauRho hRhoOne
  activeFine_eq_refined :=
    (C.base.cover tau hdeltaTau
      (hTauRho.trans hRhoOne)).activeCoarse_eq_refined
  activeCoarse_eq_refined :=
    (C.base.cover rho
      (hdeltaTau.trans hTauRho) hRhoOne).activeCoarse_eq_refined
  parent_mem := C.parent_mem tau rho hdeltaTau hTauRho hRhoOne
  parent_surjective :=
    C.parent_surjective tau rho hdeltaTau hTauRho hRhoOne
  carrier_subset := C.carrier_subset tau rho hdeltaTau hTauRho hRhoOne

/-- Fixing the lower endpoint `tau` gives a literal multiscale cover of the
actual chosen `tau`-tube family at every scale in `[tau,1]`. -/
def intervalMultiscaleCover (C : CoherentStickyMultiscaleCover fine)
    (tau : NNReal) (hdeltaTau : delta <= tau) (hTauOne : tau <= 1) :
    StickyMultiscaleCover (C.base.cover tau hdeltaTau hTauOne).coarse where
  cover := fun rho hTauRho hRhoOne =>
    C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne

@[simp] theorem intervalMultiscaleCover_cover
    (C : CoherentStickyMultiscaleCover fine)
    (tau rho : NNReal) (hdeltaTau : delta <= tau)
    (hTauOne : tau <= 1) (hTauRho : tau <= rho)
    (hRhoOne : rho <= 1) :
    (C.intervalMultiscaleCover tau hdeltaTau hTauOne).cover
        rho hTauRho hRhoOne =
      C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne := by
  rfl

/-- Every lower endpoint of a finite scale sequence lies below one. -/
theorem tau_le_one {depth : Nat}
    (S : FiniteScaleSequence delta depth) (m : Fin depth) :
    S.tau m <= 1 :=
  (S.tau_le_theta m).trans (S.theta_le_one m)

/-- A coherent global cover automatically produces the actual interval data
used by both Frostman and Katz--Tao no-split runs. -/
def toActualIntervalCovers {depth : Nat}
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth) : ActualIntervalCovers S where
  fineCard := fun m =>
    (C.base.cover (S.tau m) (S.delta_le_tau m)
      (tau_le_one S m)).coarseCard
  fine := fun m =>
    (C.base.cover (S.tau m) (S.delta_le_tau m)
      (tau_le_one S m)).coarse
  multiscale := fun m =>
    C.intervalMultiscaleCover (S.tau m)
      (S.delta_le_tau m) (tau_le_one S m)

/-- The generated adjacent fiber value is the literal fiber `Delta_max` of
the coherent `tau_m -> theta_m` cover. -/
theorem toActualIntervalCovers_adjacentFiberValue_eq {depth : Nat}
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth) (m : Fin depth) :
    (C.toActualIntervalCovers S).adjacentFiberValue m =
      StickyScaleCover.fiberDeltaMax
        (C.intervalScaleCover (S.tau m) (S.theta m)
          (S.delta_le_tau m) (S.tau_le_theta m) (S.theta_le_one m)) := by
  exact (C.toActualIntervalCovers S).adjacentFiberValue_eq m

/-- The generated adjacent coarse value is the literal coarse `Delta_max` of
the same coherent `tau_m -> theta_m` cover. -/
theorem toActualIntervalCovers_adjacentCoarseValue_eq {depth : Nat}
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth) (m : Fin depth) :
    (C.toActualIntervalCovers S).adjacentCoarseValue m =
      StickyScaleCover.coarseDeltaMax
        (C.intervalScaleCover (S.tau m) (S.theta m)
          (S.delta_le_tau m) (S.tau_le_theta m) (S.theta_le_one m)) := by
  exact (C.toActualIntervalCovers S).adjacentCoarseValue_eq m

end CoherentStickyMultiscaleCover

#print axioms CoherentStickyMultiscaleCover.intervalScaleCover
#print axioms CoherentStickyMultiscaleCover.intervalMultiscaleCover_cover
#print axioms CoherentStickyMultiscaleCover.tau_le_one
#print axioms CoherentStickyMultiscaleCover.toActualIntervalCovers
#print axioms CoherentStickyMultiscaleCover.toActualIntervalCovers_adjacentFiberValue_eq
#print axioms CoherentStickyMultiscaleCover.toActualIntervalCovers_adjacentCoarseValue_eq

end
end FamilyStickyScaleChainCoherentIntervalProducerV1
