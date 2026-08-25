import FamilyStickyGrounding.FamilyStickyScaleChainNestedMassLocalizationV1
import FamilyStickyGrounding.FamilyStickyScaleChainCoherentIntervalProducerV1

set_option autoImplicit false

open scoped ENNReal NNReal

namespace FamilyStickyScaleChainCoherentMassLocalizationProducerV1

open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainNestedMassLocalizationV1.StickyScaleCover

noncomputable section

/-!
# Sticky Kakeya: coherent-cover localization producer

The generic nested-mass theorem is specialized here to the actual interval
cover cut out of one coherent multiscale cover.  The endpoint identities show
that its fine and coarse maximal concentrations are exactly the literal
coarse values selected at the two scales.  Thus no numerical localization
inequality is supplied as data.
-/

namespace CoherentStickyMultiscaleCover

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  (C : CoherentStickyMultiscaleCover fine)

/-- The fine endpoint of an actual coherent interval cover is exactly the
global coarse family selected at the lower scale. -/
theorem intervalScaleCover_fineDeltaMax_eq_actualCoarseDeltaMaxAt
    (sigma rho : NNReal) (hdeltaSigma : delta <= sigma)
    (hSigmaRho : sigma <= rho) (hRhoOne : rho <= 1) :
    fineDeltaMax
        (C.intervalScaleCover sigma rho hdeltaSigma hSigmaRho hRhoOne) =
      StickyMultiscaleCover.actualCoarseDeltaMaxAt C.base sigma := by
  rw [StickyMultiscaleCover.actualCoarseDeltaMaxAt_eq C.base sigma
    hdeltaSigma (hSigmaRho.trans hRhoOne)]
  rfl

/-- The coarse endpoint of an actual coherent interval cover is exactly the
global coarse family selected at the upper scale. -/
theorem intervalScaleCover_coarseDeltaMax_eq_actualCoarseDeltaMaxAt
    (sigma rho : NNReal) (hdeltaSigma : delta <= sigma)
    (hSigmaRho : sigma <= rho) (hRhoOne : rho <= 1) :
    coarseDeltaMax
        (C.intervalScaleCover sigma rho hdeltaSigma hSigmaRho hRhoOne) =
      StickyMultiscaleCover.actualCoarseDeltaMaxAt C.base rho := by
  rw [StickyMultiscaleCover.actualCoarseDeltaMaxAt_eq C.base rho
    (hdeltaSigma.trans hSigmaRho) hRhoOne]
  rfl

/-- Coarse-value localization produced from the actual coherent interval
cover, its literal parent fibers, and captured-body thickening geometry. -/
theorem actualCoarseDeltaMaxAt_le_of_nestedGeometry
    (sigma rho : NNReal) (hdeltaSigma : delta <= sigma)
    (hSigmaRho : sigma <= rho) (hRhoOne : rho <= 1)
    (massLoss bodyLoss : ENNReal)
    (M : ParentFiberMassMonotonicity
      (C.intervalScaleCover sigma rho hdeltaSigma hSigmaRho hRhoOne)
      massLoss)
    (V : CapturingThickeningVolumeControl
      (C.intervalScaleCover sigma rho hdeltaSigma hSigmaRho hRhoOne)
      bodyLoss) :
    StickyMultiscaleCover.actualCoarseDeltaMaxAt C.base sigma <=
      (massLoss * bodyLoss) * StickyMultiscaleCover.actualCoarseDeltaMaxAt C.base rho := by
  rw [← intervalScaleCover_fineDeltaMax_eq_actualCoarseDeltaMaxAt C
      sigma rho hdeltaSigma hSigmaRho hRhoOne,
    ← intervalScaleCover_coarseDeltaMax_eq_actualCoarseDeltaMaxAt C
      sigma rho hdeltaSigma hSigmaRho hRhoOne]
  exact fineDeltaMax_le_coarseDeltaMax_of_nestedGeometry
    (C.intervalScaleCover sigma rho hdeltaSigma hSigmaRho hRhoOne) M V

/-- The interval data generated from `C` evaluates to the same global
coarse value at every legal intermediate scale. -/
theorem toActualIntervalCovers_coarseValueAt_eq_base
    {depth : Nat} (S : FiniteScaleSequence delta depth)
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoOne : rho <= 1) :
    (C.toActualIntervalCovers S).coarseValueAt m rho =
      StickyMultiscaleCover.actualCoarseDeltaMaxAt C.base rho := by
  rw [ActualIntervalCovers.coarseValueAt_eq
      (C.toActualIntervalCovers S) m rho hTauRho hRhoOne,
    StickyMultiscaleCover.actualCoarseDeltaMaxAt_eq C.base rho
      ((S.delta_le_tau m).trans hTauRho) hRhoOne]
  rfl

/-- The same producer, in the exact `ActualIntervalCovers.coarseValueAt`
language used by terminal scale search. -/
theorem toActualIntervalCovers_coarseValueAt_le_of_nestedGeometry
    {depth : Nat} (S : FiniteScaleSequence delta depth)
    (m : Fin depth) (sigma rho : NNReal)
    (hTauSigma : S.tau m <= sigma) (hSigmaRho : sigma <= rho)
    (hRhoOne : rho <= 1)
    (massLoss bodyLoss : ENNReal)
    (M : ParentFiberMassMonotonicity
      (C.intervalScaleCover sigma rho
        ((S.delta_le_tau m).trans hTauSigma) hSigmaRho hRhoOne)
      massLoss)
    (V : CapturingThickeningVolumeControl
      (C.intervalScaleCover sigma rho
        ((S.delta_le_tau m).trans hTauSigma) hSigmaRho hRhoOne)
      bodyLoss) :
    (C.toActualIntervalCovers S).coarseValueAt m sigma <=
      (massLoss * bodyLoss) *
        (C.toActualIntervalCovers S).coarseValueAt m rho := by
  rw [toActualIntervalCovers_coarseValueAt_eq_base C S m sigma hTauSigma
      (hSigmaRho.trans hRhoOne),
    toActualIntervalCovers_coarseValueAt_eq_base C S m rho
      (hTauSigma.trans hSigmaRho) hRhoOne]
  exact actualCoarseDeltaMaxAt_le_of_nestedGeometry C sigma rho
    ((S.delta_le_tau m).trans hTauSigma) hSigmaRho hRhoOne
    massLoss bodyLoss M V

end CoherentStickyMultiscaleCover

#print axioms CoherentStickyMultiscaleCover.intervalScaleCover_fineDeltaMax_eq_actualCoarseDeltaMaxAt
#print axioms CoherentStickyMultiscaleCover.intervalScaleCover_coarseDeltaMax_eq_actualCoarseDeltaMaxAt
#print axioms CoherentStickyMultiscaleCover.actualCoarseDeltaMaxAt_le_of_nestedGeometry
#print axioms CoherentStickyMultiscaleCover.toActualIntervalCovers_coarseValueAt_eq_base
#print axioms CoherentStickyMultiscaleCover.toActualIntervalCovers_coarseValueAt_le_of_nestedGeometry

end
end FamilyStickyScaleChainCoherentMassLocalizationProducerV1
