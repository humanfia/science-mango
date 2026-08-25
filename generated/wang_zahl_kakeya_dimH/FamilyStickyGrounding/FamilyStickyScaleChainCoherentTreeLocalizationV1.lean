import FamilyStickyGrounding.FamilyStickyScaleChainCoherentMassLocalizationProducerV1
import FamilyStickyGrounding.FamilyStickyScaleChainTreeThresholdTransferV1

set_option autoImplicit false

open scoped ENNReal NNReal

namespace FamilyStickyScaleChainCoherentTreeLocalizationV1

open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainTerminalFiniteSearchV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainNestedMassLocalizationV1.StickyScaleCover
open FamilyStickyScaleChainCoherentMassLocalizationProducerV1.CoherentStickyMultiscaleCover
open FamilyStickyScaleChainRootedRefinementTreeV1
open FamilyStickyScaleChainRootedRefinementTreeV1.IntervalRootedRefinementScaleTree
open FamilyStickyScaleChainTreeThresholdTransferV1

noncomputable section

/-!
# Sticky Kakeya: coherent nested-cover producer for tree localization

This module discharges the sole numerical localization field of the finite
tree from actual coherent interval covers.  The supplied geometric data stop
at the earliest local statements: per-parent fiber mass monotonicity and the
captured-body thickening volume estimate.  A separate exponent budget bounds
their product by the scale-ratio power.  No coarse-value, threshold, split,
or no-split inequality is stored in those inputs.
-/

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {depth : Nat} {epsilon : Real} {eta : Nat -> Real} {stage : Nat}
  {S : FiniteScaleSequence delta depth}

/-- Local geometric estimates for every actual coherent subinterval. -/
structure CoherentIntervalLocalizationGeometry
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth) where
  massLoss : Fin depth -> NNReal -> NNReal -> ENNReal
  bodyLoss : Fin depth -> NNReal -> NNReal -> ENNReal
  parentFiberMass : forall m sigma rho
      (hTauSigma : S.tau m <= sigma) (hSigmaRho : sigma <= rho)
      (hRhoOne : rho <= 1),
    ParentFiberMassMonotonicity
      (C.intervalScaleCover sigma rho
        ((S.delta_le_tau m).trans hTauSigma) hSigmaRho hRhoOne)
      (massLoss m sigma rho)
  capturingThickening : forall m sigma rho
      (hTauSigma : S.tau m <= sigma) (hSigmaRho : sigma <= rho)
      (hRhoOne : rho <= 1),
    CapturingThickeningVolumeControl
      (C.intervalScaleCover sigma rho
        ((S.delta_le_tau m).trans hTauSigma) hSigmaRho hRhoOne)
      (bodyLoss m sigma rho)

namespace CoherentIntervalLocalizationGeometry

variable {C : CoherentStickyMultiscaleCover fine}
  {R : IntervalRootedRefinementScaleTree S}

/-- Exponent absorption for the two literal geometric losses at the located
node.  This contains no concentration or threshold value. -/
structure LocatedLossExponentBudget
    (D : CoherentIntervalLocalizationGeometry C S) : Prop where
  loss_le : forall m rho, S.IsBuffered epsilon m rho ->
    D.massLoss m (R.tree.scale m (R.tree.locate m rho)) rho *
        D.bodyLoss m (R.tree.scale m (R.tree.locate m rho)) rho <=
      (((rho / R.tree.scale m (R.tree.locate m rho) : NNReal) : ENNReal) ^
        eta stage)

/-- Actual nested covers and their local mass/volume estimates produce the
weak coarse-value localization consumed by the finite threshold layer. -/
theorem toLocatedCoarseValueLocalization
    (D : CoherentIntervalLocalizationGeometry C S)
    (B : LocatedLossExponentBudget (epsilon := epsilon)
      (eta := eta) (stage := stage) (R := R) D)
    (heta : 0 <= eta stage) (heta_epsilon : eta stage <= epsilon) :
    LocatedCoarseValueLocalization
      (epsilon := epsilon) (eta := eta) (stage := stage)
      (C.toActualIntervalCovers S) R where
  localized_le := by
    intro m rho hrho
    have hepsilon : 0 <= epsilon := heta.trans heta_epsilon
    let sigma : NNReal := R.tree.scale m (R.tree.locate m rho)
    have hsigma := R.located_scale_mem_interval hepsilon m rho hrho
    have hrhoOne := le_one_of_isBuffered hepsilon m rho hrho
    have hgeometry :=
      toActualIntervalCovers_coarseValueAt_le_of_nestedGeometry C S m
        sigma rho hsigma.1 hsigma.2 hrhoOne
        (D.massLoss m sigma rho) (D.bodyLoss m sigma rho)
        (D.parentFiberMass m sigma rho hsigma.1 hsigma.2 hrhoOne)
        (D.capturingThickening m sigma rho hsigma.1 hsigma.2 hrhoOne)
    exact hgeometry.trans (by
      gcongr
      exact B.loss_le m rho hrho)

/-- Consequently, finite node checks give the exact terminal no-split
condition without any continuum enumeration field. -/
theorem terminal_noSplit
    (D : CoherentIntervalLocalizationGeometry C S)
    (B : LocatedLossExponentBudget (epsilon := epsilon)
      (eta := eta) (stage := stage) (R := R) D)
    (V : VerifiedTreeNodeLowerBounds
      (epsilon := epsilon) (eta := eta) (stage := stage)
      (C.toActualIntervalCovers S) R)
    (heta : 0 <= eta stage) (heta_epsilon : eta stage <= epsilon) :
    forall m, ¬ S.IsLarge epsilon m ->
      ¬ (exists rho, S.IsBuffered epsilon m rho ∧
        (C.toActualIntervalCovers S).coarseValueAt m rho <
          splitThreshold S eta stage m rho) :=
  V.terminal_noSplit
    (D.toLocatedCoarseValueLocalization B heta heta_epsilon)
    heta heta_epsilon

end CoherentIntervalLocalizationGeometry

#print axioms CoherentIntervalLocalizationGeometry.toLocatedCoarseValueLocalization
#print axioms CoherentIntervalLocalizationGeometry.terminal_noSplit

end
end FamilyStickyScaleChainCoherentTreeLocalizationV1
