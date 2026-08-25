import FamilyStickyGrounding.FamilyStickyScaleChainCoherentTreeLocalizationV1

set_option autoImplicit false

open scoped ENNReal NNReal

namespace FamilyStickyScaleChainStrictLocatedLocalizationV2

open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainNestedMassLocalizationV1.StickyScaleCover
open FamilyStickyScaleChainCoherentMassLocalizationProducerV1.CoherentStickyMultiscaleCover
open FamilyStickyScaleChainRootedRefinementTreeV1
open FamilyStickyScaleChainRootedRefinementTreeV1.IntervalRootedRefinementScaleTree
open FamilyStickyScaleChainTreeThresholdTransferV1
open FamilyStickyScaleChainCoherentTreeLocalizationV1

noncomputable section

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {depth : Nat} {epsilon : Real} {eta : Nat -> Real} {stage : Nat}
  {S : FiniteScaleSequence delta depth}

namespace CoherentIntervalLocalizationGeometry

variable {C : CoherentStickyMultiscaleCover fine}
  {R : IntervalRootedRefinementScaleTree S}

/-- Loss absorption is needed only when localization moves to a genuinely
smaller tree scale.  At an exact tree node, coarse-value localization is
reflexive and no geometric loss needs to be absorbed. -/
structure StrictLocatedLossExponentBudget
    (D : CoherentIntervalLocalizationGeometry C S) : Prop where
  loss_le : forall m rho, S.IsBuffered epsilon m rho ->
    R.tree.scale m (R.tree.locate m rho) < rho ->
      D.massLoss m (R.tree.scale m (R.tree.locate m rho)) rho *
          D.bodyLoss m (R.tree.scale m (R.tree.locate m rho)) rho <=
        (((rho / R.tree.scale m (R.tree.locate m rho) : NNReal) : ENNReal) ^
          eta stage)

/-- Strict-interval loss absorption plus the reflexive exact-node case
produces the original coarse-value localization interface. -/
theorem toLocatedCoarseValueLocalization
    (D : CoherentIntervalLocalizationGeometry C S)
    (B : StrictLocatedLossExponentBudget (epsilon := epsilon)
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
    have hsigma_pos : 0 < sigma := (R.tau_pos m).trans_le hsigma.1
    change (C.toActualIntervalCovers S).coarseValueAt m sigma <=
      (((rho / sigma : NNReal) : ENNReal) ^ eta stage) *
        (C.toActualIntervalCovers S).coarseValueAt m rho
    rcases lt_or_eq_of_le hsigma.2 with hstrict | heq
    · have hrhoOne := le_one_of_isBuffered hepsilon m rho hrho
      have hgeometry :=
        toActualIntervalCovers_coarseValueAt_le_of_nestedGeometry C S m
          sigma rho hsigma.1 hsigma.2 hrhoOne
          (D.massLoss m sigma rho) (D.bodyLoss m sigma rho)
          (D.parentFiberMass m sigma rho hsigma.1 hsigma.2 hrhoOne)
          (D.capturingThickening m sigma rho hsigma.1 hsigma.2 hrhoOne)
      exact hgeometry.trans (by
        gcongr
        exact B.loss_le m rho hrho hstrict)
    · have heq' : sigma = rho := by simpa [sigma] using heq
      rw [← heq']
      simp [div_self hsigma_pos.ne']

#print axioms toLocatedCoarseValueLocalization

end CoherentIntervalLocalizationGeometry

end
end FamilyStickyScaleChainStrictLocatedLocalizationV2
