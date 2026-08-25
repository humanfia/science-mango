import FamilyStickyGrounding.FamilyStickyScaleChainRootedRefinementTreeV1

set_option autoImplicit false

open scoped ENNReal NNReal

namespace FamilyStickyScaleChainTreeThresholdTransferV1

open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainTerminalFiniteSearchV1
open FamilyStickyScaleChainDiscreteRefinementTreeV1
open FamilyStickyScaleChainRootedRefinementTreeV1

noncomputable section

/-!
# Sticky Kakeya: finite-node threshold transfer

Every buffered continuous scale is localized to a node of a finite rooted
tree.  The sole analytic bridge in this module is a normalized coarse-value
comparison between that node and the input scale.  It is strictly weaker
than a no-split or interpolation conclusion and will be produced from actual
nested covers in the next module.
-/

variable {delta : NNReal} {depth : Nat} {epsilon : Real}
  {eta : Nat -> Real} {stage : Nat}
  {S : FiniteScaleSequence delta depth}

/-- Exact multiplicative relation between the splitting thresholds at two
positive scales. -/
theorem splitThreshold_factorization
    (m : Fin depth) (sigma rho : NNReal)
    (hsigma : 0 < sigma) (hrho : 0 < rho)
    (heta : 0 <= eta stage) :
    splitThreshold S eta stage m sigma =
      (((rho / sigma : NNReal) : ENNReal) ^ eta stage) *
        splitThreshold S eta stage m rho := by
  unfold splitThreshold
  rw [← ENNReal.mul_rpow_of_nonneg _ _ heta]
  congr 1
  norm_cast
  field_simp [hsigma.ne', hrho.ne']

/-- Cancellation of the positive finite scale-ratio power transports a
verified lower threshold from the located node to the continuous scale. -/
theorem splitThreshold_le_of_located_coarseValue
    (A : ActualIntervalCovers S) (m : Fin depth)
    (sigma rho : NNReal)
    (hsigma : 0 < sigma) (hrho : 0 < rho)
    (heta : 0 <= eta stage)
    (hnode : splitThreshold S eta stage m sigma <=
      A.coarseValueAt m sigma)
    (hlocalize : A.coarseValueAt m sigma <=
      (((rho / sigma : NNReal) : ENNReal) ^ eta stage) *
        A.coarseValueAt m rho) :
    splitThreshold S eta stage m rho <= A.coarseValueAt m rho := by
  let q : ENNReal :=
    (((rho / sigma : NNReal) : ENNReal) ^ eta stage)
  have hratio_pos : 0 < rho / sigma := div_pos hrho hsigma
  have hq0 : q ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hratio_pos)
      ENNReal.coe_ne_top).ne'
  have hqTop : q ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg heta ENNReal.coe_ne_top
  have hmul : q * splitThreshold S eta stage m rho <=
      q * A.coarseValueAt m rho := by
    rw [← splitThreshold_factorization m sigma rho hsigma hrho heta]
    exact hnode.trans hlocalize
  exact (ENNReal.mul_le_mul_iff_right hq0 hqTop).1 hmul

/-- The weakest analytic bridge used by the finite tree: the actual coarse
value at the located node is bounded by the literal scale-ratio power times
the actual value at the input scale.  No threshold occurs in this field. -/
structure LocatedCoarseValueLocalization
    (A : ActualIntervalCovers S)
    (R : IntervalRootedRefinementScaleTree S) : Prop where
  localized_le : forall m rho,
    S.IsBuffered epsilon m rho ->
      A.coarseValueAt m
          (R.tree.scale m (R.tree.locate m rho)) <=
        (((rho / R.tree.scale m (R.tree.locate m rho) : NNReal) : ENNReal) ^
            eta stage) * A.coarseValueAt m rho

/-- The genuinely finite analytic checks: one actual lower inequality per
tree node.  There is no quantification over arbitrary continuous scales. -/
structure VerifiedTreeNodeLowerBounds
    (A : ActualIntervalCovers S)
    (R : IntervalRootedRefinementScaleTree S) : Prop where
  checked : forall m, ¬ S.IsLarge epsilon m ->
    forall i : Fin (R.tree.levelCount m),
      splitThreshold S eta stage m (R.tree.scale m i) <=
        A.coarseValueAt m (R.tree.scale m i)

namespace VerifiedTreeNodeLowerBounds

variable {A : ActualIntervalCovers S}
  {R : IntervalRootedRefinementScaleTree S}

/-- A checked finite node, together with located coarse-value localization,
gives the lower inequality at every buffered continuous scale. -/
theorem buffered_lower
    (V : VerifiedTreeNodeLowerBounds
      (epsilon := epsilon) (eta := eta) (stage := stage) A R)
    (L : LocatedCoarseValueLocalization
      (epsilon := epsilon) (eta := eta) (stage := stage) A R)
    (heta : 0 <= eta stage) (heta_epsilon : eta stage <= epsilon)
    (m : Fin depth) (hlarge : ¬ S.IsLarge epsilon m)
    (rho : NNReal) (hrho : S.IsBuffered epsilon m rho) :
    splitThreshold S eta stage m rho <= A.coarseValueAt m rho := by
  have hepsilon : 0 <= epsilon := heta.trans heta_epsilon
  let sigma : NNReal := R.tree.scale m (R.tree.locate m rho)
  have hsigma_pos : 0 < sigma :=
    (R.tau_pos m).trans_le (R.tau_le_scale m (R.tree.locate m rho))
  have hrho_pos : 0 < rho :=
    (R.tau_pos m).trans_le (R.tau_le_of_isBuffered hepsilon m rho hrho)
  exact splitThreshold_le_of_located_coarseValue A m sigma rho
    hsigma_pos hrho_pos heta
    (V.checked m hlarge (R.tree.locate m rho))
    (L.localized_le m rho hrho)

/-- Finite node checks and the localization bridge synthesize the exact
terminal no-split proposition.  It is not stored in either input. -/
theorem terminal_noSplit
    (V : VerifiedTreeNodeLowerBounds
      (epsilon := epsilon) (eta := eta) (stage := stage) A R)
    (L : LocatedCoarseValueLocalization
      (epsilon := epsilon) (eta := eta) (stage := stage) A R)
    (heta : 0 <= eta stage) (heta_epsilon : eta stage <= epsilon) :
    forall m, ¬ S.IsLarge epsilon m ->
      ¬ (exists rho, S.IsBuffered epsilon m rho ∧
        A.coarseValueAt m rho < splitThreshold S eta stage m rho) := by
  intro m hlarge
  rintro ⟨rho, hrho, hstrict⟩
  exact (not_lt_of_ge
    (V.buffered_lower L heta heta_epsilon m hlarge rho hrho)) hstrict

end VerifiedTreeNodeLowerBounds

#print axioms splitThreshold_factorization
#print axioms splitThreshold_le_of_located_coarseValue
#print axioms VerifiedTreeNodeLowerBounds.buffered_lower
#print axioms VerifiedTreeNodeLowerBounds.terminal_noSplit

end
end FamilyStickyScaleChainTreeThresholdTransferV1
