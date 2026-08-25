import FamilyStickyGrounding.FamilyStickyScaleChainActualStrictLossWithConstantV1
import FamilyStickyGrounding.FamilyStickyScaleChainTerminalFiniteSearchV1

set_option autoImplicit false

open scoped ENNReal NNReal

namespace FamilyStickyScaleChainFiniteStrictSeparationAbsorptionV1

open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainTerminalFiniteSearchV1
open FamilyStickyScaleChainRootedRefinementTreeV1
open FamilyStickyScaleChainRootedRefinementTreeV1.IntervalRootedRefinementScaleTree
open FamilyStickyScaleChainTreeThresholdTransferV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentTreeLocalizationV1
open FamilyStickyScaleChainActualStrictLossWithConstantV1

noncomputable section

/-!
# Finite strict-scale separation absorbs the actual A7 loss

The preceding actual-geometry module leaves the exact factor

`K * (rho / sigma_loc) ^ (2 - eta stage)`.

This file isolates the weakest pointwise numerical condition that removes
that factor and then produces it from the existing finite `CandidateSearch`:
take the minimum of the finitely many strict candidate ratios and check one
explicit inequality there.  No geometric loss or localization inequality is
accepted from the caller.

The exponent condition is sharp in direction.  When `eta stage <= 2` and
`K > 1`, increasing scale separation cannot help: the factor is always
strictly larger than one.
-/

variable {delta : NNReal} {depth : Nat} {epsilon : Real}
  {eta : Nat -> Real} {stage : Nat}
  {S : FiniteScaleSequence delta depth}

/-! ## Weakest pointwise absorption interface -/

/-- The exact residual numerical condition, imposed only at genuinely
strict located intervals. -/
structure StrictExponentGapAbsorptionBudget
    (R : IntervalRootedRefinementScaleTree S) (K : ENNReal) : Prop where
  absorb : forall m rho, S.IsBuffered epsilon m rho ->
    R.tree.scale m (R.tree.locate m rho) < rho ->
      K *
        (((rho / R.tree.scale m (R.tree.locate m rho) : NNReal) : ENNReal) ^
          ((2 : Real) - eta stage)) <= 1

namespace VerifiedTreeNodeLowerBounds

variable {A : ActualIntervalCovers S}
  {R : IntervalRootedRefinementScaleTree S}
  {K : ENNReal}

/-- The exact residual factor bound is sufficient to restore the original
constant-one lower threshold at every buffered scale.  Exact tree nodes use
their checked inequality directly, so no condition is imposed there. -/
theorem buffered_lower_of_strictExponentGapAbsorption
    (V : VerifiedTreeNodeLowerBounds
      (epsilon := epsilon) (eta := eta) (stage := stage) A R)
    (L : StrictQuadraticLocatedCoarseValueLocalization
      (epsilon := epsilon) A R K)
    (B : StrictExponentGapAbsorptionBudget
      (epsilon := epsilon) (eta := eta) (stage := stage) R K)
    (heta : 0 <= eta stage) (heta_epsilon : eta stage <= epsilon)
    (m : Fin depth) (hlarge : ¬ S.IsLarge epsilon m)
    (rho : NNReal) (hrho : S.IsBuffered epsilon m rho) :
    splitThreshold S eta stage m rho <= A.coarseValueAt m rho := by
  have hepsilon : 0 <= epsilon := heta.trans heta_epsilon
  let sigma : NNReal := R.tree.scale m (R.tree.locate m rho)
  have hsigma := R.located_scale_mem_interval hepsilon m rho hrho
  have hsigmaPos : 0 < sigma := (R.tau_pos m).trans_le hsigma.1
  have hrhoPos : 0 < rho := hsigmaPos.trans_le hsigma.2
  rcases lt_or_eq_of_le hsigma.2 with hstrict | heq
  · have hgap :=
      splitThreshold_le_constant_mul_scaleRatio_gap_of_located_coarseValue
        A m sigma rho hsigmaPos hrhoPos heta K
        (V.checked m hlarge (R.tree.locate m rho))
        (L.localized_le m rho hrho hstrict)
    calc
      splitThreshold S eta stage m rho <=
          (K *
            (((rho / R.tree.scale m (R.tree.locate m rho) : NNReal) : ENNReal) ^
              ((2 : Real) - eta stage))) * A.coarseValueAt m rho := by
        simpa only [mul_assoc] using hgap
      _ <= 1 * A.coarseValueAt m rho :=
        mul_le_mul' (B.absorb m rho hrho hstrict) le_rfl
      _ = A.coarseValueAt m rho := by simp
  · have hnode := V.checked m hlarge (R.tree.locate m rho)
    simpa [sigma] using (heq ▸ hnode)

/-- Hence the absorbed strict loss supplies the literal terminal no-split
predicate expected by the original dividing-scales API. -/
theorem terminal_noSplit_of_strictExponentGapAbsorption
    (V : VerifiedTreeNodeLowerBounds
      (epsilon := epsilon) (eta := eta) (stage := stage) A R)
    (L : StrictQuadraticLocatedCoarseValueLocalization
      (epsilon := epsilon) A R K)
    (B : StrictExponentGapAbsorptionBudget
      (epsilon := epsilon) (eta := eta) (stage := stage) R K)
    (heta : 0 <= eta stage) (heta_epsilon : eta stage <= epsilon) :
    forall m, ¬ S.IsLarge epsilon m ->
      ¬ (exists rho, S.IsBuffered epsilon m rho ∧
        A.coarseValueAt m rho < splitThreshold S eta stage m rho) := by
  intro m hlarge
  rintro ⟨rho, hrho, hbad⟩
  exact (not_lt_of_ge
    (FamilyStickyScaleChainFiniteStrictSeparationAbsorptionV1.VerifiedTreeNodeLowerBounds.buffered_lower_of_strictExponentGapAbsorption
      V L B heta heta_epsilon m hlarge rho hrho)) hbad

end VerifiedTreeNodeLowerBounds

/-! ## A finite separation computed from `CandidateSearch` -/

namespace FiniteCandidateSeparation

variable {A : ActualIntervalCovers S}
  (Q : CandidateSearch A epsilon eta stage)
  (R : IntervalRootedRefinementScaleTree S)

/-- Ratios of all enumerated candidates lying genuinely above their located
tree node.  Irrelevant extra candidates only make the resulting minimum more
conservative. -/
def strictCandidateRatios (m : Fin depth) : Finset NNReal := by
  classical
  exact ((Q.candidates m).filter fun rho =>
    R.tree.scale m (R.tree.locate m rho) < rho).image fun rho =>
      rho / R.tree.scale m (R.tree.locate m rho)

theorem ratio_mem_strictCandidateRatios
    (m : Fin depth) (rho : NNReal)
    (hrho : rho ∈ Q.candidates m)
    (hstrict : R.tree.scale m (R.tree.locate m rho) < rho) :
    rho / R.tree.scale m (R.tree.locate m rho) ∈
      strictCandidateRatios Q R m := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨rho, Finset.mem_filter.mpr ⟨hrho, hstrict⟩, rfl⟩

/-- The minimum strict ratio, defaulting to one only when there is no strict
candidate. -/
def strictCandidateSeparation (m : Fin depth) : NNReal :=
  if h : (strictCandidateRatios Q R m).Nonempty then
    (strictCandidateRatios Q R m).min' h
  else 1

theorem strictCandidateSeparation_le_ratio
    (m : Fin depth) (rho : NNReal)
    (hrho : rho ∈ Q.candidates m)
    (hstrict : R.tree.scale m (R.tree.locate m rho) < rho) :
    strictCandidateSeparation Q R m <=
      rho / R.tree.scale m (R.tree.locate m rho) := by
  have hmem := ratio_mem_strictCandidateRatios Q R m rho hrho hstrict
  have hnonempty : (strictCandidateRatios Q R m).Nonempty := ⟨_, hmem⟩
  rw [strictCandidateSeparation, dif_pos hnonempty]
  exact Finset.min'_le _ _ hmem

theorem one_lt_strictCandidateSeparation
    (m : Fin depth)
    (hnonempty : (strictCandidateRatios Q R m).Nonempty) :
    1 < strictCandidateSeparation Q R m := by
  rw [strictCandidateSeparation, dif_pos hnonempty]
  have hminmem := Finset.min'_mem (strictCandidateRatios Q R m) hnonempty
  rcases Finset.mem_image.mp hminmem with ⟨rho, hrho, heq⟩
  have hstrict := (Finset.mem_filter.mp hrho).2
  have hdenPos : 0 < R.tree.scale m (R.tree.locate m rho) :=
    (R.tau_pos m).trans_le (R.tau_le_scale m (R.tree.locate m rho))
  have hone : 1 < rho / R.tree.scale m (R.tree.locate m rho) :=
    (one_lt_div hdenPos).2 hstrict
  rw [<- heq]
  exact hone

/-- A single finite numerical check at each computed minimum.  The exponent
slack is explicit, and no local loss/localization proposition is a field. -/
structure FiniteStrictSeparationAbsorptionBudget (K : ENNReal) : Prop where
  exponentSlack : (2 : Real) < eta stage
  constant_le_separation_rpow : forall m,
    (strictCandidateRatios Q R m).Nonempty ->
      K <= ((strictCandidateSeparation Q R m : NNReal) : ENNReal) ^
        (eta stage - 2)

namespace FiniteStrictSeparationAbsorptionBudget

variable {Q : CandidateSearch A epsilon eta stage}
  {R : IntervalRootedRefinementScaleTree S}
  {K : ENNReal}

/-- The finite minimum check implies the exact pointwise absorption bound
for every buffered strict scale, using `buffered_complete` only to place the
scale in the finite candidate set. -/
theorem absorb
    (B : FiniteStrictSeparationAbsorptionBudget Q R K)
    (m : Fin depth) (rho : NNReal)
    (hrho : S.IsBuffered epsilon m rho)
    (hstrict : R.tree.scale m (R.tree.locate m rho) < rho) :
    K *
      (((rho / R.tree.scale m (R.tree.locate m rho) : NNReal) : ENNReal) ^
        ((2 : Real) - eta stage)) <= 1 := by
  let ratio : NNReal := rho / R.tree.scale m (R.tree.locate m rho)
  let sep : NNReal := strictCandidateSeparation Q R m
  have hcand : rho ∈ Q.candidates m := Q.buffered_complete m rho hrho
  have hmem := ratio_mem_strictCandidateRatios Q R m rho hcand hstrict
  have hnonempty : (strictCandidateRatios Q R m).Nonempty := ⟨_, hmem⟩
  have hsep : sep <= ratio :=
    strictCandidateSeparation_le_ratio Q R m rho hcand hstrict
  have hsepOne : 1 < sep := one_lt_strictCandidateSeparation Q R m hnonempty
  have hratioOne : 1 < ratio := hsepOne.trans_le hsep
  have hgapNeg : (2 : Real) - eta stage < 0 := sub_neg.mpr B.exponentSlack
  have hpowNN : ratio ^ ((2 : Real) - eta stage) <=
      sep ^ ((2 : Real) - eta stage) :=
    NNReal.rpow_le_rpow_of_nonpos (zero_lt_one.trans hsepOne)
      hsep hgapNeg.le
  have hpow : (ratio : ENNReal) ^ ((2 : Real) - eta stage) <=
      (sep : ENNReal) ^ ((2 : Real) - eta stage) := by
    rw [<- ENNReal.coe_rpow_of_ne_zero (zero_lt_one.trans hratioOne).ne',
      <- ENNReal.coe_rpow_of_ne_zero (zero_lt_one.trans hsepOne).ne']
    exact_mod_cast hpowNN
  have hminimum :
      K * (sep : ENNReal) ^ ((2 : Real) - eta stage) <= 1 := by
    have hK := B.constant_le_separation_rpow m hnonempty
    have hgap : (2 : Real) - eta stage = -(eta stage - 2) := by ring
    rw [hgap, ENNReal.rpow_neg]
    calc
      K * ((sep : ENNReal) ^ (eta stage - 2))⁻¹ <=
          ((sep : ENNReal) ^ (eta stage - 2)) *
            ((sep : ENNReal) ^ (eta stage - 2))⁻¹ :=
        mul_le_mul' hK le_rfl
      _ <= 1 := ENNReal.mul_inv_le_one _
  calc
    K *
        (((rho / R.tree.scale m (R.tree.locate m rho) : NNReal) : ENNReal) ^
          ((2 : Real) - eta stage)) =
        K * (ratio : ENNReal) ^ ((2 : Real) - eta stage) := by rfl
    _ <= K * (sep : ENNReal) ^ ((2 : Real) - eta stage) :=
      mul_le_mul' le_rfl hpow
    _ <= 1 := hminimum

/-- Package the finite minimum calculation as the exact strict absorption
interface used by the threshold theorem. -/
theorem toStrictExponentGapAbsorptionBudget
    (B : FiniteStrictSeparationAbsorptionBudget Q R K) :
    StrictExponentGapAbsorptionBudget
      (epsilon := epsilon) (eta := eta) (stage := stage) R K where
  absorb := B.absorb

end FiniteStrictSeparationAbsorptionBudget
end FiniteCandidateSeparation

/-! ## Actual callback-free terminal producer -/

namespace CoherentIntervalLocalizationGeometry

variable {iota : Type*} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {C : CoherentStickyMultiscaleCover fine}
  {R : IntervalRootedRefinementScaleTree S}
  {Q : CandidateSearch (C.toActualIntervalCovers S) epsilon eta stage}

/-- Actual A6 geometry, finite tree-node checks, and the computed finite
candidate separation produce the literal terminal no-split statement. -/
theorem actual_terminal_noSplit_of_finiteStrictSeparation
    (tau_pos : forall m, 0 < S.tau m)
    (V : VerifiedTreeNodeLowerBounds
      (epsilon := epsilon) (eta := eta) (stage := stage)
      (C.toActualIntervalCovers S) R)
    (B : FiniteCandidateSeparation.FiniteStrictSeparationAbsorptionBudget Q R
      (actualStrictLocalizationConstant iota))
    (heta_epsilon : eta stage <= epsilon) :
    forall m, ¬ S.IsLarge epsilon m ->
      ¬ (exists rho, S.IsBuffered epsilon m rho ∧
        (C.toActualIntervalCovers S).coarseValueAt m rho <
          splitThreshold S eta stage m rho) := by
  have heta : 0 <= eta stage :=
    (by norm_num : (0 : Real) <= 2).trans B.exponentSlack.le
  exact
    FamilyStickyScaleChainFiniteStrictSeparationAbsorptionV1.VerifiedTreeNodeLowerBounds.terminal_noSplit_of_strictExponentGapAbsorption
      V
      (FamilyStickyScaleChainActualStrictLossWithConstantV1.CoherentIntervalLocalizationGeometry.toActualStrictQuadraticLocatedCoarseValueLocalization
        (C := C) (R := R) tau_pos (heta.trans heta_epsilon))
      B.toStrictExponentGapAbsorptionBudget
      heta heta_epsilon

end CoherentIntervalLocalizationGeometry

/-! ## Sharp obstruction when there is no exponent slack -/

/-- If the stopping exponent is at most two, every legal scale ratio makes
the residual power at least one. -/
theorem one_le_scaleRatio_exponentGap_of_eta_le_two
    (x K : ENNReal) (hx : 1 <= x) (hK : 1 <= K)
    (hetaTwo : eta stage <= 2) :
    1 <= K * x ^ ((2 : Real) - eta stage) := by
  have hgap : 0 <= (2 : Real) - eta stage := sub_nonneg.mpr hetaTwo
  have hpow : (1 : ENNReal) <= x ^ ((2 : Real) - eta stage) := by
    have := ENNReal.rpow_le_rpow_of_exponent_le hx hgap
    simpa using this
  calc
    (1 : ENNReal) = 1 * 1 := by simp
    _ <= K * x ^ ((2 : Real) - eta stage) := mul_le_mul' hK hpow

/-- In particular, with a genuinely nontrivial constant, no amount of scale
separation can satisfy the needed absorption condition when `eta <= 2`. -/
theorem not_scaleRatio_exponentGap_absorption_of_one_lt_constant
    (x K : ENNReal) (hx : 1 <= x) (hK : 1 < K)
    (hetaTwo : eta stage <= 2) :
    ¬ K * x ^ ((2 : Real) - eta stage) <= 1 := by
  have hpow : (1 : ENNReal) <= x ^ ((2 : Real) - eta stage) := by
    have hgap : 0 <= (2 : Real) - eta stage := sub_nonneg.mpr hetaTwo
    have := ENNReal.rpow_le_rpow_of_exponent_le hx hgap
    simpa using this
  have hstrict : 1 < K * x ^ ((2 : Real) - eta stage) := by
    calc
      (1 : ENNReal) < K := hK
      _ = K * 1 := by simp
      _ <= K * x ^ ((2 : Real) - eta stage) := mul_le_mul' le_rfl hpow
  exact not_le_of_gt hstrict

#print axioms VerifiedTreeNodeLowerBounds.buffered_lower_of_strictExponentGapAbsorption
#print axioms VerifiedTreeNodeLowerBounds.terminal_noSplit_of_strictExponentGapAbsorption
#print axioms FiniteCandidateSeparation.ratio_mem_strictCandidateRatios
#print axioms FiniteCandidateSeparation.strictCandidateSeparation_le_ratio
#print axioms FiniteCandidateSeparation.one_lt_strictCandidateSeparation
#print axioms FiniteCandidateSeparation.FiniteStrictSeparationAbsorptionBudget.absorb
#print axioms FiniteCandidateSeparation.FiniteStrictSeparationAbsorptionBudget.toStrictExponentGapAbsorptionBudget
#print axioms CoherentIntervalLocalizationGeometry.actual_terminal_noSplit_of_finiteStrictSeparation
#print axioms one_le_scaleRatio_exponentGap_of_eta_le_two
#print axioms not_scaleRatio_exponentGap_absorption_of_one_lt_constant

end
end FamilyStickyScaleChainFiniteStrictSeparationAbsorptionV1
