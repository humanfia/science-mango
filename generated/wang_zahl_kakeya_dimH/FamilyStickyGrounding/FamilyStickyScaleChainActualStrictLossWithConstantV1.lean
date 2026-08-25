import FamilyStickyGrounding.FamilyStickyCapturedTubeBoxWidthCleanV2
import FamilyStickyGrounding.FamilyStickyFiniteFamilyMaximalConcentrationV1
import FamilyStickyGrounding.FamilyStickyScaleChainCoherentLocalGeometryProducerCleanV2
import FamilyStickyGrounding.FamilyStickyScaleChainParentFiberMassToFiberDeltaV1
import FamilyStickyGrounding.FamilyStickyScaleChainStrictLocatedLocalizationV2

set_option autoImplicit false

open scoped ENNReal NNReal

namespace FamilyStickyScaleChainActualStrictLossWithConstantV1

open Submission.Kakeya.Uniformity
open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexGeometry
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainTerminalFiniteSearchV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyFiniteFamilyMaximalConcentrationV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentMassLocalizationProducerV1.CoherentStickyMultiscaleCover
open FamilyStickyScaleChainCoherentParentFiberMassProducerV1.CoherentIntervalLocalizationGeometry
open FamilyStickyScaleChainParentFiberMassProducerV1.StickyScaleCover
open FamilyStickyScaleChainParentFiberMassToFiberDeltaV1.StickyScaleCover
open FamilyStickyScaleChainRootedRefinementTreeV1
open FamilyStickyScaleChainRootedRefinementTreeV1.IntervalRootedRefinementScaleTree
open FamilyStickyScaleChainTreeThresholdTransferV1
open FamilyStickyScaleChainCoherentTreeLocalizationV1
open FamilyStickyCapturedTubeBoxWidthV1

noncomputable section

/-!
# Callback-free strict local loss with an explicit constant

The finite-family cardinality bounds the actual parent-fiber mass loss.
The captured-tube box estimate supplies exactly two powers of the scale
ratio.  Their product gives an automatic constant-bearing localization
statement, with no loss inequality supplied by the caller.

The constant cannot be removed on arbitrarily short strict intervals: the
ratio `rho / sigma` can approach one.  Accordingly the finite-tree endpoint
proved here is the strongest unconditional one available from these data:
the splitting threshold is at most the same explicit constant times the
actual coarse value.
-/

/-! ## Captured-box loss algebra -/

/-- The fixed dimension-three constant left by the certified box and the
elementary width estimates. -/
def capturedTubeBoxDimensionalConstant : ENNReal :=
  (288 : ENNReal) ^ 3 * 49 * 25

theorem one_le_scaleRatio
    {sigma rho : NNReal} (hsigma : 0 < sigma) (hSigmaRho : sigma <= rho) :
    1 <= rho / sigma :=
  (one_le_div hsigma).2 hSigmaRho

theorem shortWidthFactor_le_five_mul_scaleRatio
    {sigma rho : NNReal} (hsigma : 0 < sigma)
    (hSigmaRho : sigma <= rho) :
    shortWidthFactor sigma rho <= 5 * (rho / sigma) := by
  have hratio := one_le_scaleRatio hsigma hSigmaRho
  rw [shortWidthFactor]
  nlinarith

theorem longWidthFactor_le_49
    {rho : NNReal} (hRhoOne : rho <= 1) :
    longWidthFactor rho <= 49 := by
  rw [longWidthFactor]
  nlinarith

/-- The full captured-body loss has only the two transverse scale-ratio
powers. -/
theorem capturedTubeBoxLoss_le_dimensionalConstant_mul_scaleRatio_sq
    {sigma rho : NNReal} (hsigma : 0 < sigma)
    (hSigmaRho : sigma <= rho) (hRhoOne : rho <= 1) :
    capturedTubeBoxLoss sigma rho <=
      capturedTubeBoxDimensionalConstant *
        (((rho / sigma : NNReal) : ENNReal) ^ (2 : Real)) := by
  have hshort :
      ((shortWidthFactor sigma rho : NNReal) : ENNReal) <=
        (5 : ENNReal) * ((rho / sigma : NNReal) : ENNReal) := by
    exact_mod_cast shortWidthFactor_le_five_mul_scaleRatio hsigma hSigmaRho
  have hlong :
      ((longWidthFactor rho : NNReal) : ENNReal) <= 49 := by
    exact_mod_cast longWidthFactor_le_49 hRhoOne
  calc
    capturedTubeBoxLoss sigma rho <=
        (288 : ENNReal) ^ 3 * 49 *
          ((5 : ENNReal) * ((rho / sigma : NNReal) : ENNReal)) ^ 2 := by
      unfold capturedTubeBoxLoss
      gcongr
    _ = capturedTubeBoxDimensionalConstant *
        (((rho / sigma : NNReal) : ENNReal) ^ (2 : Real)) := by
      rw [capturedTubeBoxDimensionalConstant, ENNReal.rpow_two]
      ring

/-! ## Actual finite-family loss -/

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The actual fiber maximum is bounded by the number of active fine
tubes. -/
theorem fiberDeltaMax_le_activeFine_card (S : StickyScaleCover fine rho) :
    fiberDeltaMax S <= (S.activeFine.card : ENNReal) := by
  apply fiberDeltaMax_le S
  intro k hk
  calc
    maximalConcentration (S.fiberFamily k) <=
        (Fintype.card {i // i ∈ S.fiber k} : ENNReal) :=
      maximalConcentration_le_card (S.fiberFamily k)
    _ = (S.fiber k).card := by
      exact_mod_cast Fintype.card_coe (S.fiber k)
    _ <= S.activeFine.card := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

/-- Surjectivity of the actual parent map bounds active parents by active
children. -/
theorem activeCoarse_card_le_activeFine_card (S : StickyScaleCover fine rho) :
    S.activeCoarse.card <= S.activeFine.card := by
  apply Finset.card_le_card_of_surjOn S.parent
  intro k hk
  obtain ⟨i, hi, hparent⟩ := S.parent_surjective k hk
  exact ⟨i, hi, hparent⟩

end StickyScaleCover

/-- The raw constant furnished by the actual finite family and the
dimension-three captured-box estimate. -/
def actualLocalLossConstant (iota : Type*) [Fintype iota] : ENNReal :=
  (Fintype.card iota : ENNReal) * capturedTubeBoxDimensionalConstant

/-- The strict-localization constant is normalized to be at least one, so
the reflexive exact-node case is included without a nonemptiness assumption
on the original index type. -/
def actualStrictLocalizationConstant (iota : Type*) [Fintype iota] : ENNReal :=
  max 1 (actualLocalLossConstant iota)

theorem one_le_actualStrictLocalizationConstant
    (iota : Type*) [Fintype iota] :
    1 <= actualStrictLocalizationConstant iota :=
  le_max_left _ _

theorem actualLocalLossConstant_le_actualStrictLocalizationConstant
    (iota : Type*) [Fintype iota] :
    actualLocalLossConstant iota <= actualStrictLocalizationConstant iota :=
  le_max_right _ _

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- Every interval fiber maximum is bounded uniformly by the cardinality of
the original fine family. -/
theorem interval_fiberDeltaMax_le_original_card
    (C : CoherentStickyMultiscaleCover fine)
    {sigma rho : NNReal} (hdeltaSigma : delta <= sigma)
    (hSigmaRho : sigma <= rho) (hRhoOne : rho <= 1) :
    fiberDeltaMax
        (C.intervalScaleCover sigma rho hdeltaSigma hSigmaRho hRhoOne) <=
      (Fintype.card iota : ENNReal) := by
  let B := C.base.cover sigma hdeltaSigma (hSigmaRho.trans hRhoOne)
  let I := C.intervalScaleCover sigma rho hdeltaSigma hSigmaRho hRhoOne
  calc
    fiberDeltaMax I <= (I.activeFine.card : ENNReal) :=
      StickyScaleCover.fiberDeltaMax_le_activeFine_card I
    _ = (B.activeCoarse.card : ENNReal) := by rfl
    _ <= (B.activeFine.card : ENNReal) := by
      exact_mod_cast StickyScaleCover.activeCoarse_card_le_activeFine_card B
    _ <= (Fintype.card iota : ENNReal) := by
      exact_mod_cast Finset.card_le_univ B.activeFine

variable {depth : Nat}
  (C : CoherentStickyMultiscaleCover fine)
  (S : FiniteScaleSequence delta depth)

/-- The integrated local geometry has a completely automatic raw loss
bound.  This statement is valid even at equal scales. -/
theorem actualLocalLoss_le_constant_mul_scaleRatio_sq
    (tau_pos : forall m, 0 < S.tau m)
    (m : Fin depth) {sigma rho : NNReal}
    (hTauSigma : S.tau m <= sigma) (hSigmaRho : sigma <= rho)
    (hRhoOne : rho <= 1) :
    let D :=
      FamilyStickyScaleChainCoherentLocalGeometryProducerV1.CoherentIntervalLocalizationGeometry.ofActualLocalGeometry
        C S tau_pos
    D.massLoss m sigma rho * D.bodyLoss m sigma rho <=
      actualLocalLossConstant iota *
        (((rho / sigma : NNReal) : ENNReal) ^ (2 : Real)) := by
  dsimp only
  rw [FamilyStickyScaleChainCoherentLocalGeometryProducerV1.CoherentIntervalLocalizationGeometry.ofActualLocalGeometry_bodyLoss]
  have hsigmaPos : 0 < sigma := (tau_pos m).trans_le hTauSigma
  let I := C.intervalScaleCover sigma rho
    ((S.delta_le_tau m).trans hTauSigma) hSigmaRho hRhoOne
  have hmass :
      FamilyStickyScaleChainCoherentParentFiberMassProducerV1.CoherentIntervalLocalizationGeometry.coherentActualParentFiberMassLoss
          C S m sigma rho <= (Fintype.card iota : ENNReal) := by
    rw [FamilyStickyScaleChainCoherentParentFiberMassProducerV1.CoherentIntervalLocalizationGeometry.coherentActualParentFiberMassLoss_eq
      C S m sigma rho hTauSigma hSigmaRho hRhoOne]
    exact (actualParentFiberMassLoss_le_fiberDeltaMax I).trans
      (interval_fiberDeltaMax_le_original_card C
        ((S.delta_le_tau m).trans hTauSigma) hSigmaRho hRhoOne)
  have hbody :=
    capturedTubeBoxLoss_le_dimensionalConstant_mul_scaleRatio_sq
      hsigmaPos hSigmaRho hRhoOne
  calc
    FamilyStickyScaleChainCoherentParentFiberMassProducerV1.CoherentIntervalLocalizationGeometry.coherentActualParentFiberMassLoss
          C S m sigma rho * capturedTubeBoxLoss sigma rho <=
      (Fintype.card iota : ENNReal) *
        (capturedTubeBoxDimensionalConstant *
          (((rho / sigma : NNReal) : ENNReal) ^ (2 : Real))) :=
      mul_le_mul' hmass hbody
    _ = actualLocalLossConstant iota *
        (((rho / sigma : NNReal) : ENNReal) ^ (2 : Real)) := by
      rw [actualLocalLossConstant]
      ac_rfl

/-- For every exponent at least two, the same automatic estimate has the
matching scale-ratio power, retaining the explicit constant. -/
theorem actualLocalLoss_le_strictConstant_mul_scaleRatio_rpow
    (tau_pos : forall m, 0 < S.tau m)
    {exponent : Real} (hTwoExponent : (2 : Real) <= exponent)
    (m : Fin depth) {sigma rho : NNReal}
    (hTauSigma : S.tau m <= sigma) (hSigmaRho : sigma <= rho)
    (hRhoOne : rho <= 1) :
    let D :=
      FamilyStickyScaleChainCoherentLocalGeometryProducerV1.CoherentIntervalLocalizationGeometry.ofActualLocalGeometry
        C S tau_pos
    D.massLoss m sigma rho * D.bodyLoss m sigma rho <=
      actualStrictLocalizationConstant iota *
        (((rho / sigma : NNReal) : ENNReal) ^ exponent) := by
  dsimp only
  have hsigmaPos : 0 < sigma := (tau_pos m).trans_le hTauSigma
  have hratioNN : 1 <= rho / sigma :=
    one_le_scaleRatio hsigmaPos hSigmaRho
  have hratio : (1 : ENNReal) <=
      ((rho / sigma : NNReal) : ENNReal) := by
    exact_mod_cast hratioNN
  calc
    (FamilyStickyScaleChainCoherentLocalGeometryProducerV1.CoherentIntervalLocalizationGeometry.ofActualLocalGeometry
        C S tau_pos).massLoss m sigma rho *
        (FamilyStickyScaleChainCoherentLocalGeometryProducerV1.CoherentIntervalLocalizationGeometry.ofActualLocalGeometry
          C S tau_pos).bodyLoss m sigma rho <=
      actualLocalLossConstant iota *
        (((rho / sigma : NNReal) : ENNReal) ^ (2 : Real)) :=
      actualLocalLoss_le_constant_mul_scaleRatio_sq C S tau_pos m
        hTauSigma hSigmaRho hRhoOne
    _ <= actualStrictLocalizationConstant iota *
        (((rho / sigma : NNReal) : ENNReal) ^ exponent) := by
      exact mul_le_mul'
        (actualLocalLossConstant_le_actualStrictLocalizationConstant iota)
        (ENNReal.rpow_le_rpow_of_exponent_le hratio hTwoExponent)

/-! ## Constant-bearing tree localization -/

variable {epsilon : Real} {eta : Nat -> Real} {stage : Nat}
  {S : FiniteScaleSequence delta depth}

/-- Strict localization with an explicit multiplicative constant.  It asks
for an estimate only when the located node is genuinely below the input
scale; the exact-node case is handled reflexively. -/
structure StrictConstantLocatedCoarseValueLocalization
    (A : ActualIntervalCovers S)
    (R : IntervalRootedRefinementScaleTree S)
    (K : ENNReal) : Prop where
  localized_le : forall m rho, S.IsBuffered epsilon m rho ->
    R.tree.scale m (R.tree.locate m rho) < rho ->
      A.coarseValueAt m
          (R.tree.scale m (R.tree.locate m rho)) <=
        K *
          (((rho / R.tree.scale m (R.tree.locate m rho) : NNReal) : ENNReal) ^
            eta stage) * A.coarseValueAt m rho

/-- Cancellation of the finite positive scale-ratio power retains exactly
the localization constant. -/
theorem splitThreshold_le_constant_mul_of_located_coarseValue
    (A : ActualIntervalCovers S) (m : Fin depth)
    (sigma rho : NNReal)
    (hsigma : 0 < sigma) (hrho : 0 < rho)
    (heta : 0 <= eta stage) (K : ENNReal)
    (hnode : splitThreshold S eta stage m sigma <=
      A.coarseValueAt m sigma)
    (hlocalize : A.coarseValueAt m sigma <=
      K * (((rho / sigma : NNReal) : ENNReal) ^ eta stage) *
        A.coarseValueAt m rho) :
    splitThreshold S eta stage m rho <=
      K * A.coarseValueAt m rho := by
  let q : ENNReal :=
    (((rho / sigma : NNReal) : ENNReal) ^ eta stage)
  have hratio_pos : 0 < rho / sigma := div_pos hrho hsigma
  have hq0 : q ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hratio_pos)
      ENNReal.coe_ne_top).ne'
  have hqTop : q ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg heta ENNReal.coe_ne_top
  have hmul : q * splitThreshold S eta stage m rho <=
      q * (K * A.coarseValueAt m rho) := by
    rw [<- splitThreshold_factorization m sigma rho hsigma hrho heta]
    calc
      splitThreshold S eta stage m sigma <=
          A.coarseValueAt m sigma := hnode
      _ <= K * q * A.coarseValueAt m rho := hlocalize
      _ = q * (K * A.coarseValueAt m rho) := by ac_rfl
  exact (ENNReal.mul_le_mul_iff_right hq0 hqTop).1 hmul

namespace VerifiedTreeNodeLowerBounds

variable {A : ActualIntervalCovers S}
  {R : IntervalRootedRefinementScaleTree S}
  {K : ENNReal}

/-- Finite node checks plus strict constant-bearing localization give the
strongest unconditional continuous-scale lower bound: the constant remains
in front of the actual coarse value. -/
theorem buffered_lower_with_constant
    (V : VerifiedTreeNodeLowerBounds
      (epsilon := epsilon) (eta := eta) (stage := stage) A R)
    (L : StrictConstantLocatedCoarseValueLocalization
      (epsilon := epsilon) (eta := eta) (stage := stage) A R K)
    (hK : 1 <= K)
    (heta : 0 <= eta stage) (heta_epsilon : eta stage <= epsilon)
    (m : Fin depth) (hlarge : ¬ S.IsLarge epsilon m)
    (rho : NNReal) (hrho : S.IsBuffered epsilon m rho) :
    splitThreshold S eta stage m rho <= K * A.coarseValueAt m rho := by
  have hepsilon : 0 <= epsilon := heta.trans heta_epsilon
  let sigma : NNReal := R.tree.scale m (R.tree.locate m rho)
  have hsigma := R.located_scale_mem_interval hepsilon m rho hrho
  have hsigmaPos : 0 < sigma := (R.tau_pos m).trans_le hsigma.1
  have hrhoPos : 0 < rho := hsigmaPos.trans_le hsigma.2
  rcases lt_or_eq_of_le hsigma.2 with hstrict | heq
  · exact splitThreshold_le_constant_mul_of_located_coarseValue
      A m sigma rho hsigmaPos hrhoPos heta K
      (V.checked m hlarge (R.tree.locate m rho))
      (L.localized_le m rho hrho hstrict)
  · have heq' : sigma = rho := by simpa [sigma] using heq
    rw [<- heq']
    calc
      splitThreshold S eta stage m sigma <= A.coarseValueAt m sigma :=
        V.checked m hlarge (R.tree.locate m rho)
      _ = 1 * A.coarseValueAt m sigma := by simp
      _ <= K * A.coarseValueAt m sigma := mul_le_mul' hK le_rfl

/-- Equivalently, no buffered scale is bad after multiplying the actual
coarse value by the unavoidable explicit constant. -/
theorem terminal_noConstantBad
    (V : VerifiedTreeNodeLowerBounds
      (epsilon := epsilon) (eta := eta) (stage := stage) A R)
    (L : StrictConstantLocatedCoarseValueLocalization
      (epsilon := epsilon) (eta := eta) (stage := stage) A R K)
    (hK : 1 <= K)
    (heta : 0 <= eta stage) (heta_epsilon : eta stage <= epsilon) :
    forall m, ¬ S.IsLarge epsilon m ->
      ¬ (exists rho, S.IsBuffered epsilon m rho ∧
        K * A.coarseValueAt m rho < splitThreshold S eta stage m rho) := by
  intro m hlarge
  rintro ⟨rho, hrho, hstrict⟩
  exact (not_lt_of_ge
    (FamilyStickyScaleChainActualStrictLossWithConstantV1.VerifiedTreeNodeLowerBounds.buffered_lower_with_constant V L hK heta heta_epsilon
      m hlarge rho hrho)) hstrict

end VerifiedTreeNodeLowerBounds

namespace CoherentIntervalLocalizationGeometry

variable {C : CoherentStickyMultiscaleCover fine}
  {R : IntervalRootedRefinementScaleTree S}

/-- Actual parent-fiber and captured-box geometry automatically produce the
strict constant-bearing localization interface for every exponent at least
two. -/
theorem toActualStrictConstantLocatedCoarseValueLocalization
    (tau_pos : forall m, 0 < S.tau m)
    (hTwoEta : (2 : Real) <= eta stage)
    (heta_epsilon : eta stage <= epsilon) :
    StrictConstantLocatedCoarseValueLocalization
      (epsilon := epsilon) (eta := eta) (stage := stage)
      (C.toActualIntervalCovers S) R
      (actualStrictLocalizationConstant iota) where
  localized_le := by
    intro m rho hrho hstrict
    have heta : 0 <= eta stage := (by norm_num : (0 : Real) <= 2).trans hTwoEta
    have hepsilon : 0 <= epsilon := heta.trans heta_epsilon
    let sigma : NNReal := R.tree.scale m (R.tree.locate m rho)
    have hsigma := R.located_scale_mem_interval hepsilon m rho hrho
    have hrhoOne := le_one_of_isBuffered hepsilon m rho hrho
    let D :=
      FamilyStickyScaleChainCoherentLocalGeometryProducerV1.CoherentIntervalLocalizationGeometry.ofActualLocalGeometry
        C S tau_pos
    have hgeometry :=
      toActualIntervalCovers_coarseValueAt_le_of_nestedGeometry C S m
        sigma rho hsigma.1 hsigma.2 hrhoOne
        (D.massLoss m sigma rho) (D.bodyLoss m sigma rho)
        (D.parentFiberMass m sigma rho hsigma.1 hsigma.2 hrhoOne)
        (D.capturingThickening m sigma rho hsigma.1 hsigma.2 hrhoOne)
    have hloss := actualLocalLoss_le_strictConstant_mul_scaleRatio_rpow
      C S tau_pos hTwoEta m hsigma.1 hsigma.2 hrhoOne
    exact hgeometry.trans (mul_le_mul' hloss le_rfl)

/-- The concrete finite-tree conclusion obtained from the actual local
geometry and finite node checks. -/
theorem actual_buffered_lower_with_constant
    (tau_pos : forall m, 0 < S.tau m)
    (V : VerifiedTreeNodeLowerBounds
      (epsilon := epsilon) (eta := eta) (stage := stage)
      (C.toActualIntervalCovers S) R)
    (hTwoEta : (2 : Real) <= eta stage)
    (heta_epsilon : eta stage <= epsilon)
    (m : Fin depth) (hlarge : ¬ S.IsLarge epsilon m)
    (rho : NNReal) (hrho : S.IsBuffered epsilon m rho) :
    splitThreshold S eta stage m rho <=
      actualStrictLocalizationConstant iota *
        (C.toActualIntervalCovers S).coarseValueAt m rho := by
  have heta : 0 <= eta stage := (by norm_num : (0 : Real) <= 2).trans hTwoEta
  exact FamilyStickyScaleChainActualStrictLossWithConstantV1.VerifiedTreeNodeLowerBounds.buffered_lower_with_constant V
    (toActualStrictConstantLocatedCoarseValueLocalization
      (C := C) (R := R) tau_pos hTwoEta heta_epsilon)
    (one_le_actualStrictLocalizationConstant iota)
    heta heta_epsilon m hlarge rho hrho

/-- The corresponding honest terminal statement excludes precisely the
constant-adjusted bad-scale predicate. -/
theorem actual_terminal_noConstantBad
    (tau_pos : forall m, 0 < S.tau m)
    (V : VerifiedTreeNodeLowerBounds
      (epsilon := epsilon) (eta := eta) (stage := stage)
      (C.toActualIntervalCovers S) R)
    (hTwoEta : (2 : Real) <= eta stage)
    (heta_epsilon : eta stage <= epsilon) :
    forall m, ¬ S.IsLarge epsilon m ->
      ¬ (exists rho, S.IsBuffered epsilon m rho ∧
        actualStrictLocalizationConstant iota *
            (C.toActualIntervalCovers S).coarseValueAt m rho <
          splitThreshold S eta stage m rho) := by
  have heta : 0 <= eta stage := (by norm_num : (0 : Real) <= 2).trans hTwoEta
  exact FamilyStickyScaleChainActualStrictLossWithConstantV1.VerifiedTreeNodeLowerBounds.terminal_noConstantBad V
    (toActualStrictConstantLocatedCoarseValueLocalization
      (C := C) (R := R) tau_pos hTwoEta heta_epsilon)
    (one_le_actualStrictLocalizationConstant iota)
    heta heta_epsilon

end CoherentIntervalLocalizationGeometry

/-! ## The unconditional exponent-gap endpoint -/

/-- Actual captured-box geometry carries the fixed quadratic power.  This
strict interface records that power without pretending that it can be
absorbed by the usually much smaller stopping exponent. -/
structure StrictQuadraticLocatedCoarseValueLocalization
    (A : ActualIntervalCovers S)
    (R : IntervalRootedRefinementScaleTree S)
    (K : ENNReal) : Prop where
  localized_le : forall m rho, S.IsBuffered epsilon m rho ->
    R.tree.scale m (R.tree.locate m rho) < rho ->
      A.coarseValueAt m
          (R.tree.scale m (R.tree.locate m rho)) <=
        K *
          (((rho / R.tree.scale m (R.tree.locate m rho) : NNReal) : ENNReal) ^
            (2 : Real)) * A.coarseValueAt m rho

/-- Cancelling the threshold power from a quadratic localization leaves the
exact exponent gap `2 - eta stage`. -/
theorem splitThreshold_le_constant_mul_scaleRatio_gap_of_located_coarseValue
    (A : ActualIntervalCovers S) (m : Fin depth)
    (sigma rho : NNReal)
    (hsigma : 0 < sigma) (hrho : 0 < rho)
    (heta : 0 <= eta stage) (K : ENNReal)
    (hnode : splitThreshold S eta stage m sigma <=
      A.coarseValueAt m sigma)
    (hlocalize : A.coarseValueAt m sigma <=
      K * (((rho / sigma : NNReal) : ENNReal) ^ (2 : Real)) *
        A.coarseValueAt m rho) :
    splitThreshold S eta stage m rho <=
      K * (((rho / sigma : NNReal) : ENNReal) ^
        ((2 : Real) - eta stage)) * A.coarseValueAt m rho := by
  let x : ENNReal := ((rho / sigma : NNReal) : ENNReal)
  let q : ENNReal := x ^ eta stage
  have hratioPos : 0 < rho / sigma := div_pos hrho hsigma
  have hx0 : x ≠ 0 := ENNReal.coe_ne_zero.mpr hratioPos.ne'
  have hxTop : x ≠ ∞ := ENNReal.coe_ne_top
  have hq0 : q ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hratioPos) hxTop).ne'
  have hqTop : q ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg heta hxTop
  have hpow : x ^ (2 : Real) =
      q * x ^ ((2 : Real) - eta stage) := by
    calc
      x ^ (2 : Real) =
          x ^ (eta stage + ((2 : Real) - eta stage)) := by congr 1; ring
      _ = x ^ eta stage * x ^ ((2 : Real) - eta stage) :=
        ENNReal.rpow_add (eta stage) ((2 : Real) - eta stage) hx0 hxTop
      _ = q * x ^ ((2 : Real) - eta stage) := by rfl
  have hmul : q * splitThreshold S eta stage m rho <=
      q * (K * x ^ ((2 : Real) - eta stage) *
        A.coarseValueAt m rho) := by
    rw [<- splitThreshold_factorization m sigma rho hsigma hrho heta]
    calc
      splitThreshold S eta stage m sigma <=
          A.coarseValueAt m sigma := hnode
      _ <= K * x ^ (2 : Real) * A.coarseValueAt m rho := by
        simpa [x] using hlocalize
      _ = q * (K * x ^ ((2 : Real) - eta stage) *
          A.coarseValueAt m rho) := by rw [hpow]; ac_rfl
  exact (ENNReal.mul_le_mul_iff_right hq0 hqTop).1 hmul

namespace VerifiedTreeNodeLowerBounds

variable {A : ActualIntervalCovers S}
  {R : IntervalRootedRefinementScaleTree S}
  {K : ENNReal}

/-- This is the strongest continuous-scale threshold estimate supplied by
quadratic captured-box localization without a scale-separation input. -/
theorem buffered_lower_with_exponent_gap
    (V : VerifiedTreeNodeLowerBounds
      (epsilon := epsilon) (eta := eta) (stage := stage) A R)
    (L : StrictQuadraticLocatedCoarseValueLocalization
      (epsilon := epsilon) A R K)
    (hK : 1 <= K)
    (heta : 0 <= eta stage) (heta_epsilon : eta stage <= epsilon)
    (m : Fin depth) (hlarge : ¬ S.IsLarge epsilon m)
    (rho : NNReal) (hrho : S.IsBuffered epsilon m rho) :
    splitThreshold S eta stage m rho <=
      K *
        (((rho / R.tree.scale m (R.tree.locate m rho) : NNReal) : ENNReal) ^
          ((2 : Real) - eta stage)) * A.coarseValueAt m rho := by
  have hepsilon : 0 <= epsilon := heta.trans heta_epsilon
  let sigma : NNReal := R.tree.scale m (R.tree.locate m rho)
  have hsigma := R.located_scale_mem_interval hepsilon m rho hrho
  have hsigmaPos : 0 < sigma := (R.tau_pos m).trans_le hsigma.1
  have hrhoPos : 0 < rho := hsigmaPos.trans_le hsigma.2
  rcases lt_or_eq_of_le hsigma.2 with hstrict | heq
  · exact
      splitThreshold_le_constant_mul_scaleRatio_gap_of_located_coarseValue
        A m sigma rho hsigmaPos hrhoPos heta K
        (V.checked m hlarge (R.tree.locate m rho))
        (L.localized_le m rho hrho hstrict)
  · have hnodeRho := V.checked m hlarge (R.tree.locate m rho)
    rw [heq] at hnodeRho
    have hratio :
        ((rho / R.tree.scale m (R.tree.locate m rho) : NNReal) : ENNReal) =
          1 := by rw [heq]; simp [div_self hrhoPos.ne']
    rw [hratio, ENNReal.one_rpow]
    calc
      splitThreshold S eta stage m rho <= A.coarseValueAt m rho := hnodeRho
      _ = 1 * A.coarseValueAt m rho := by simp
      _ <= K * A.coarseValueAt m rho := mul_le_mul' hK le_rfl
      _ = K * 1 * A.coarseValueAt m rho := by simp

/-- The exact terminal consequence excludes badness only after retaining
both the dimensional constant and the located-scale exponent gap. -/
theorem terminal_noExponentGapBad
    (V : VerifiedTreeNodeLowerBounds
      (epsilon := epsilon) (eta := eta) (stage := stage) A R)
    (L : StrictQuadraticLocatedCoarseValueLocalization
      (epsilon := epsilon) A R K)
    (hK : 1 <= K)
    (heta : 0 <= eta stage) (heta_epsilon : eta stage <= epsilon) :
    forall m, ¬ S.IsLarge epsilon m ->
      ¬ (exists rho, S.IsBuffered epsilon m rho ∧
        K *
            (((rho / R.tree.scale m (R.tree.locate m rho) : NNReal) : ENNReal) ^
              ((2 : Real) - eta stage)) * A.coarseValueAt m rho <
          splitThreshold S eta stage m rho) := by
  intro m hlarge
  rintro ⟨rho, hrho, hstrict⟩
  exact (not_lt_of_ge
    (FamilyStickyScaleChainActualStrictLossWithConstantV1.VerifiedTreeNodeLowerBounds.buffered_lower_with_exponent_gap
      V L hK heta heta_epsilon m hlarge rho hrho)) hstrict

end VerifiedTreeNodeLowerBounds

namespace CoherentIntervalLocalizationGeometry

variable {C : CoherentStickyMultiscaleCover fine}
  {R : IntervalRootedRefinementScaleTree S}

/-- The actual finite-family and captured-box geometry produce quadratic
strict localization with no loss callback and no relation between `eta` and
two. -/
theorem toActualStrictQuadraticLocatedCoarseValueLocalization
    (tau_pos : forall m, 0 < S.tau m)
    (hepsilon : 0 <= epsilon) :
    StrictQuadraticLocatedCoarseValueLocalization
      (epsilon := epsilon) (C.toActualIntervalCovers S) R
      (actualStrictLocalizationConstant iota) where
  localized_le := by
    intro m rho hrho hstrict
    let sigma : NNReal := R.tree.scale m (R.tree.locate m rho)
    have hsigma := R.located_scale_mem_interval hepsilon m rho hrho
    have hrhoOne := le_one_of_isBuffered hepsilon m rho hrho
    let D :=
      FamilyStickyScaleChainCoherentLocalGeometryProducerV1.CoherentIntervalLocalizationGeometry.ofActualLocalGeometry
        C S tau_pos
    have hgeometry :=
      toActualIntervalCovers_coarseValueAt_le_of_nestedGeometry C S m
        sigma rho hsigma.1 hsigma.2 hrhoOne
        (D.massLoss m sigma rho) (D.bodyLoss m sigma rho)
        (D.parentFiberMass m sigma rho hsigma.1 hsigma.2 hrhoOne)
        (D.capturingThickening m sigma rho hsigma.1 hsigma.2 hrhoOne)
    have hraw := actualLocalLoss_le_constant_mul_scaleRatio_sq
      C S tau_pos m hsigma.1 hsigma.2 hrhoOne
    have hloss : D.massLoss m sigma rho * D.bodyLoss m sigma rho <=
        actualStrictLocalizationConstant iota *
          (((rho / sigma : NNReal) : ENNReal) ^ (2 : Real)) :=
      hraw.trans (mul_le_mul'
        (actualLocalLossConstant_le_actualStrictLocalizationConstant iota)
        le_rfl)
    exact hgeometry.trans (mul_le_mul' hloss le_rfl)

/-- Concrete unconditional finite-tree endpoint.  Unlike the exponent-two
special case, this theorem applies in the intended small-`eta` regime. -/
theorem actual_buffered_lower_with_exponent_gap
    (tau_pos : forall m, 0 < S.tau m)
    (V : VerifiedTreeNodeLowerBounds
      (epsilon := epsilon) (eta := eta) (stage := stage)
      (C.toActualIntervalCovers S) R)
    (heta : 0 <= eta stage) (heta_epsilon : eta stage <= epsilon)
    (m : Fin depth) (hlarge : ¬ S.IsLarge epsilon m)
    (rho : NNReal) (hrho : S.IsBuffered epsilon m rho) :
    splitThreshold S eta stage m rho <=
      actualStrictLocalizationConstant iota *
        (((rho / R.tree.scale m (R.tree.locate m rho) : NNReal) : ENNReal) ^
          ((2 : Real) - eta stage)) *
        (C.toActualIntervalCovers S).coarseValueAt m rho := by
  exact FamilyStickyScaleChainActualStrictLossWithConstantV1.VerifiedTreeNodeLowerBounds.buffered_lower_with_exponent_gap V
    (toActualStrictQuadraticLocatedCoarseValueLocalization
      (C := C) (R := R) tau_pos (heta.trans heta_epsilon))
    (one_le_actualStrictLocalizationConstant iota)
    heta heta_epsilon m hlarge rho hrho

/-- Honest terminal version of the unconditional exponent-gap endpoint. -/
theorem actual_terminal_noExponentGapBad
    (tau_pos : forall m, 0 < S.tau m)
    (V : VerifiedTreeNodeLowerBounds
      (epsilon := epsilon) (eta := eta) (stage := stage)
      (C.toActualIntervalCovers S) R)
    (heta : 0 <= eta stage) (heta_epsilon : eta stage <= epsilon) :
    forall m, ¬ S.IsLarge epsilon m ->
      ¬ (exists rho, S.IsBuffered epsilon m rho ∧
        actualStrictLocalizationConstant iota *
            (((rho / R.tree.scale m (R.tree.locate m rho) : NNReal) : ENNReal) ^
              ((2 : Real) - eta stage)) *
            (C.toActualIntervalCovers S).coarseValueAt m rho <
          splitThreshold S eta stage m rho) := by
  exact FamilyStickyScaleChainActualStrictLossWithConstantV1.VerifiedTreeNodeLowerBounds.terminal_noExponentGapBad V
    (toActualStrictQuadraticLocatedCoarseValueLocalization
      (C := C) (R := R) tau_pos (heta.trans heta_epsilon))
    (one_le_actualStrictLocalizationConstant iota)
    heta heta_epsilon

end CoherentIntervalLocalizationGeometry

#print axioms capturedTubeBoxLoss_le_dimensionalConstant_mul_scaleRatio_sq
#print axioms StickyScaleCover.fiberDeltaMax_le_activeFine_card
#print axioms interval_fiberDeltaMax_le_original_card
#print axioms actualLocalLoss_le_constant_mul_scaleRatio_sq
#print axioms actualLocalLoss_le_strictConstant_mul_scaleRatio_rpow
#print axioms splitThreshold_le_constant_mul_of_located_coarseValue
#print axioms VerifiedTreeNodeLowerBounds.buffered_lower_with_constant
#print axioms VerifiedTreeNodeLowerBounds.terminal_noConstantBad
#print axioms CoherentIntervalLocalizationGeometry.toActualStrictConstantLocatedCoarseValueLocalization
#print axioms CoherentIntervalLocalizationGeometry.actual_buffered_lower_with_constant
#print axioms CoherentIntervalLocalizationGeometry.actual_terminal_noConstantBad
#print axioms splitThreshold_le_constant_mul_scaleRatio_gap_of_located_coarseValue
#print axioms VerifiedTreeNodeLowerBounds.buffered_lower_with_exponent_gap
#print axioms VerifiedTreeNodeLowerBounds.terminal_noExponentGapBad
#print axioms CoherentIntervalLocalizationGeometry.toActualStrictQuadraticLocatedCoarseValueLocalization
#print axioms CoherentIntervalLocalizationGeometry.actual_buffered_lower_with_exponent_gap
#print axioms CoherentIntervalLocalizationGeometry.actual_terminal_noExponentGapBad

end
end FamilyStickyScaleChainActualStrictLossWithConstantV1
