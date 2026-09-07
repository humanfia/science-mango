import Family8Grounding.Family8EndpointFirstCrossingIdentityBufferedSingletonFiberV2
import Family8Grounding.Family8EndpointIdentityFullRefinementCoreSelectorV1
import Family8Grounding.Family8FirstCrossingActiveFiberRatioCardLowerV7
import Family8Grounding.Family8FirstCrossingBufferedRelativeScaleGainV1
import Family8Grounding.Family8NormalizedCrossingSourceTauShadingV2
import Family8Grounding.Family8StickyParentPopularCanonicalUnionV1
import FamilyStickyGrounding.FamilyStickyHierarchyEndpointNonemptyProducerV1
import FamilyStickyGrounding.FamilyStickyScaleChainChildEndpointThresholdProducerV2
import Mathlib.Tactic

/-!
# The endpoint identity cover has no small-scale FirstCrossing branch

For the radius-changed identity coherent cover, every literal buffered
interval fibre has at most one child.  The general FirstCrossing lower bound
therefore gives

`(rho / tau)^2 <= 16 * (rho / tau)^eta`.

At the endpoint scale sequence, bufferedness and non-largeness also give
`tau / rho <= delta^(epsilon^2)`.  Below one explicit positive threshold,
the latter ratio is at most `1/32`, whereas the former inequality and
`eta < 1` force it to be at least `1/16`.  Thus a nonzero full-refinement
datum has no FirstCrossing witness, and the direct endpoint selector must
return its LongCore branch.

No exact tube-volume formula is used: the dimensional constant sixteen is
the existing consequence of the proved tube-volume sandwich.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8EndpointIdentityFirstCrossingImpossibleV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8EndpointFirstCrossingIdentityBufferedSingletonFiberV2
open Family8EndpointIdentityCoreSelectorV2
open Family8EndpointIdentityFullRefinementCoreSelectorV1
open Family8FirstCrossingActiveFiberRatioCardLowerV7
open Family8FirstCrossingBufferedRelativeScaleGainV1
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCrossingFrozenComparableAdapterV3
open Family8NormalizedCrossingSourceTauShadingV2
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8StickyParentPopularCanonicalUnionV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainChildEndpointThresholdProducerV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- Injectivity of the literal identity parent gives the singleton-cardinality
bound on the original buffered cover, before active-fine restriction. -/
theorem endpointFirstCrossing_identityBufferedIntervalCover_fiber_card_le_one
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (eta : Nat -> Real) (N : Nat)
    (W : FirstActualNormalizedCrossingWitness
      D hD (identityRadiusCoherentCover D.family)
        S epsilon hepsilon eta N)
    (k : Fin (bufferedIntervalCover D hD
      (identityRadiusCoherentCover D.family) S epsilon hepsilon
        W.m W.rho W.buffered).coarseCard) :
    ((bufferedIntervalCover D hD
      (identityRadiusCoherentCover D.family) S epsilon hepsilon
        W.m W.rho W.buffered).fiber k).card <= 1 := by
  classical
  let U := bufferedIntervalCover D hD
    (identityRadiusCoherentCover D.family) S epsilon hepsilon
      W.m W.rho W.buffered
  change (U.fiber k).card <= 1
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hiData := (U.mem_fiber i k).mp hi
  have hjData := (U.mem_fiber j k).mp hj
  exact
    (endpointFirstCrossing_identityBufferedIntervalCover_parent_injective
      D hD S epsilon hepsilon eta N W)
      (hiData.2.trans hjData.2.symm)

/-- One uniform endpoint threshold supplies both `rho <= 1/2` and the strict
ratio separation needed to contradict the singleton FirstCrossing bound. -/
def endpointIdentityFirstCrossingImpossibleThreshold
    (P : ParameterLadder epsilon0 beta gamma) : NNReal :=
  childEndpointDeltaThreshold (1 / 32 : NNReal) P.epsilon

theorem endpointIdentityFirstCrossingImpossibleThreshold_pos
    (P : ParameterLadder epsilon0 beta gamma) :
    0 < endpointIdentityFirstCrossingImpossibleThreshold P := by
  exact childEndpointDeltaThreshold_pos (by norm_num) P.epsilon

/-- Below the explicit threshold, positive source mass rules out a
FirstCrossing witness on the endpoint identity cover of the full refinement. -/
theorem endpointIdentity_fullRefinement_not_firstCrossing
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hmass : D.shading.shadingMass ≠ 0)
    (hsmall : delta <=
      endpointIdentityFirstCrossingImpossibleThreshold P) :
    let E := fullRefinementDatum D
    let hE := fullRefinementDatum_isAdmissible hD
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    Not (Nonempty (FirstActualNormalizedCrossingWitness
      E hE (identityRadiusCoherentCover E.family) S
        P.epsilon P.epsilon_pos.le P.eta P.N)) := by
  dsimp only
  rintro ⟨W⟩
  let hindex : Nonempty index :=
    nonempty_of_shadingMass_pos D.shading
      (bot_lt_iff_ne_bot.mpr hmass)
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let L := sourceTauCover E C S W.m
  let U := bufferedIntervalCover E hE C S P.epsilon
    P.epsilon_pos.le W.m W.rho W.buffered
  have hfine : E.family.refinement.refined.Nonempty := by
    rw [show E.family.refinement.refined = Finset.univ by
      simpa only [E] using fullRefinementDatum_refined D]
    let i : index := Classical.choice hindex
    exact ⟨i, Finset.mem_univ i⟩
  have hLcoarse : L.activeCoarse.Nonempty :=
    FamilyStickyHierarchyEndpointNonemptyProducerV1.StickyScaleCover.activeCoarse_nonempty_of_refined_nonempty L hfine
  have hUfine : U.activeFine.Nonempty := by
    have hactive : U.activeFine = L.activeCoarse := by
      simpa only [U, L] using
        bufferedIntervalCover_activeFine E hE C S P.epsilon
          P.epsilon_pos.le W.m W.rho W.buffered
    rw [hactive]
    exact hLcoarse
  obtain ⟨k, hk⟩ :=
    FamilyStickyHierarchyEndpointNonemptyProducerV1.StickyScaleCover.activeCoarse_nonempty_of_activeFine_nonempty U hUfine
  have hscale : S.tau W.m <= W.rho :=
    actualDatum_tau_le_of_isBuffered E hE S P.epsilon_pos.le
      W.m W.rho W.buffered
  have htau : 0 < S.tau W.m :=
    hE.delta_pos.trans_le (S.delta_le_tau W.m)
  have hrho : 0 < W.rho := htau.trans_le hscale
  have hrhoThirtyTwo : W.rho <= (1 / 32 : NNReal) :=
    bufferedRadius_le_target_of_delta_le_threshold
      S W.m W.rho (1 / 32 : NNReal) hE.delta_pos P.epsilon_pos
        W.notLarge W.buffered hsmall
  have hrhoHalf : W.rho <= (2 : NNReal)⁻¹ :=
    have hconstant : (1 / 32 : NNReal) <= (2 : NNReal)⁻¹ := by
      rw [← NNReal.coe_le_coe]
      norm_num
    hrhoThirtyTwo.trans hconstant
  have htauHalf : S.tau W.m <= (2 : NNReal)⁻¹ :=
    hscale.trans hrhoHalf
  have hcardNat : (U.fiber k).card <= 1 := by
    simpa only [U, C] using
      endpointFirstCrossing_identityBufferedIntervalCover_fiber_card_le_one
        E hE S P.epsilon P.epsilon_pos.le P.eta P.N W k
  have hcard : ((U.fiber k).card : ENNReal) <= 1 := by
    exact_mod_cast hcardNat
  let R : ENNReal :=
    (W.rho : ENNReal) / (S.tau W.m : ENNReal)
  have hRoneNN : (1 : NNReal) <= W.rho / S.tau W.m :=
    (one_le_div htau).2 hscale
  have hRone : (1 : ENNReal) <= R := by
    rw [show R = ((W.rho / S.tau W.m : NNReal) : ENNReal) by
      simp only [R, ENNReal.coe_div htau.ne']]
    exact_mod_cast hRoneNN
  have hetaOne : P.eta W.stage <= 1 := by
    have hepsilonLt : P.epsilon < 1 :=
      parameterLadder_epsilon_lt_one P hbeta hgamma
    have heta := P.eta_le_epsilon_div_five W.stage
    linarith
  have hReta : R ^ P.eta W.stage <= R := by
    simpa only [ENNReal.rpow_one] using
      ENNReal.rpow_le_rpow_of_exponent_le hRone hetaOne
  have hratioRaw : R ^ (2 : Real) <=
      16 * (R ^ P.eta W.stage) * ((U.fiber k).card : ENNReal) := by
    simpa only [R, U, C, ENNReal.coe_div htau.ne'] using
      firstCrossing_ratio_sq_le_sixteen_mul_frostman_mul_fiberCard
        E hE C S P.epsilon P.epsilon_pos.le P.eta P.N W
          htauHalf hrhoHalf k hk
  have hratio : R ^ (2 : Real) <= 16 * R := by
    calc
      R ^ (2 : Real) <=
          16 * (R ^ P.eta W.stage) * ((U.fiber k).card : ENNReal) :=
        hratioRaw
      _ <= 16 * (R ^ P.eta W.stage) * 1 :=
        mul_le_mul' le_rfl hcard
      _ = 16 * (R ^ P.eta W.stage) := by rw [mul_one]
      _ <= 16 * R := mul_le_mul' le_rfl hReta
  have hratioMul : R * R <= R * 16 := by
    simpa only [ENNReal.rpow_two, pow_two, mul_comm] using hratio
  have hratioMulNN :
      (W.rho / S.tau W.m) * (W.rho / S.tau W.m) <=
        (W.rho / S.tau W.m) * (16 : NNReal) := by
    rw [<- ENNReal.coe_le_coe]
    simpa only [ENNReal.coe_mul, ENNReal.coe_ofNat, R,
      ENNReal.coe_div htau.ne'] using hratioMul
  have hRposNN : 0 < W.rho / S.tau W.m := div_pos hrho htau
  have hRleNN : W.rho / S.tau W.m <= (16 : NNReal) :=
    le_of_mul_le_mul_left hratioMulNN hRposNN
  have hqLower : (1 / 16 : NNReal) <= S.tau W.m / W.rho := by
    apply (le_div_iff₀ hrho).2
    have hrhoLe : W.rho <= 16 * S.tau W.m :=
      (div_le_iff₀ htau).1 hRleNN
    calc
      (1 / 16 : NNReal) * W.rho <=
          (1 / 16 : NNReal) * (16 * S.tau W.m) := by
        exact mul_le_mul_of_nonneg_left hrhoLe (by positivity)
      _ = S.tau W.m := by ring
  have hqGain : S.tau W.m / W.rho <= delta ^ (P.epsilon ^ 2) := by
    simpa only [E, C, S] using
      firstCrossing_tau_div_rho_le_rpow_sq
        E hE C S P.epsilon P.epsilon_pos.le P.eta P.N W
  have hdeltaPower : delta ^ (P.epsilon ^ 2) <= (1 / 32 : NNReal) :=
    delta_rpow_sq_le_target_of_le_childEndpointDeltaThreshold
      P.epsilon_pos hsmall
  have hfalse : (1 / 16 : NNReal) <= (1 / 32 : NNReal) :=
    hqLower.trans (hqGain.trans hdeltaPower)
  have hnot : ¬ ((1 / 16 : NNReal) <= (1 / 32 : NNReal)) := by
    rw [← NNReal.coe_le_coe]
    norm_num
  exact hnot hfalse

/-- The direct endpoint selector therefore returns LongCore unconditionally
on every sufficiently small nonzero-mass datum. -/
theorem endpointIdentity_fullRefinement_longCore_of_small_nonzero
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hmass : D.shading.shadingMass ≠ 0)
    (hsmall : delta <=
      endpointIdentityFirstCrossingImpossibleThreshold P) :
    let E := fullRefinementDatum D
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    Nonempty (NormalizedLongIntervalCoreWitness
      E.family (identityRadiusCoherentCover E.family)
        P.N P.epsilon P.eta S) := by
  dsimp only
  rcases endpointIdentity_fullRefinement_longCore_or_firstCrossing
      D hD P hbeta hgamma with hlong | hfirst
  · exact hlong
  · exact (endpointIdentity_fullRefinement_not_firstCrossing
      D hD P hbeta hgamma hmass hsmall hfirst).elim

#print axioms
  endpointFirstCrossing_identityBufferedIntervalCover_fiber_card_le_one
#print axioms endpointIdentity_fullRefinement_not_firstCrossing
#print axioms endpointIdentity_fullRefinement_longCore_of_small_nonzero

end

end Family8EndpointIdentityFirstCrossingImpossibleV1
