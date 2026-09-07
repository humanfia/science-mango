import Family8Grounding.Family8EndpointIdentityFirstCrossingImpossibleV1
import Family8Grounding.Family8FirstParentwiseNormalizedCrossingWitnessV1
import Family8Grounding.Family8ParentwiseBadParentFactorReplacementV1
import Family8Grounding.Family8ParentwiseNormalizedLongIntervalCoreSelectorV1
import Mathlib.Tactic

/-!
# The endpoint identity cover has no literal-parent FirstCrossing branch

The parentwise finite selector returns one actual active parent whose normalized
Frostman constant lies strictly below the stage barrier.  This is weaker than a
strict upper bound for the maximum over all parents, so it cannot be repackaged
as the older `FirstActualNormalizedCrossingWitness`.

For the endpoint identity cover the selected literal fibre has cardinality at
most one.  Its own low `CFAt` certificate gives Frostman control on that same
fibre, which is exactly what the scale-ratio contradiction needs.  Thus the
argument stays on the selected parent throughout and never invokes `CFMax`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8EndpointIdentityParentwiseFirstCrossingImpossibleV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalLowerBufferedScaleV4
open Family8EndpointIdentityCoreSelectorV2
open Family8EndpointIdentityFirstCrossingImpossibleV1
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCFDividingWitnessParentwiseFiniteSelectionV1.CoherentStickyMultiscaleCover
open Family8NormalizedCrossingFrozenComparableAdapterV3
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8ParameterLadderV1
open Family8ParentwiseBadParentFactorReplacementV1
open Family8ParentwiseNormalizedLongIntervalCoreSelectorV1
open Family8StickyFiberFrostmanParentCardScaleV3
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

/-- Local compatibility name for the unique positive witness owned by
`Family8FirstParentwiseNormalizedCrossingWitnessV1`. -/
abbrev FirstParentwiseNormalizedCrossingWitness
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (eta : Nat -> Real) (N : Nat) :=
  Family8FirstParentwiseNormalizedCrossingWitnessV1.FirstParentwiseNormalizedCrossingWitness
    D hD C S epsilon hepsilon eta N

namespace FirstParentwiseNormalizedCrossingWitness

/-- The not-large and buffered fields alone give the standard relative-scale
gain; no maximum-CF crossing field is involved. -/
theorem tau_div_rho_le_rpow_sq
    {D : ActualTubeDatum delta index} {hD : D.IsAdmissible}
    {C : CoherentStickyMultiscaleCover D.family}
    {S : FiniteScaleSequence delta depth}
    {epsilon : Real} {hepsilon : 0 <= epsilon}
    {eta : Nat -> Real} {N : Nat}
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) :
    S.tau W.m / W.rho <= delta ^ (epsilon ^ 2) := by
  have htau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have htheta : 0 < S.theta W.m :=
    htau.trans_le (S.tau_le_theta W.m)
  have hnotLarge := W.notLarge
  unfold FiniteScaleSequence.IsLarge at hnotLarge
  have hlong :
      (S.tau W.m : ENNReal) <=
        (delta : ENNReal) ^ epsilon * (S.theta W.m : ENNReal) :=
    le_of_not_ge hnotLarge
  have hlower :
      canonicalLowerBufferedScale (S.tau W.m) (S.theta W.m) epsilon <=
        W.rho := by
    rw [<- ENNReal.coe_le_coe,
      canonicalLowerBufferedScale_eq_lowerEndpoint htau epsilon]
    simpa only [ENNReal.coe_mul,
      ENNReal.coe_rpow_of_ne_zero (div_pos htheta htau).ne'] using
        W.buffered.1
  have hlowerPos :
      0 < canonicalLowerBufferedScale
        (S.tau W.m) (S.theta W.m) epsilon := by
    rw [canonicalLowerBufferedScale_eq_lowerEndpoint htau epsilon]
    positivity
  calc
    S.tau W.m / W.rho <=
        S.tau W.m /
          canonicalLowerBufferedScale
            (S.tau W.m) (S.theta W.m) epsilon := by
      exact div_le_div_of_nonneg_left (by positivity) hlowerPos hlower
    _ <= delta ^ (epsilon ^ 2) :=
      Family8CanonicalBufferedGlobalRelativeScaleGainV1.tau_div_canonicalLowerBufferedScale_le_rpow_sq
        hD.delta_pos (S.delta_le_tau W.m) (S.tau_le_theta W.m)
          hepsilon hlong

/-- The low `CFAt` field supplies Frostman control on the same selected fibre;
the tube-volume sandwich then yields the ratio/cardinality inequality needed
by the endpoint contradiction. -/
theorem ratio_sq_le_sixteen_mul_frostman_mul_selectedFiberCard
    {D : ActualTubeDatum delta index} {hD : D.IsAdmissible}
    {C : CoherentStickyMultiscaleCover D.family}
    {S : FiniteScaleSequence delta depth}
    {epsilon : Real} {hepsilon : 0 <= epsilon}
    {eta : Nat -> Real} {N : Nat}
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (htauHalf : S.tau W.m <= (2 : NNReal)⁻¹)
    (hrhoHalf : W.rho <= (2 : NNReal)⁻¹) :
    let U := paperBufferedIntervalCover
      D hD C S epsilon hepsilon W.m W.rho W.buffered
    (((W.rho : ENNReal) / (S.tau W.m : ENNReal)) ^ (2 : Real)) <=
      16 *
        (((W.rho / S.tau W.m : NNReal) : ENNReal) ^ eta W.stage) *
        ((U.fiber W.q.1).card : ENNReal) := by
  dsimp only
  let U := paperBufferedIntervalCover
    D hD C S epsilon hepsilon W.m W.rho W.buffered
  let frostmanC : ENNReal :=
    (((W.rho / S.tau W.m : NNReal) : ENNReal) ^ eta W.stage)
  have htau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hqFiber : (U.fiber W.q.1).Nonempty := by
    obtain ⟨i, hi, hparent⟩ := U.parent_surjective W.q.1 W.q.2
    exact ⟨i, (U.mem_fiber i W.q.1).2 ⟨hi, hparent⟩⟩
  have hIn : IsFrostmanIn frostmanC
      (U.fiberFamily W.q.1) (U.activeCoarseFamily W.q) := by
    simpa only [U, frostmanC] using
      badParent_isFrostmanIn U htau W.q W.strict_crossing
  have hF : IsFrostmanOn frostmanC
      (bufferedLowerFamily D C S W.m).bodyFamily
      (U.fiber W.q.1) (U.coarse.tubes W.q.1).body := by
    exact (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
      (bufferedLowerFamily D C S W.m).bodyFamily
        (U.fiber W.q.1) (U.coarse.tubes W.q.1).body).mpr hIn
  have hparent : volume (U.coarse.tubes W.q.1).carrier <=
      frostmanC * ((U.fiber W.q.1).card : ENNReal) *
        (8 * (S.tau W.m : ENNReal) ^ 2) :=
    parentVolume_le_frostman_mul_fiberCardScale
      U htau htauHalf W.q.1 hqFiber hF
  have hraw : (W.rho : ENNReal) ^ 2 / 2 <=
      frostmanC * ((U.fiber W.q.1).card : ENNReal) *
        (8 * (S.tau W.m : ENNReal) ^ 2) :=
    ((U.coarse.tubes W.q.1).half_sq_le_volume_of_le_half hrhoHalf).trans
      hparent
  have hscaled : (W.rho : ENNReal) ^ 2 <=
      (16 * frostmanC * ((U.fiber W.q.1).card : ENNReal)) *
        (S.tau W.m : ENNReal) ^ 2 := by
    calc
      (W.rho : ENNReal) ^ 2 =
          2 * ((W.rho : ENNReal) ^ 2 / 2) := by
        calc
          (W.rho : ENNReal) ^ 2 =
              ((W.rho : ENNReal) ^ 2 / 2) * 2 :=
            (ENNReal.div_mul_cancel (by norm_num) (by norm_num)).symm
          _ = 2 * ((W.rho : ENNReal) ^ 2 / 2) := mul_comm _ _
      _ <= 2 * (frostmanC * ((U.fiber W.q.1).card : ENNReal) *
          (8 * (S.tau W.m : ENNReal) ^ 2)) :=
        mul_le_mul' le_rfl hraw
      _ = (16 * frostmanC * ((U.fiber W.q.1).card : ENNReal)) *
          (S.tau W.m : ENNReal) ^ 2 := by ring
  rw [ENNReal.div_rpow_of_nonneg _ _ (by norm_num)]
  rw [ENNReal.rpow_two]
  rw [ENNReal.rpow_two]
  apply (ENNReal.div_le_iff_le_mul
    (Or.inl (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr htau.ne')))
    (Or.inl (ENNReal.pow_ne_top ENNReal.coe_ne_top))).2
  simpa only [U, frostmanC, mul_assoc] using hscaled

end FirstParentwiseNormalizedCrossingWitness

/-- The endpoint identity parent map is injective on the exact selected
buffered cover, so the literal crossing fibre has at most one member. -/
theorem endpointIdentity_selectedParent_fiber_card_le_one
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (eta : Nat -> Real) (N : Nat)
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD (identityRadiusCoherentCover D.family)
        S epsilon hepsilon eta N) :
    let U := paperBufferedIntervalCover D hD
      (identityRadiusCoherentCover D.family) S epsilon hepsilon
        W.m W.rho W.buffered
    (U.fiber W.q.1).card <= 1 := by
  dsimp only
  classical
  let U := paperBufferedIntervalCover D hD
    (identityRadiusCoherentCover D.family) S epsilon hepsilon
      W.m W.rho W.buffered
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hiData := (U.mem_fiber i W.q.1).mp hi
  have hjData := (U.mem_fiber j W.q.1).mp hj
  have hparent : U.parent i = U.parent j := hiData.2.trans hjData.2.symm
  change i = j at hparent
  exact hparent

/-- A literal-parent first crossing on the full-refinement endpoint identity
cover contradicts the same explicit small-scale threshold as the older
maximum-based endpoint argument.  Positive source mass is unnecessary here:
the witness already stores an active parent. -/
theorem endpointIdentity_fullRefinement_not_firstParentwiseCrossing
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hsmall : delta <=
      endpointIdentityFirstCrossingImpossibleThreshold P) :
    let E := fullRefinementDatum D
    let hE := fullRefinementDatum_isAdmissible hD
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    ¬ Nonempty (FirstParentwiseNormalizedCrossingWitness
      E hE C S P.epsilon P.epsilon_pos.le P.eta P.N) := by
  dsimp only
  rintro ⟨W⟩
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let U := paperBufferedIntervalCover
    E hE C S P.epsilon P.epsilon_pos.le W.m W.rho W.buffered
  have hscale : S.tau W.m <= W.rho :=
    actualDatum_tau_le_of_isBuffered
      E hE S P.epsilon_pos.le W.m W.rho W.buffered
  have htau : 0 < S.tau W.m :=
    hE.delta_pos.trans_le (S.delta_le_tau W.m)
  have hrho : 0 < W.rho := htau.trans_le hscale
  have hrhoThirtyTwo : W.rho <= (1 / 32 : NNReal) :=
    bufferedRadius_le_target_of_delta_le_threshold
      S W.m W.rho (1 / 32 : NNReal) hE.delta_pos P.epsilon_pos
        W.notLarge W.buffered hsmall
  have hrhoHalf : W.rho <= (2 : NNReal)⁻¹ :=
    hrhoThirtyTwo.trans (by
      rw [<- NNReal.coe_le_coe]
      norm_num)
  have htauHalf : S.tau W.m <= (2 : NNReal)⁻¹ :=
    hscale.trans hrhoHalf
  have hcardNat : (U.fiber W.q.1).card <= 1 := by
    simpa only [U, E, C, S] using
      endpointIdentity_selectedParent_fiber_card_le_one
        E hE S P.epsilon P.epsilon_pos.le P.eta P.N W
  have hcard : ((U.fiber W.q.1).card : ENNReal) <= 1 := by
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
      16 * (R ^ P.eta W.stage) * ((U.fiber W.q.1).card : ENNReal) := by
    simpa only [R, U, E, C, S, ENNReal.coe_div htau.ne'] using
      W.ratio_sq_le_sixteen_mul_frostman_mul_selectedFiberCard
        htauHalf hrhoHalf
  have hratio : R ^ (2 : Real) <= 16 * R := by
    calc
      R ^ (2 : Real) <=
          16 * (R ^ P.eta W.stage) *
            ((U.fiber W.q.1).card : ENNReal) := hratioRaw
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
    simpa only [E, C, S] using W.tau_div_rho_le_rpow_sq
  have hdeltaPower : delta ^ (P.epsilon ^ 2) <= (1 / 32 : NNReal) :=
    delta_rpow_sq_le_target_of_le_childEndpointDeltaThreshold
      P.epsilon_pos hsmall
  have hfalse : (1 / 16 : NNReal) <= (1 / 32 : NNReal) :=
    hqLower.trans (hqGain.trans hdeltaPower)
  have hnot : ¬ ((1 / 16 : NNReal) <= (1 / 32 : NNReal)) := by
    rw [<- NNReal.coe_le_coe]
    norm_num
  exact hnot hfalse

/-- The live parentwise endpoint selector therefore lands in its faithful
LongCore branch below the explicit endpoint threshold. -/
theorem endpointIdentity_fullRefinement_parentwiseLongCore_of_small
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hsmall : delta <=
      endpointIdentityFirstCrossingImpossibleThreshold P) :
    let E := fullRefinementDatum D
    let hE := fullRefinementDatum_isAdmissible hD
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    Nonempty (ParentwiseNormalizedLongIntervalCoreWitness
      E hE C P.N P.epsilon P.epsilon_pos.le P.eta S) := by
  dsimp only
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  rcases allLarge_or_parentwiseLongIntervalCore_or_firstParentwiseCrossing
      E hE C S P with (hall | hlong) | hfirst
  · have hnotAll := endpointScaleSequence_not_allStepsLarge
      hE.delta_pos hE.delta_le_half
        (parameterLadder_epsilon_lt_one P hbeta hgamma)
    exact (hnotAll hall).elim
  · exact hlong
  · have hcross : Nonempty (FirstParentwiseNormalizedCrossingWitness
        E hE C S P.epsilon P.epsilon_pos.le P.eta P.N) :=
      Family8FirstParentwiseNormalizedCrossingWitnessV1.FirstParentwiseNormalizedCrossingWitness.nonempty_of_selector_output
        hfirst
    exact (endpointIdentity_fullRefinement_not_firstParentwiseCrossing
      D hD P hbeta hgamma hsmall hcross).elim

#print axioms
  Family8FirstParentwiseNormalizedCrossingWitnessV1.FirstParentwiseNormalizedCrossingWitness.nonempty_of_selector_output
#print axioms FirstParentwiseNormalizedCrossingWitness.tau_div_rho_le_rpow_sq
#print axioms
  FirstParentwiseNormalizedCrossingWitness.ratio_sq_le_sixteen_mul_frostman_mul_selectedFiberCard
#print axioms endpointIdentity_selectedParent_fiber_card_le_one
#print axioms endpointIdentity_fullRefinement_not_firstParentwiseCrossing
#print axioms endpointIdentity_fullRefinement_parentwiseLongCore_of_small

end
end Family8EndpointIdentityParentwiseFirstCrossingImpossibleV1
