import FamilyStickyGrounding.FamilyStickyScaleChainSelectedIdentityDirectNormalizerProducerV1
import FamilyStickyGrounding.FamilyStickyScaleChainCapturingThickeningProducerCleanV2
import FamilyStickyGrounding.FamilyStickyAdjacentTestBodyGeometryV1
import FamilyStickyGrounding.FamilyStickyScaleChainActualStrictLossWithConstantV1
import FamilyStickyGrounding.FamilyStickyScaleChainFirstNonLargeAdjacentCardBudgetProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainSelectedIdentityAutomaticAllLargeProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainArbitraryRadiusInterpolationV1
open FamilyStickyScaleChainArbitraryRadiusBoundsV1
open FamilyStickyScaleChainParentNormalizerReverseProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyScaleChainSelectedIdentityDirectNormalizerProducerV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open FamilyStickyScaleChainNestedMassLocalizationV1.StickyScaleCover
open FamilyStickyAdjacentTestBodyGeometryV1
open FamilyStickyCapturedTubeBoxWidthV1
open FamilyStickyScaleChainCapturingThickeningProducerV1.StickyScaleCover
open FamilyStickyScaleChainParentFiberMassProducerV1.StickyScaleCover
open FamilyStickyScaleChainParentFiberMassToFiberDeltaV1.StickyScaleCover
open FamilyStickyScaleChainActualStrictLossWithConstantV1
open FamilyStickyScaleChainFirstNonLargeAdjacentCardBudgetProducerV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
open FamilyStickyScaleChainRootedRefinementTreeV1
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleChainFirstNonLargeRelevantNodeProducerV1
open FamilyStickyScaleChainTotalStoppingDiagnosticProducerV1
open FamilyStickyScaleChainActualSmallDeltaRecoveredEndpointV1
open FamilyStickyScaleChainActualStoppingUpstreamClosureV1
open FamilyStickyScaleChainDividingFiniteNodeProducerV1
open FamilyStickyHierarchyTerminalSourceChartBucketProducerV1
open FamilyStickyHierarchySelectedSourceNestedRestrictionV1
open FamilyStickyHierarchySelectedSourceDirectTerminalWZConsumerV1

noncomputable section

/-!
# Automatic finite all-large endpoint for the identity cover

The remaining local-geometry and discrete endpoint inputs of the direct
identity-normalizer theorem are automatic.  The only branch-specific datum is
the honest stopping certificate that every adjacent scale interval is large.

The Frostman denominator is controlled without a nonemptiness assumption on
an arbitrary test body.  Instead, for each active parent, parent surjectivity
chooses one literal child.  Common-fine-tube geometry puts that parent in the
four-radius thickening of the child body, and the captured-tube John-box bound
compares the parent volume with the full fiber volume.  The resulting constants
are explicit finite expressions; no `top`-valued cap is used.
-/

universe u

variable {delta rho : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## A finite Frostman endpoint at one actual scale -/

/-- A selected fine tube contributes one term to its literal parent fiber. -/
theorem fineTubeVolume_le_fiberFamilyVolume
    (S : StickyScaleCover fine rho) (k : Fin S.coarseCard)
    (i : iota) (hi : i ∈ S.fiber k) :
    volume (fine.tubes i).carrier <= familyVolume (S.fiberFamily k) := by
  classical
  unfold familyVolume
  have hsingle := Finset.single_le_sum
      (s := Finset.univ)
      (f := fun j : {j // j ∈ S.fiber k} =>
        volume (S.fiberFamily k j : Set Space))
      (fun _ _ => bot_le) (Finset.mem_univ (⟨i, hi⟩ : {j // j ∈ S.fiber k}))
  simpa [StickyScaleCover.fiberFamily, UniformTubeFamily.bodyFamily,
    Tube.coe_body] using hsingle

/-- One child of an active parent captures enough geometry to compare the
parent tube volume with the volume of its complete fine fiber. -/
theorem parentVolume_le_capturedTubeBoxLoss_mul_fiberFamilyVolume
    (S : StickyScaleCover fine rho) (hdelta : 0 < delta)
    (k : Fin S.coarseCard) (hk : k ∈ S.activeCoarse) :
    volume (S.coarse.tubes k).carrier <=
      capturedTubeBoxLoss delta rho * familyVolume (S.fiberFamily k) := by
  obtain ⟨i, hi, hip⟩ := S.parent_surjective k hk
  have hifiber : i ∈ S.fiber k :=
    (S.mem_fiber i k).2 ⟨hi, hip⟩
  let K : ConvexBody Space := (fine.tubes i).body
  have hcaptured :
      (containedIndices (activeFineFamily S) K).Nonempty := by
    refine ⟨⟨i, hi⟩, ?_⟩
    rw [mem_containedIndices]
    exact Subset.rfl
  have hthick :=
    (actualCapturingThickeningVolumeControl S hdelta).thickeningVolume_le
      K hcaptured
  have hparentSubset :
      (S.coarse.tubes k).carrier ⊆
        (closedThickeningBody K (4 * rho) : Set Space) := by
    simpa [hip] using
      FamilyStickyAdjacentTestBodyGeometryV1.StickyScaleCover.coarse_parent_subset_four_rho_closedThickening
        S K i hi
        (show (fine.tubes i).carrier ⊆ (K : Set Space) by exact Subset.rfl)
  calc
    volume (S.coarse.tubes k).carrier <=
        volume (closedThickeningBody K (4 * rho) : Set Space) :=
      measure_mono hparentSubset
    _ <= capturedTubeBoxLoss delta rho * volume (K : Set Space) := hthick
    _ <= capturedTubeBoxLoss delta rho * familyVolume (S.fiberFamily k) := by
      gcongr
      exact fineTubeVolume_le_fiberFamilyVolume S k i hifiber

/-- The actual parent concentration is large enough to normalize every test
body, with the captured-tube loss as an explicit reciprocal bound. -/
theorem one_le_capturedTubeBoxLoss_mul_parentConcentration
    (S : StickyScaleCover fine rho) (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (k : Fin S.coarseCard) (hk : k ∈ S.activeCoarse) :
    1 <= capturedTubeBoxLoss delta rho *
      concentration (S.fiberFamily k) (S.coarse.tubes k).body := by
  have hparent :=
    parentVolume_le_capturedTubeBoxLoss_mul_fiberFamilyVolume S hdelta k hk
  have hpos : volume (S.coarse.tubes k).carrier ≠ 0 :=
    (S.coarse.tubes k).volume_pos hrho |>.ne'
  have htop : volume (S.coarse.tubes k).carrier ≠ ∞ :=
    (S.coarse.tubes k).volume_lt_top.ne
  have hdiv :
      1 <= (capturedTubeBoxLoss delta rho * familyVolume (S.fiberFamily k)) /
        volume (S.coarse.tubes k).carrier := by
    exact (ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl htop)).2
      (by simpa using hparent)
  have hratio :=
    parentFiberMassRatio_eq_concentration_parent S ⟨k, hk⟩
  change parentFiberMassRatio S ⟨k, hk⟩ =
    concentration (S.fiberFamily k) (S.coarse.tubes k).body at hratio
  rw [← hratio]
  unfold parentFiberMassRatio
  simpa [mul_div_assoc,
    FamilyStickyAtEveryScaleCoreV1.StickyScaleCover.activeCoarseFamily,
    UniformTubeFamily.bodyFamily, Tube.coe_body] using hdiv

/-- Every finite actual scale cover has an explicit Frostman constant. -/
theorem isFrostmanAtScale_card_mul_capturedTubeBoxLoss
    (S : StickyScaleCover fine rho) (hdelta : 0 < delta)
    (hrho : 0 < rho) :
    S.IsFrostmanAtScale
      ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta rho) := by
  intro k hk K hK
  have hnormalizer :=
    one_le_capturedTubeBoxLoss_mul_parentConcentration S hdelta hrho k hk
  calc
    concentration (S.fiberFamily k) K <=
        maximalConcentration (S.fiberFamily k) :=
      concentration_le_maximalConcentration (S.fiberFamily k) K
    _ <= fiberDeltaMax S :=
      maximalConcentration_fiber_le_fiberDeltaMax S ⟨k, hk⟩
    _ <= (S.activeFine.card : ENNReal) :=
      StickyScaleCover.fiberDeltaMax_le_activeFine_card S
    _ <= (Fintype.card iota : ENNReal) := by
      exact_mod_cast Finset.card_le_univ S.activeFine
    _ = (Fintype.card iota : ENNReal) * 1 := by simp
    _ <= (Fintype.card iota : ENNReal) *
        (capturedTubeBoxLoss delta rho *
          concentration (S.fiberFamily k) (S.coarse.tubes k).body) := by
      gcongr
    _ = ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta rho) *
        concentration (S.fiberFamily k) (S.coarse.tubes k).body := by
      ac_rfl

/-! ## Uniformizing the genuine local losses -/

theorem parentFiberMassMonotonicity_mono
    {S : StickyScaleCover fine rho} {a b : ENNReal}
    (M : ParentFiberMassMonotonicity S a) (hab : a <= b) :
    ParentFiberMassMonotonicity S b where
  fiberVolume_le_parent := by
    intro k
    exact (M.fiberVolume_le_parent k).trans (by gcongr)

theorem capturingThickeningVolumeControl_mono
    {S : StickyScaleCover fine rho} {a b : ENNReal}
    (V : CapturingThickeningVolumeControl S a) (hab : a <= b) :
    CapturingThickeningVolumeControl S b where
  thickeningVolume_le := by
    intro K hK
    exact (V.thickeningVolume_le K hK).trans (by gcongr)

/-- Every captured-box loss inside `[delta,1]` is bounded by the single
explicit endpoint expression `capturedTubeBoxLoss delta 1`. -/
theorem capturedTubeBoxLoss_le_global
    {sigma upper : NNReal}
    (hdelta : 0 < delta) (hDeltaSigma : delta <= sigma)
    (hUpperOne : upper <= 1) :
    capturedTubeBoxLoss sigma upper <= capturedTubeBoxLoss delta 1 := by
  have hratio : upper / sigma <= 1 / delta := by
    exact div_le_div₀ (by positivity) hUpperOne hdelta hDeltaSigma
  have hlong : longWidthFactor upper <= longWidthFactor 1 := by
    unfold longWidthFactor
    gcongr
  have hshort :
      shortWidthFactor sigma upper <= shortWidthFactor delta 1 := by
    unfold shortWidthFactor
    gcongr
  unfold capturedTubeBoxLoss
  gcongr

variable {depth : Nat}

/-- With the present shared parameterization, every scale interval is
automatically large as soon as `epsilon >= 1`: `delta^epsilon <= delta`,
`theta <= 1`, and `delta <= tau`.  This records the exact degeneracy in the
current stopping API. -/
theorem allStepsLarge_of_one_le_epsilon
    (T : FiniteScaleSequence delta depth) {epsilon : Real}
    (hone : (1 : Real) <= epsilon) :
    T.AllStepsLarge epsilon := by
  intro m
  unfold FiniteScaleSequence.IsLarge
  have hdeltaOne : (delta : ENNReal) <= 1 := by
    exact_mod_cast (T.delta_le_tau m).trans
      ((T.tau_le_theta m).trans (T.theta_le_one m))
  have hpower : (delta : ENNReal) ^ epsilon <= (delta : ENNReal) := by
    calc
      (delta : ENNReal) ^ epsilon <= (delta : ENNReal) ^ (1 : Real) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hdeltaOne hone
      _ = (delta : ENNReal) := ENNReal.rpow_one delta
  calc
    (delta : ENNReal) ^ epsilon * (T.theta m : ENNReal) <=
        (delta : ENNReal) * 1 := by
      gcongr
      exact_mod_cast T.theta_le_one m
    _ = (delta : ENNReal) := mul_one (delta : ENNReal)
    _ <= (T.tau m : ENNReal) := by exact_mod_cast T.delta_le_tau m

/-- The identity coherent cover has all local geometry automatically, with
finite uniform constants depending only on the original cardinality and
the captured-box endpoint loss. -/
theorem identityLargeIntervalLocalGeometry
    (fine : UniformTubeFamily delta iota)
    (T : FiniteScaleSequence delta depth)
    {epsilon : Real} (hdelta : 0 < delta) :
    LargeIntervalLocalGeometry (identityRadiusCoherentCover fine) T epsilon
      (Fintype.card iota : ENNReal)
      (capturedTubeBoxLoss delta 1)
      ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) where
  parent_compatible := by
    intro m r hTauRho hRhoTheta i hi
    rfl
  parentFiberMass := by
    intro m r hTauRho hRhoTheta hlarge
    let I := rhoToUpperCover (identityRadiusCoherentCover fine) T m r
      hTauRho hRhoTheta
    have htheta : 0 < T.theta m :=
      hdelta.trans_le ((T.delta_le_tau m).trans
        (hTauRho.trans hRhoTheta))
    have M := actualParentFiberMassMonotonicity I htheta
    apply parentFiberMassMonotonicity_mono M
    exact (actualParentFiberMassLoss_le_fiberDeltaMax I).trans
      (interval_fiberDeltaMax_le_original_card
        (identityRadiusCoherentCover fine)
        ((T.delta_le_tau m).trans hTauRho) hRhoTheta
        (T.theta_le_one m))
  thickeningVolume := by
    intro m r hTauRho hRhoTheta hlarge
    let I := rhoToUpperCover (identityRadiusCoherentCover fine) T m r
      hTauRho hRhoTheta
    have hr : 0 < r :=
      hdelta.trans_le ((T.delta_le_tau m).trans hTauRho)
    have V := actualCapturingThickeningVolumeControl I hr
    apply capturingThickeningVolumeControl_mono V
    exact capturedTubeBoxLoss_le_global hdelta
      ((T.delta_le_tau m).trans hTauRho) (T.theta_le_one m)
  katzTaoLoss_bound := le_rfl

/-! ## Automatic discrete endpoint bounds -/

theorem upperEndpoint_isFrostmanAtScale_explicit
    (C : CoherentStickyMultiscaleCover fine)
    (T : FiniteScaleSequence delta depth)
    (hdelta : 0 < delta) (m : Fin depth) :
    (upperEndpointCover C T m).IsFrostmanAtScale
      ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) := by
  apply (isFrostmanAtScale_card_mul_capturedTubeBoxLoss
    (upperEndpointCover C T m) hdelta
    (hdelta.trans_le ((T.delta_le_tau m).trans (T.tau_le_theta m)))).mono
  gcongr
  exact capturedTubeBoxLoss_le_global hdelta le_rfl (T.theta_le_one m)

theorem upperEndpoint_isKatzTaoAtScale_originalCard
    (C : CoherentStickyMultiscaleCover fine)
    (T : FiniteScaleSequence delta depth) (m : Fin depth) :
    (upperEndpointCover C T m).IsKatzTaoAtScale
      (Fintype.card iota : ENNReal) := by
  apply (FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover.isKatzTaoAtScale_iff_coarseDeltaMax_le
    (upperEndpointCover C T m) (Fintype.card iota : ENNReal)).2
  exact interval_coarseDeltaMax_le_original_card C
    (T.delta_le_tau m) (T.tau_le_theta m) (T.theta_le_one m)

/-- Once the stopping process reports all steps large, both discrete endpoint
bounds are automatic with explicit finite constants. -/
theorem discreteAllLargeStickyBounds_explicit
    (C : CoherentStickyMultiscaleCover fine)
    (T : FiniteScaleSequence delta depth)
    {epsilon : Real} (hdelta : 0 < delta)
    (hall : T.AllStepsLarge epsilon) :
    DiscreteAllLargeStickyBounds C T epsilon
      ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
      (Fintype.card iota : ENNReal) where
  all_large := hall
  frostman_endpoint := upperEndpoint_isFrostmanAtScale_explicit C T hdelta
  katzTao_endpoint := upperEndpoint_isKatzTaoAtScale_originalCard C T

/-! ## The closed direct identity endpoint -/

/-- The all-large branch now yields arbitrary-radius Sticky directly.  The
reverse normalizer is one, while the local Katz loss is the finite cardinal
times the captured-box endpoint loss. -/
theorem identityIsStickyAtEveryScale_of_allStepsLarge
    (fine : UniformTubeFamily delta iota)
    (T : FiniteScaleSequence delta depth)
    {epsilon : Real} (hdepth : 0 < depth) (hdelta : 0 < delta)
    (hall : T.AllStepsLarge epsilon) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
      ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
      (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
        (Fintype.card iota : ENNReal)) := by
  exact isStickyAtEveryScale_of_identityDirectNormalizer fine T hdepth hdelta
    (identityLargeIntervalLocalGeometry fine T hdelta)
    (discreteAllLargeStickyBounds_explicit
      (identityRadiusCoherentCover fine) T hdelta hall)

/-- Under the current shared `epsilon` convention, the all-large premise is
redundant whenever `epsilon` is at least one. -/
theorem identityIsStickyAtEveryScale_of_one_le_epsilon
    (fine : UniformTubeFamily delta iota)
    (T : FiniteScaleSequence delta depth)
    {epsilon : Real} (hdepth : 0 < depth) (hdelta : 0 < delta)
    (hone : (1 : Real) <= epsilon) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
      ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
      (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
        (Fintype.card iota : ENNReal)) := by
  exact identityIsStickyAtEveryScale_of_allStepsLarge fine T hdepth hdelta
    (allStepsLarge_of_one_le_epsilon T hone)

/-! ## Selected-hierarchy specialization -/

variable {nominalRadius : Nat -> NNReal} {Index : Nat -> Type u}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}

/-- The concrete selected level-zero identity cover inherits the fully
automatic all-large endpoint.  No ancestor coordinates, WZ certificate, or
sibling-rigidity input remains. -/
theorem selectedIdentityIsStickyAtEveryScale_of_allStepsLarge
    (R : SelectedTerminalSourceChartBucketGeometry (H := H))
    (T : FiniteScaleSequence
      ((selectedHierarchy R).effectiveRadius 0) depth)
    {epsilon : Real} (hdepth : 0 < depth)
    (hdelta : 0 < H.effectiveRadius 0)
    (hall : T.AllStepsLarge epsilon) :
    (selectedIdentityCoherentCover R).base.IsStickyAtEveryScale
      ((Fintype.card (SelectedHierarchyIndex R 0) : ENNReal) *
        capturedTubeBoxLoss ((selectedHierarchy R).effectiveRadius 0) 1)
      (((Fintype.card (SelectedHierarchyIndex R 0) : ENNReal) *
          capturedTubeBoxLoss ((selectedHierarchy R).effectiveRadius 0) 1) *
        (Fintype.card (SelectedHierarchyIndex R 0) : ENNReal)) := by
  exact identityIsStickyAtEveryScale_of_allStepsLarge
    ((selectedHierarchy R).effectiveFamily 0) T hdepth
    (selectedHierarchy_effectiveRadius_zero_pos (S := R) hdelta) hall

/-- Selected level zero has the same parameter-degenerate endpoint without
an explicit all-large certificate. -/
theorem selectedIdentityIsStickyAtEveryScale_of_one_le_epsilon
    (R : SelectedTerminalSourceChartBucketGeometry (H := H))
    (T : FiniteScaleSequence
      ((selectedHierarchy R).effectiveRadius 0) depth)
    {epsilon : Real} (hdepth : 0 < depth)
    (hdelta : 0 < H.effectiveRadius 0)
    (hone : (1 : Real) <= epsilon) :
    (selectedIdentityCoherentCover R).base.IsStickyAtEveryScale
      ((Fintype.card (SelectedHierarchyIndex R 0) : ENNReal) *
        capturedTubeBoxLoss ((selectedHierarchy R).effectiveRadius 0) 1)
      (((Fintype.card (SelectedHierarchyIndex R 0) : ENNReal) *
          capturedTubeBoxLoss ((selectedHierarchy R).effectiveRadius 0) 1) *
        (Fintype.card (SelectedHierarchyIndex R 0) : ENNReal)) := by
  exact selectedIdentityIsStickyAtEveryScale_of_allStepsLarge R T hdepth hdelta
    (allStepsLarge_of_one_le_epsilon T hone)

/-! ## Strong total-diagnostic consumer -/

variable {outerDepth N : Nat}

/-- The standard diagnostic room assumptions force `epsilon > 2`, hence in
particular `epsilon >= 1`. -/
theorem one_le_epsilon_of_diagnosticRoom
    {epsilon : Real} (slot : Fin N) (eta : Nat -> Real)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < epsilon) :
    (1 : Real) <= epsilon := by
  have hstage : eta 0 <= eta (oneBasedStage slot) :=
    eta_monotone (Nat.zero_le _)
  linarith

/-- Therefore the total diagnostic parameter regime has only the all-large
branch.  The tree, buffered-chain, and small-delta-threshold arguments are not
reached and consequently do not occur in this stronger conclusion. -/
theorem identityTotalStoppingDiagnostic_collapsesToSticky
    {epsilon : Real}
    (fine : UniformTubeFamily delta iota)
    (T : FiniteScaleSequence delta outerDepth)
    (hdepth : 0 < outerDepth)
    (slot : Fin N)
    (eta : Nat -> Real)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < epsilon)
    (delta_pos : 0 < delta) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
      ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
      (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
        (Fintype.card iota : ENNReal)) := by
  exact identityIsStickyAtEveryScale_of_one_le_epsilon
    fine T hdepth delta_pos
    (one_le_epsilon_of_diagnosticRoom slot eta eta_monotone two_le_zero strict_room)

#print axioms fineTubeVolume_le_fiberFamilyVolume
#print axioms parentVolume_le_capturedTubeBoxLoss_mul_fiberFamilyVolume
#print axioms one_le_capturedTubeBoxLoss_mul_parentConcentration
#print axioms isFrostmanAtScale_card_mul_capturedTubeBoxLoss
#print axioms capturedTubeBoxLoss_le_global
#print axioms allStepsLarge_of_one_le_epsilon
#print axioms identityLargeIntervalLocalGeometry
#print axioms upperEndpoint_isFrostmanAtScale_explicit
#print axioms upperEndpoint_isKatzTaoAtScale_originalCard
#print axioms discreteAllLargeStickyBounds_explicit
#print axioms identityIsStickyAtEveryScale_of_allStepsLarge
#print axioms identityIsStickyAtEveryScale_of_one_le_epsilon
#print axioms selectedIdentityIsStickyAtEveryScale_of_allStepsLarge
#print axioms selectedIdentityIsStickyAtEveryScale_of_one_le_epsilon
#print axioms one_le_epsilon_of_diagnosticRoom
#print axioms identityTotalStoppingDiagnostic_collapsesToSticky

end
end FamilyStickyScaleChainSelectedIdentityAutomaticAllLargeProducerV1
