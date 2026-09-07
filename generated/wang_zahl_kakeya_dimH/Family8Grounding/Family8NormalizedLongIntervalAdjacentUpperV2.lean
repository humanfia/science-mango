import Family8Grounding.Family8NormalizedLongIntervalAdjacentUpperV1
import Family8Grounding.Family8NormalizedLongIntervalFrostmanInheritanceV1
import Family8Grounding.Family8NormalizedCFDividingWitnessBridgeV4

/-!
# Callback-free adjacent normalized upper from base Frostman data

The V1 adjacent endpoint exposed a genuine all-scale Frostman certificate on
each interval cover.  This successor constructs that certificate from the
source all-scale Frostman bound, the commuting parent square, and explicit
two-sided assigned-parent mass densities.  The loss is exactly
`upper * lower⁻¹`.

A second constructor instantiates the two density sides with repository
objects: the geometric parent-fibre floor and the literal computed
`actualParentFiberMassLoss`.  Thus its sole structural residue is the
commuting parent square; no interval Frostman or normalized-upper callback is
introduced.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8NormalizedLongIntervalAdjacentUpperV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessBridgeV4.StickyScaleCover
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8NormalizedLongIntervalWitnessV1
open Family8NormalizedLongIntervalSourceUpperV1
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentIntervalProducerV1.CoherentStickyMultiscaleCover
open FamilyStickyScaleChainNestedMassLocalizationV1.StickyScaleCover
open FamilyStickyScaleChainParentFiberMassProducerV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {depth : Nat}

/-! ## Actual density instantiation -/

/-- The current repository's actual parent-density producers fill both mass
sides of the minimal inheritance package.

The lower side is the proved one-child tube-volume floor.  The upper side is
the exact finite supremum `actualParentFiberMassLoss`.  Neither is a
Frostman assertion. -/
theorem actualIntervalParentMassComparison
    (C : CoherentStickyMultiscaleCover fine)
    (tau : NNReal) (hdeltaTau : delta ≤ tau) (hTauOne : tau ≤ 1)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (htauHalf : tau ≤ (2 : NNReal)⁻¹)
    (hparent : ∀ (rho : NNReal) (hTauRho : tau ≤ rho)
      (hRhoOne : rho ≤ 1) (i : iota),
      i ∈ (C.base.cover tau hdeltaTau hTauOne).activeFine →
        (C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne).parent i =
          C.parent tau rho hdeltaTau hTauRho hRhoOne
            ((C.base.cover tau hdeltaTau hTauOne).parent i)) :
    IntervalParentMassComparison C tau hdeltaTau hTauOne
      (parentFiberMassRatioFloor delta tau)
      (actualParentFiberMassLoss
        (C.base.cover tau hdeltaTau hTauOne)) where
  parent_compatible := hparent
  lower_parent_mass := by
    intro q hq
    let T := C.base.cover tau hdeltaTau hTauOne
    let qq : {q // q ∈ T.activeCoarse} := ⟨q, hq⟩
    have htauPos : 0 < tau := hdeltaPos.trans_le hdeltaTau
    have hratio :=
      parentFiberMassRatioFloor_le T hdeltaHalf htauHalf qq
    have hvol0 : volume (T.coarse.tubes q).carrier ≠ 0 :=
      (T.coarse.tubes q).volume_pos htauPos |>.ne'
    have hvolTop : volume (T.coarse.tubes q).carrier ≠ ∞ :=
      (T.coarse.tubes q).volume_lt_top.ne
    have hcross :=
      (ENNReal.le_div_iff_mul_le (Or.inl hvol0) (Or.inl hvolTop)).1 hratio
    simpa only [parentFiberMassRatio, StickyScaleCover.activeCoarseFamily,
      UniformTubeFamily.bodyFamily, Tube.coe_body, T, qq] using hcross
  upper_parent_mass := by
    intro q hq
    let T := C.base.cover tau hdeltaTau hTauOne
    let qq : {q // q ∈ T.activeCoarse} := ⟨q, hq⟩
    have htauPos : 0 < tau := hdeltaPos.trans_le hdeltaTau
    have hupper :=
      (actualParentFiberMassMonotonicity T htauPos).fiberVolume_le_parent qq
    simpa only [StickyScaleCover.activeCoarseFamily,
      UniformTubeFamily.bodyFamily, Tube.coe_body, T, qq] using hupper

/-- The geometric floor is positive at positive source radius. -/
theorem parentFiberMassRatioFloor_ne_zero
    (hdeltaPos : 0 < delta) (tau : NNReal) :
    parentFiberMassRatioFloor delta tau ≠ 0 := by
  unfold parentFiberMassRatioFloor
  apply ENNReal.div_ne_zero.2
  constructor
  · apply ENNReal.div_ne_zero.2
    constructor
    · positivity
    · norm_num
  · finiteness

/-- The geometric floor is finite. -/
theorem parentFiberMassRatioFloor_ne_top
    (delta tau : NNReal) (htauPos : 0 < tau) :
    parentFiberMassRatioFloor delta tau ≠ ∞ := by
  unfold parentFiberMassRatioFloor
  exact ENNReal.div_ne_top
    (ENNReal.div_ne_top (by finiteness) (by norm_num)) (by positivity)

/-! ## Adjacent upper with no interval Frostman callback -/

/-- Source all-scale Frostman plus one minimal mass-comparison package at
each lower endpoint produces all adjacent normalized uppers.  The comparison
constant may vary with the interval, and its exact loss is displayed in
`herror`. -/
theorem adjacentUpper_of_baseFrostman_parentMassComparison
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    {baseError : ENNReal}
    (hFbase : C.base.IsFrostmanAtEveryScale baseError)
    (lower upper : Fin depth → ENNReal)
    (hlower0 : ∀ m, lower m ≠ 0)
    (hlowerTop : ∀ m, lower m ≠ ∞)
    (H : ∀ m : Fin depth,
      IntervalParentMassComparison C (S.tau m)
        (S.delta_le_tau m)
        ((S.tau_le_theta m).trans (S.theta_le_one m))
        (lower m) (upper m))
    (eta : Nat → Real) (N : Nat)
    (herror : ∀ m : Fin depth,
      baseError * upper m * (lower m)⁻¹ ≤
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^
          eta (N - 1))) :
    ∀ m : Fin depth,
      parentNormalizedFiberCFMax
          (C.intervalScaleCover (S.tau m) (S.theta m)
            (S.delta_le_tau m) (S.tau_le_theta m)
            (S.theta_le_one m)) ≤
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^
          eta (N - 1)) := by
  intro m
  have htauPos : 0 < S.tau m :=
    hD.delta_pos.trans_le (S.delta_le_tau m)
  have hAt :=
    intervalScaleCover_isFrostmanAtScale C (S.tau m) (S.theta m)
      (S.delta_le_tau m)
      ((S.tau_le_theta m).trans (S.theta_le_one m))
      (S.tau_le_theta m) (S.theta_le_one m)
      (hlower0 m) (hlowerTop m) (H m)
      (hFbase (S.theta m)
        ((S.delta_le_tau m).trans (S.tau_le_theta m))
        (S.theta_le_one m))
  exact
    ((isFrostmanAtScale_iff_parentNormalizedFiberCFMax_le
      (C.intervalScaleCover (S.tau m) (S.theta m)
        (S.delta_le_tau m) (S.tau_le_theta m)
        (S.theta_le_one m)) htauPos
      (baseError * upper m * (lower m)⁻¹)).mp hAt).trans (herror m)

/-- Specialization using the actual parent-density floor and computed upper
loss.  The only remaining structure is the explicit parent square. -/
theorem adjacentUpper_of_baseFrostman_actualParentDensity
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    {baseError : ENNReal}
    (hFbase : C.base.IsFrostmanAtEveryScale baseError)
    (htauHalf : ∀ m : Fin depth, S.tau m ≤ (2 : NNReal)⁻¹)
    (hparent : ∀ (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m ≤ rho) (hRhoOne : rho ≤ 1) (i : iota),
      i ∈ (C.base.cover (S.tau m) (S.delta_le_tau m)
        ((S.tau_le_theta m).trans (S.theta_le_one m))).activeFine →
        (C.base.cover rho ((S.delta_le_tau m).trans hTauRho)
          hRhoOne).parent i =
          C.parent (S.tau m) rho (S.delta_le_tau m)
            hTauRho hRhoOne
            ((C.base.cover (S.tau m) (S.delta_le_tau m)
              ((S.tau_le_theta m).trans
                (S.theta_le_one m))).parent i))
    (eta : Nat → Real) (N : Nat)
    (herror : ∀ m : Fin depth,
      baseError *
          actualParentFiberMassLoss
            (C.base.cover (S.tau m) (S.delta_le_tau m)
              ((S.tau_le_theta m).trans (S.theta_le_one m))) *
          (parentFiberMassRatioFloor delta (S.tau m))⁻¹ ≤
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^
          eta (N - 1))) :
    ∀ m : Fin depth,
      parentNormalizedFiberCFMax
          (C.intervalScaleCover (S.tau m) (S.theta m)
            (S.delta_le_tau m) (S.tau_le_theta m)
            (S.theta_le_one m)) ≤
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^
          eta (N - 1)) := by
  apply adjacentUpper_of_baseFrostman_parentMassComparison
    D hD C S hFbase
    (fun m => parentFiberMassRatioFloor delta (S.tau m))
    (fun m => actualParentFiberMassLoss
      (C.base.cover (S.tau m) (S.delta_le_tau m)
        ((S.tau_le_theta m).trans (S.theta_le_one m))))
  · intro m
    exact parentFiberMassRatioFloor_ne_zero hD.delta_pos (S.tau m)
  · intro m
    exact parentFiberMassRatioFloor_ne_top delta (S.tau m)
      (hD.delta_pos.trans_le (S.delta_le_tau m))
  · intro m
    exact actualIntervalParentMassComparison C (S.tau m)
      (S.delta_le_tau m)
      ((S.tau_le_theta m).trans (S.theta_le_one m))
      hD.delta_pos hD.delta_le_half (htauHalf m)
      (hparent m)
  · exact herror

/-! ## Stopping trichotomy successor -/

/-- The normalized stopping trichotomy with the adjacent side constructed
from base Frostman and two-sided parent-mass data.  No interval all-scale
Frostman callback remains. -/
theorem allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_of_parentMassComparison
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (eta : Nat → Real) (N : Nat) (hN : 1 ≤ N)
    {sourceError : ENNReal}
    (hFsource : C.base.IsFrostmanAtEveryScale sourceError)
    (hsourceError : ∀ m : Fin depth,
      sourceError ≤ (((S.tau m / delta : NNReal) : ENNReal) ^
        eta (N - 1)))
    (lower upper : Fin depth → ENNReal)
    (hlower0 : ∀ m, lower m ≠ 0)
    (hlowerTop : ∀ m, lower m ≠ ∞)
    (H : ∀ m : Fin depth,
      IntervalParentMassComparison C (S.tau m)
        (S.delta_le_tau m)
        ((S.tau_le_theta m).trans (S.theta_le_one m))
        (lower m) (upper m))
    (hadjacentError : ∀ m : Fin depth,
      sourceError * upper m * (lower m)⁻¹ ≤
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^
          eta (N - 1))) :
    ((S.AllStepsLarge epsilon ∨
        Nonempty
          (NormalizedLongIntervalWitness D.family C N epsilon eta S)) ∨
      Nonempty
        (FirstActualNormalizedCrossingWitness
          D hD C S epsilon hepsilon eta N)) := by
  exact
    allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_of_sourceAllScaleFrostman
      D hD C S epsilon hepsilon eta N hN hFsource hsourceError
      (adjacentUpper_of_baseFrostman_parentMassComparison
        D hD C S hFsource lower upper hlower0 hlowerTop H
        eta N hadjacentError)

#print axioms actualIntervalParentMassComparison
#print axioms parentFiberMassRatioFloor_ne_zero
#print axioms parentFiberMassRatioFloor_ne_top
#print axioms adjacentUpper_of_baseFrostman_parentMassComparison
#print axioms adjacentUpper_of_baseFrostman_actualParentDensity
#print axioms
  allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_of_parentMassComparison

end

end Family8NormalizedLongIntervalAdjacentUpperV2
