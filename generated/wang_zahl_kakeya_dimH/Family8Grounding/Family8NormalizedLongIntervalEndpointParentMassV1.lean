import Family8Grounding.Family8NormalizedLongIntervalAdjacentUpperV2
import Family8Grounding.Family8Def212ConvexWolffAtEveryScaleV2
import FamilyStickyGrounding.FamilyStickyScaleChainParentNormalizerReverseProducerV1

/-!
# Endpoint-only parent compatibility for the normalized adjacent upper

The adjacent normalized selector only evaluates the interval cover at its
upper endpoint `theta`.  It therefore does not need the stronger commuting
square at every radius above `tau` stored by
`IntervalParentMassComparison`.  This file isolates the exact endpoint
square, repeats the same honest parent-mass inheritance argument at that one
scale, and connects it to the already existing
`LargeIntervalLocalGeometry.parent_compatible` field.

This does not infer a parent square for an arbitrary coherent cover.  The
last finite theorem records why the parent-map axioms alone cannot do so.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8NormalizedLongIntervalEndpointParentMassV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessBridgeV4.StickyScaleCover
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8NormalizedLongIntervalAdjacentUpperV2
open Family8NormalizedLongIntervalSourceUpperV1
open Family8NormalizedLongIntervalWitnessV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainArbitraryRadiusBoundsV1
open FamilyStickyScaleChainArbitraryRadiusInterpolationV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentIntervalProducerV1.CoherentStickyMultiscaleCover
open FamilyStickyScaleChainNestedMassLocalizationV1.StickyScaleCover
open FamilyStickyScaleChainParentFiberMassProducerV1.StickyScaleCover
open FamilyStickyScaleChainParentNormalizerReverseProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {depth : Nat}

/-! ## The exact one-scale structural datum -/

/-- Parent compatibility and two-sided assigned mass at one fixed endpoint.
Unlike `IntervalParentMassComparison`, this structure has no quantifier over
all later radii. -/
structure IntervalEndpointParentMassComparison
    (C : CoherentStickyMultiscaleCover fine)
    (tau rho : NNReal) (hdeltaTau : delta ≤ tau)
    (hTauRho : tau ≤ rho) (hRhoOne : rho ≤ 1)
    (lower upper : ENNReal) : Prop where
  parent_compatible : ∀ (i : iota),
    i ∈ (C.base.cover tau hdeltaTau (hTauRho.trans hRhoOne)).activeFine →
      (C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne).parent i =
        C.parent tau rho hdeltaTau hTauRho hRhoOne
          ((C.base.cover tau hdeltaTau
            (hTauRho.trans hRhoOne)).parent i)
  lower_parent_mass : ∀ q,
    q ∈ (C.base.cover tau hdeltaTau
      (hTauRho.trans hRhoOne)).activeCoarse →
      lower * volume
          ((C.base.cover tau hdeltaTau
            (hTauRho.trans hRhoOne)).coarse.tubes q).carrier ≤
        familyVolume
          ((C.base.cover tau hdeltaTau
            (hTauRho.trans hRhoOne)).fiberFamily q)
  upper_parent_mass : ∀ q,
    q ∈ (C.base.cover tau hdeltaTau
      (hTauRho.trans hRhoOne)).activeCoarse →
      familyVolume
          ((C.base.cover tau hdeltaTau
            (hTauRho.trans hRhoOne)).fiberFamily q) ≤
        upper * volume
          ((C.base.cover tau hdeltaTau
            (hTauRho.trans hRhoOne)).coarse.tubes q).carrier

namespace IntervalEndpointParentMassComparison

variable {C : CoherentStickyMultiscaleCover fine}
  {tau rho : NNReal} {hdeltaTau : delta ≤ tau}
  {hTauRho : tau ≤ rho} {hRhoOne : rho ≤ 1}
  {lower upper : ENNReal}

/-- Restrict the actual `delta -> tau` factorization to the `tau` parents
over one fixed `rho` parent. -/
def endpointFiberFactorization
    (_H : IntervalEndpointParentMassComparison C tau rho hdeltaTau
      hTauRho hRhoOne lower upper)
    (k : Fin (C.intervalScaleCover tau rho hdeltaTau hTauRho
      hRhoOne).coarseCard) :
    ConvexFactorization fine.bodyFamily
      (C.base.cover tau hdeltaTau
        (hTauRho.trans hRhoOne)).coarse.bodyFamily where
  index := selectedIndexFactorization
    (C.base.cover tau hdeltaTau
      (hTauRho.trans hRhoOne)).activeFine
    (C.base.cover tau hdeltaTau
      (hTauRho.trans hRhoOne)).parent
    ((C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne).fiber k)
  contained := by
    intro i hi
    have hiTau : i ∈ (C.base.cover tau hdeltaTau
        (hTauRho.trans hRhoOne)).activeFine :=
      (Finset.mem_filter.mp hi).1
    exact (C.base.cover tau hdeltaTau
      (hTauRho.trans hRhoOne)).carrier_subset i hiTau

/-- The endpoint square identifies the selected original indices with the
literal global `delta`-fibre at `rho`. -/
theorem endpointFiberFactorization_fine_eq_baseFiber
    (H : IntervalEndpointParentMassComparison C tau rho hdeltaTau
      hTauRho hRhoOne lower upper)
    (k : Fin (C.intervalScaleCover tau rho hdeltaTau hTauRho
      hRhoOne).coarseCard) :
    (H.endpointFiberFactorization k).index.fine =
      (C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne).fiber k := by
  classical
  let T := C.base.cover tau hdeltaTau (hTauRho.trans hRhoOne)
  let R := C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne
  let I := C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne
  ext i
  change i ∈ selectedFineIndices T.activeFine T.parent (I.fiber k) ↔
    i ∈ R.fiber k
  unfold selectedFineIndices StickyScaleCover.fiber
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hiTau, hparentFiber⟩
    have hiRho : i ∈ R.activeFine := by
      rw [R.activeFine_eq_refined, ← T.activeFine_eq_refined]
      exact hiTau
    have hparentFiber' := hparentFiber
    refine ⟨hiRho, ?_⟩
    rw [← hparentFiber'.2]
    exact H.parent_compatible i hiTau
  · rintro ⟨hiRho, hparentRho⟩
    have hiTau : i ∈ T.activeFine := by
      rw [T.activeFine_eq_refined, ← R.activeFine_eq_refined]
      exact hiRho
    refine ⟨hiTau, ⟨T.parent_mem i hiTau, ?_⟩⟩
    rw [← hparentRho]
    exact (H.parent_compatible i hiTau).symm

/-- Restricting to an endpoint fibre preserves the mass assigned to each
retained `tau` parent. -/
theorem endpointFiberFactorization_fiberBodyMass_eq
    (H : IntervalEndpointParentMassComparison C tau rho hdeltaTau
      hTauRho hRhoOne lower upper)
    (k : Fin (C.intervalScaleCover tau rho hdeltaTau hTauRho
      hRhoOne).coarseCard)
    (q : Fin (C.base.cover tau hdeltaTau
      (hTauRho.trans hRhoOne)).coarseCard)
    (hq : q ∈ (C.intervalScaleCover tau rho hdeltaTau hTauRho
      hRhoOne).fiber k) :
    fiberBodyMass (H.endpointFiberFactorization k) q =
      familyVolume
        ((C.base.cover tau hdeltaTau
          (hTauRho.trans hRhoOne)).fiberFamily q) := by
  classical
  let T := C.base.cover tau hdeltaTau (hTauRho.trans hRhoOne)
  unfold fiberBodyMass
  change (∑ i ∈
      (selectedIndexFactorization T.activeFine T.parent
        ((C.intervalScaleCover tau rho hdeltaTau hTauRho
          hRhoOne).fiber k)).fiber q,
      volume (fine.bodyFamily i : Set Space)) = _
  rw [selected_fiber_eq_raw_fiber T.activeFine T.parent _ hq]
  change (∑ i ∈ T.fiber q,
      volume (fine.bodyFamily i : Set Space)) =
    ∑ i : {i // i ∈ T.fiber q},
      volume (fine.bodyFamily i.1 : Set Space)
  exact Finset.sum_subtype (M := ENNReal)
    (T.fiber q) (fun _i => Iff.rfl) _

end IntervalEndpointParentMassComparison

/-! ## Endpoint Frostman inheritance -/

/-- Base Frostman control at one fixed endpoint, the one endpoint square,
and two-sided assigned-parent masses give Frostman control of the literal
`tau -> rho` cover at that endpoint. -/
theorem intervalScaleCover_isFrostmanAtScale_of_endpointParentMassComparison
    (C : CoherentStickyMultiscaleCover fine)
    (tau rho : NNReal) (hdeltaTau : delta ≤ tau)
    (hTauRho : tau ≤ rho) (hRhoOne : rho ≤ 1)
    {baseError lower upper : ENNReal}
    (hlower0 : lower ≠ 0) (hlowerTop : lower ≠ ∞)
    (H : IntervalEndpointParentMassComparison C tau rho hdeltaTau
      hTauRho hRhoOne lower upper)
    (hbase : StickyScaleCover.IsFrostmanAtScale
      (C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne) baseError) :
    StickyScaleCover.IsFrostmanAtScale
      (C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne)
      (baseError * upper * lower⁻¹) := by
  intro k hk K hK
  let T := C.base.cover tau hdeltaTau (hTauRho.trans hRhoOne)
  let R := C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne
  let I := C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne
  let P := H.endpointFiberFactorization k
  have hfineSubtype :
      IsFrostmanIn baseError (R.fiberFamily k) (R.coarse.tubes k).body := by
    apply (isFrostmanIn_iff_concentration_le).2
    refine ⟨R.fiber_carrier_subset_parent k, ?_⟩
    exact hbase k hk
  have hfineActive :
      IsFrostmanOn baseError fine.bodyFamily P.index.fine
        (R.coarse.tubes k).body := by
    rw [IntervalEndpointParentMassComparison.endpointFiberFactorization_fine_eq_baseFiber]
    exact (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
      fine.bodyFamily (R.fiber k) (R.coarse.tubes k).body).2 hfineSubtype
  have hcoarseContained : ∀ q ∈ P.index.coarse,
      (T.coarse.bodyFamily q : Set Space) ⊆
        ((R.coarse.tubes k).body : Set Space) := by
    intro q hq
    have hqFiber : q ∈ I.fiber k := hq
    have hqData := (I.mem_fiber q k).1 hqFiber
    have hcarrier := I.carrier_subset q hqData.1
    rw [hqData.2] at hcarrier
    simpa only [UniformTubeFamily.bodyFamily, Tube.coe_body, I, R, T,
      CoherentStickyMultiscaleCover.intervalScaleCover] using hcarrier
  have hlocal :
      IsFrostmanOn (baseError * upper * lower⁻¹)
        T.coarse.bodyFamily P.index.coarse (R.coarse.tubes k).body := by
    apply
      Family8FrostmanInheritanceToActiveCoarseV3.activeCoarse_isFrostmanOn_of_comparable_fiberDensity
        P (R.coarse.tubes k).body hlower0 hlowerTop hfineActive
        hcoarseContained
    · intro q hq
      have hqFiber : q ∈ I.fiber k := hq
      have hqActive := (I.mem_fiber q k).1 hqFiber |>.1
      rw [H.endpointFiberFactorization_fiberBodyMass_eq k q hqFiber]
      exact H.lower_parent_mass q hqActive
    · intro q hq
      have hqFiber : q ∈ I.fiber k := hq
      have hqActive := (I.mem_fiber q k).1 hqFiber |>.1
      rw [H.endpointFiberFactorization_fiberBodyMass_eq k q hqFiber]
      exact H.upper_parent_mass q hqActive
  have hlocalSubtype :
      IsFrostmanIn (baseError * upper * lower⁻¹)
        (I.fiberFamily k) (R.coarse.tubes k).body := by
    exact (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
      T.coarse.bodyFamily (I.fiber k) (R.coarse.tubes k).body).1 hlocal
  exact (isFrostmanIn_iff_concentration_le).1 hlocalSubtype |>.2 K hK

/-! ## Actual density and selected local-geometry connectors -/

/-- The repository's actual lower and upper parent-mass producers fill the
endpoint-only package. -/
theorem actualIntervalEndpointParentMassComparison
    (C : CoherentStickyMultiscaleCover fine)
    (tau rho : NNReal) (hdeltaTau : delta ≤ tau)
    (hTauRho : tau ≤ rho) (hRhoOne : rho ≤ 1)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (htauHalf : tau ≤ (2 : NNReal)⁻¹)
    (hparent : ∀ (i : iota),
      i ∈ (C.base.cover tau hdeltaTau
        (hTauRho.trans hRhoOne)).activeFine →
        (C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne).parent i =
          C.parent tau rho hdeltaTau hTauRho hRhoOne
            ((C.base.cover tau hdeltaTau
              (hTauRho.trans hRhoOne)).parent i)) :
    IntervalEndpointParentMassComparison C tau rho hdeltaTau hTauRho
      hRhoOne (parentFiberMassRatioFloor delta tau)
      (actualParentFiberMassLoss
        (C.base.cover tau hdeltaTau (hTauRho.trans hRhoOne))) where
  parent_compatible := hparent
  lower_parent_mass := by
    intro q hq
    let T := C.base.cover tau hdeltaTau (hTauRho.trans hRhoOne)
    let qq : {q // q ∈ T.activeCoarse} := ⟨q, hq⟩
    have htauPos : 0 < tau := hdeltaPos.trans_le hdeltaTau
    have hratio := parentFiberMassRatioFloor_le T hdeltaHalf htauHalf qq
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
    let T := C.base.cover tau hdeltaTau (hTauRho.trans hRhoOne)
    let qq : {q // q ∈ T.activeCoarse} := ⟨q, hq⟩
    have htauPos : 0 < tau := hdeltaPos.trans_le hdeltaTau
    have hupper :=
      (actualParentFiberMassMonotonicity T htauPos).fiberVolume_le_parent qq
    simpa only [StickyScaleCover.activeCoarseFamily,
      UniformTubeFamily.bodyFamily, Tube.coe_body, T, qq] using hupper

/-- The genuinely minimal structural datum along a finite scale sequence:
one fine-parent commuting square for each adjacent pair. -/
def AdjacentFineParentCompatible
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth) : Prop :=
  ∀ (m : Fin depth) (i : iota),
    i ∈ (C.base.cover (S.tau m) (S.delta_le_tau m)
      ((S.tau_le_theta m).trans (S.theta_le_one m))).activeFine →
      (C.base.cover (S.theta m)
        ((S.delta_le_tau m).trans (S.tau_le_theta m))
        (S.theta_le_one m)).parent i =
      C.parent (S.tau m) (S.theta m) (S.delta_le_tau m)
        (S.tau_le_theta m) (S.theta_le_one m)
        ((C.base.cover (S.tau m) (S.delta_le_tau m)
          ((S.tau_le_theta m).trans (S.theta_le_one m))).parent i)

/-- Definition 2.10 doubled-parent partitioning at each upper endpoint
forces the adjacent fine-parent square.  The direct upper parent and the
cross-scale parent both contain the same fine tube in their doubled fibres,
so disjointness makes the two active parents equal. -/
theorem adjacentFineParentCompatible_of_doubledParentPartitioning
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth)
    (hpartition : ∀ m : Fin depth,
      IsDoubledParentPartitioning
        (C.base.cover (S.theta m)
          ((S.delta_le_tau m).trans (S.tau_le_theta m))
          (S.theta_le_one m))) :
    AdjacentFineParentCompatible C S := by
  intro m i hi
  let T := C.base.cover (S.tau m) (S.delta_le_tau m)
    ((S.tau_le_theta m).trans (S.theta_le_one m))
  let R := C.base.cover (S.theta m)
    ((S.delta_le_tau m).trans (S.tau_le_theta m))
    (S.theta_le_one m)
  let l : Fin R.coarseCard :=
    C.parent (S.tau m) (S.theta m)
      (S.delta_le_tau m) (S.tau_le_theta m) (S.theta_le_one m)
      (T.parent i)
  have hiR : i ∈ R.activeFine := by
    rw [R.activeFine_eq_refined, ← T.activeFine_eq_refined]
    exact hi
  have hk : R.parent i ∈ R.activeCoarse := R.parent_mem i hiR
  have hTi : T.parent i ∈ T.activeCoarse := T.parent_mem i hi
  have hl : l ∈ R.activeCoarse := by
    simpa only [l, R, T] using
      C.parent_mem (S.tau m) (S.theta m)
        (S.delta_le_tau m) (S.tau_le_theta m) (S.theta_le_one m)
        (T.parent i) hTi
  change R.parent i = l
  by_contra hne
  have hik : i ∈ doubledFiber R (R.parent i) := by
    exact fiber_subset_doubledFiber R (R.parent i)
      ((R.mem_fiber i (R.parent i)).2 ⟨hiR, rfl⟩)
  have hil : i ∈ doubledFiber R l := by
    rw [mem_doubledFiber]
    refine ⟨hiR, ?_⟩
    have hFineCross :
        (fine.tubes i).carrier ⊆
          (R.coarse.tubes l).carrier := by
      simpa only [l, R, T] using
        (T.carrier_subset i hi).trans
          (C.carrier_subset (S.tau m) (S.theta m)
            (S.delta_le_tau m) (S.tau_le_theta m) (S.theta_le_one m)
            (T.parent i) hTi)
    exact hFineCross.trans
      (carrier_subset_twoFoldTubeCarrier
        (R.coarse.tubes l))
  exact (Finset.disjoint_left.mp
    (hpartition m (R.parent i) hk l hl hne)
    hik hil)

/-- The exact-scale version of the paper's Definition 2.12 package already
contains the geometric datum needed for adjacent parent compatibility. -/
theorem adjacentFineParentCompatible_of_exactScaleDef212Inputs
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth)
    {K : NNReal}
    (H : ExactScaleDef212Inputs C.base K) :
    AdjacentFineParentCompatible C S := by
  apply adjacentFineParentCompatible_of_doubledParentPartitioning C S
  intro m
  exact H.doubled_parent_partitioning
    (S.theta m)
    ((S.delta_le_tau m).trans (S.tau_le_theta m))
    (S.theta_le_one m)

/-- Existing large-interval local geometry supplies the minimal adjacent
square by evaluating its all-intermediate-radius field at `rho = tau`. -/
theorem adjacentFineParentCompatible_of_largeIntervalLocalGeometry
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth) {epsilon : Real}
    {massLoss bodyLoss katzTaoLoss : ENNReal}
    (G : LargeIntervalLocalGeometry C S epsilon
      massLoss bodyLoss katzTaoLoss) :
    AdjacentFineParentCompatible C S := by
  intro m i hi
  have h := G.parent_compatible m (S.tau m) le_rfl
    (S.tau_le_theta m) i (by
      simpa only [lowerScaleCover] using hi)
  simpa only [lowerScaleCover, upperEndpointCover, rhoToUpperCover,
    CoherentStickyMultiscaleCover.intervalScaleCover] using h

/-- Base all-scale Frostman plus only the adjacent squares gives the entire
adjacent normalized-upper family. -/
theorem adjacentUpper_of_baseFrostman_adjacentFineParentCompatible
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    {baseError : ENNReal}
    (hFbase : C.base.IsFrostmanAtEveryScale baseError)
    (htauHalf : ∀ m : Fin depth, S.tau m ≤ (2 : NNReal)⁻¹)
    (hparent : AdjacentFineParentCompatible C S)
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
  intro m
  have H := actualIntervalEndpointParentMassComparison C
    (S.tau m) (S.theta m) (S.delta_le_tau m)
    (S.tau_le_theta m) (S.theta_le_one m)
    hD.delta_pos hD.delta_le_half (htauHalf m) (hparent m)
  have hAt :=
    intervalScaleCover_isFrostmanAtScale_of_endpointParentMassComparison
      C (S.tau m) (S.theta m) (S.delta_le_tau m)
      (S.tau_le_theta m) (S.theta_le_one m)
      (parentFiberMassRatioFloor_ne_zero hD.delta_pos (S.tau m))
      (parentFiberMassRatioFloor_ne_top delta (S.tau m)
        (hD.delta_pos.trans_le (S.delta_le_tau m))) H
      (hFbase (S.theta m)
        ((S.delta_le_tau m).trans (S.tau_le_theta m))
        (S.theta_le_one m))
  exact
    ((isFrostmanAtScale_iff_parentNormalizedFiberCFMax_le
      (C.intervalScaleCover (S.tau m) (S.theta m)
        (S.delta_le_tau m) (S.tau_le_theta m)
        (S.theta_le_one m))
      (hD.delta_pos.trans_le (S.delta_le_tau m))
      (baseError *
        actualParentFiberMassLoss
          (C.base.cover (S.tau m) (S.delta_le_tau m)
            ((S.tau_le_theta m).trans (S.theta_le_one m))) *
        (parentFiberMassRatioFloor delta (S.tau m))⁻¹)).mp hAt).trans
      (herror m)

/-- The same endpoint with the adjacent square obtained from existing
large-interval local geometry.  Its other quantitative fields are not used
by this bridge. -/
theorem adjacentUpper_of_baseFrostman_largeIntervalLocalGeometry
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    {epsilon : Real} {massLoss bodyLoss katzTaoLoss baseError : ENNReal}
    (G : LargeIntervalLocalGeometry C S epsilon
      massLoss bodyLoss katzTaoLoss)
    (hFbase : C.base.IsFrostmanAtEveryScale baseError)
    (htauHalf : ∀ m : Fin depth, S.tau m ≤ (2 : NNReal)⁻¹)
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
  exact adjacentUpper_of_baseFrostman_adjacentFineParentCompatible
    D hD C S hFbase htauHalf
    (adjacentFineParentCompatible_of_largeIntervalLocalGeometry C S G)
    eta N herror

/-- Full normalized stopping trichotomy using only endpoint parent squares,
not the stronger all-radii interval comparison package. -/
theorem allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_of_adjacentFineParentCompatible
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
    (htauHalf : ∀ m : Fin depth, S.tau m ≤ (2 : NNReal)⁻¹)
    (hparent : AdjacentFineParentCompatible C S)
    (hadjacentError : ∀ m : Fin depth,
      sourceError *
          actualParentFiberMassLoss
            (C.base.cover (S.tau m) (S.delta_le_tau m)
              ((S.tau_le_theta m).trans (S.theta_le_one m))) *
          (parentFiberMassRatioFloor delta (S.tau m))⁻¹ ≤
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^
          eta (N - 1))) :
    ((S.AllStepsLarge epsilon ∨
        Nonempty (NormalizedLongIntervalWitness
          D.family C N epsilon eta S)) ∨
      Nonempty (FirstActualNormalizedCrossingWitness
        D hD C S epsilon hepsilon eta N)) := by
  exact
    allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_of_sourceAllScaleFrostman
      D hD C S epsilon hepsilon eta N hN hFsource hsourceError
      (adjacentUpper_of_baseFrostman_adjacentFineParentCompatible
        D hD C S hFsource htauHalf hparent eta N hadjacentError)

/-! ## Why arbitrary coherent-cover axioms do not supply the square -/

/-- Surjectivity of the lower, upper, and cross-scale parent maps does not
force the fine-parent square: on `Bool`, take identity at the lower scale,
negation at the upper scale, and identity across scales. -/
theorem surjective_parent_maps_do_not_force_fine_parent_square :
    ∃ (lower upper cross : Bool → Bool),
      Function.Surjective lower ∧
      Function.Surjective upper ∧
      Function.Surjective cross ∧
      ¬ (∀ i, upper i = cross (lower i)) := by
  refine ⟨id, Bool.not, id, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨i, rfl⟩
  · intro i
    exact ⟨!i, by simp⟩
  · intro i
    exact ⟨i, rfl⟩
  · intro h
    have hfalse := h false
    simp at hfalse

#print axioms IntervalEndpointParentMassComparison.endpointFiberFactorization_fine_eq_baseFiber
#print axioms IntervalEndpointParentMassComparison.endpointFiberFactorization_fiberBodyMass_eq
#print axioms intervalScaleCover_isFrostmanAtScale_of_endpointParentMassComparison
#print axioms actualIntervalEndpointParentMassComparison
#print axioms adjacentFineParentCompatible_of_doubledParentPartitioning
#print axioms adjacentFineParentCompatible_of_exactScaleDef212Inputs
#print axioms adjacentFineParentCompatible_of_largeIntervalLocalGeometry
#print axioms adjacentUpper_of_baseFrostman_adjacentFineParentCompatible
#print axioms adjacentUpper_of_baseFrostman_largeIntervalLocalGeometry
#print axioms
  allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_of_adjacentFineParentCompatible
#print axioms surjective_parent_maps_do_not_force_fine_parent_square

end

end Family8NormalizedLongIntervalEndpointParentMassV1
