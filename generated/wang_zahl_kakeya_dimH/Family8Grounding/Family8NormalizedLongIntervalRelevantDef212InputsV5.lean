import Family8Grounding.Family8NormalizedLongIntervalFiniteDef212InputsV4

/-!
# Definition 2.12 input only on relevant long intervals

The finite selector reads its two endpoint upper bounds only after it has
selected a long terminal interval.  In particular, it need not pay a fixed
rescaled-fibre constant at the final endpoint `tau = delta`, when that step
is already large.  This file records the logically minimal conditional
version of the finite Definition 2.12 input and rebuilds the stopping
trichotomy from it.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8NormalizedLongIntervalRelevantDef212InputsV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8Def212RescaledCWASourceFrostmanV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8NormalizedLongIntervalCUniformEndpointV1
open Family8NormalizedLongIntervalEndpointParentMassV1
open Family8NormalizedLongIntervalFiniteDef212InputsV4
open Family8NormalizedLongIntervalWitnessV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentIntervalProducerV1.CoherentStickyMultiscaleCover

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}
  {fine : UniformTubeFamily delta iota}

/-- The one adjacent fine-parent square needed at a fixed sequence index. -/
def AdjacentFineParentCompatibleAt
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth) (m : Fin depth) : Prop :=
  forall i : iota,
    i ∈ (C.base.cover (S.tau m) (S.delta_le_tau m)
      ((S.tau_le_theta m).trans (S.theta_le_one m))).activeFine ->
      (C.base.cover (S.theta m)
        ((S.delta_le_tau m).trans (S.tau_le_theta m))
        (S.theta_le_one m)).parent i =
      C.parent (S.tau m) (S.theta m) (S.delta_le_tau m)
        (S.tau_le_theta m) (S.theta_le_one m)
        ((C.base.cover (S.tau m) (S.delta_le_tau m)
          ((S.tau_le_theta m).trans (S.theta_le_one m))).parent i)

/-- Upper doubled-parent partitioning forces the fixed adjacent square. -/
theorem adjacentFineParentCompatibleAt_of_doubledParentPartitioning
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth) (m : Fin depth)
    (hpartition : IsDoubledParentPartitioning
      (C.base.cover (S.theta m)
        ((S.delta_le_tau m).trans (S.tau_le_theta m))
        (S.theta_le_one m))) :
    AdjacentFineParentCompatibleAt C S m := by
  intro i hi
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
  have hik : i ∈ doubledFiber R (R.parent i) :=
    fiber_subset_doubledFiber R (R.parent i)
      ((R.mem_fiber i (R.parent i)).2 ⟨hiR, rfl⟩)
  have hil : i ∈ doubledFiber R l := by
    rw [mem_doubledFiber]
    refine ⟨hiR, ?_⟩
    have hFineCross :
        (fine.tubes i).carrier ⊆ (R.coarse.tubes l).carrier := by
      simpa only [l, R, T] using
        (T.carrier_subset i hi).trans
          (C.carrier_subset (S.tau m) (S.theta m)
            (S.delta_le_tau m) (S.tau_le_theta m) (S.theta_le_one m)
            (T.parent i) hTi)
    exact hFineCross.trans
      (carrier_subset_twoFoldTubeCarrier (R.coarse.tubes l))
  exact (Finset.disjoint_left.mp
    (hpartition (R.parent i) hk l hl hne) hik hil)

/-- Definition 2.12 data is required only if the corresponding interval can
become the long terminal output of the finite selector. -/
structure RelevantFiniteSequenceDef212Inputs
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth) (epsilon : Real) (K : NNReal) where
  tau_c_uniform : forall m : Fin depth, S.IsLong epsilon m ->
    IsCUniform
      (C.base.cover (S.tau m) (S.delta_le_tau m)
        ((S.tau_le_theta m).trans (S.theta_le_one m)))
      (K : ENNReal)
  theta_doubled_parent_partitioning :
    forall m : Fin depth, S.IsLong epsilon m ->
      IsDoubledParentPartitioning
        (C.base.cover (S.theta m)
          ((S.delta_le_tau m).trans (S.tau_le_theta m))
          (S.theta_le_one m))
  tau_unitRescalingGeometry : forall m : Fin depth, S.IsLong epsilon m ->
    UnitRescalingGeometry
      (C.base.cover (S.tau m) (S.delta_le_tau m)
        ((S.tau_le_theta m).trans (S.theta_le_one m)))
  tau_rescaled_fibres_cwa : forall m : Fin depth,
    forall hlong : S.IsLong epsilon m,
      (tau_unitRescalingGeometry m hlong).FibresSatisfyCWA (K : ENNReal)
  theta_unitRescalingGeometry : forall m : Fin depth, S.IsLong epsilon m ->
    UnitRescalingGeometry
      (C.base.cover (S.theta m)
        ((S.delta_le_tau m).trans (S.tau_le_theta m))
        (S.theta_le_one m))
  theta_rescaled_fibres_cwa : forall m : Fin depth,
    forall hlong : S.IsLong epsilon m,
      (theta_unitRescalingGeometry m hlong).FibresSatisfyCWA (K : ENNReal)

/-- The unconditional finite input restricts to the relevant one. -/
noncomputable def RelevantFiniteSequenceDef212Inputs.ofFinite
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth) (epsilon : Real) {K : NNReal}
    (H : FiniteSequenceDef212Inputs C S K) :
    RelevantFiniteSequenceDef212Inputs C S epsilon K where
  tau_c_uniform := fun m _hlong => H.tau_c_uniform m
  theta_doubled_parent_partitioning := fun m _hlong =>
    H.theta_doubled_parent_partitioning m
  tau_unitRescalingGeometry := fun m _hlong =>
    H.tau_unitRescalingGeometry m
  tau_rescaled_fibres_cwa := fun m _hlong =>
    H.tau_rescaled_fibres_cwa m
  theta_unitRescalingGeometry := fun m _hlong =>
    H.theta_unitRescalingGeometry m
  theta_rescaled_fibres_cwa := fun m _hlong =>
    H.theta_rescaled_fibres_cwa m

/-- Source normalized control is needed only at a long terminal index. -/
theorem sourceUpper_of_relevantFiniteSequenceDef212Inputs
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth) (epsilon : Real) {K : NNReal}
    (H : RelevantFiniteSequenceDef212Inputs C S epsilon K)
    (eta : Nat -> Real) (N : Nat)
    (herror : forall m : Fin depth, forall _hlong : S.IsLong epsilon m,
      ((K : ENNReal) * 16 * volume (unitBallBody : Set Space)) <=
        (((S.tau m / delta : NNReal) : ENNReal) ^ eta (N - 1))) :
    forall m : Fin depth, S.IsLong epsilon m ->
      parentNormalizedFiberCFMax
          (C.base.cover (S.tau m) (S.delta_le_tau m)
            ((S.tau_le_theta m).trans (S.theta_le_one m))) <=
        (((S.tau m / delta : NNReal) : ENNReal) ^ eta (N - 1)) := by
  intro m hlong
  have hAt := ScaleCover.isFrostmanAtScale_of_rescaledFibresCWA
    (C.base.cover (S.tau m) (S.delta_le_tau m)
      ((S.tau_le_theta m).trans (S.theta_le_one m)))
    hD.delta_le_half (H.tau_unitRescalingGeometry m hlong)
    (H.tau_rescaled_fibres_cwa m hlong)
  exact
    ((isFrostmanAtScale_iff_parentNormalizedFiberCFMax_le
      (C.base.cover (S.tau m) (S.delta_le_tau m)
        ((S.tau_le_theta m).trans (S.theta_le_one m)))
      hD.delta_pos
      ((K : ENNReal) * 16 * volume (unitBallBody : Set Space))).mp hAt).trans
      (herror m hlong)

/-- Adjacent normalized control is likewise local to the selected long
terminal interval. -/
theorem adjacentUpper_of_relevantFiniteSequenceDef212Inputs
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth) (epsilon : Real) {K : NNReal}
    (H : RelevantFiniteSequenceDef212Inputs C S epsilon K)
    (htauHalf : forall m : Fin depth, S.IsLong epsilon m ->
      S.tau m <= (2 : NNReal)⁻¹)
    (eta : Nat -> Real) (N : Nat)
    (herror : forall m : Fin depth, forall _hlong : S.IsLong epsilon m,
      ((K : ENNReal) * 16 * volume (unitBallBody : Set Space)) *
          ((16 * (K : ENNReal)) * 16) <=
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (N - 1))) :
    forall m : Fin depth, S.IsLong epsilon m ->
      parentNormalizedFiberCFMax
          (C.intervalScaleCover (S.tau m) (S.theta m)
            (S.delta_le_tau m) (S.tau_le_theta m)
            (S.theta_le_one m)) <=
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (N - 1)) := by
  intro m hlong
  have hparent : AdjacentFineParentCompatibleAt C S m :=
    adjacentFineParentCompatibleAt_of_doubledParentPartitioning C S m
      (H.theta_doubled_parent_partitioning m hlong)
  have hbaseAt := ScaleCover.isFrostmanAtScale_of_rescaledFibresCWA
    (C.base.cover (S.theta m)
      ((S.delta_le_tau m).trans (S.tau_le_theta m))
      (S.theta_le_one m))
    hD.delta_le_half (H.theta_unitRescalingGeometry m hlong)
    (H.theta_rescaled_fibres_cwa m hlong)
  have hAt :=
    intervalScaleCover_isFrostmanAtScale_of_baseFrostman_cUniform
      C (S.tau m) (S.theta m) (S.delta_le_tau m)
      (S.tau_le_theta m) (S.theta_le_one m)
      hD.delta_pos hD.delta_le_half (htauHalf m hlong)
      hparent (H.tau_c_uniform m hlong) hbaseAt
  exact
    ((isFrostmanAtScale_iff_parentNormalizedFiberCFMax_le
      (C.intervalScaleCover (S.tau m) (S.theta m)
        (S.delta_le_tau m) (S.tau_le_theta m)
        (S.theta_le_one m))
      (hD.delta_pos.trans_le (S.delta_le_tau m))
      (((K : ENNReal) * 16 * volume (unitBallBody : Set Space)) *
        ((16 * (K : ENNReal)) * 16))).mp hAt).trans
      (herror m hlong)

/-- The selector only applies endpoint estimates to its long terminal
output.  The first-crossing branch requires neither endpoint estimate. -/
theorem allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_of_longBounds
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (eta : Nat -> Real) (N : Nat) (hN : 1 <= N)
    (hsource : forall m : Fin depth, S.IsLong epsilon m ->
      parentNormalizedFiberCFMax
          (C.base.cover (S.tau m) (S.delta_le_tau m)
            ((S.tau_le_theta m).trans (S.theta_le_one m))) <=
        (((S.tau m / delta : NNReal) : ENNReal) ^ eta (N - 1)))
    (hadjacent : forall m : Fin depth, S.IsLong epsilon m ->
      parentNormalizedFiberCFMax
          (C.intervalScaleCover (S.tau m) (S.theta m)
            (S.delta_le_tau m) (S.tau_le_theta m)
            (S.theta_le_one m)) <=
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (N - 1))) :
    ((S.AllStepsLarge epsilon ∨
        Nonempty (NormalizedLongIntervalWitness
          D.family C N epsilon eta S)) ∨
      Nonempty (FirstActualNormalizedCrossingWitness
        D hD C S epsilon hepsilon eta N)) := by
  rcases
      Family8NormalizedCFDividingWitnessFiniteSelectionV6.CoherentStickyMultiscaleCover.allLarge_or_longTerminalActualBarrier_or_firstActualNormalizedCrossing
        D hD C S epsilon hepsilon eta N with
    hterminal | hfirst
  · left
    rcases hterminal with hall | ⟨m, hlong, hbarrier⟩
    · exact Or.inl hall
    · exact Or.inr ⟨
        NormalizedLongIntervalWitness.of_longTerminalActualBarrier
          D hD C S hepsilon hN m hlong hbarrier
            (hsource m hlong) (hadjacent m hlong)⟩
  · right
    exact FirstActualNormalizedCrossingWitness.nonempty_of_selector_output
      hfirst

/-- Full stopping closure from Definition 2.12 data and numerical bounds only
on long intervals. -/
theorem allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_of_relevantDef212
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (eta : Nat -> Real) (N : Nat) (hN : 1 <= N)
    {K : NNReal}
    (H : RelevantFiniteSequenceDef212Inputs C S epsilon K)
    (hsourceError : forall m : Fin depth,
      forall _hlong : S.IsLong epsilon m,
        ((K : ENNReal) * 16 * volume (unitBallBody : Set Space)) <=
          (((S.tau m / delta : NNReal) : ENNReal) ^ eta (N - 1)))
    (htauHalf : forall m : Fin depth, S.IsLong epsilon m ->
      S.tau m <= (2 : NNReal)⁻¹)
    (hadjacentError : forall m : Fin depth,
      forall _hlong : S.IsLong epsilon m,
        ((K : ENNReal) * 16 * volume (unitBallBody : Set Space)) *
            ((16 * (K : ENNReal)) * 16) <=
          (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (N - 1))) :
    ((S.AllStepsLarge epsilon ∨
        Nonempty (NormalizedLongIntervalWitness
          D.family C N epsilon eta S)) ∨
      Nonempty (FirstActualNormalizedCrossingWitness
        D hD C S epsilon hepsilon eta N)) := by
  exact
    allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_of_longBounds
      D hD C S epsilon hepsilon eta N hN
      (sourceUpper_of_relevantFiniteSequenceDef212Inputs
        D hD C S epsilon H eta N hsourceError)
      (adjacentUpper_of_relevantFiniteSequenceDef212Inputs
        D hD C S epsilon H htauHalf eta N hadjacentError)

#print axioms adjacentFineParentCompatibleAt_of_doubledParentPartitioning
#print axioms RelevantFiniteSequenceDef212Inputs.ofFinite
#print axioms sourceUpper_of_relevantFiniteSequenceDef212Inputs
#print axioms adjacentUpper_of_relevantFiniteSequenceDef212Inputs
#print axioms
  allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_of_longBounds
#print axioms
  allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_of_relevantDef212

end
end Family8NormalizedLongIntervalRelevantDef212InputsV5
