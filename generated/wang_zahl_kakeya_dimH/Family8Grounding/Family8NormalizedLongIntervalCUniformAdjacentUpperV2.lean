import Family8Grounding.Family8NormalizedLongIntervalCUniformEndpointV1

/-!
# C-uniform adjacent normalized upper bounds

The endpoint-only parent square follows from Definition 2.10 doubled-parent
partitioning.  Definition 2.12 C-uniformity then compares every pair of
lower endpoint fibre masses, so summing the comparison removes the absolute
parent-density floor.  This file packages that fixed-loss endpoint estimate
along a finite scale sequence and plugs it into the normalized stopping
trichotomy.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8NormalizedLongIntervalCUniformAdjacentUpperV2

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
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8NormalizedLongIntervalCUniformEndpointV1
open Family8NormalizedLongIntervalEndpointParentMassV1
open Family8NormalizedLongIntervalSourceUpperV1
open Family8NormalizedLongIntervalWitnessV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentIntervalProducerV1.CoherentStickyMultiscaleCover

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}

/-- Doubled-parent partitioning supplies the endpoint square, while
C-uniformity gives a fixed `256 * uniformity` adjacent Frostman loss. -/
theorem adjacentUpper_of_baseFrostman_cUniform_partitioning
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    {baseError uniformity : ENNReal}
    (hFbase : C.base.IsFrostmanAtEveryScale baseError)
    (htauHalf : ∀ m : Fin depth, S.tau m ≤ (2 : NNReal)⁻¹)
    (hpartition : ∀ m : Fin depth,
      IsDoubledParentPartitioning
        (C.base.cover (S.theta m)
          ((S.delta_le_tau m).trans (S.tau_le_theta m))
          (S.theta_le_one m)))
    (huniform : ∀ m : Fin depth,
      IsCUniform
        (C.base.cover (S.tau m) (S.delta_le_tau m)
          ((S.tau_le_theta m).trans (S.theta_le_one m)))
        uniformity)
    (eta : Nat → Real) (N : Nat)
    (herror : ∀ m : Fin depth,
      baseError * ((16 * uniformity) * 16) ≤
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^
          eta (N - 1))) :
    ∀ m : Fin depth,
      parentNormalizedFiberCFMax
          (C.intervalScaleCover (S.tau m) (S.theta m)
            (S.delta_le_tau m) (S.tau_le_theta m)
            (S.theta_le_one m)) ≤
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^
          eta (N - 1)) := by
  have hparent : AdjacentFineParentCompatible C S :=
    adjacentFineParentCompatible_of_doubledParentPartitioning
      C S hpartition
  intro m
  have hAt :=
    intervalScaleCover_isFrostmanAtScale_of_baseFrostman_cUniform
      C (S.tau m) (S.theta m) (S.delta_le_tau m)
      (S.tau_le_theta m) (S.theta_le_one m)
      hD.delta_pos hD.delta_le_half (htauHalf m)
      (hparent m) (huniform m)
      (hFbase (S.theta m)
        ((S.delta_le_tau m).trans (S.tau_le_theta m))
        (S.theta_le_one m))
  exact
    ((isFrostmanAtScale_iff_parentNormalizedFiberCFMax_le
      (C.intervalScaleCover (S.tau m) (S.theta m)
        (S.delta_le_tau m) (S.tau_le_theta m)
        (S.theta_le_one m))
      (hD.delta_pos.trans_le (S.delta_le_tau m))
      (baseError * ((16 * uniformity) * 16))).mp hAt).trans
      (herror m)

/-- The exact-scale Definition 2.12 input package provides both geometric
premises of the previous theorem at every scale. -/
theorem adjacentUpper_of_baseFrostman_exactScaleDef212Inputs
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    {K : NNReal}
    (H : ExactScaleDef212Inputs C.base K)
    {baseError : ENNReal}
    (hFbase : C.base.IsFrostmanAtEveryScale baseError)
    (htauHalf : ∀ m : Fin depth, S.tau m ≤ (2 : NNReal)⁻¹)
    (eta : Nat → Real) (N : Nat)
    (herror : ∀ m : Fin depth,
      baseError * ((16 * (K : ENNReal)) * 16) ≤
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^
          eta (N - 1))) :
    ∀ m : Fin depth,
      parentNormalizedFiberCFMax
          (C.intervalScaleCover (S.tau m) (S.theta m)
            (S.delta_le_tau m) (S.tau_le_theta m)
            (S.theta_le_one m)) ≤
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^
          eta (N - 1)) := by
  apply adjacentUpper_of_baseFrostman_cUniform_partitioning
    D hD C S hFbase htauHalf
  · intro m
    exact H.doubled_parent_partitioning
      (S.theta m)
      ((S.delta_le_tau m).trans (S.tau_le_theta m))
      (S.theta_le_one m)
  · intro m
    exact H.c_uniform
      (S.tau m) (S.delta_le_tau m)
      ((S.tau_le_theta m).trans (S.theta_le_one m))
  · exact herror

/-- Exact-scale Definition 2.12 geometry closes every adjacent interval in
the normalized stopping trichotomy.  The only remaining quantitative input
is the genuine all-scale Frostman bound for the source hierarchy. -/
theorem allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_of_exactScaleDef212Inputs
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (eta : Nat → Real) (N : Nat) (hN : 1 ≤ N)
    {K : NNReal}
    (H : ExactScaleDef212Inputs C.base K)
    {sourceError : ENNReal}
    (hFsource : C.base.IsFrostmanAtEveryScale sourceError)
    (hsourceError : ∀ m : Fin depth,
      sourceError ≤ (((S.tau m / delta : NNReal) : ENNReal) ^
        eta (N - 1)))
    (htauHalf : ∀ m : Fin depth, S.tau m ≤ (2 : NNReal)⁻¹)
    (hadjacentError : ∀ m : Fin depth,
      sourceError * ((16 * (K : ENNReal)) * 16) ≤
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
      (adjacentUpper_of_baseFrostman_exactScaleDef212Inputs
        D hD C S H hFsource htauHalf eta N hadjacentError)

#print axioms adjacentUpper_of_baseFrostman_cUniform_partitioning
#print axioms adjacentUpper_of_baseFrostman_exactScaleDef212Inputs
#print axioms
  allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_of_exactScaleDef212Inputs

end
end Family8NormalizedLongIntervalCUniformAdjacentUpperV2
