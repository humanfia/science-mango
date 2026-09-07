import Family8Grounding.Family8NormalizedLongIntervalExactDef212ClosureV3

/-!
# Minimal finite-sequence Definition 2.12 input

The normalized stopping argument reads geometry only at the finitely many
lower endpoints `tau_m` and upper endpoints `theta_m`.  It does not need an
exact Definition 2.12 package at every real radius.  This file isolates the
minimal common-cover data: C-uniformity at each lower endpoint, doubled
partitioning at each upper endpoint, and rescaled fibre CWA at both.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8NormalizedLongIntervalFiniteDef212InputsV4

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

/-- Exactly the Definition 2.12 fields consumed at the finite stopping
sequence.  All covers retain one common fine index type and belong to the
same coherent hierarchy. -/
structure FiniteSequenceDef212Inputs
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth) (K : NNReal) where
  tau_c_uniform : ∀ m : Fin depth,
    IsCUniform
      (C.base.cover (S.tau m) (S.delta_le_tau m)
        ((S.tau_le_theta m).trans (S.theta_le_one m)))
      (K : ENNReal)
  theta_doubled_parent_partitioning : ∀ m : Fin depth,
    IsDoubledParentPartitioning
      (C.base.cover (S.theta m)
        ((S.delta_le_tau m).trans (S.tau_le_theta m))
        (S.theta_le_one m))
  tau_unitRescalingGeometry : ∀ m : Fin depth,
    UnitRescalingGeometry
      (C.base.cover (S.tau m) (S.delta_le_tau m)
        ((S.tau_le_theta m).trans (S.theta_le_one m)))
  tau_rescaled_fibres_cwa : ∀ m : Fin depth,
    (tau_unitRescalingGeometry m).FibresSatisfyCWA (K : ENNReal)
  theta_unitRescalingGeometry : ∀ m : Fin depth,
    UnitRescalingGeometry
      (C.base.cover (S.theta m)
        ((S.delta_le_tau m).trans (S.tau_le_theta m))
        (S.theta_le_one m))
  theta_rescaled_fibres_cwa : ∀ m : Fin depth,
    (theta_unitRescalingGeometry m).FibresSatisfyCWA (K : ENNReal)

/-- The stronger exact all-radius package restricts to the finite data above. -/
noncomputable def FiniteSequenceDef212Inputs.ofExactScale
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth) {K : NNReal}
    (H : ExactScaleDef212Inputs C.base K) :
    FiniteSequenceDef212Inputs C S K where
  tau_c_uniform := fun m ↦ H.c_uniform
    (S.tau m) (S.delta_le_tau m)
    ((S.tau_le_theta m).trans (S.theta_le_one m))
  theta_doubled_parent_partitioning := fun m ↦
    H.doubled_parent_partitioning
      (S.theta m)
      ((S.delta_le_tau m).trans (S.tau_le_theta m))
      (S.theta_le_one m)
  tau_unitRescalingGeometry := fun m ↦ H.unitRescalingGeometry
    (S.tau m) (S.delta_le_tau m)
    ((S.tau_le_theta m).trans (S.theta_le_one m))
  tau_rescaled_fibres_cwa := fun m ↦ H.rescaled_fibres_cwa
    (S.tau m) (S.delta_le_tau m)
    ((S.tau_le_theta m).trans (S.theta_le_one m))
  theta_unitRescalingGeometry := fun m ↦ H.unitRescalingGeometry
    (S.theta m)
    ((S.delta_le_tau m).trans (S.tau_le_theta m))
    (S.theta_le_one m)
  theta_rescaled_fibres_cwa := fun m ↦ H.rescaled_fibres_cwa
    (S.theta m)
    ((S.delta_le_tau m).trans (S.tau_le_theta m))
    (S.theta_le_one m)

/-- Rescaled CWA at the finitely many lower endpoints produces every source
normalized upper bound used by the selector. -/
theorem sourceUpper_of_finiteSequenceDef212Inputs
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth) {K : NNReal}
    (H : FiniteSequenceDef212Inputs C S K)
    (eta : Nat → Real) (N : Nat)
    (herror : ∀ m : Fin depth,
      ((K : ENNReal) * 16 * volume (unitBallBody : Set Space)) ≤
        (((S.tau m / delta : NNReal) : ENNReal) ^
          eta (N - 1))) :
    ∀ m : Fin depth,
      parentNormalizedFiberCFMax
          (C.base.cover (S.tau m) (S.delta_le_tau m)
            ((S.tau_le_theta m).trans (S.theta_le_one m))) ≤
        (((S.tau m / delta : NNReal) : ENNReal) ^
          eta (N - 1)) := by
  intro m
  have hAt := ScaleCover.isFrostmanAtScale_of_rescaledFibresCWA
    (C.base.cover (S.tau m) (S.delta_le_tau m)
      ((S.tau_le_theta m).trans (S.theta_le_one m)))
    hD.delta_le_half (H.tau_unitRescalingGeometry m)
    (H.tau_rescaled_fibres_cwa m)
  exact
    ((isFrostmanAtScale_iff_parentNormalizedFiberCFMax_le
      (C.base.cover (S.tau m) (S.delta_le_tau m)
        ((S.tau_le_theta m).trans (S.theta_le_one m)))
      hD.delta_pos
      ((K : ENNReal) * 16 * volume (unitBallBody : Set Space))).mp hAt).trans
      (herror m)

/-- Upper-endpoint CWA supplies the base fibre Frostman bound; lower-endpoint
C-uniformity and upper doubled partitioning then close every adjacent bound. -/
theorem adjacentUpper_of_finiteSequenceDef212Inputs
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth) {K : NNReal}
    (H : FiniteSequenceDef212Inputs C S K)
    (htauHalf : ∀ m : Fin depth, S.tau m ≤ (2 : NNReal)⁻¹)
    (eta : Nat → Real) (N : Nat)
    (herror : ∀ m : Fin depth,
      ((K : ENNReal) * 16 * volume (unitBallBody : Set Space)) *
          ((16 * (K : ENNReal)) * 16) ≤
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
      C S H.theta_doubled_parent_partitioning
  intro m
  have hbaseAt := ScaleCover.isFrostmanAtScale_of_rescaledFibresCWA
    (C.base.cover (S.theta m)
      ((S.delta_le_tau m).trans (S.tau_le_theta m))
      (S.theta_le_one m))
    hD.delta_le_half (H.theta_unitRescalingGeometry m)
    (H.theta_rescaled_fibres_cwa m)
  have hAt :=
    intervalScaleCover_isFrostmanAtScale_of_baseFrostman_cUniform
      C (S.tau m) (S.theta m) (S.delta_le_tau m)
      (S.tau_le_theta m) (S.theta_le_one m)
      hD.delta_pos hD.delta_le_half (htauHalf m)
      (hparent m) (H.tau_c_uniform m) hbaseAt
  exact
    ((isFrostmanAtScale_iff_parentNormalizedFiberCFMax_le
      (C.intervalScaleCover (S.tau m) (S.theta m)
        (S.delta_le_tau m) (S.tau_le_theta m)
        (S.theta_le_one m))
      (hD.delta_pos.trans_le (S.delta_le_tau m))
      (((K : ENNReal) * 16 * volume (unitBallBody : Set Space)) *
        ((16 * (K : ENNReal)) * 16))).mp hAt).trans
      (herror m)

/-- The normalized stopping trichotomy needs only the finite-sequence input,
not the stronger exact all-radius package. -/
theorem allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_of_finiteDef212
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (eta : Nat → Real) (N : Nat) (hN : 1 ≤ N)
    {K : NNReal}
    (H : FiniteSequenceDef212Inputs C S K)
    (hsourceError : ∀ m : Fin depth,
      ((K : ENNReal) * 16 * volume (unitBallBody : Set Space)) ≤
        (((S.tau m / delta : NNReal) : ENNReal) ^
          eta (N - 1)))
    (htauHalf : ∀ m : Fin depth, S.tau m ≤ (2 : NNReal)⁻¹)
    (hadjacentError : ∀ m : Fin depth,
      ((K : ENNReal) * 16 * volume (unitBallBody : Set Space)) *
          ((16 * (K : ENNReal)) * 16) ≤
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^
          eta (N - 1))) :
    ((S.AllStepsLarge epsilon ∨
        Nonempty (NormalizedLongIntervalWitness
          D.family C N epsilon eta S)) ∨
      Nonempty (FirstActualNormalizedCrossingWitness
        D hD C S epsilon hepsilon eta N)) := by
  exact allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness
    D hD C S epsilon hepsilon eta N hN
    (sourceUpper_of_finiteSequenceDef212Inputs
      D hD C S H eta N hsourceError)
    (adjacentUpper_of_finiteSequenceDef212Inputs
      D hD C S H htauHalf eta N hadjacentError)

#print axioms FiniteSequenceDef212Inputs.ofExactScale
#print axioms sourceUpper_of_finiteSequenceDef212Inputs
#print axioms adjacentUpper_of_finiteSequenceDef212Inputs
#print axioms
  allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_of_finiteDef212

end
end Family8NormalizedLongIntervalFiniteDef212InputsV4
