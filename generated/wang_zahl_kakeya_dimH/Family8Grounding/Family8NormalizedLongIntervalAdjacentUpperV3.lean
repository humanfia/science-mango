import Family8Grounding.Family8NormalizedLongIntervalAdjacentUpperV2
import FamilyStickyGrounding.FamilyStickyHierarchyTerminalIdentityMultiscaleFrostmanBridgeV1

/-!
# Concrete identity-cover adjacent normalized upper

For the repository's radius-changed identity coherent cover, the missing
parent square in V2 commutes definitionally and the source all-scale
Frostman certificate is already produced.  This successor therefore removes
both structural callbacks.  Only the displayed scalar loss and the geometric
half-scale range remain.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8NormalizedLongIntervalAdjacentUpperV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessBridgeV4.StickyScaleCover
open Family8NormalizedLongIntervalAdjacentUpperV2
open Family8NormalizedLongIntervalWitnessV1
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCapturedTubeBoxWidthV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentIntervalProducerV1.CoherentStickyMultiscaleCover
open FamilyStickyScaleChainParentFiberMassProducerV1.StickyScaleCover
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyHierarchyTerminalIdentityMultiscaleFrostmanBridgeV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}

/-- The actual density endpoint for the concrete identity coherent cover.
Its cross-scale parent square is `rfl`, and its source Frostman certificate
is the existing singleton-fibre producer. -/
theorem adjacentUpper_identityRadius_actualParentDensity
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (htauHalf : forall m : Fin depth,
      S.tau m <= (2 : NNReal)⁻¹)
    (eta : Nat -> Real) (N : Nat)
    (herror : forall m : Fin depth,
      capturedTubeBoxLoss delta 1 *
          actualParentFiberMassLoss
            ((identityRadiusCoherentCover D.family).base.cover
              (S.tau m) (S.delta_le_tau m)
              ((S.tau_le_theta m).trans (S.theta_le_one m))) *
          (parentFiberMassRatioFloor delta (S.tau m))⁻¹ <=
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^
          eta (N - 1))) :
    forall m : Fin depth,
      parentNormalizedFiberCFMax
          ((identityRadiusCoherentCover D.family).intervalScaleCover
            (S.tau m) (S.theta m) (S.delta_le_tau m)
            (S.tau_le_theta m) (S.theta_le_one m)) <=
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^
          eta (N - 1)) := by
  apply adjacentUpper_of_baseFrostman_actualParentDensity
    D hD (identityRadiusCoherentCover D.family) S
    (identityRadiusCoherentCover_isFrostmanAtEveryScale
      D.family hD.delta_pos)
    htauHalf
  · intro m rho hTauRho hRhoOne i hi
    rfl
  · exact herror

/-- The stopping trichotomy on the same concrete identity cover, with both
all-scale structure and adjacent parent coherence constructed internally. -/
theorem allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_identityRadius
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (eta : Nat -> Real) (N : Nat) (hN : 1 <= N)
    (htauHalf : forall m : Fin depth,
      S.tau m <= (2 : NNReal)⁻¹)
    (hsourceError : forall m : Fin depth,
      capturedTubeBoxLoss delta 1 <=
        (((S.tau m / delta : NNReal) : ENNReal) ^ eta (N - 1)))
    (hadjacentError : forall m : Fin depth,
      capturedTubeBoxLoss delta 1 *
          actualParentFiberMassLoss
            ((identityRadiusCoherentCover D.family).base.cover
              (S.tau m) (S.delta_le_tau m)
              ((S.tau_le_theta m).trans (S.theta_le_one m))) *
          (parentFiberMassRatioFloor delta (S.tau m))⁻¹ <=
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^
          eta (N - 1))) :
    ((S.AllStepsLarge epsilon ∨
        Nonempty
          (NormalizedLongIntervalWitness D.family
            (identityRadiusCoherentCover D.family) N epsilon eta S)) ∨
      Nonempty
        (FirstActualNormalizedCrossingWitness D hD
          (identityRadiusCoherentCover D.family) S epsilon hepsilon eta N)) := by
  apply
    allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_of_parentMassComparison
      D hD (identityRadiusCoherentCover D.family) S epsilon hepsilon eta N hN
      (identityRadiusCoherentCover_isFrostmanAtEveryScale
        D.family hD.delta_pos)
      hsourceError
      (fun m => parentFiberMassRatioFloor delta (S.tau m))
      (fun m => actualParentFiberMassLoss
        ((identityRadiusCoherentCover D.family).base.cover
          (S.tau m) (S.delta_le_tau m)
          ((S.tau_le_theta m).trans (S.theta_le_one m))))
  · intro m
    exact parentFiberMassRatioFloor_ne_zero hD.delta_pos (S.tau m)
  · intro m
    exact parentFiberMassRatioFloor_ne_top delta (S.tau m)
      (hD.delta_pos.trans_le (S.delta_le_tau m))
  · intro m
    exact actualIntervalParentMassComparison
      (identityRadiusCoherentCover D.family) (S.tau m)
      (S.delta_le_tau m)
      ((S.tau_le_theta m).trans (S.theta_le_one m))
      hD.delta_pos hD.delta_le_half (htauHalf m) (by
        intro rho hTauRho hRhoOne i hi
        rfl)
  · exact hadjacentError

#print axioms adjacentUpper_identityRadius_actualParentDensity
#print axioms
  allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness_identityRadius

end

end Family8NormalizedLongIntervalAdjacentUpperV3
