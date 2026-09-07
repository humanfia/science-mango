import Family8Grounding.Family8PlankRetainedOwnerAmbientVolumeCapV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankRetainedOwnerDyadicWeightBallCrossV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth
open Submission.Kakeya.ConvexFactoring.BallwiseLocalVolumeUniformization
open Submission.Kakeya.ConvexFactoring.CubeWeightUniformization
open Submission.Kakeya.ConvexFactoring.CubeWeightMaster
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerThickenedInducedShadingV2
open Family8PlankRetainedOwnerCubeWeightDenseBallV1
open Family8PlankRetainedOwnerCutoffBallCrossV1
open Family8PlankRetainedOwnerAmbientVolumeCapV1

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Dyadic dense-ball weight crossed with retained mass

The ambient-volume cap turns the exact cutoff/packing-card cross estimate into
a fixed-constant inequality.  Since the selected dyadic weight is
`w = 2^n * cutoff`, the same literal weight that appears in every local
radius-`rho` ball controls the retained global mass times the smaller packing
ball volume.  Both the packing cardinality and ambient volume are eliminated.
-/

/-- On the exact packing and cell-mass data used by CubeWeight, retained mass
times the packing-ball volume is at most `250 * K * w`. -/
theorem retainedOwnerFineMass_mul_packingBallVolume_le_dyadicWeight
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (rho : NNReal) (hrho : 0 < rho) (hrhoUpper : rho ≤ 1)
    (hthetaUpper : theta ≤ 1)
    (P : PackingCertificate
      (familyUnion (retainedOwnerPlankFamily D C q).family ∪
        familyUnion (retainedOwnerThickenedFamily D C q))
      ((rho / 2) / 3))
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (n : Nat) :
    let fine := (retainedOwnerPlankFamily D C q).shading
    let cell := packingCellFin P
    let hcell := measurableSet_packingCellFin
      ((familyUnion_measurableSet
          (retainedOwnerPlankFamily D C q).family).union
        (familyUnion_measurableSet
          (retainedOwnerThickenedFamily D C q))) P
    let mass := fun p => cellMass fine cell hcell p
    let K := Fintype.card {i // i ∈ retainedOwnerSourceIndices C q}
    let w := 2 ^ n * dominanceCutoff mass K
    fine.shadingMass * volume (Metric.ball (0 : Space)
        ((((rho / 2) / 3 : NNReal)) : Real)) ≤
      ((250 * K : Nat) : ENNReal) * (w : ENNReal) := by
  dsimp only
  let fine := (retainedOwnerPlankFamily D C q).shading
  let cell := packingCellFin P
  let hcell := measurableSet_packingCellFin
    ((familyUnion_measurableSet
        (retainedOwnerPlankFamily D C q).family).union
      (familyUnion_measurableSet
        (retainedOwnerThickenedFamily D C q))) P
  let mass := fun p => cellMass fine cell hcell p
  let K := Fintype.card {i // i ∈ retainedOwnerSourceIndices C q}
  have hcross :=
    retainedOwnerFineMass_mul_packingBallVolume_le_cutoff_mul_ambient
      D C q rho hrho P hmass
  dsimp only at hcross
  have hamb :=
    retainedOwnerPacking_ambientThickening_volume_le_oneTwentyFive
      D C q rho hrhoUpper hthetaUpper hmass
  have hpow : (1 : NNReal) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hcutoffWeight : dominanceCutoff mass K ≤
      2 ^ n * dominanceCutoff mass K := by
    calc
      dominanceCutoff mass K = 1 * dominanceCutoff mass K :=
        (one_mul _).symm
      _ ≤ 2 ^ n * dominanceCutoff mass K := by gcongr
  calc
    fine.shadingMass * volume (Metric.ball (0 : Space)
        ((((rho / 2) / 3 : NNReal)) : Real)) ≤
      ((2 * K : Nat) : ENNReal) *
        (dominanceCutoff mass K : ENNReal) *
        volume (Metric.thickening
          (((((rho / 2) / 3 : NNReal)) : Real) +
            ((theta * b : NNReal) : Real))
          (D.ambient : Set Space)) := hcross
    _ ≤ ((2 * K : Nat) : ENNReal) *
        (dominanceCutoff mass K : ENNReal) * 125 := by gcongr
    _ = ((250 * K : Nat) : ENNReal) *
        (dominanceCutoff mass K : ENNReal) := by
      push_cast
      ring
    _ ≤ ((250 * K : Nat) : ENNReal) *
        ((2 ^ n * dominanceCutoff mass K : NNReal) : ENNReal) := by
      gcongr
    _ = _ := rfl

#print axioms retainedOwnerFineMass_mul_packingBallVolume_le_dyadicWeight

end
end Family8PlankRetainedOwnerDyadicWeightBallCrossV1
