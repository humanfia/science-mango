import Family8Grounding.Family8PlankRetainedOwnerDyadicWeightBallCrossV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankRetainedOwnerCubeWeightDensityCrossV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth
open Submission.Kakeya.ConvexFactoring.BallwiseLocalVolumeUniformization
open Submission.Kakeya.ConvexFactoring.CubeWeightUniformization
open Submission.Kakeya.ConvexFactoring.CubeWeightMaster
open Submission.Kakeya.ConvexFactoring.CubeWeightExactRadiusMaster
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerThickenedInducedShadingV2
open Family8PlankRetainedOwnerCubeWeightDenseBallV1
open Family8PlankRetainedOwnerDyadicWeightBallCrossV1

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Same-output dense-ball and cutoff-density cross

This endpoint augments the callback-free CubeWeight dense-ball selection on
the retained owner family with the crossed global-mass estimate proved for its
literal packing certificate and dyadic weight.  Hence every local radius-rho
lower bound and the inequality `fineMass * vol(B_(rho/6)) ≤ 250*K*w` concern
the same `P`, `n`, selected cells, final fine shading, and final coarse shading.
-/

/-- One actual CubeWeight output simultaneously has retained mass, the common
fine/coarse restriction, exact-radius local volume bands, and the division-free
global-mass-to-dyadic-weight estimate. -/
theorem exists_retainedOwner_commonWeightedDenseBallLevel_with_densityCross
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (rho : NNReal) (hrho : 0 < rho) (hrhoUpper : rho ≤ 1)
    (hthetaUpper : theta ≤ 1)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0) :
    let fine := (retainedOwnerPlankFamily D C q).shading
    let coarse := retainedOwnerThickenedShading D C q
    let A := familyUnion (retainedOwnerPlankFamily D C q).family ∪
      familyUnion (retainedOwnerThickenedFamily D C q)
    let K := Fintype.card {i // i ∈ retainedOwnerSourceIndices C q}
    ∃ P : PackingCertificate A ((rho / 2) / 3),
      ∃ n, n ≤ cubeExponent (a := Fin P.centers.card) K ∧
        let cell := packingCellFin P
        let hcell := measurableSet_packingCellFin
          ((familyUnion_measurableSet
              (retainedOwnerPlankFamily D C q).family).union
            (familyUnion_measurableSet
              (retainedOwnerThickenedFamily D C q))) P
        let mass := fun p => cellMass fine cell hcell p
        let loc := fun p => localCellVolume fine cell p
        let selected := (highCells mass loc K).filter fun p =>
          cubeBucket (dominanceCutoff mass K)
            (cubeExponent (a := Fin P.centers.card) K) (loc p) = n
        let finalFine := restrictToCells fine cell hcell selected
        let finalCoarse := restrictToCells coarse cell hcell selected
        let w := 2 ^ n * dominanceCutoff mass K
        fine.shadingMass ≤
            (2 * (cubeExponent (a := Fin P.centers.card) K + 1)) •
              finalFine.shadingMass ∧
          finalFine.shadedUnion ⊆ finalCoarse.shadedUnion ∧
          finalFine.shadingMass ≤ K • finalCoarse.shadingMass ∧
          fine.shadingMass ≤
            (2 * (cubeExponent (a := Fin P.centers.card) K + 1)) •
              (K • finalCoarse.shadingMass) ∧
          (∀ p ∈ selected,
            w ≤ localCellVolume finalFine cell p ∧
              localCellVolume finalFine cell p < 2 * w) ∧
          (∀ x ∈ finalCoarse.shadedUnion,
            (w : ENNReal) ≤ volume (finalFine.shadedUnion ∩
              Metric.ball x (rho : Real)) ∧
            volume (finalFine.shadedUnion ∩ Metric.ball x (rho : Real)) ≤
              2000 * (w : ENNReal)) ∧
          fine.shadingMass * volume (Metric.ball (0 : Space)
              ((((rho / 2) / 3 : NNReal)) : Real)) ≤
            ((250 * K : Nat) : ENNReal) * (w : ENNReal) := by
  dsimp only
  obtain ⟨P, n, hn, hout⟩ :=
    exists_retainedOwner_commonWeightedDenseBallLevel
      D C q rho hrho hmass
  refine ⟨P, n, hn, ?_⟩
  dsimp only at hout ⊢
  rcases hout with ⟨hretain, hcover, hsame, hsource,
    hcellBand, hballBand⟩
  refine ⟨hretain, hcover, hsame, hsource, hcellBand, hballBand, ?_⟩
  exact retainedOwnerFineMass_mul_packingBallVolume_le_dyadicWeight
    D C q rho hrho hrhoUpper hthetaUpper P hmass n

#print axioms exists_retainedOwner_commonWeightedDenseBallLevel_with_densityCross

end
end Family8PlankRetainedOwnerCubeWeightDensityCrossV1
