import Family8Grounding.Family8PlankRetainedOwnerFullBallNormalizationV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankRetainedOwnerFullBallDensityEndpointV2

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
open Family8PlankRetainedOwnerDensityCardCrossV1
open Family8PlankRetainedOwnerLocalDenseBallEndpointV1
open Family8PlankRetainedOwnerFullBallNormalizationV1

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Callback-free retained-owner full-ball density endpoint

This is the same CubeWeight selection and the same final fine/coarse shadings
as the local dense-ball endpoint.  The last estimate is normalized to the
radius-`rho` ball and the literal plank cross-section `a * b`.
-/

theorem exists_retainedOwner_fullBallDensityEndpoint
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (rho : NNReal) (hrho : 0 < rho) (hrhoUpper : rho ≤ 1)
    (hthetaUpper : theta ≤ 1)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (density loss : ENNReal)
    (hdensity : density ≤ D.shading.shadingDensity)
    (hretain : D.shading.shadingMass ≤
      loss * (retainedOwnerPlankFamily D C q).shading.shadingMass) :
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
          ∀ x ∈ finalCoarse.shadedUnion,
            density * ((a : ENNReal) * (b : ENNReal)) *
                volume (Metric.ball (0 : Space) (rho : Real)) ≤
              54000 * (D.comparisonConstant : ENNReal) ^ 3 * loss *
                volume (finalFine.shadedUnion ∩
                  Metric.ball x (rho : Real)) := by
  dsimp only
  obtain ⟨P, n, hn, hout⟩ :=
    exists_retainedOwner_localDenseBallDensityEndpoint
      D C q rho hrho hrhoUpper hthetaUpper hmass
        density loss hdensity hretain
  refine ⟨P, n, hn, ?_⟩
  dsimp only at hout ⊢
  rcases hout with ⟨hretainFine, hcover, hsame, hsource,
    hcellBand, hballBand, hlocal⟩
  refine ⟨hretainFine, hcover, hsame, hsource,
    hcellBand, hballBand, ?_⟩
  intro x hx
  exact density_mul_crossSection_mul_ballVolume_le_of_packingBall
    D C q hmass rho density loss _ (hlocal x hx)

#print axioms exists_retainedOwner_fullBallDensityEndpoint

end
end Family8PlankRetainedOwnerFullBallDensityEndpointV2
