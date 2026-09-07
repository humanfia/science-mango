import Family8Grounding.Family8PlankRetainedOwnerFullBallDensityEndpointV2
import Family8Grounding.Family8PlankRetainedOwnerBetaUniformCoefficientEnvelopeV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankRetainedOwnerUniformFullBallPowerEndpointV1

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
open Family8PlankRetainedOwnerFullBallPowerAbsorptionV1
open Family8PlankRetainedOwnerFullBallDensityEndpointV2
open Family8PlankRetainedOwnerBetaCountReserveV1
open Family8PlankRetainedOwnerBetaUniformPowerEnvelopeV2
open Family8PlankRetainedOwnerBetaUniformCoefficientEnvelopeV1

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Uniform retained-owner full-ball power endpoint

The callback-free full-ball density endpoint and the datum-uniform coefficient
envelope are applied to the same retained-owner datum.  The packing certificate,
dyadic exponent, selected cells, and final fine/coarse shadings are unchanged.
The literal logarithmic owner-selection loss is paid by the canonical
`comparisonConstant = 576` count reserve.
-/

theorem exists_retainedOwner_uniformFullBallPowerEndpoint
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (rho : NNReal) (hrho : 0 < rho) (hrhoUpper : rho ≤ 1)
    (hthetaUpper : theta ≤ 1)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (density : ENNReal) (hcomparison : D.comparisonConstant = 576)
    {beta absorbExponent : Real} (hbeta : beta ∈ Ioc 0 1)
    (ha : 0 < a) (habsorb : 0 < absorbExponent)
    (hsmall : a ≤ retainedOwnerBetaUniformThreshold beta absorbExponent)
    (hdensity : density ≤ D.shading.shadingDensity)
    (hretain : D.shading.shadingMass ≤
      ((Nat.log 2 (Fintype.card iota) + 1 : Nat) : ENNReal) *
        (retainedOwnerPlankFamily D C q).shading.shadingMass) :
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
              ((a : ENNReal) ^ (-absorbExponent) *
                (Fintype.card iota : ENNReal) ^ (1 - beta / 2)) *
                  volume (finalFine.shadedUnion ∩
                    Metric.ball x (rho : Real)) := by
  dsimp only
  obtain ⟨P, n, hn, hout⟩ :=
    exists_retainedOwner_fullBallDensityEndpoint
      D C q rho hrho hrhoUpper hthetaUpper hmass density
        ((Nat.log 2 (Fintype.card iota) + 1 : Nat) : ENNReal)
        hdensity hretain
  refine ⟨P, n, hn, ?_⟩
  dsimp only at hout ⊢
  rcases hout with ⟨hretainFine, hcover, hsame, hsource,
    hcellBand, hballBand, hfull⟩
  refine ⟨hretainFine, hcover, hsame, hsource,
    hcellBand, hballBand, ?_⟩
  have hcoefficient :=
    fixedComparison_retainedLogCoefficient_le_uniformPower
      D C q hmass hcomparison hbeta ha habsorb hsmall
  intro x hx
  calc
    density * ((a : ENNReal) * (b : ENNReal)) *
        volume (Metric.ball (0 : Space) (rho : Real)) ≤
      retainedOwnerFullBallCoefficient D
          ((Nat.log 2 (Fintype.card iota) + 1 : Nat) : ENNReal) *
        volume ((restrictToCells
          (retainedOwnerPlankFamily D C q).shading
          (packingCellFin P)
          (measurableSet_packingCellFin
            ((familyUnion_measurableSet
                (retainedOwnerPlankFamily D C q).family).union
              (familyUnion_measurableSet
                (retainedOwnerThickenedFamily D C q))) P)
          ((highCells
            (fun p => cellMass (retainedOwnerPlankFamily D C q).shading
              (packingCellFin P)
              (measurableSet_packingCellFin
                ((familyUnion_measurableSet
                    (retainedOwnerPlankFamily D C q).family).union
                  (familyUnion_measurableSet
                    (retainedOwnerThickenedFamily D C q))) P) p)
            (fun p => localCellVolume (retainedOwnerPlankFamily D C q).shading
              (packingCellFin P) p)
            (Fintype.card {i // i ∈ retainedOwnerSourceIndices C q})).filter fun p =>
              cubeBucket
                (dominanceCutoff
                  (fun p => cellMass (retainedOwnerPlankFamily D C q).shading
                    (packingCellFin P)
                    (measurableSet_packingCellFin
                      ((familyUnion_measurableSet
                          (retainedOwnerPlankFamily D C q).family).union
                        (familyUnion_measurableSet
                          (retainedOwnerThickenedFamily D C q))) P) p)
                  (Fintype.card {i // i ∈ retainedOwnerSourceIndices C q}))
                (cubeExponent (a := Fin P.centers.card)
                  (Fintype.card {i // i ∈ retainedOwnerSourceIndices C q}))
                (localCellVolume (retainedOwnerPlankFamily D C q).shading
                  (packingCellFin P) p) = n)).shadedUnion ∩
            Metric.ball x (rho : Real)) := by
      simpa only [retainedOwnerFullBallCoefficient, mul_assoc] using hfull x hx
    _ ≤ ((a : ENNReal) ^ (-absorbExponent) *
          (Fintype.card iota : ENNReal) ^ (1 - beta / 2)) *
        volume ((restrictToCells
          (retainedOwnerPlankFamily D C q).shading
          (packingCellFin P)
          (measurableSet_packingCellFin
            ((familyUnion_measurableSet
                (retainedOwnerPlankFamily D C q).family).union
              (familyUnion_measurableSet
                (retainedOwnerThickenedFamily D C q))) P)
          ((highCells
            (fun p => cellMass (retainedOwnerPlankFamily D C q).shading
              (packingCellFin P)
              (measurableSet_packingCellFin
                ((familyUnion_measurableSet
                    (retainedOwnerPlankFamily D C q).family).union
                  (familyUnion_measurableSet
                    (retainedOwnerThickenedFamily D C q))) P) p)
            (fun p => localCellVolume (retainedOwnerPlankFamily D C q).shading
              (packingCellFin P) p)
            (Fintype.card {i // i ∈ retainedOwnerSourceIndices C q})).filter fun p =>
              cubeBucket
                (dominanceCutoff
                  (fun p => cellMass (retainedOwnerPlankFamily D C q).shading
                    (packingCellFin P)
                    (measurableSet_packingCellFin
                      ((familyUnion_measurableSet
                          (retainedOwnerPlankFamily D C q).family).union
                        (familyUnion_measurableSet
                          (retainedOwnerThickenedFamily D C q))) P) p)
                  (Fintype.card {i // i ∈ retainedOwnerSourceIndices C q}))
                (cubeExponent (a := Fin P.centers.card)
                  (Fintype.card {i // i ∈ retainedOwnerSourceIndices C q}))
                (localCellVolume (retainedOwnerPlankFamily D C q).shading
                  (packingCellFin P) p) = n)).shadedUnion ∩
            Metric.ball x (rho : Real)) := by
      gcongr

#print axioms exists_retainedOwner_uniformFullBallPowerEndpoint

end
end Family8PlankRetainedOwnerUniformFullBallPowerEndpointV1
