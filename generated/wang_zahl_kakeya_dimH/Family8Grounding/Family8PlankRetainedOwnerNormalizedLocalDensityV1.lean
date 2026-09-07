import Family8Grounding.Family8PlankRetainedOwnerDensityCardCrossV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankRetainedOwnerNormalizedLocalDensityV1

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
open Family8PlankRetainedOwnerDyadicWeightBallCrossV1
open Family8PlankRetainedOwnerDensityCardCrossV1

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Cardinality-free normalized local density

The source-density/cardinality lower bound and the packing/dyadic-weight upper
bound contain the same positive retained cardinality.  Cancelling that literal
cardinality gives the paper's division-free local-density scale: no source
cardinality, retained mass, packing cardinality, or ambient volume remains.
-/

theorem retainedOwner_normalizedDensity_mul_packingBallVolume_le_dyadicWeight
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
    (n : Nat) (density loss : ENNReal)
    (hdensity : density ≤ D.shading.shadingDensity)
    (hretain : D.shading.shadingMass ≤
      loss * (retainedOwnerPlankFamily D C q).shading.shadingMass) :
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
    density * plankCertifiedLowerVolume D *
        volume (Metric.ball (0 : Space)
          ((((rho / 2) / 3 : NNReal)) : Real)) ≤
      250 * loss * (w : ENNReal) := by
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
  have hdensityCard :=
    retainedOwner_density_mul_card_mul_certifiedLowerVolume_le_mass
      D C q density loss hdensity hretain
  have hdyadic :=
    retainedOwnerFineMass_mul_packingBallVolume_le_dyadicWeight
      D C q rho hrho hrhoUpper hthetaUpper P hmass n
  dsimp only at hdyadic
  have hK : 0 < K := by
    exact Fintype.card_pos_iff.mpr
      (retainedOwnerIndex_nonempty_of_shadingMass_ne_zero D C q hmass)
  have hKne : (K : ENNReal) ≠ 0 := by exact_mod_cast hK.ne'
  apply (ENNReal.mul_le_mul_iff_left hKne ENNReal.coe_ne_top).mp
  calc
    (density * plankCertifiedLowerVolume D *
        volume (Metric.ball (0 : Space)
          ((((rho / 2) / 3 : NNReal)) : Real))) * (K : ENNReal) =
      (density * (K : ENNReal) * plankCertifiedLowerVolume D) *
        volume (Metric.ball (0 : Space)
          ((((rho / 2) / 3 : NNReal)) : Real)) := by ring
    _ ≤ (loss * fine.shadingMass) *
        volume (Metric.ball (0 : Space)
          ((((rho / 2) / 3 : NNReal)) : Real)) := by gcongr
    _ = loss * (fine.shadingMass *
        volume (Metric.ball (0 : Space)
          ((((rho / 2) / 3 : NNReal)) : Real))) := by ring
    _ ≤ loss * (((250 * K : Nat) : ENNReal) *
        ((2 ^ n * dominanceCutoff mass K : NNReal) : ENNReal)) := by
      gcongr
    _ = (250 * loss *
        ((2 ^ n * dominanceCutoff mass K : NNReal) : ENNReal)) *
          (K : ENNReal) := by
      push_cast
      ring

#print axioms retainedOwner_normalizedDensity_mul_packingBallVolume_le_dyadicWeight

end
end Family8PlankRetainedOwnerNormalizedLocalDensityV1
