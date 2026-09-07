import Family8Grounding.Family8PlankRetainedOwnerPackingAmbientBoundV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankRetainedOwnerCutoffBallCrossV1

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
open Family8PlankRetainedOwnerPackingAmbientBoundV1

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Crossed cutoff and packing-ball estimate

The CubeWeight cutoff divides the retained fine mass by the genuine packing
cardinality.  The preceding ambient-packing theorem controls that same
cardinality times the packing-ball volume.  This module crosses the two exact
identities on the literal packing certificate, eliminating the cardinality
without estimating it or accepting a scalar comparison callback.
-/

/-- The retained fine mass times the actual packing-ball volume is bounded by
the CubeWeight cutoff times the explicit ambient-thickening volume. -/
theorem retainedOwnerFineMass_mul_packingBallVolume_le_cutoff_mul_ambient
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (rho : NNReal) (hrho : 0 < rho)
    (P : PackingCertificate
      (familyUnion (retainedOwnerPlankFamily D C q).family ∪
        familyUnion (retainedOwnerThickenedFamily D C q))
      ((rho / 2) / 3))
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0) :
    let fine := (retainedOwnerPlankFamily D C q).shading
    let cell := packingCellFin P
    let hcell := measurableSet_packingCellFin
      ((familyUnion_measurableSet
          (retainedOwnerPlankFamily D C q).family).union
        (familyUnion_measurableSet
          (retainedOwnerThickenedFamily D C q))) P
    let mass := fun p => cellMass fine cell hcell p
    let K := Fintype.card {i // i ∈ retainedOwnerSourceIndices C q}
    fine.shadingMass * volume (Metric.ball (0 : Space)
        ((((rho / 2) / 3 : NNReal)) : Real)) ≤
      ((2 * K : Nat) : ENNReal) *
        (dominanceCutoff mass K : ENNReal) *
        volume (Metric.thickening
          (((((rho / 2) / 3 : NNReal)) : Real) +
            ((theta * b : NNReal) : Real))
          (D.ambient : Set Space)) := by
  dsimp only
  let fine := (retainedOwnerPlankFamily D C q).shading
  let A := familyUnion (retainedOwnerPlankFamily D C q).family ∪
    familyUnion (retainedOwnerThickenedFamily D C q)
  let cell := packingCellFin P
  let hcell := measurableSet_packingCellFin
    ((familyUnion_measurableSet
        (retainedOwnerPlankFamily D C q).family).union
      (familyUnion_measurableSet
        (retainedOwnerThickenedFamily D C q))) P
  let mass := fun p => cellMass fine cell hcell p
  let K := Fintype.card {i // i ∈ retainedOwnerSourceIndices C q}
  have hAmeas : MeasurableSet A :=
    (familyUnion_measurableSet
      (retainedOwnerPlankFamily D C q).family).union
      (familyUnion_measurableSet (retainedOwnerThickenedFamily D C q))
  have hFineA : fine.shadedUnion ⊆ A :=
    fine.shadedUnion_subset_familyUnion.trans Set.subset_union_left
  have hsum : (∑ p, mass p) = fine.shadingMass.toNNReal := by
    simpa [mass, cell, hcell] using
      packing_sum_cellMass_eq_shadingMass fine hAmeas P
        (show 0 < rho / 2 by positivity) hFineA
  have hpositive : 0 < fine.shadingMass.toNNReal := by
    apply bot_lt_iff_ne_bot.mpr
    intro hzero
    apply hmass
    calc
      fine.shadingMass = (fine.shadingMass.toNNReal : ENNReal) :=
        (ENNReal.coe_toNNReal fine.shadingMass_lt_top.ne).symm
      _ = 0 := by simp [hzero]
  have hK : 0 < K := by
    exact Fintype.card_pos_iff.mpr
      (retainedOwnerIndex_nonempty_of_shadingMass_ne_zero D C q hmass)
  have hP : 0 < P.centers.card := by
    by_contra hP
    have hP0 : P.centers.card = 0 := Nat.eq_zero_of_not_pos hP
    have hzero : (∑ p, mass p) = 0 := by
      let hempty : IsEmpty (Fin P.centers.card) :=
        Fintype.card_eq_zero_iff.mp (by simpa using hP0)
      exact Finset.sum_eq_zero fun p _ => (hempty.false p).elim
    rw [hsum] at hzero
    exact hpositive.ne' hzero
  have hcutoff :
      ((2 * K * P.centers.card : Nat) : NNReal) *
          dominanceCutoff mass K = fine.shadingMass.toNNReal := by
    rw [dominanceCutoff, hsum]
    simp only [Fintype.card_fin]
    field_simp
    norm_cast
  have hpacking :=
    retainedOwnerPacking_card_smul_ballVolume_le_ambientThickening
      D C q ((rho / 2) / 3) P
  calc
    fine.shadingMass * volume (Metric.ball (0 : Space)
        ((((rho / 2) / 3 : NNReal)) : Real)) =
      (((2 * K : Nat) : ENNReal) *
        (dominanceCutoff mass K : ENNReal)) *
        (P.centers.card • volume (Metric.ball (0 : Space)
          ((((rho / 2) / 3 : NNReal)) : Real))) := by
      rw [show fine.shadingMass = (fine.shadingMass.toNNReal : ENNReal) by
        exact (ENNReal.coe_toNNReal fine.shadingMass_lt_top.ne).symm]
      rw [← hcutoff]
      push_cast
      simp only [nsmul_eq_mul]
      ring
    _ ≤ (((2 * K : Nat) : ENNReal) *
        (dominanceCutoff mass K : ENNReal)) *
        volume (Metric.thickening
          (((((rho / 2) / 3 : NNReal)) : Real) +
            ((theta * b : NNReal) : Real))
          (D.ambient : Set Space)) := by
      gcongr
    _ = _ := by ring

#print axioms retainedOwnerFineMass_mul_packingBallVolume_le_cutoff_mul_ambient

end
end Family8PlankRetainedOwnerCutoffBallCrossV1
