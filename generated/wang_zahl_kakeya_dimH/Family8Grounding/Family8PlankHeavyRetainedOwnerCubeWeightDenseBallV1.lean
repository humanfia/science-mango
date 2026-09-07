import Family8Grounding.Family8PlankHeavyRetainedOwnerActualDatumV2
import «CubeWeightExactRadiusMaster»
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankHeavyRetainedOwnerCubeWeightDenseBallV1

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
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankHeavyRetainedOwnerActualDatumV2

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# CubeWeight refinement after the heavy owner restriction

The exact-radius common-cell construction is rerun on the literal heavy
source datum and its induced thickened-owner shading.  Thus its retained mass
and every later active row come only from owners which already satisfy the
common half-average fibre-mass floor.
-/

theorem heavyRetainedOwnerIndex_nonempty_of_shadingMass_ne_zero
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (hmass : (heavyRetainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0) :
    Nonempty {i // i ∈ heavyRetainedOwnerSourceIndices C q} := by
  have hindices : (heavyRetainedOwnerSourceIndices C q).Nonempty := by
    by_contra hempty
    have hzero : heavyRetainedOwnerSourceIndices C q = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    apply hmass
    rw [heavyRetainedOwnerPlankFamily_shadingMass,
      ← sum_heavyRetained_eq_heavyRetainedOwnerMass, hzero]
    simp
  exact ⟨⟨hindices.choose, hindices.choose_spec⟩⟩

/-- Nonzero retained mass implies nonzero mass after the honest factor-two
heavy restriction. -/
theorem heavyRetainedOwner_shadingMass_ne_zero_of_retainedMass_ne_zero
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0) :
    (heavyRetainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0 := by
  intro hzero
  have hle :=
    retainedOwnerPlankFamily_mass_le_two_mul_heavyActualMass D C q
  rw [hzero, mul_zero] at hle
  exact hmass (bot_unique hle)

/-- Concrete common weighted dense-ball output for the heavy fine and coarse
shadings.  No cell, local density, or rowwise mass callback is assumed. -/
theorem exists_heavyRetainedOwner_commonWeightedDenseBallLevel
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (rho : NNReal) (hrho : 0 < rho)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0) :
    let fine := (heavyRetainedOwnerPlankFamily D C q).shading
    let coarse := heavyRetainedOwnerThickenedShading D C q
    let A := familyUnion (heavyRetainedOwnerPlankFamily D C q).family ∪
      familyUnion (heavyRetainedOwnerThickenedFamily D C q)
    let K := Fintype.card {i // i ∈ heavyRetainedOwnerSourceIndices C q}
    ∃ P : PackingCertificate A ((rho / 2) / 3),
      ∃ n, n ≤ cubeExponent (a := Fin P.centers.card) K ∧
        let cell := packingCellFin P
        let hcell := measurableSet_packingCellFin
          ((familyUnion_measurableSet
              (heavyRetainedOwnerPlankFamily D C q).family).union
            (familyUnion_measurableSet
              (heavyRetainedOwnerThickenedFamily D C q))) P
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
          ∀ x ∈ finalCoarse.shadedUnion,
            (w : ENNReal) ≤ volume (finalFine.shadedUnion ∩
              Metric.ball x (rho : Real)) ∧
            volume (finalFine.shadedUnion ∩ Metric.ball x (rho : Real)) ≤
              2000 * (w : ENNReal) := by
  let fine := (heavyRetainedOwnerPlankFamily D C q).shading
  let coarse := heavyRetainedOwnerThickenedShading D C q
  let A := familyUnion (heavyRetainedOwnerPlankFamily D C q).family ∪
    familyUnion (heavyRetainedOwnerThickenedFamily D C q)
  let K := Fintype.card {i // i ∈ heavyRetainedOwnerSourceIndices C q}
  let P : PackingCertificate A ((rho / 2) / 3) := Classical.choice <|
    exists_finiteFamily_halfRadius_packingCertificate
      (heavyRetainedOwnerPlankFamily D C q).family
      (heavyRetainedOwnerThickenedFamily D C q) hrho
  refine ⟨P, ?_⟩
  have hAmeas : MeasurableSet A :=
    (familyUnion_measurableSet
      (heavyRetainedOwnerPlankFamily D C q).family).union
      (familyUnion_measurableSet
        (heavyRetainedOwnerThickenedFamily D C q))
  have hFineA : fine.shadedUnion ⊆ A :=
    fine.shadedUnion_subset_familyUnion.trans Set.subset_union_left
  have hHeavyMass : fine.shadingMass ≠ 0 := by
    exact heavyRetainedOwner_shadingMass_ne_zero_of_retainedMass_ne_zero
      D C q hmass
  have hK : 0 < K := by
    exact Fintype.card_pos_iff.mpr
      (heavyRetainedOwnerIndex_nonempty_of_shadingMass_ne_zero
        D C q hHeavyMass)
  have hpoint : ∀ x, fine.pointMultiplicity x ≤ K := by
    intro x
    exact fine.pointMultiplicity_le_card x
  have hpositive : 0 < fine.shadingMass.toNNReal := by
    apply bot_lt_iff_ne_bot.mpr
    intro hzero
    apply hHeavyMass
    calc
      fine.shadingMass = (fine.shadingMass.toNNReal : ENNReal) :=
        (ENNReal.coe_toNNReal fine.shadingMass_lt_top.ne).symm
      _ = 0 := by simp [hzero]
  have hcover : fine.shadedUnion ⊆ coarse.shadedUnion := by
    rw [heavyRetainedOwnerThickenedShading_shadedUnion_eq D C q]
  exact exists_common_weightedPackingLevel_exactRadius
    fine coarse hAmeas P hrho hFineA K hK hpoint hpositive hcover
      fine.shadingMass le_rfl

#print axioms heavyRetainedOwnerIndex_nonempty_of_shadingMass_ne_zero
#print axioms heavyRetainedOwner_shadingMass_ne_zero_of_retainedMass_ne_zero
#print axioms exists_heavyRetainedOwner_commonWeightedDenseBallLevel

end
end Family8PlankHeavyRetainedOwnerCubeWeightDenseBallV1
