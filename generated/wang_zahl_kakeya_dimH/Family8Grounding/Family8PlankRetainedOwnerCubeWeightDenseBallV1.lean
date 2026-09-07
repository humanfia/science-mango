import Family8Grounding.Family8PlankRetainedOwnerThickenedMassTransportV1
import «CubeWeightExactRadiusMaster»
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankRetainedOwnerCubeWeightDenseBallV1

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

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Callback-free dense-ball refinement of the retained owner datum

The retained fine shading and the induced thickened-owner shading have the
same literal shaded union.  Apply the existing exact-radius CubeWeight master
to these two actual shadings.  Compactness supplies its maximal separated
packing; the ambient fine cardinality supplies the pointwise multiplicity cap;
and nonzero retained mass supplies every positivity input.

The output is one common spatial restriction of both shadings.  It retains
the fine mass with the explicit finite logarithmic loss and, at every point of
the final thickened-owner union, has a common local fine-union mass in the
radius-`rho` ball up to the fixed factor `2000`.  No cell cover, local mass
band, or density conclusion is assumed.
-/

/-- The actual retained source index type is nonempty whenever its shading
mass is nonzero. -/
theorem retainedOwnerIndex_nonempty_of_shadingMass_ne_zero
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0) :
    Nonempty {i // i ∈ retainedOwnerSourceIndices C q} := by
  have hindices :=
    retainedOwnerSourceIndices_nonempty_of_mass_ne_zero D C q hmass
  exact ⟨⟨hindices.choose, hindices.choose_spec⟩⟩

/-- Concrete dense-ball output for the literal retained fine and
thickened-owner shadings. -/
theorem exists_retainedOwner_commonWeightedDenseBallLevel
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (rho : NNReal) (hrho : 0 < rho)
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
        let mass := fun p ↦ cellMass fine cell hcell p
        let loc := fun p ↦ localCellVolume fine cell p
        let selected := (highCells mass loc K).filter fun p ↦
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
  let fine := (retainedOwnerPlankFamily D C q).shading
  let coarse := retainedOwnerThickenedShading D C q
  let A := familyUnion (retainedOwnerPlankFamily D C q).family ∪
    familyUnion (retainedOwnerThickenedFamily D C q)
  let K := Fintype.card {i // i ∈ retainedOwnerSourceIndices C q}
  let P : PackingCertificate A ((rho / 2) / 3) := Classical.choice <|
    exists_finiteFamily_halfRadius_packingCertificate
      (retainedOwnerPlankFamily D C q).family
      (retainedOwnerThickenedFamily D C q) hrho
  refine ⟨P, ?_⟩
  have hAmeas : MeasurableSet A :=
    (familyUnion_measurableSet
      (retainedOwnerPlankFamily D C q).family).union
      (familyUnion_measurableSet (retainedOwnerThickenedFamily D C q))
  have hFineA : fine.shadedUnion ⊆ A :=
    fine.shadedUnion_subset_familyUnion.trans Set.subset_union_left
  have hK : 0 < K := by
    exact Fintype.card_pos_iff.mpr
      (retainedOwnerIndex_nonempty_of_shadingMass_ne_zero D C q hmass)
  have hpoint : ∀ x, fine.pointMultiplicity x ≤ K := by
    intro x
    exact fine.pointMultiplicity_le_card x
  have hpositive : 0 < fine.shadingMass.toNNReal := by
    apply bot_lt_iff_ne_bot.mpr
    intro hzero
    apply hmass
    calc
      fine.shadingMass = (fine.shadingMass.toNNReal : ENNReal) :=
        (ENNReal.coe_toNNReal fine.shadingMass_lt_top.ne).symm
      _ = 0 := by simp [hzero]
  have hcover : fine.shadedUnion ⊆ coarse.shadedUnion := by
    rw [retainedOwnerThickenedShading_shadedUnion_eq D C q]
  exact exists_common_weightedPackingLevel_exactRadius
    fine coarse hAmeas P hrho hFineA K hK hpoint hpositive hcover
      fine.shadingMass le_rfl

#print axioms retainedOwnerIndex_nonempty_of_shadingMass_ne_zero
#print axioms exists_retainedOwner_commonWeightedDenseBallLevel

end
end Family8PlankRetainedOwnerCubeWeightDenseBallV1
