import Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyFullCatalogueCWAV1
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnFreshSelectionV2
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnCopyTransportCoreV1
import Family8Grounding.Family8FiniteRandomRigidMotionB2KatzTaoTransportV1
import Family8Grounding.Family8CardinalCWARestrictionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000
set_option linter.style.haveILetI false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyRefinementCWAV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8CardinalCWARestrictionV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionB2KatzTaoTransportV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionPaperFixedJohnCopyTransportCoreV1
open Family8FiniteRandomRigidMotionPaperFixedJohnFreshSelectionV2
open Family8FiniteRigidMotionOrthogonalScaleOnlyCatalogueScaleV1
open Family8FiniteRigidMotionOrthogonalTranslationCWAProductMeanV1
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyConflictMeanV1
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyFullCatalogueCWAV1
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyJointSelectorV1
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyProductLawV1
open Family8FiniteRigidMotionOrthogonalTranslationV2
open Family8GeneralizedFrostmanMultiplicityV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PolynomialJohnFrameBoxVolumeV2

noncomputable section

/-!
# Fresh refinement of the scale-only joint rigid copy

The common scale-only tuple already controls both finite-test families.  This
module feeds its actual conflict-degree output to the existing fresh greedy
selector and restricts the full copied-family Convex Wolff certificate to the
same selected set.
-/

/-- The literal greedy loss associated to the projected conflict threshold. -/
def scaleOnlyJointGreedyLoss (AConflict : Real) (C : ENNReal) : Nat :=
  scaleOnlyJointConflictThreshold AConflict C + 1

/-- One common scale-only tuple yields a genuine fresh admissible refinement
carrying both Katz--Tao and cardinal-normalized Convex Wolff control. -/
theorem exists_scaleOnlyJointChoice_refinement_CWA
    {delta : NNReal} {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {C : ENNReal} (hCTop : C ≠ ∞)
    (hKT : IsKatzTao C D.family.bodyFamily)
    (repetitions : Nat) (hrepetitions : 0 < repetitions)
    (AJohn AConflict : Real) (hAJohn : 0 ≤ AJohn)
    (hscaleJ :
      (repetitions : ENNReal) * scaleOnlyJointJohnMeanCoefficient iota *
          scaleOnlyJointHalfSq delta ≤
        (128 * C) * scaleOnlyJointMotionBallVolume)
    (hscaleE :
      (repetitions : ENNReal) *
          scaleOnlyJointConflictMeanCoefficient delta iota *
          scaleOnlyJointHalfSq delta ≤
        (128 * C) * scaleOnlyJointMotionBallVolume)
    (htailRoom :
      (Fintype.card (ScaleOnlyFixedJohnTest delta hD.delta_pos) : Real) *
            Real.exp (Real.exp 1 - 1) * Real.exp AConflict +
          (Fintype.card
            (ScaleOnlyFixedJohnElongatedTest D hD.delta_pos
              (scaleOnlyOrthogonalCatalogueScale D hD.delta_pos)) : Real) *
            Real.exp (Real.exp 1 - 1) * Real.exp AJohn <
        Real.exp AJohn * Real.exp AConflict) :
    ∃ (omega : Fin repetitions → ScaleOnlyJointChoice D hD.delta_pos)
      (selected : Finset (Fin repetitions × iota)),
      selected.Nonempty ∧
      (restrictActualTubeDatum
        (eighthNormalizedDatum
          (indexedRigidCopyDatum
            (fun j ↦
              scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D
                hD.delta_pos
                (scaleOnlyOrthogonalCatalogueScale D hD.delta_pos)
                (omega j)) D)) selected).IsAdmissible ∧
      (Fintype.card (Fin repetitions × iota) : ENNReal) ≤
        (scaleOnlyJointGreedyLoss AConflict (128 * C) : ENNReal) *
          (selected.card : ENNReal) ∧
      (eighthNormalizedDatum
        (indexedRigidCopyDatum
          (fun j ↦
            scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D
              hD.delta_pos
              (scaleOnlyOrthogonalCatalogueScale D hD.delta_pos)
              (omega j)) D)).shading.shadingMass ≤
        (scaleOnlyJointGreedyLoss AConflict (128 * C) : ENNReal) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum
              (indexedRigidCopyDatum
                (fun j ↦
                  scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D
                    hD.delta_pos
                    (scaleOnlyOrthogonalCatalogueScale D hD.delta_pos)
                    (omega j)) D)) selected).shading.shadingMass ∧
      IsKatzTao (128 * ((repetitions : ENNReal) * C))
        (restrictActualTubeDatum
          (eighthNormalizedDatum
            (indexedRigidCopyDatum
              (fun j ↦
                scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D
                  hD.delta_pos
                  (scaleOnlyOrthogonalCatalogueScale D hD.delta_pos)
                  (omega j)) D)) selected).family.bodyFamily ∧
      SatisfiesConvexWolffAxioms
        ((scaleOnlyJointGreedyLoss AConflict (128 * C) : ENNReal) *
          (scaleOnlyFullCopiedCWAParameter D hD.delta_pos repetitions AJohn
              (128 * C) * johnCatalogueVolumeConstant))
        (restrictActualTubeDatum
          (eighthNormalizedDatum
            (indexedRigidCopyDatum
              (fun j ↦
                scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D
                  hD.delta_pos
                  (scaleOnlyOrthogonalCatalogueScale D hD.delta_pos)
                  (omega j)) D)) selected).family.bodyFamily ∧
      D.shading.averageMultiplicity ≤
        (scaleOnlyJointGreedyLoss AConflict (128 * C) : ENNReal) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum
              (indexedRigidCopyDatum
                (fun j ↦
                  scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D
                    hD.delta_pos
                    (scaleOnlyOrthogonalCatalogueScale D hD.delta_pos)
                    (omega j)) D)) selected).shading.averageMultiplicity := by
  have h128CTop : (128 * C : ENNReal) ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hCTop
  have hnormalizedKT :
      IsKatzTao (128 * C)
        (eighthNormalizedDatum D).family.bodyFamily :=
    eighthNormalizedDatum_isKatzTao D hD.delta_le_half hKT
  obtain ⟨omega, hjohn, hconflict⟩ :=
    exists_scaleOnlyJointChoice_john_and_conflict_bounds
      D hD.delta_pos hD.delta_le_half h128CTop hnormalizedKT
      repetitions AJohn AConflict hscaleJ hscaleE htailRoom
  let n := scaleOnlyOrthogonalCatalogueScale D hD.delta_pos
  let motion : ScaleOnlyJointChoice D hD.delta_pos → RigidMotion :=
    scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hD.delta_pos n
  let copied := indexedRigidCopyDatum (fun j ↦ motion (omega j)) D
  let normalized := eighthNormalizedDatum copied
  let threshold := scaleOnlyJointConflictThreshold AConflict (128 * C)
  let loss := scaleOnlyJointGreedyLoss AConflict (128 * C)
  letI : Nonempty (Fin repetitions) :=
    Fin.pos_iff_nonempty.mp hrepetitions
  have hcopyB2 : ∀ a,
      (copied.family.tubes a).carrier ⊆
        Metric.closedBall (0 : Space) 2 := by
    intro a
    change (rigidTube (motion (omega a.1))
      (D.family.tubes a.2)).carrier ⊆ Metric.closedBall (0 : Space) 2
    rw [rigidTube_carrier]
    refine (Set.image_mono (hD.contained_in_unit_ball a.2)).trans ?_
    dsimp only [motion, n]
    unfold scaleOnlyFixedJohnSampledOrthogonalTranslationMotion
    exact orthogonalTranslationRigidMotion_image_unitBall_subset_two
      (scaleOnlyFixedJohnPackingGridVector_norm_le_one
        hD.delta_pos (omega a.1).1)
  have hcopyKT : IsKatzTao ((repetitions : ENNReal) * C)
      copied.family.bodyFamily := by
    change IsKatzTao ((repetitions : ENNReal) * C)
      (indexedRigidCopyTubeFamily
        (fun j ↦ motion (omega j)) D.family).bodyFamily
    simpa only [Fintype.card_fin] using
      indexedRigidCopyTubeFamily_isKatzTao_card_mul
        (fun j ↦ motion (omega j)) D.family hKT
  obtain ⟨selected, hselected, hadmissible, hcard, hmass,
      hselectedKT, hcopyMultiplicity⟩ :=
    exists_normalized_refinement_admissible_isKatzTao_of_scale_B2
      copied hD.delta_pos hD.delta_le_half hcopyB2
      (by simpa only [copied, motion, n, threshold] using hconflict)
      hcopyKT
  have hsourceB2 : ∀ i,
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2 := by
    intro i
    exact (hD.contained_in_unit_ball i).trans
      (Metric.closedBall_subset_closedBall (by norm_num))
  have hfullCWA : SatisfiesConvexWolffAxioms
      (scaleOnlyFullCopiedCWAParameter D hD.delta_pos repetitions AJohn
          (128 * C) * johnCatalogueVolumeConstant)
      normalized.family.bodyFamily := by
    simpa only [normalized, copied, motion, n] using
      fullNormalizedCopied_satisfiesConvexWolffAxioms_of_scaleOnlyJohnTail
        D hD.delta_pos hD.delta_le_half hsourceB2 omega AJohn hAJohn
        h128CTop hjohn
  have hselectedCWA0 :=
    satisfiesConvexWolffAxioms_restrict hfullCWA hcard
  have hselectedCWA : SatisfiesConvexWolffAxioms
      ((loss : ENNReal) *
        (scaleOnlyFullCopiedCWAParameter D hD.delta_pos repetitions AJohn
            (128 * C) * johnCatalogueVolumeConstant))
      (restrictActualTubeDatum normalized selected).family.bodyFamily := by
    change SatisfiesConvexWolffAxioms
      ((loss : ENNReal) *
        (scaleOnlyFullCopiedCWAParameter D hD.delta_pos repetitions AJohn
            (128 * C) * johnCatalogueVolumeConstant))
      (restrictConvexFamily normalized.family.bodyFamily selected)
    simpa only [loss, threshold, scaleOnlyJointGreedyLoss] using hselectedCWA0
  have hsourceCopy : D.shading.averageMultiplicity ≤
      copied.shading.averageMultiplicity := by
    change D.shading.averageMultiplicity ≤
      (indexedRigidCopyShading
        (fun j ↦ motion (omega j)) D.family D.shading).averageMultiplicity
    exact source_averageMultiplicity_le_indexedRigidCopy
      (fun j ↦ motion (omega j)) D.family D.shading
  refine ⟨omega, selected, hselected, hadmissible, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [loss, threshold, scaleOnlyJointGreedyLoss] using hcard
  · simpa only [normalized, copied, motion, n, loss, threshold,
      scaleOnlyJointGreedyLoss] using hmass
  · simpa only [normalized, copied, motion, n] using hselectedKT
  · simpa only [normalized, copied, motion, n, loss, threshold,
      scaleOnlyJointGreedyLoss] using hselectedCWA
  · simpa only [normalized, copied, motion, n, loss, threshold,
      scaleOnlyJointGreedyLoss] using hsourceCopy.trans hcopyMultiplicity

#print axioms scaleOnlyJointGreedyLoss
#print axioms exists_scaleOnlyJointChoice_refinement_CWA

end
end Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyRefinementCWAV1
