import Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyRefinementCWAV1
import Family8Grounding.Family8FiniteRandomRigidMotionB2FrostmanConnectorV1
import Family8Grounding.Family8FrozenCoarseB2DensityTransportScaleOnlyV1
import Family8Grounding.Family8EighthNormalizationSelectionDensityBudgetAlgebraV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000
set_option linter.style.haveILetI false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyFrostmanCWAV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8EighthNormalizationSelectionDensityBudgetAlgebraV1
open Family8FiniteRandomRigidMotionB2FrostmanConnectorV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionPaperFixedJohnCopyTransportCoreV1
open Family8FiniteRigidMotionOrthogonalScaleOnlyCatalogueScaleV1
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyConflictMeanV1
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyFullCatalogueCWAV1
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyJointSelectorV1
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyProductLawV1
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyRefinementCWAV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FrozenCoarseB2DensityTransportScaleOnlyV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PolynomialJohnFrameBoxVolumeV2

noncomputable section

/-!
# Frostman output from the scale-only joint refinement

This module composes the common scale-only choice and fresh CWA refinement
with the existing honest B2 Frostman connector.  The factor `128` in the
density premise is exactly the proved loss from eighth normalization; rigid
copying itself preserves the source density.

The repetition count, the two product-mean scale budgets, and the two-family
tail-room inequality remain explicit.  This theorem does not claim their
automatic numerical discharge.
-/

/-- Under the explicit probabilistic and Frostman scalar budgets, one common
scale-only tuple yields the selected CWA refinement and the final source
Frostman multiplicity estimate. -/
theorem exists_scaleOnlyJointChoice_refinement_CWA_frostman
    {beta epsilon eta : Real} {delta0 delta : NNReal}
    {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (hF : FrostmanAtParameters beta epsilon eta delta0)
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
        Real.exp AJohn * Real.exp AConflict)
    (hdelta0 : delta / 8 ≤ delta0)
    (hdensityBudget :
      ((delta / 8 : NNReal) : ENNReal) ^ eta *
          (128 *
            (scaleOnlyJointGreedyLoss AConflict (128 * C) : ENNReal)) ≤
        D.shading.shadingDensity)
    (hbaseBudget :
      (scaleOnlyJointGreedyLoss AConflict (128 * C) : ENNReal) *
          ((128 * ((repetitions : ENNReal) * C)) *
            volume (unitBallBody : Set Space)) ≤
        ((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card (Fin repetitions × iota) : ENNReal) *
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2))) :
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
          frostmanMultiplicityRHS (delta / 8)
            (restrictActualTubeDatum
              (eighthNormalizedDatum
                (indexedRigidCopyDatum
                  (fun j ↦
                    scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D
                      hD.delta_pos
                      (scaleOnlyOrthogonalCatalogueScale D hD.delta_pos)
                      (omega j)) D)) selected).actualFamilyVolume
            epsilon beta := by
  obtain ⟨omega, selected, hselected, hadmissible, hcard, hmass,
      hselectedKT, hselectedCWA, _hsourceSelected⟩ :=
    exists_scaleOnlyJointChoice_refinement_CWA D hD hCTop hKT
      repetitions hrepetitions AJohn AConflict hAJohn hscaleJ hscaleE htailRoom
  let n := scaleOnlyOrthogonalCatalogueScale D hD.delta_pos
  let motion : ScaleOnlyJointChoice D hD.delta_pos → RigidMotion :=
    scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hD.delta_pos n
  let copied := indexedRigidCopyDatum (fun j ↦ motion (omega j)) D
  let normalized := eighthNormalizedDatum copied
  let loss := scaleOnlyJointGreedyLoss AConflict (128 * C)
  letI : Nonempty (Fin repetitions) :=
    Fin.pos_iff_nonempty.mp hrepetitions
  letI : NeZero loss := ⟨by
    dsimp only [loss, scaleOnlyJointGreedyLoss]
    omega⟩
  have hcopyDensity : copied.shading.shadingDensity =
      D.shading.shadingDensity := by
    change
      (indexedRigidCopyShading (fun j ↦ motion (omega j))
        D.family D.shading).shadingDensity = D.shading.shadingDensity
    exact indexedRigidCopyShading_shadingDensity
      (fun j ↦ motion (omega j)) D.family D.shading
  have hnormalizedDensity : copied.shading.shadingDensity / 128 ≤
      normalized.shading.shadingDensity := by
    exact source_shadingDensity_div_128_le_eighthNormalized_of_scale
      copied hD.delta_pos hD.delta_le_half
  have hdensityCopied :
      ((delta / 8 : NNReal) : ENNReal) ^ eta ≤
        normalized.shading.shadingDensity / (loss : ENNReal) := by
    apply target_le_normalized_div_loss_of_mul_128_loss_le_lower
      _ copied.shading.shadingDensity normalized.shading.shadingDensity
        D.shading.shadingDensity (loss : ENNReal)
    · exact_mod_cast (NeZero.ne loss)
    · exact ENNReal.coe_ne_top
    · exact hcopyDensity.ge
    · exact hnormalizedDensity
    · simpa only [loss] using hdensityBudget
  have hcopyFrostman : copied.shading.averageMultiplicity ≤
      (loss : ENNReal) *
        frostmanMultiplicityRHS (delta / 8)
          (restrictActualTubeDatum normalized selected).actualFamilyVolume
            epsilon beta := by
    apply
      @source_averageMultiplicity_le_normalized_loss_mul_frostmanRHS_of_refinement
        _ _ _ _ _ _ _ _ hF copied selected loss inferInstance
          (128 * ((repetitions : ENNReal) * C)) hdelta0
    · simpa only [normalized, copied, motion, n] using hadmissible
    · simpa only [loss] using hcard
    · simpa only [normalized, copied, motion, n, loss] using hmass
    · simpa only [normalized, copied, motion, n] using hselectedKT
    · exact hdensityCopied
    · simpa only [loss] using hbaseBudget
  have hsourceCopy : D.shading.averageMultiplicity ≤
      copied.shading.averageMultiplicity := by
    change D.shading.averageMultiplicity ≤
      (indexedRigidCopyShading (fun j ↦ motion (omega j))
        D.family D.shading).averageMultiplicity
    exact source_averageMultiplicity_le_indexedRigidCopy
      (fun j ↦ motion (omega j)) D.family D.shading
  refine ⟨omega, selected, hselected, hadmissible, hcard, hmass,
    hselectedKT, hselectedCWA, ?_⟩
  simpa only [normalized, copied, motion, n, loss] using
    hsourceCopy.trans hcopyFrostman

#print axioms exists_scaleOnlyJointChoice_refinement_CWA_frostman

end
end Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyFrostmanCWAV1
