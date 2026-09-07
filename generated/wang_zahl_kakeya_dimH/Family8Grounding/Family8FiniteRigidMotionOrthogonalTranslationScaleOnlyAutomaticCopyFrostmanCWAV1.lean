import Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyFrostmanCWAV1
import Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyTailNumericsV1
import Family8Grounding.Family8FiniteRandomRigidMotionRelativeCanonicalCardAutomaticCopyCountV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyAutomaticCopyFrostmanCWAV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6CanonicalFrostmanConstantCoreV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionRelativeCanonicalCardAutomaticCopyCountV1
open Family8FiniteRigidMotionOrthogonalScaleOnlyCatalogueScaleV1
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyFrostmanCWAV1
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyFullCatalogueCWAV1
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyJointSelectorV1
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyProductLawV1
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyRefinementCWAV1
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyTailNumericsV1
open Family8GeneralizedFrostmanCanonicalCardInterpolationV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PolynomialJohnFrameBoxVolumeV2

noncomputable section

/-!
# Canonical copy count for the scale-only joint Frostman refinement

The copy index is now the natural ceiling of the eighth-normalized source
canonical Frostman constant.  Its existing nonzero/finiteness lemmas provide
both positivity and the sharp upper bound by twice that constant.  The
canonical two-family tail parameters remove the tail-room callback at the
same time.

The two product-mean scale inequalities and the Frostman density/base budgets
remain explicit; this module does not assert that they hold automatically.
-/

/-- The complete output attached to the canonical copy count and canonical
two-family tail parameters. -/
def ScaleOnlyCanonicalCopyRefinementCWAFrostmanEndpoint
    {beta epsilon : Real} {delta : NNReal} {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : ENNReal) : Prop :=
  ∃ (omega : Fin (relativeCanonicalCardCopyCount D) →
        ScaleOnlyJointChoice D hD.delta_pos)
    (selected : Finset (Fin (relativeCanonicalCardCopyCount D) × iota)),
    selected.Nonempty ∧
    (restrictActualTubeDatum
      (eighthNormalizedDatum
        (indexedRigidCopyDatum
          (fun j ↦
            scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D
              hD.delta_pos
              (scaleOnlyOrthogonalCatalogueScale D hD.delta_pos)
              (omega j)) D)) selected).IsAdmissible ∧
    (Fintype.card
        (Fin (relativeCanonicalCardCopyCount D) × iota) : ENNReal) ≤
      (scaleOnlyJointGreedyLoss
          (scaleOnlyJointConflictTailParameter D hD.delta_pos)
          (128 * C) : ENNReal) * (selected.card : ENNReal) ∧
    (eighthNormalizedDatum
      (indexedRigidCopyDatum
        (fun j ↦
          scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D
            hD.delta_pos
            (scaleOnlyOrthogonalCatalogueScale D hD.delta_pos)
            (omega j)) D)).shading.shadingMass ≤
      (scaleOnlyJointGreedyLoss
          (scaleOnlyJointConflictTailParameter D hD.delta_pos)
          (128 * C) : ENNReal) *
        (restrictActualTubeDatum
          (eighthNormalizedDatum
            (indexedRigidCopyDatum
              (fun j ↦
                scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D
                  hD.delta_pos
                  (scaleOnlyOrthogonalCatalogueScale D hD.delta_pos)
                  (omega j)) D)) selected).shading.shadingMass ∧
    IsKatzTao
      (128 * ((relativeCanonicalCardCopyCount D : ENNReal) * C))
      (restrictActualTubeDatum
        (eighthNormalizedDatum
          (indexedRigidCopyDatum
            (fun j ↦
              scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D
                hD.delta_pos
                (scaleOnlyOrthogonalCatalogueScale D hD.delta_pos)
                (omega j)) D)) selected).family.bodyFamily ∧
    SatisfiesConvexWolffAxioms
      ((scaleOnlyJointGreedyLoss
          (scaleOnlyJointConflictTailParameter D hD.delta_pos)
          (128 * C) : ENNReal) *
        (scaleOnlyFullCopiedCWAParameter D hD.delta_pos
            (relativeCanonicalCardCopyCount D)
            (scaleOnlyJointJohnTailParameter delta hD.delta_pos)
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
      (scaleOnlyJointGreedyLoss
          (scaleOnlyJointConflictTailParameter D hD.delta_pos)
          (128 * C) : ENNReal) *
        frostmanMultiplicityRHS (delta / 8)
          (restrictActualTubeDatum
            (eighthNormalizedDatum
              (indexedRigidCopyDatum
                (fun j ↦
                  scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D
                    hD.delta_pos
                    (scaleOnlyOrthogonalCatalogueScale D hD.delta_pos)
                    (omega j)) D)) selected).actualFamilyVolume
          epsilon beta ∧
    (selected.card : ENNReal) ≤
      2 * sourceCanonicalFrostmanConstant (eighthNormalizedDatum D) *
        (Fintype.card iota : ENNReal)

/-- The canonical Frostman copy count and canonical logarithmic tails feed the
common scale-only selector while preserving the sharp selected-card upper
bound. -/
theorem scaleOnlyCanonicalCopy_refinement_CWA_frostman
    {beta epsilon eta : Real} {delta0 delta : NNReal}
    {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {C : ENNReal} (hCTop : C ≠ ∞)
    (hKT : IsKatzTao C D.family.bodyFamily)
    (hcanonical0 :
      sourceCanonicalFrostmanConstant (eighthNormalizedDatum D) ≠ 0)
    (hcanonicalTop :
      sourceCanonicalFrostmanConstant (eighthNormalizedDatum D) ≠ ∞)
    (hscaleJ :
      (relativeCanonicalCardCopyCount D : ENNReal) *
          scaleOnlyJointJohnMeanCoefficient iota *
          scaleOnlyJointHalfSq delta ≤
        (128 * C) * scaleOnlyJointMotionBallVolume)
    (hscaleE :
      (relativeCanonicalCardCopyCount D : ENNReal) *
          scaleOnlyJointConflictMeanCoefficient delta iota *
          scaleOnlyJointHalfSq delta ≤
        (128 * C) * scaleOnlyJointMotionBallVolume)
    (hdelta0 : delta / 8 ≤ delta0)
    (hdensityBudget :
      ((delta / 8 : NNReal) : ENNReal) ^ eta *
          (128 *
            (scaleOnlyJointGreedyLoss
              (scaleOnlyJointConflictTailParameter D hD.delta_pos)
              (128 * C) : ENNReal)) ≤
        D.shading.shadingDensity)
    (hbaseBudget :
      (scaleOnlyJointGreedyLoss
          (scaleOnlyJointConflictTailParameter D hD.delta_pos)
          (128 * C) : ENNReal) *
          ((128 *
              ((relativeCanonicalCardCopyCount D : ENNReal) * C)) *
            volume (unitBallBody : Set Space)) ≤
        ((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card
              (Fin (relativeCanonicalCardCopyCount D) × iota) : ENNReal) *
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2))) :
    ScaleOnlyCanonicalCopyRefinementCWAFrostmanEndpoint
      (beta := beta) (epsilon := epsilon) D hD C := by
  have hJ : 0 < relativeCanonicalCardCopyCount D :=
    relativeCanonicalCardCopyCount_pos D hcanonical0 hcanonicalTop
  obtain ⟨omega, selected, hselected, hadmissible, hcard, hmass,
      hselectedKT, hselectedCWA, hfrostman⟩ :=
    exists_scaleOnlyJointChoice_refinement_CWA_frostman
      hF D hD hCTop hKT (relativeCanonicalCardCopyCount D) hJ
      (scaleOnlyJointJohnTailParameter delta hD.delta_pos)
      (scaleOnlyJointConflictTailParameter D hD.delta_pos)
      (zero_le_one.trans
        (one_le_scaleOnlyJointJohnTailParameter delta hD.delta_pos))
      hscaleJ hscaleE (scaleOnlyJointTailRoom D hD.delta_pos)
      hdelta0 hdensityBudget hbaseBudget
  have hselectedUpper : (selected.card : ENNReal) ≤
      2 * sourceCanonicalFrostmanConstant (eighthNormalizedDatum D) *
        (Fintype.card iota : ENNReal) :=
    selected_card_le_two_mul_eighth_sourceCanonical_mul_sourceCard
      D selected hcanonical0 hcanonicalTop
  exact ⟨omega, selected, hselected, hadmissible, hcard, hmass,
    hselectedKT, hselectedCWA, hfrostman, hselectedUpper⟩

#print axioms ScaleOnlyCanonicalCopyRefinementCWAFrostmanEndpoint
#print axioms scaleOnlyCanonicalCopy_refinement_CWA_frostman

end
end Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyAutomaticCopyFrostmanCWAV1
