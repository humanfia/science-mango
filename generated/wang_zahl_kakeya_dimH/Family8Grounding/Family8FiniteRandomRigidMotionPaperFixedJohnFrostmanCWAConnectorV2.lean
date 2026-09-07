import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnFullCatalogueCWAV3
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnDensityNondegeneracyV4
import Family8Grounding.Family8FiniteRandomRigidMotionB2FrostmanConnectorV1
import Family8Grounding.Family8CardinalCWARestrictionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000
set_option linter.style.haveILetI false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionPaperFixedJohnFrostmanCWAConnectorV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2FrostmanConnectorV1
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperFixedJohnBoundedPackingMeanV5
open Family8FiniteRandomRigidMotionPaperFixedJohnExactMeanSelectorV4
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticDensityRepetitionsV2
open Family8FiniteRandomRigidMotionPaperFixedJohnCopyTransportCoreV1
open Family8FiniteRandomRigidMotionPaperFixedJohnFreshSelectionV2
open Family8FiniteRandomRigidMotionPaperFixedJohnFullCatalogueCWAV3
open Family8CardinalCWARestrictionV1
open Family8PolynomialJohnFrameBoxVolumeV2

noncomputable section

/-!
# Fully automatic fixed-John refinement/Frostman/CWA connector

The automatic bounded translation law chooses both `J` and the tuple.  Its
conflict cap drives fresh greedy selection; its catalogue-cardinality tail
drives Definition 2.12 CWA.  The copied family need not be admissible before
selection.  The only remaining premises are the real Frostman theorem and
the two explicit pre-selection scalar density/base budgets.
-/

def fixedJohnAutomaticGreedyLoss
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) : Nat :=
  fixedJohnLoadThreshold (fixedJohnPackingGridVector D hD) D hD + 1

/-- One endpoint packages the automatic tuple, genuine selected admissible
datum, retained cardinality and mass, selected Katz--Tao and CWA bounds, and
the final source Frostman multiplicity estimate. -/
theorem exists_automaticFixedJohn_refinement_CWA_frostman
    {beta epsilon eta : Real} {delta0 delta : NNReal}
    {iota : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {C : ENNReal} (hKT : IsKatzTao C D.family.bodyFamily)
    (hdelta0 : delta / 8 <= delta0)
    (hdensityBudget :
      ((delta / 8 : NNReal) : ENNReal) ^ eta <=
        (eighthNormalizedDatum D).shading.shadingDensity /
          (fixedJohnAutomaticGreedyLoss D hD : ENNReal))
    (hbaseBudget :
      (fixedJohnAutomaticGreedyLoss D hD : ENNReal) *
          ((128 *
              ((fixedJohnAutomaticDensityRepetitions D hD : ENNReal) * C)) *
            volume (unitBallBody : Set Space)) <=
        ((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card
              (Fin (fixedJohnAutomaticDensityRepetitions D hD) × iota) : ENNReal) *
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2))) :
    ∃ (omega : Fin (fixedJohnAutomaticDensityRepetitions D hD) ->
          FixedJohnPackingTranslation D hD)
      (selected : Finset
        (Fin (fixedJohnAutomaticDensityRepetitions D hD) × iota)),
      selected.Nonempty ∧
      (restrictActualTubeDatum
        (eighthNormalizedDatum
          (indexedRigidCopyDatum
            (fun j => translationRigidMotion
              (fixedJohnPackingGridVector D hD (omega j))) D))
        selected).IsAdmissible ∧
      (Fintype.card
          (Fin (fixedJohnAutomaticDensityRepetitions D hD) × iota) : ENNReal) <=
        (fixedJohnAutomaticGreedyLoss D hD : ENNReal) *
          (selected.card : ENNReal) ∧
      (eighthNormalizedDatum
        (indexedRigidCopyDatum
          (fun j => translationRigidMotion
            (fixedJohnPackingGridVector D hD (omega j))) D)).shading.shadingMass <=
        (fixedJohnAutomaticGreedyLoss D hD : ENNReal) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum
              (indexedRigidCopyDatum
                (fun j => translationRigidMotion
                  (fixedJohnPackingGridVector D hD (omega j))) D))
            selected).shading.shadingMass ∧
      IsKatzTao
        (128 *
          ((fixedJohnAutomaticDensityRepetitions D hD : ENNReal) * C))
        (restrictActualTubeDatum
          (eighthNormalizedDatum
            (indexedRigidCopyDatum
              (fun j => translationRigidMotion
                (fixedJohnPackingGridVector D hD (omega j))) D))
          selected).family.bodyFamily ∧
      SatisfiesConvexWolffAxioms
        ((fixedJohnAutomaticGreedyLoss D hD : ENNReal) *
          (fixedJohnFullCopiedCWAParameter D hD *
            johnCatalogueVolumeConstant))
        (restrictActualTubeDatum
          (eighthNormalizedDatum
            (indexedRigidCopyDatum
              (fun j => translationRigidMotion
                (fixedJohnPackingGridVector D hD (omega j))) D))
          selected).family.bodyFamily ∧
      D.shading.averageMultiplicity <=
        (fixedJohnAutomaticGreedyLoss D hD : ENNReal) *
          frostmanMultiplicityRHS (delta / 8)
            (restrictActualTubeDatum
              (eighthNormalizedDatum
                (indexedRigidCopyDatum
                  (fun j => translationRigidMotion
                    (fixedJohnPackingGridVector D hD (omega j))) D))
              selected).actualFamilyVolume epsilon beta := by
  let J := fixedJohnAutomaticDensityRepetitions D hD
  let gridVector := fixedJohnPackingGridVector D hD
  let threshold := fixedJohnLoadThreshold gridVector D hD
  let loss := threshold + 1
  have hJ : 0 < J :=
    one_le_fixedJohnAutomaticDensityRepetitions D hD
  haveI : Nonempty (Fin J) := Fin.pos_iff_nonempty.mp hJ
  haveI : NeZero loss := ⟨by dsimp only [loss]; omega⟩
  obtain ⟨omega, htail, hconflict⟩ :=
    exists_boundedPackingTuple_automaticDensityRepetitions D hD
  let v : Fin J -> Space := fun j => gridVector (omega j)
  let copied := indexedRigidCopyDatum
    (fun j : Fin J => translationRigidMotion (v j)) D
  let normalized := eighthNormalizedDatum copied
  have hv : forall j, ‖v j‖ <= 1 := by
    intro j
    simpa only [v, gridVector] using
      fixedJohnPackingGridVector_norm_le_one D hD (omega j)
  have hB2 : forall a,
      (copied.family.tubes a).carrier ⊆
        Metric.closedBall (0 : Space) 2 := by
    simpa only [copied, v] using
      indexedTranslation_carrier_subset_twoBall v D hD hv
  have hcopyKT : IsKatzTao ((J : ENNReal) * C)
      copied.family.bodyFamily := by
    change IsKatzTao ((J : ENNReal) * C)
      (indexedRigidCopyTubeFamily
        (fun j : Fin J => translationRigidMotion (v j)) D.family).bodyFamily
    simpa only [Fintype.card_fin] using
      indexedRigidCopyTubeFamily_isKatzTao_card_mul
        (fun j : Fin J => translationRigidMotion (v j)) D.family hKT
  obtain ⟨selected, hselected, hadmissible, hcard, hmass,
      hselectedKT, _hcopyMultiplicity⟩ :=
    exists_normalized_refinement_admissible_isKatzTao_of_scale_B2
      copied hD.delta_pos hD.delta_le_half hB2
      (by simpa only [copied, threshold, J, v, gridVector] using hconflict)
      hcopyKT
  have hfullCWA : SatisfiesConvexWolffAxioms
      (fixedJohnFullCopiedCWAParameter D hD *
        johnCatalogueVolumeConstant) normalized.family.bodyFamily := by
    simpa only [normalized, copied, v, gridVector, J] using
      fullNormalizedCopied_satisfiesConvexWolffAxioms D hD omega htail
  have hselectedCWA0 := satisfiesConvexWolffAxioms_restrict
    hfullCWA hcard
  have hselectedCWA : SatisfiesConvexWolffAxioms
      ((loss : ENNReal) *
        (fixedJohnFullCopiedCWAParameter D hD *
          johnCatalogueVolumeConstant))
      (restrictActualTubeDatum normalized selected).family.bodyFamily := by
    change SatisfiesConvexWolffAxioms
      ((loss : ENNReal) *
        (fixedJohnFullCopiedCWAParameter D hD *
          johnCatalogueVolumeConstant))
      (restrictConvexFamily normalized.family.bodyFamily selected)
    simpa only [loss, threshold, gridVector] using hselectedCWA0
  have hdensityCopied :
      ((delta / 8 : NNReal) : ENNReal) ^ eta <=
        normalized.shading.shadingDensity / (loss : ENNReal) := by
    rw [show normalized.shading.shadingDensity =
        (eighthNormalizedDatum D).shading.shadingDensity by
      exact eighthNormalizedIndexedTranslation_shadingDensity v D]
    simpa only [loss, threshold, gridVector,
      fixedJohnAutomaticGreedyLoss] using hdensityBudget
  have hcopyFrostman : copied.shading.averageMultiplicity <=
      (loss : ENNReal) *
        frostmanMultiplicityRHS (delta / 8)
          (restrictActualTubeDatum normalized selected).actualFamilyVolume
            epsilon beta := by
    exact
      source_averageMultiplicity_le_normalized_loss_mul_frostmanRHS_of_refinement
        hF copied selected loss
        (128 * ((J : ENNReal) * C)) hdelta0 hadmissible hcard hmass
        hselectedKT hdensityCopied
        (by simpa only [loss, threshold, gridVector, J,
          fixedJohnAutomaticGreedyLoss] using hbaseBudget)
  have hsourceCopy : D.shading.averageMultiplicity <=
      copied.shading.averageMultiplicity := by
    change D.shading.averageMultiplicity <=
      (indexedRigidCopyShading
        (fun j : Fin J => translationRigidMotion (v j))
        D.family D.shading).averageMultiplicity
    exact source_averageMultiplicity_le_indexedRigidCopy
      (fun j : Fin J => translationRigidMotion (v j)) D.family D.shading
  refine ⟨omega, selected, hselected, hadmissible, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [loss, threshold, gridVector, J,
      fixedJohnAutomaticGreedyLoss] using hcard
  · simpa only [normalized, copied, v, loss, threshold, gridVector, J,
      fixedJohnAutomaticGreedyLoss] using hmass
  · simpa only [normalized, copied, v, J] using hselectedKT
  · simpa only [normalized, copied, v, loss, threshold, gridVector, J,
      fixedJohnAutomaticGreedyLoss] using hselectedCWA
  · simpa only [normalized, copied, v, loss, threshold, gridVector, J,
      fixedJohnAutomaticGreedyLoss] using hsourceCopy.trans hcopyFrostman

#print axioms fixedJohnAutomaticGreedyLoss
#print axioms exists_automaticFixedJohn_refinement_CWA_frostman

end
end Family8FiniteRandomRigidMotionPaperFixedJohnFrostmanCWAConnectorV2
