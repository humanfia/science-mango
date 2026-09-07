import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnFrostmanCWAConnectorV2
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnCWAParameterBudgetV3
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

namespace Family8FiniteRandomRigidMotionPaperFixedJohnFrostmanCWATailConnectorV5

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
theorem exists_automaticFixedJohn_refinement_tailCWA_frostman
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
          (ENNReal.ofReal
              (38016 * fixedJohnTailParameter D hD) *
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
  obtain ⟨omega, selected, hselected, hadmissible, hcard, hmass,
      hselectedKT, hselectedCWA, hfrostman⟩ :=
    Family8FiniteRandomRigidMotionPaperFixedJohnFrostmanCWAConnectorV2.exists_automaticFixedJohn_refinement_CWA_frostman
        hF D hD hKT hdelta0 hdensityBudget hbaseBudget
  refine ⟨omega, selected, hselected, hadmissible, hcard, hmass,
    hselectedKT, ?_, hfrostman⟩
  intro K
  refine (hselectedCWA K).trans ?_
  gcongr
  · rfl
  · exact
      Family8FiniteRandomRigidMotionPaperFixedJohnCWAParameterBudgetV3.fixedJohnFullCopiedCWAParameter_le_tail D hD

#print axioms fixedJohnAutomaticGreedyLoss
#print axioms exists_automaticFixedJohn_refinement_tailCWA_frostman

end
end Family8FiniteRandomRigidMotionPaperFixedJohnFrostmanCWATailConnectorV5
