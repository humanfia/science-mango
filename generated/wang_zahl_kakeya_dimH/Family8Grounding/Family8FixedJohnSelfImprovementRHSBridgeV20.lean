import Family8Grounding.Family8FixedJohnSelfImprovementRHSBridgeV19

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FixedJohnSelfImprovementRHSBridgeV20

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperFixedJohnBoundedPackingMeanV5
open Family8FiniteRandomRigidMotionPaperFixedJohnExactMeanSelectorV4
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticDensityRepetitionsV2
open Family8FiniteRandomRigidMotionPaperFixedJohnFrostmanCWATailConnectorV5
open Family8PolynomialJohnFrameBoxVolumeV2
open Family8FrostmanRHSScaleVolumeAlgebraV4
open Family8FixedJohnSelfImprovementRHSBridgeV19

noncomputable section

/-!
# Existential fixed-John endpoint with the scalar power cap exposed

This is the mechanical composition of the V5 finite refinement endpoint and
the actual-datum V19 power absorption lemma.  All selected-family witnesses,
Katz--Tao control, and Convex Wolff control are retained.  The only new
quantitative input is the explicit scalar power cap; neither `himprove` nor
the desired improved right-hand side is assumed.
-/

theorem exists_automaticFixedJohn_refinement_tailCWA_improvedRHS_of_powerCap
    {sourceEpsilon targetEpsilon gamma nu kappa eta lambda : Real}
    {delta0 delta : NNReal}
    {iota : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (hF : FrostmanAtParameters gamma sourceEpsilon eta delta0)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hFD : FrostmanHypotheses D lambda)
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
              (Fin (fixedJohnAutomaticDensityRepetitions D hD) × iota) :
                ENNReal) *
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2)))
    (hgamma : gamma <= 2)
    (hscalar :
      fixedJohnFrostmanTransportScalar
          (fixedJohnAutomaticGreedyLoss D hD : ENNReal)
          ((fixedJohnAutomaticDensityRepetitions D hD : ENNReal) *
            (1 / 4 : ENNReal)) sourceEpsilon gamma <=
        (delta : ENNReal) ^ (-kappa))
    (hnu : 0 <= nu)
    (hbudget :
      kappa + 2 * nu + lambda * nu / 2 <=
        targetEpsilon - sourceEpsilon) :
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
        frostmanMultiplicityRHS delta D.actualFamilyVolume
          targetEpsilon (gamma - nu) := by
  obtain ⟨omega, selected, hselected, hadmissible, hcard, hmass,
      hselectedKT, hselectedCWA, hsource⟩ :=
    exists_automaticFixedJohn_refinement_tailCWA_frostman
      hF D hD hKT hdelta0 hdensityBudget hbaseBudget
  refine ⟨omega, selected, hselected, hadmissible, hcard, hmass,
    hselectedKT, hselectedCWA, ?_⟩
  exact
    source_averageMultiplicity_le_improvedRHS_of_fixedJohn_powerCap
      D hD hFD omega selected hgamma hsource hscalar hnu hbudget

#print axioms
  exists_automaticFixedJohn_refinement_tailCWA_improvedRHS_of_powerCap

end
end Family8FixedJohnSelfImprovementRHSBridgeV20
