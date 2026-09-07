import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnFrostmanCWAConnectorV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionPaperFixedJohnFrostmanPropertyConnectorV1

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
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticDensityRepetitionsV2
open Family8FiniteRandomRigidMotionPaperFixedJohnFullCatalogueCWAV3
open Family8FiniteRandomRigidMotionPaperFixedJohnFrostmanCWAConnectorV2
open Family8PolynomialJohnFrameBoxVolumeV2

noncomputable section

/-!
# Property-level automatic fixed-John Frostman/CWA connector

The fixed-parameter automatic theorem already constructs one common selected
family carrying admissibility, cardinal and mass retention, Katz--Tao, CWA,
and the source Frostman multiplicity estimate.  This file only exposes that
endpoint as a named proposition and moves the `FrostmanProperty` quantifiers
to their correct order: `eta` and `delta0` are selected uniformly before the
datum.  Exactly three scalar obligations remain afterwards: the terminal
scale comparison, density retention budget, and unit-ball base budget.
-/

/-- The complete common-selection output of the automatic fixed-John
connector.  Every field below refers to the same `omega` and `selected`. -/
def AutomaticFixedJohnRefinementCWAFrostmanEndpoint
    {delta : NNReal} {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : ENNReal) (epsilon beta : Real) : Prop :=
  ∃ (omega : Fin (fixedJohnAutomaticDensityRepetitions D hD) →
        FixedJohnPackingTranslation D hD)
    (selected : Finset
      (Fin (fixedJohnAutomaticDensityRepetitions D hD) × iota)),
    selected.Nonempty ∧
    (restrictActualTubeDatum
      (eighthNormalizedDatum
        (indexedRigidCopyDatum
          (fun j ↦ translationRigidMotion
            (fixedJohnPackingGridVector D hD (omega j))) D))
      selected).IsAdmissible ∧
    (Fintype.card
        (Fin (fixedJohnAutomaticDensityRepetitions D hD) × iota) : ENNReal) ≤
      (fixedJohnAutomaticGreedyLoss D hD : ENNReal) *
        (selected.card : ENNReal) ∧
    (eighthNormalizedDatum
      (indexedRigidCopyDatum
        (fun j ↦ translationRigidMotion
          (fixedJohnPackingGridVector D hD (omega j))) D)).shading.shadingMass ≤
      (fixedJohnAutomaticGreedyLoss D hD : ENNReal) *
        (restrictActualTubeDatum
          (eighthNormalizedDatum
            (indexedRigidCopyDatum
              (fun j ↦ translationRigidMotion
                (fixedJohnPackingGridVector D hD (omega j))) D))
          selected).shading.shadingMass ∧
    IsKatzTao
      (128 *
        ((fixedJohnAutomaticDensityRepetitions D hD : ENNReal) * C))
      (restrictActualTubeDatum
        (eighthNormalizedDatum
          (indexedRigidCopyDatum
            (fun j ↦ translationRigidMotion
              (fixedJohnPackingGridVector D hD (omega j))) D))
        selected).family.bodyFamily ∧
    SatisfiesConvexWolffAxioms
      ((fixedJohnAutomaticGreedyLoss D hD : ENNReal) *
        (fixedJohnFullCopiedCWAParameter D hD *
          johnCatalogueVolumeConstant))
      (restrictActualTubeDatum
        (eighthNormalizedDatum
          (indexedRigidCopyDatum
            (fun j ↦ translationRigidMotion
              (fixedJohnPackingGridVector D hD (omega j))) D))
        selected).family.bodyFamily ∧
    D.shading.averageMultiplicity ≤
      (fixedJohnAutomaticGreedyLoss D hD : ENNReal) *
        frostmanMultiplicityRHS (delta / 8)
          (restrictActualTubeDatum
            (eighthNormalizedDatum
              (indexedRigidCopyDatum
                (fun j ↦ translationRigidMotion
                  (fixedJohnPackingGridVector D hD (omega j))) D))
            selected).actualFamilyVolume epsilon beta

/-- Fixed-parameter spelling of the automatic theorem using the named common
endpoint. -/
theorem automaticFixedJohn_refinement_CWA_frostmanEndpoint_of_parameters
    {beta epsilon eta : Real} {delta0 delta : NNReal}
    {iota : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {C : ENNReal} (hKT : IsKatzTao C D.family.bodyFamily)
    (hdelta0 : delta / 8 ≤ delta0)
    (hdensityBudget :
      ((delta / 8 : NNReal) : ENNReal) ^ eta ≤
        (eighthNormalizedDatum D).shading.shadingDensity /
          (fixedJohnAutomaticGreedyLoss D hD : ENNReal))
    (hbaseBudget :
      (fixedJohnAutomaticGreedyLoss D hD : ENNReal) *
          ((128 *
              ((fixedJohnAutomaticDensityRepetitions D hD : ENNReal) * C)) *
            volume (unitBallBody : Set Space)) ≤
        ((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card
              (Fin (fixedJohnAutomaticDensityRepetitions D hD) × iota) :
                ENNReal) *
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2))) :
    AutomaticFixedJohnRefinementCWAFrostmanEndpoint D hD C epsilon beta := by
  exact exists_automaticFixedJohn_refinement_CWA_frostman
    hF D hD hKT hdelta0 hdensityBudget hbaseBudget

/-- Quantifier-correct `FrostmanProperty` connector.  The property first
chooses uniform positive parameters.  For every later datum, the automatic
fixed-John endpoint follows from precisely the displayed three scalar
budgets, with no random-selection callback. -/
theorem exists_parameters_automaticFixedJohn_refinement_CWA_frostman
    {beta epsilon : Real}
    (hF : FrostmanProperty beta) (hepsilon : 0 < epsilon) :
    ∃ eta : Real, ∃ delta0 : NNReal,
      0 < eta ∧ 0 < delta0 ∧ delta0 ≤ (2 : NNReal)⁻¹ ∧
      ∀ {delta : NNReal} {iota : Type}
          [Fintype iota] [Nonempty iota] [DecidableEq iota]
          (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
          {C : ENNReal} (_hKT : IsKatzTao C D.family.bodyFamily),
        delta / 8 ≤ delta0 →
        ((delta / 8 : NNReal) : ENNReal) ^ eta ≤
            (eighthNormalizedDatum D).shading.shadingDensity /
              (fixedJohnAutomaticGreedyLoss D hD : ENNReal) →
        (fixedJohnAutomaticGreedyLoss D hD : ENNReal) *
              ((128 *
                  ((fixedJohnAutomaticDensityRepetitions D hD : ENNReal) *
                    C)) *
                volume (unitBallBody : Set Space)) ≤
            ((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
              ((Fintype.card
                  (Fin (fixedJohnAutomaticDensityRepetitions D hD) × iota) :
                    ENNReal) *
                (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2)) →
        AutomaticFixedJohnRefinementCWAFrostmanEndpoint
          D hD C epsilon beta := by
  obtain ⟨eta, delta0, heta, hdelta0, hdelta0Half, hAtParameters⟩ :=
    hF.exists_parameters hepsilon
  refine ⟨eta, delta0, heta, hdelta0, hdelta0Half, ?_⟩
  intro delta iota _ _ _ D hD C hKT hscale hdensity hbase
  exact automaticFixedJohn_refinement_CWA_frostmanEndpoint_of_parameters
    hAtParameters D hD hKT hscale hdensity hbase

#print axioms AutomaticFixedJohnRefinementCWAFrostmanEndpoint
#print axioms automaticFixedJohn_refinement_CWA_frostmanEndpoint_of_parameters
#print axioms exists_parameters_automaticFixedJohn_refinement_CWA_frostman

end
end Family8FiniteRandomRigidMotionPaperFixedJohnFrostmanPropertyConnectorV1
