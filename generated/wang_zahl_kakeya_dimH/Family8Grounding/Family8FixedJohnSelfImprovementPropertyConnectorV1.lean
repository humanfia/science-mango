import Family8Grounding.Family8FixedJohnSelfImprovementRHSBridgeV20

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FixedJohnSelfImprovementPropertyConnectorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperFixedJohnBoundedPackingMeanV5
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticDensityRepetitionsV2
open Family8FiniteRandomRigidMotionPaperFixedJohnFrostmanCWATailConnectorV5
open Family8PolynomialJohnFrameBoxVolumeV2
open Family8FrostmanRHSScaleVolumeAlgebraV4
open Family8FixedJohnSelfImprovementRHSBridgeV20

noncomputable section

/-!
# Property-level fixed-John self-improvement connector

`Family8FixedJohnSelfImprovementRHSBridgeV20` already constructs the copied
radius-two family, sends it to the unit ball by eighth-normalization, performs
the common fixed-John selection, and returns the improved source Frostman
right-hand side.  This file only puts that result under the quantifier order
of `FrostmanProperty`: the old loss exponent and terminal scale are fixed
before the later datum.  The remaining inputs are precisely the explicit
density, base, scalar-power, and exponent budgets.
-/

/-- Quantifier-correct property lift of the V20 fixed-John endpoint.  The
same exponent `eta` selected by the source property is used in the later
source Frostman hypotheses and in the scalar absorption budget. -/
theorem exists_parameters_fixedJohn_improvedRHS_of_powerCap
    {gamma sourceEpsilon targetEpsilon nu kappa : Real}
    (hF : FrostmanProperty gamma)
    (hsourceEpsilon : 0 < sourceEpsilon)
    (hgamma : gamma <= 2)
    (hnu : 0 <= nu) :
    ∃ eta : Real, ∃ delta0 : NNReal,
      0 < eta ∧ 0 < delta0 ∧ delta0 <= (2 : NNReal)⁻¹ ∧
      ((kappa + 2 * nu + eta * nu / 2 <=
          targetEpsilon - sourceEpsilon) ->
      ∀ {delta : NNReal} {iota : Type}
          [Fintype iota] [Nonempty iota] [DecidableEq iota]
          (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible),
        delta <= delta0 ->
        FrostmanHypotheses D eta ->
        ∀ {C : ENNReal}, IsKatzTao C D.family.bodyFamily ->
        (((delta / 8 : NNReal) : ENNReal) ^ eta <=
            (eighthNormalizedDatum D).shading.shadingDensity /
              (fixedJohnAutomaticGreedyLoss D hD : ENNReal)) ->
        ((fixedJohnAutomaticGreedyLoss D hD : ENNReal) *
              ((128 *
                  ((fixedJohnAutomaticDensityRepetitions D hD : ENNReal) *
                    C)) *
                volume (unitBallBody : Set Space)) <=
            ((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
              ((Fintype.card
                  (Fin (fixedJohnAutomaticDensityRepetitions D hD) × iota) :
                    ENNReal) *
                (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2))) ->
        (fixedJohnFrostmanTransportScalar
              (fixedJohnAutomaticGreedyLoss D hD : ENNReal)
              ((fixedJohnAutomaticDensityRepetitions D hD : ENNReal) *
                (1 / 4 : ENNReal)) sourceEpsilon gamma <=
            (delta : ENNReal) ^ (-kappa)) ->
        D.shading.averageMultiplicity <=
          frostmanMultiplicityRHS delta D.actualFamilyVolume
            targetEpsilon (gamma - nu)) := by
  obtain ⟨eta, delta0, heta, hdelta0, hdelta0Half, hAt⟩ :=
    hF.exists_parameters hsourceEpsilon
  refine ⟨eta, delta0, heta, hdelta0, hdelta0Half, ?_⟩
  intro hbudget delta iota _ _ _ D hD hdelta hSource C hKT
    hdensity hbase hscalar
  have hnormalizedScale : delta / 8 <= delta0 := by
    exact (div_le_self (show 0 <= delta from bot_le)
      (by norm_num : (1 : NNReal) <= 8)).trans hdelta
  obtain ⟨omega, selected, hselected, hadmissible, hcard, hmass,
      hselectedKT, hselectedCWA, himproved⟩ :=
    exists_automaticFixedJohn_refinement_tailCWA_improvedRHS_of_powerCap
      hAt D hD hSource hKT hnormalizedScale hdensity hbase hgamma
        hscalar hnu hbudget
  exact himproved

#print axioms exists_parameters_fixedJohn_improvedRHS_of_powerCap

end
end Family8FixedJohnSelfImprovementPropertyConnectorV1
