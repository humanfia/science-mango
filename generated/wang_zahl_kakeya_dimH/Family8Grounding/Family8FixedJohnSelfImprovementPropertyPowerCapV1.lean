import Family8Grounding.Family8FixedJohnSelfImprovementPropertyConnectorV1
import Family8Grounding.Family8FixedJohnTransportScalarPowerCapV1
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnScalarBudgetReductionV2

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FixedJohnSelfImprovementPropertyPowerCapV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticDensityRepetitionsV2
open Family8FiniteRandomRigidMotionPaperFixedJohnFrostmanCWAConnectorV2
open Family8FrostmanRHSScaleVolumeAlgebraV4
open Family8FiniteRandomRigidMotionPaperFixedJohnScalarBudgetReductionV2
open Family8FixedJohnSelfImprovementPropertyConnectorV1
open Family8FixedJohnTransportScalarPowerCapV1

noncomputable section

/-!
# Property-level fixed-John connector with an automatic scalar cap

The scalar-power callback in the preceding property connector is discharged
from a source Katz--Tao cardinality power and a datum-independent small-scale
threshold.  The existing scalar-budget reduction also replaces the copied
base budget by its one-copy source-card version.
-/

/-- Property-level fixed-John improvement with the transport scalar generated
from the source cardinality power.  In particular, there is no scalar-power
callback after the datum is chosen. -/
theorem exists_parameters_fixedJohn_improvedRHS_of_sourcePower
    {gamma sourceEpsilon targetEpsilon nu kappa sourceEta tailEta : Real}
    (hF : FrostmanProperty gamma)
    (hsourceEpsilon : 0 < sourceEpsilon)
    (hgamma : gamma <= 2)
    (hnu : 0 <= nu)
    (hsourceEta : 0 <= sourceEta)
    (htailEta : 0 < tailEta)
    (hgap : fixedJohnTransportNormalizedExponent
      tailEta sourceEta gamma < kappa) :
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
        C <= (delta : ENNReal) ^ (-sourceEta) ->
        (((delta / 8 : NNReal) : ENNReal) ^ eta *
              (fixedJohnAutomaticGreedyLoss D hD : ENNReal) <=
            (eighthNormalizedDatum D).shading.shadingDensity) ->
        ((fixedJohnAutomaticGreedyLoss D hD : ENNReal) *
              ((128 * C) * volume (unitBallBody : Set Space)) <=
            ((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
              ((Fintype.card iota : ENNReal) *
                (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2))) ->
        D.shading.averageMultiplicity <=
          frostmanMultiplicityRHS delta D.actualFamilyVolume
            targetEpsilon (gamma - nu)) := by
  obtain ⟨eta, deltaBase, heta, hdeltaBase, hdeltaBaseHalf, hAt⟩ :=
    exists_parameters_fixedJohn_improvedRHS_of_powerCap
      hF hsourceEpsilon hgamma hnu
  let deltaScalar : NNReal := fixedJohnTransportSharpScalarThreshold
    tailEta sourceEta sourceEpsilon gamma kappa
  let delta0 : NNReal := min deltaBase deltaScalar
  have hdeltaScalar : 0 < deltaScalar := by
    dsimp only [deltaScalar]
    exact fixedJohnTransportSharpScalarThreshold_pos _ _ _ _ _
  refine ⟨eta, delta0, heta, lt_min hdeltaBase hdeltaScalar, ?_, ?_⟩
  · exact (min_le_left deltaBase deltaScalar).trans hdeltaBaseHalf
  · intro hbudget delta iota _ _ _ D hD hdelta hSource C hKT hC
      hdensity hbase
    have hdeltaBase' : delta <= deltaBase :=
      hdelta.trans (min_le_left deltaBase deltaScalar)
    have hdeltaScalar' : delta <=
        fixedJohnTransportSharpScalarThreshold
          tailEta sourceEta sourceEpsilon gamma kappa := by
      simpa only [deltaScalar] using
        hdelta.trans (min_le_right deltaBase deltaScalar)
    obtain ⟨hdensity', hbase'⟩ :=
      fixedJohnScalarBudgets_of_reduced D hD C hdensity hbase
    have hscalar :=
      fixedJohnFrostmanTransportScalar_le_deltaPower_sharp
        D hD hsourceEta htailEta hgamma hgap hKT hC hdeltaScalar'
    exact hAt hbudget D hD hdeltaBase' hSource hKT hdensity' hbase' hscalar

#print axioms exists_parameters_fixedJohn_improvedRHS_of_sourcePower

end
end Family8FixedJohnSelfImprovementPropertyPowerCapV1
