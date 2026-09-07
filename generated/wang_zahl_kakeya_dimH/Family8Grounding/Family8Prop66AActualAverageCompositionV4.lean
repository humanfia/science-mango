import Family8Grounding.Family8Prop66AActualAverageCompositionV2
import Family8Grounding.Family8Prop66AActualFamilyVolumeTransportV1

/-!
# Proposition 6.6(A): actual tube-volume composition, V4

This successor specializes V2 to an actual tube datum and composes its exact
card-scale conclusion with the proved tube-volume comparison.  Consequently
the two actual Lemma 6.4 estimates feed directly into the genuine Family 8
Frostman RHS, with only the explicit factor
`proposition66AFrostmanAspectGain * 2^(1-beta/2)`.

No outer or inner geometric estimate is asserted here; both remain visible
as the analytic outputs consumed by the theorem.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Prop66AActualAverageCompositionV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Family8KatzTaoFrostmanPropertiesV1
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8Prop66AActualFamilyVolumeTransportV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

namespace ExactAssembly

variable {delta : NNReal} {iota kappa : Type}
  [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {W : ConvexFamily kappa}
  {D : ActualTubeDatum delta iota}
  {P : ConvexFactorization D.family.bodyFamily W} {loss : Nat}

/-- Actual-datum form of the two Lemma 6.4 composition.  The card-scale
normalization is eliminated using the genuine summed tube volume. -/
theorem refinement_averageMultiplicity_le_gain_mul_actualFrostmanRHS
    (A : FactoringMultiplicityAssembly.ExactAssembly P D.shading loss)
    (hsource :
      (IndexedShadingRefinement.restrictTo D.shading
        P.index.fine).shading.shadingMass ≠ 0)
    {a b : NNReal} {plankCount tubesPerPlank : Nat}
    {CF : ENNReal} {epsilon beta : Real}
    (hD : D.IsAdmissible) (ha : 0 < a) (hb : 0 < b)
    (hbeta : 0 <= beta) (hbetaOne : beta <= 1)
    (hcount : Fintype.card iota = plankCount * tubesPerPlank)
    (houter :
      (P.inducedShading A.refinement.shading).averageMultiplicity <=
        proposition66AOuterFactor delta a b plankCount CF epsilon beta)
    (hinner : forall k, k ∈ P.index.coarse ->
      (sourceFineLevelShading A k).averageMultiplicity <=
        proposition66AInnerFactor delta a b tubesPerPlank epsilon beta) :
    A.refinement.shading.averageMultiplicity <=
      (proposition66AFrostmanAspectGain a b CF beta *
          (2 : ENNReal) ^ (1 - beta / 2)) *
        frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon beta := by
  have hprop : A.refinement.shading.averageMultiplicity <=
      proposition66AFrostmanFactor delta a b (Fintype.card iota)
        CF epsilon beta :=
    Family8Prop66AActualAverageCompositionV2.ExactAssembly.refinement_averageMultiplicity_le_proposition66AFrostmanFactor
      A hsource hD.delta_pos ha hb hbeta hbetaOne hcount houter hinner
  exact hprop.trans
    (proposition66AFrostmanFactor_le_actualRHS_with_two_rpow
      D hD.delta_le_half (hbetaOne.trans (by norm_num)))

#print axioms
  refinement_averageMultiplicity_le_gain_mul_actualFrostmanRHS

end ExactAssembly

end
end Family8Prop66AActualAverageCompositionV4
