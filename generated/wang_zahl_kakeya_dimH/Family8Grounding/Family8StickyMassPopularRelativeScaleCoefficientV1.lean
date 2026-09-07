import Family8Grounding.Family8StickyBoundedMassPopularRelativePowerFactorV1
import Family8Grounding.Family8ParentAggregatedShadingActiveCoarseXUpperV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyMassPopularRelativeScaleCoefficientV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8ContractedJohnActualTubeProxyV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8StickyFiberContractedJohnSourcePowerEndpointV1
open Family8StickySelectedFineSubtypeScaleCoverV1
open Family8StickySelectedFineAssemblyFiberBridgeV1
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyBoundedMassPopularRelativePowerFactorV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Sharp relative-scale envelopes for the mass-popular coefficients

The apparently separate active-parent cardinality loss is exactly the
normalized parent mass `X = |T_rho| rho^2` times `(delta/rho)^2`.  This
identity prevents an artificial extra cardinality power in both scalar
budgets.  The resulting wrapper consumes only an assembly-loss envelope,
an `X` envelope, and two global relative-scale inequalities.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Exact conversion of fine tube area per parent into normalized active
parent mass and the relative-scale square. -/
theorem activeCoarse_card_mul_delta_sq_eq_cardScaleMass_mul_ratio_sq
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) :
    (S.activeCoarse.card : ENNReal) * (delta : ENNReal) ^ 2 =
      (activeCoarseCardScaleMass S : ENNReal) *
        (((delta : ENNReal) / (rho : ENNReal)) ^ 2) := by
  have hrho0 : (rho : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hrho.ne'
  have hrhoTop : (rho : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hratio :
      ((delta : ENNReal) / (rho : ENNReal)) * (rho : ENNReal) =
        (delta : ENNReal) :=
    ENNReal.div_mul_cancel hrho0 hrhoTop
  have hratioSq :
      (((delta : ENNReal) / (rho : ENNReal)) ^ 2) *
          (rho : ENNReal) ^ 2 = (delta : ENNReal) ^ 2 := by
    calc
      (((delta : ENNReal) / (rho : ENNReal)) ^ 2) *
          (rho : ENNReal) ^ 2 =
          (((delta : ENNReal) / (rho : ENNReal)) *
            (rho : ENNReal)) ^ 2 := by ring
      _ = (delta : ENNReal) ^ 2 := by rw [hratio]
  calc
    (S.activeCoarse.card : ENNReal) * (delta : ENNReal) ^ 2 =
        (S.activeCoarse.card : ENNReal) *
          ((((delta : ENNReal) / (rho : ENNReal)) ^ 2) *
            (rho : ENNReal) ^ 2) := by rw [hratioSq]
    _ = ((S.activeCoarse.card : ENNReal) * (rho : ENNReal) ^ 2) *
        (((delta : ENNReal) / (rho : ENNReal)) ^ 2) := by ac_rfl
    _ = (activeCoarseCardScaleMass S : ENNReal) *
        (((delta : ENNReal) / (rho : ENNReal)) ^ 2) := by
      simp only [activeCoarseCardScaleMass, ENNReal.coe_mul,
        ENNReal.coe_natCast, ENNReal.coe_pow]

/-- The density coefficient costs the genuine bounded-assembly loss
`A.loss * M`, the normalized active-parent mass, and the relative square. -/
theorem densityCoefficient_le_relativeScaleEnvelope
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (M : Nat) (lossBound XUpper : ENNReal)
    (A_loss : Nat)
    (hloss : (A_loss : ENNReal) * (M : ENNReal) <= lossBound)
    (hX : (activeCoarseCardScaleMass S : ENNReal) <= XUpper) :
    (((A_loss : ENNReal) * (S.activeCoarse.card : ENNReal)) *
        ((M : ENNReal) * (8 * (delta : ENNReal) ^ 2))) <=
      lossBound *
        (8 * (XUpper *
          (((delta : ENNReal) / (rho : ENNReal)) ^ 2))) := by
  have hidentity :=
    activeCoarse_card_mul_delta_sq_eq_cardScaleMass_mul_ratio_sq S hrho
  calc
    (((A_loss : ENNReal) * (S.activeCoarse.card : ENNReal)) *
        ((M : ENNReal) * (8 * (delta : ENNReal) ^ 2))) =
        ((A_loss : ENNReal) * (M : ENNReal)) *
          (8 * ((S.activeCoarse.card : ENNReal) *
            (delta : ENNReal) ^ 2)) := by ring
    _ = ((A_loss : ENNReal) * (M : ENNReal)) *
          (8 * ((activeCoarseCardScaleMass S : ENNReal) *
            (((delta : ENNReal) / (rho : ENNReal)) ^ 2))) := by
      rw [hidentity]
    _ <= lossBound *
        (8 * (XUpper *
          (((delta : ENNReal) / (rho : ENNReal)) ^ 2))) := by
      exact mul_le_mul' hloss
        (mul_le_mul' le_rfl (mul_le_mul' hX le_rfl))

/-- The base coefficient has no fibre-cap loss: only `A.loss`, `X`, and the
same exact relative square remain. -/
theorem baseCoefficient_le_relativeScaleEnvelope
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (lossBound XUpper : ENNReal) (A_loss : Nat)
    (hloss : (A_loss : ENNReal) <= lossBound)
    (hX : (activeCoarseCardScaleMass S : ENNReal) <= XUpper) :
    (((A_loss : ENNReal) * (S.activeCoarse.card : ENNReal)) *
        (8 * (delta : ENNReal) ^ 2)) <=
      lossBound *
        (8 * (XUpper *
          (((delta : ENNReal) / (rho : ENNReal)) ^ 2))) := by
  have hidentity :=
    activeCoarse_card_mul_delta_sq_eq_cardScaleMass_mul_ratio_sq S hrho
  calc
    (((A_loss : ENNReal) * (S.activeCoarse.card : ENNReal)) *
        (8 * (delta : ENNReal) ^ 2)) =
        (A_loss : ENNReal) *
          (8 * ((S.activeCoarse.card : ENNReal) *
            (delta : ENNReal) ^ 2)) := by ring
    _ = (A_loss : ENNReal) *
          (8 * ((activeCoarseCardScaleMass S : ENNReal) *
            (((delta : ENNReal) / (rho : ENNReal)) ^ 2))) := by
      rw [hidentity]
    _ <= lossBound *
        (8 * (XUpper *
          (((delta : ENNReal) / (rho : ENNReal)) ^ 2))) := by
      exact mul_le_mul' hloss
        (mul_le_mul' le_rfl (mul_le_mul' hX le_rfl))

/-- Sharp-envelope version of the bounded mass-popular first factor.  The
two final scalar premises now contain only global quantities and the exact
relative-scale square. -/
theorem exists_boundedAssembly_massPopular_relativePower_factorized_of_envelopes
    {beta epsilon eta p a : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) (r : Real)
    (hscale : delta <= rho) (hcoarse : S.activeCoarse.Nonempty)
    (M : Nat)
    (hM : ∀ k, k ∈ S.activeCoarse -> (S.fiber k).card <= M)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (boundedFiberCoarseTubePartition S hscale hcoarse M hM
        ).asConvexFactorization Y r)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hdeltaRho : delta <= rho)
    {C : ENNReal} (hKT : IsKatzTao C fine.bodyFamily)
    (hp : 0 < p) (ha : 0 < a)
    (hgap : 0 <= eta - (p + a))
    (hdelta0 : contractedJohnProxyRadius delta rho / 8 <= delta0)
    (hsmallRatio : delta / rho <=
      contractedJohnSourcePowerEndpointThreshold a)
    (hCratio : C <=
      (((delta : ENNReal) / (rho : ENNReal)) ^ (-p)))
    (hsource :
      (IndexedShadingRefinement.restrictTo Y S.activeFine).shading.shadingMass
        ≠ 0)
    {assemblyLossBound lossBound XUpper : ENNReal}
    (hassemblyLoss :
      (A.loss : ENNReal) * (M : ENNReal) <= assemblyLossBound)
    (hloss : (A.loss : ENNReal) <= lossBound)
    (hX : (activeCoarseCardScaleMass S : ENNReal) <= XUpper)
    (hdensityEnvelope :
      (assemblyLossBound *
          (8 * (XUpper *
            (((delta : ENNReal) / (rho : ENNReal)) ^ 2)))) *
        (((((delta : ENNReal) / (rho : ENNReal)) ^
            (eta - (p + a))) * 93312) * 128) <=
      (sourceActiveFineShading (toConvexFactorization S) Y).shadingMass)
    (hbaseEnvelope :
      (lossBound *
          (8 * (XUpper *
            (((delta : ENNReal) / (rho : ENNReal)) ^ 2)))) *
        ((3 / 64 : ENNReal) ^ (-(2 * p + a)) *
          (((delta : ENNReal) / (rho : ENNReal)) ^ (-(2 * p + a)))) <=
      (((3 / 64 : ENNReal) ^ (-eta) *
          (((delta : ENNReal) / (rho : ENNReal)) ^ (-eta)) *
        (((3 / 64 : ENNReal) ^ 2 *
          (((delta : ENNReal) / (rho : ENNReal)) ^ 2)) / 2)) *
        (sourceActiveFineShading (toConvexFactorization S) Y).shadingMass)) :
    ∃ q : {q // q ∈
        (selectedFineScaleCover S A.refinement.indices
          (assembly_indices_subset_activeFine S Y r A)).activeCoarse},
      ∃ selected : Finset {i // i ∈
          (selectedFineScaleCover S A.refinement.indices
            (assembly_indices_subset_activeFine S Y r A)).fiber q.1},
        selected.Nonempty ∧
        (actualRefinementShading A).averageMultiplicity <=
          4 * (A.frozenCoarse.averageMultiplicity *
            (stickyFiberContractedJohnSourceClosedLoss C *
              frostmanMultiplicityRHS
                (contractedJohnProxyRadius delta rho / 8)
                (restrictActualTubeDatum
                  (eighthNormalizedDatum
                    (stickyFiberContractedJohnProxyDatum
                      (selectedFineScaleCover S A.refinement.indices
                        (assembly_indices_subset_activeFine S Y r A))
                      (selectedFineShading S A.refinement.indices
                        A.refinement.shading)
                      hrho hrhoOne q)) selected).actualFamilyVolume
                epsilon beta)) := by
  have hdensityCoefficient := densityCoefficient_le_relativeScaleEnvelope
    S hrho M assemblyLossBound XUpper A.loss hassemblyLoss hX
  have hbaseCoefficient := baseCoefficient_le_relativeScaleEnvelope
    S hrho lossBound XUpper A.loss hloss hX
  apply exists_boundedAssembly_massPopular_relativePower_factorized
    hF S Y r hscale hcoarse M hM A hdelta hdeltaHalf hrho hrhoOne
      hdeltaRho hKT hp ha hgap hdelta0 hsmallRatio hCratio hsource
  · exact (mul_le_mul' hdensityCoefficient le_rfl).trans hdensityEnvelope
  · exact (mul_le_mul' hbaseCoefficient le_rfl).trans hbaseEnvelope

#print axioms
  activeCoarse_card_mul_delta_sq_eq_cardScaleMass_mul_ratio_sq
#print axioms densityCoefficient_le_relativeScaleEnvelope
#print axioms baseCoefficient_le_relativeScaleEnvelope
#print axioms
  exists_boundedAssembly_massPopular_relativePower_factorized_of_envelopes

end
end Family8StickyMassPopularRelativeScaleCoefficientV1
