import Family8Grounding.Family8StickySelectedFineMassPopularScalarTransportV1
import Family8Grounding.Family8StickyFiberContractedJohnRelativePowerEndpointV1
import Family8Grounding.Family8StickySelectedFineRelativePowerFactorV1
import Family8Grounding.Family8StickyBoundedFiberFactorizationRoundTripV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyBoundedMassPopularRelativePowerFactorV1

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
open Family8StickyFiberContractedJohnRelativePowerEndpointV1
open Family8StickySelectedFineSubtypeScaleCoverV1
open Family8StickySelectedFineAssemblyFiberBridgeV1
open Family8StickySelectedFineRelativePowerFactorV1
open Family8StickySelectedFineMassPopularScalarTransportV1
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyBoundedFiberFactorizationRoundTripV2
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Mass-popular first Frostman factor for the bounded Sticky assembly

The mass-popular selected parent supplies both endpoint scalar budgets on the
same object.  Two division-free global inequalities are the only remaining
inputs: one absorbs the bounded density coefficient, and one absorbs the
cardinality coefficient.  Honest ENNReal cancellation then produces exactly
the relative-scale density and base premises of the contracted-John endpoint.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Cancellation form of the two fixed density-normalization losses. -/
theorem density_div_93312_div_128_of_mass_sandwich
    {coefficient target mass density : ENNReal}
    (hcoefficient0 : coefficient ≠ 0)
    (hcoefficientTop : coefficient ≠ ∞)
    (hlower : coefficient * ((target * 93312) * 128) <= mass)
    (hupper : mass <= coefficient * density) :
    target <= density / 93312 / 128 := by
  have hraw : (target * 93312) * 128 <= density :=
    (ENNReal.mul_le_mul_iff_right hcoefficient0 hcoefficientTop).mp
      (hlower.trans hupper)
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
    (Or.inl (by norm_num))).2
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
    (Or.inl (by norm_num))).2
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hraw

/-- Cross-multiplied mass-to-card cancellation in exactly the endpoint
factor order. -/
theorem baseRatio_of_mass_card_sandwich
    {coefficient base scale unit mass card : ENNReal}
    (hcoefficient0 : coefficient ≠ 0)
    (hcoefficientTop : coefficient ≠ ∞)
    (hlower : coefficient * base <= (scale * unit) * mass)
    (hupper : mass <= coefficient * card) :
    base <= scale * (card * unit) := by
  apply (ENNReal.mul_le_mul_iff_right hcoefficient0 hcoefficientTop).mp
  calc
    coefficient * base <= (scale * unit) * mass := hlower
    _ <= (scale * unit) * (coefficient * card) :=
      mul_le_mul' le_rfl hupper
    _ = coefficient * (scale * (card * unit)) := by ac_rfl

/-- The literal bounded assembly realizes its first Frostman factor on one
mass-popular selected parent.  Both former fibre-dependent hypotheses have
been replaced by two global, division-free scalar inequalities. -/
theorem exists_boundedAssembly_massPopular_relativePower_factorized
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
    (hdensityScalar :
      (((A.loss : ENNReal) * (S.activeCoarse.card : ENNReal)) *
          ((M : ENNReal) * (8 * (delta : ENNReal) ^ 2))) *
        (((((delta : ENNReal) / (rho : ENNReal)) ^
            (eta - (p + a))) * 93312) * 128) <=
      (sourceActiveFineShading (toConvexFactorization S) Y).shadingMass)
    (hbaseScalar :
      (((A.loss : ENNReal) * (S.activeCoarse.card : ENNReal)) *
          (8 * (delta : ENNReal) ^ 2)) *
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
  classical
  have hround :=
    boundedFiber_asConvexFactorization_eq_toConvexFactorization
      S hscale hcoarse M hM
  let hselected := assembly_indices_subset_activeFine S Y r A
  let T := selectedFineScaleCover S A.refinement.indices hselected
  let Z := selectedFineShading S A.refinement.indices A.refinement.shading
  let sourceMass :=
    (sourceActiveFineShading (toConvexFactorization S) Y).shadingMass
  let L : ENNReal :=
    (A.loss : ENNReal) * (S.activeCoarse.card : ENNReal)
  let volumeUnit : ENNReal := 8 * (delta : ENNReal) ^ 2
  let densityCoefficient : ENNReal := L * ((M : ENNReal) * volumeUnit)
  let cardCoefficient : ENNReal := L * volumeUnit
  let ratio : ENNReal := (delta : ENNReal) / (rho : ENNReal)
  let densityTarget : ENNReal := ratio ^ (eta - (p + a))
  let base : ENNReal :=
    (3 / 64 : ENNReal) ^ (-(2 * p + a)) * ratio ^ (-(2 * p + a))
  let baseScale : ENNReal :=
    (3 / 64 : ENNReal) ^ (-eta) * ratio ^ (-eta)
  let baseUnit : ENNReal :=
    ((3 / 64 : ENNReal) ^ 2 * ratio ^ 2) / 2
  obtain ⟨q, hmassCard, hmassDensity, _hvolume, hproduct⟩ :=
    exists_selectedFine_massPopular_card_density_product
      S Y r A hdeltaHalf M hM hsource
  let fibreCard : ENNReal := Fintype.card {i // i ∈ T.fiber q.1}
  let fibreDensity : ENNReal :=
    (stickyFiberSourceShading T Z q.1).shadingDensity
  have hsourceMass0 : sourceMass ≠ 0 := by
    dsimp only [sourceMass]
    rw [sourceActiveFineShading_shadingMass]
    simpa only [toConvexFactorization_fine] using hsource
  have hmassCard' : sourceMass <= cardCoefficient * fibreCard := by
    calc
      sourceMass <= L * (fibreCard * volumeUnit) := by
        simpa only [sourceMass, L, volumeUnit, fibreCard, T, Z, hselected]
          using hmassCard
      _ = cardCoefficient * fibreCard := by
        dsimp only [cardCoefficient]
        ac_rfl
  have hmassDensity' : sourceMass <= densityCoefficient * fibreDensity := by
    simpa only [sourceMass, densityCoefficient, L, volumeUnit, fibreDensity,
      T, Z, hselected] using hmassDensity
  have hcardCoefficient0 : cardCoefficient ≠ 0 := by
    intro hzero
    apply hsourceMass0
    exact le_antisymm (hmassCard'.trans_eq (by rw [hzero, zero_mul])) bot_le
  have hdensityCoefficient0 : densityCoefficient ≠ 0 := by
    intro hzero
    apply hsourceMass0
    exact le_antisymm (hmassDensity'.trans_eq (by rw [hzero, zero_mul])) bot_le
  have hvolumeUnitTop : volumeUnit ≠ ∞ := by
    dsimp only [volumeUnit]
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hLTop : L ≠ ∞ := by
    dsimp only [L]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.natCast_ne_top _)
  have hcardCoefficientTop : cardCoefficient ≠ ∞ := by
    dsimp only [cardCoefficient]
    exact ENNReal.mul_ne_top hLTop hvolumeUnitTop
  have hdensityCoefficientTop : densityCoefficient ≠ ∞ := by
    dsimp only [densityCoefficient]
    exact ENNReal.mul_ne_top hLTop
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hvolumeUnitTop)
  have hdensityLower : densityCoefficient *
      ((densityTarget * 93312) * 128) <= sourceMass := by
    simpa only [densityCoefficient, densityTarget, ratio, L, volumeUnit,
      sourceMass] using hdensityScalar
  have hsourceDensityRatio :
      ratio ^ (eta - (p + a)) <= fibreDensity / 93312 / 128 := by
    exact density_div_93312_div_128_of_mass_sandwich
      hdensityCoefficient0 hdensityCoefficientTop hdensityLower hmassDensity'
  have hbaseLower : cardCoefficient * base <=
      (baseScale * baseUnit) * sourceMass := by
    simpa only [cardCoefficient, base, baseScale, baseUnit, ratio, L,
      volumeUnit, sourceMass, mul_assoc] using hbaseScalar
  have hbaseRatio : base <= baseScale * (fibreCard * baseUnit) :=
    baseRatio_of_mass_card_sandwich hcardCoefficient0 hcardCoefficientTop
      hbaseLower hmassCard'
  have hKTSelected : IsKatzTao C
      (selectedFineFamily S A.refinement.indices).bodyFamily :=
    selectedFineFamily_isKatzTao S A.refinement.indices hKT
  obtain ⟨selected, hselectedNonempty, hfirst⟩ :=
    exists_stickyFiberContractedJohn_global_average_le_relativePower_frostmanRHS
      hF T Z hdelta hdeltaHalf hrho hrhoOne hdeltaRho q hKTSelected
        hp ha hgap hdelta0 hsmallRatio hCratio
        (by simpa only [ratio, fibreDensity] using hsourceDensityRatio)
        (by simpa only [base, baseScale, baseUnit, ratio, fibreCard, T,
          hselected] using hbaseRatio)
  refine ⟨q, selected, hselectedNonempty, hproduct.trans ?_⟩
  exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hfirst)

#print axioms density_div_93312_div_128_of_mass_sandwich
#print axioms baseRatio_of_mass_card_sandwich
#print axioms exists_boundedAssembly_massPopular_relativePower_factorized

end
end Family8StickyBoundedMassPopularRelativePowerFactorV1
