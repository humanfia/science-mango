import Family8Grounding.Family8StickyBoundedFiberFactorizationRoundTripV2
import Family8Grounding.Family8StickySelectedFineMassPopularScalarTransportV1
import Mathlib.Tactic

/-!
# Same-product mass-popular low-CF power inputs without source Katz--Tao

The selected-fine assembly provides one literal mass-popular parent that is
also the second factor in the frozen average product. Its mass-to-density and
mass-to-card inequalities cancel the two global scalar budgets.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2600000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyBoundedMassPopularLowCFPowerInputsNoKTV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8StickySelectedFineAssemblyFiberBridgeV1
open Family8StickySelectedFineMassPopularScalarTransportV1
open Family8StickySelectedFineSubtypeScaleCoverV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

private theorem densityTarget_le_of_mass_sandwich
    {coefficient target mass density : ENNReal}
    (hcoefficient0 : coefficient ≠ 0)
    (hcoefficientTop : coefficient ≠ ∞)
    (hlower : coefficient * ((target * 93312) * 128) ≤ mass)
    (hupper : mass ≤ coefficient * density) :
    target ≤ density / 93312 / 128 := by
  have hraw : (target * 93312) * 128 ≤ density :=
    (ENNReal.mul_le_mul_iff_right hcoefficient0 hcoefficientTop).mp
      (hlower.trans hupper)
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
    (Or.inl (by norm_num))).2
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
    (Or.inl (by norm_num))).2
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hraw

private theorem baseTarget_le_of_mass_card_sandwich
    {coefficient base scale unit mass card : ENNReal}
    (hcoefficient0 : coefficient ≠ 0)
    (hcoefficientTop : coefficient ≠ ∞)
    (hlower : coefficient * base ≤ (scale * unit) * mass)
    (hupper : mass ≤ coefficient * card) :
    base ≤ scale * (card * unit) := by
  apply (ENNReal.mul_le_mul_iff_right
    hcoefficient0 hcoefficientTop).mp
  calc
    coefficient * base ≤ (scale * unit) * mass := hlower
    _ ≤ (scale * unit) * (coefficient * card) :=
      mul_le_mul' le_rfl hupper
    _ = coefficient * (scale * (card * unit)) := by ac_rfl

/-- One literal mass-popular selected-fine parent carries the exact frozen
average product and any two uniform card powers, while the two global mass
sandwiches supply its density and base powers. -/
theorem exists_boundedAssembly_massPopular_sameProduct_fourPowerInputs_noKT
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) (r : Real)
    (hscale : delta ≤ rho) (hcoarse : S.activeCoarse.Nonempty)
    (M : Nat)
    (hM : ∀ k, k ∈ S.activeCoarse → (S.fiber k).card ≤ M)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (boundedFiberCoarseTubePartition S hscale hcoarse M hM
        ).asConvexFactorization Y r)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y
        S.activeFine).shading.shadingMass ≠ 0)
    {densityTarget baseTarget baseScale baseUnit
      proxyCardBound relativeCardBound : ENNReal}
    (hdensityScalar :
      (((A.loss : ENNReal) * (S.activeCoarse.card : ENNReal)) *
          ((M : ENNReal) * (8 * (delta : ENNReal) ^ 2))) *
        ((densityTarget * 93312) * 128) ≤
      (sourceActiveFineShading
        (toConvexFactorization S) Y).shadingMass)
    (hbaseScalar :
      (((A.loss : ENNReal) * (S.activeCoarse.card : ENNReal)) *
          (8 * (delta : ENNReal) ^ 2)) * baseTarget ≤
        (baseScale * baseUnit) *
          (sourceActiveFineShading
            (toConvexFactorization S) Y).shadingMass)
    (hcardAndCount :
      ∀ q : {q // q ∈
          (selectedFineScaleCover S A.refinement.indices
            (assembly_indices_subset_activeFine S Y r A)).activeCoarse},
        (Fintype.card {i // i ∈
            (selectedFineScaleCover S A.refinement.indices
              (assembly_indices_subset_activeFine S Y r A)).fiber q.1} :
            ENNReal) ≤ proxyCardBound ∧
        (Fintype.card {i // i ∈
            (selectedFineScaleCover S A.refinement.indices
              (assembly_indices_subset_activeFine S Y r A)).fiber q.1} :
            ENNReal) ≤ relativeCardBound) :
    ∃ q : {q // q ∈
        (selectedFineScaleCover S A.refinement.indices
          (assembly_indices_subset_activeFine S Y r A)).activeCoarse},
      let T := selectedFineScaleCover S A.refinement.indices
        (assembly_indices_subset_activeFine S Y r A)
      let Z := selectedFineShading S A.refinement.indices
        A.refinement.shading
      (actualRefinementShading A).averageMultiplicity ≤
          4 * (A.frozenCoarse.averageMultiplicity *
            (stickyFiberSourceShading T Z q.1).averageMultiplicity) ∧
      densityTarget ≤
        (stickyFiberSourceShading T Z q.1).shadingDensity / 93312 / 128 ∧
      baseTarget ≤ baseScale *
        ((Fintype.card {i // i ∈ T.fiber q.1} : ENNReal) * baseUnit) ∧
      (Fintype.card {i // i ∈ T.fiber q.1} : ENNReal) ≤
        proxyCardBound ∧
      (Fintype.card {i // i ∈ T.fiber q.1} : ENNReal) ≤
        relativeCardBound := by
  classical
  let hselected := assembly_indices_subset_activeFine S Y r A
  let T := selectedFineScaleCover S A.refinement.indices hselected
  let Z := selectedFineShading S A.refinement.indices A.refinement.shading
  let sourceMass :=
    (sourceActiveFineShading (toConvexFactorization S) Y).shadingMass
  let L : ENNReal :=
    (A.loss : ENNReal) * (S.activeCoarse.card : ENNReal)
  let volumeUnit : ENNReal := 8 * (delta : ENNReal) ^ 2
  let densityCoefficient : ENNReal :=
    L * ((M : ENNReal) * volumeUnit)
  let cardCoefficient : ENNReal := L * volumeUnit
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
  have hmassCard' : sourceMass ≤ cardCoefficient * fibreCard := by
    calc
      sourceMass ≤ L * (fibreCard * volumeUnit) := by
        simpa only [sourceMass, L, volumeUnit, fibreCard, T, Z, hselected]
          using hmassCard
      _ = cardCoefficient * fibreCard := by
        dsimp only [cardCoefficient]
        ac_rfl
  have hmassDensity' :
      sourceMass ≤ densityCoefficient * fibreDensity := by
    simpa only [sourceMass, densityCoefficient, L, volumeUnit,
      fibreDensity, T, Z, hselected] using hmassDensity
  have hcardCoefficient0 : cardCoefficient ≠ 0 := by
    intro hzero
    apply hsourceMass0
    exact le_antisymm
      (hmassCard'.trans_eq (by rw [hzero, zero_mul])) bot_le
  have hdensityCoefficient0 : densityCoefficient ≠ 0 := by
    intro hzero
    apply hsourceMass0
    exact le_antisymm
      (hmassDensity'.trans_eq (by rw [hzero, zero_mul])) bot_le
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
      ((densityTarget * 93312) * 128) ≤ sourceMass := by
    simpa only [densityCoefficient, L, volumeUnit, sourceMass] using
      hdensityScalar
  have hdensity : densityTarget ≤ fibreDensity / 93312 / 128 :=
    densityTarget_le_of_mass_sandwich hdensityCoefficient0
      hdensityCoefficientTop hdensityLower hmassDensity'
  have hbaseLower : cardCoefficient * baseTarget ≤
      (baseScale * baseUnit) * sourceMass := by
    simpa only [cardCoefficient, L, volumeUnit, sourceMass] using hbaseScalar
  have hbase : baseTarget ≤
      baseScale * (fibreCard * baseUnit) :=
    baseTarget_le_of_mass_card_sandwich hcardCoefficient0
      hcardCoefficientTop hbaseLower hmassCard'
  obtain ⟨hproxy, hrelative⟩ := hcardAndCount q
  refine ⟨q, ?_⟩
  dsimp only
  exact ⟨by
      (convert hproduct using 1; rfl),
    by simpa only [T, Z, hselected, fibreDensity] using hdensity,
    by simpa only [T, hselected, fibreCard] using hbase,
    by simpa only [T, hselected] using hproxy,
    by simpa only [T, hselected] using hrelative⟩

#print axioms
  exists_boundedAssembly_massPopular_sameProduct_fourPowerInputs_noKT

end
end Family8StickyBoundedMassPopularLowCFPowerInputsNoKTV5
