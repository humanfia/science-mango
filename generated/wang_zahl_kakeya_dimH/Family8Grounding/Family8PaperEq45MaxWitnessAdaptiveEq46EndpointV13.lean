import Family8Grounding.Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
import Family8Grounding.Family8PaperEq45MaxWitnessCommonScaleCanonicalV2
import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveThinCountUniformEq46CountV2
import Family8Grounding.Family8Prop66AUniformCountLossAlgebraV3
import Family8Grounding.Family8Prop66AActualFamilyVolumeTransportV1
import Family8Grounding.Family8ExactAssemblyActualAverageBridgeV1
import Mathlib.Tactic

/-!
# Same-object max-witness Equation (45) plus adaptive Equation (46) endpoint

Apply the max-witness Equation (45) construction one scale above an existing
sticky cover.  Its fine index type is then literally the active-parent type
of the lower cover, and its greedy partition is the same partition used by
the selected-parent Equation (46) line.

This closes two formerly implicit structural seams:

* the `R0 = univ` selected-occurrence outer shading has exactly the same
  average multiplicity as the exact assembly's induced shading;
* the max-witness occurrence count injects into the actual active-parent
  type, so every natural `tubesPerPlank` gives the honest count-loss
  inequality with `countLoss = tubesPerPlank`.

The final theorem consumes the stable Family 6 Equation (45) bound and the
uniform-count algebra on this same object.  Its only remaining Equation (46)
premise is the analytic bound on each actual `sourceFineLevelShading`; the
current adaptive producer proves caps and selected-proxy bounds, but there is
not yet a carrier/shading identification from those proxies to this exact
assembly fibre.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV13

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2.PaperEq45MaxWitnessCommonScaleInput
open Family8Prop66AActualFamilyVolumeTransportV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8Prop66AUniformCountLossAlgebraV3
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceActiveParentOwnerV7
open Family8SelectedOccurrenceMaxOwnerHullFrostmanProducerV3
open Family8SelectedOccurrenceMaxOwnerHullQualityV3
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8SelectedOccurrenceMaxWitnessCommonScaleV1
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8SelectedParentPlankCenteredAdaptiveThinCountUniformEq46CountV2
open Family8SelectedParentGreedyBlockFiberIdentityV2
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

/-! ## Exact subtype-to-induced outer shading transport -/

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa → ConvexBody Space} {active : Finset iota}

theorem selectedOccurrenceOuterShading_univ_shadingMass_eq_induced
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) :
    (selectedOccurrenceOuterShading P Y Finset.univ).shadingMass =
      ((convexFactorization F P).inducedShading Y).shadingMass := by
  rw [selectedOccurrenceOuterShading_mass]
  unfold Shading.shadingMass
  rw [Fintype.sum_option]
  have hnone : none ∉ (convexFactorization F P).index.coarse := by
    change none ∉ occurrenceIndices F P
    simp [occurrenceIndices]
  have hnoneCarrier :
      ((convexFactorization F P).inducedShading Y).carrier none = ∅ := by
    simp [ConvexFactorization.inducedShading, hnone]
  rw [hnoneCarrier]
  simp

theorem selectedOccurrenceOuterShading_univ_shadedUnion_eq_induced
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) :
    (selectedOccurrenceOuterShading P Y Finset.univ).shadedUnion =
      ((convexFactorization F P).inducedShading Y).shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨q.1, hxq⟩
  · intro hx
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hq, _i, _hi, _hxi⟩ :=
      ((convexFactorization F P).mem_inducedShading_carrier_iff Y q x).1 hxq
    rw [show (convexFactorization F P).index.coarse =
        occurrenceIndices F P from rfl] at hq
    simp only [occurrenceIndices, Finset.mem_image, Finset.mem_univ,
      true_and] at hq
    obtain ⟨k, rfl⟩ := hq
    apply Set.mem_iUnion.mpr
    refine ⟨⟨some k, ?_⟩, hxq⟩
    simp [selectedOccurrenceIndices]

theorem selectedOccurrenceOuterShading_univ_averageMultiplicity_eq_induced
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) :
    (selectedOccurrenceOuterShading P Y Finset.univ).averageMultiplicity =
      ((convexFactorization F P).inducedShading Y).averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [selectedOccurrenceOuterShading_univ_shadingMass_eq_induced P Y,
    selectedOccurrenceOuterShading_univ_shadedUnion_eq_induced P Y]

/-! ## Actual max-witness count is an active-parent count -/

variable {delta rho sigma : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {D : ActualTubeDatum delta index}
  (S : StickyScaleCover D.family rho)
  (U : StickyScaleCover (S.coarse.restrictTo S.activeCoarse) sigma)
  {Q : GreedyDensityPartition S.activeCoarseFamily
    (hullCandidates U.activeFine)
    (hullContainer S.activeCoarseFamily) U.activeFine}

theorem maxWitnessSelectedOccurrenceCount_le_activeParentCard
    (Y : Shading S.activeCoarseFamily)
    (R : Finset (Fin (blocks S.activeCoarseFamily Q).length)) :
    Fintype.card {q // q ∈ selectedOccurrenceIndices Q R} ≤
      Fintype.card (ActiveParentIndex S) := by
  exact Fintype.card_le_of_injective
    (fun q : {q // q ∈ selectedOccurrenceIndices Q R} ↦
      occurrenceMaxShadedWitness U Q Y
        (selectedOccurrencePosition U R q))
    (selectedOccurrenceMaxWitness_injective U Y R)

variable {Y : Shading S.activeCoarseFamily}
  {R0 : Finset (Fin (blocks S.activeCoarseFamily Q).length)}
  {conflictLoss : ENNReal}
  {W : DoubledParentConflictWeightedSelection U
    (occurrenceMaxOwnerMass U Q Y R0) conflictLoss}

/-- Same-object natural Equation (46) count.  In particular it can be
instantiated with the adaptive uniform cap from `UniformEq46CountV2`. -/
theorem maxWitnessCommonScale_uniformEq46Count
    (I : PaperEq45MaxWitnessCommonScaleInput U Y R0 conflictLoss W)
    (tubesPerPlank : Nat) :
    (((plankCount U I) * tubesPerPlank : Nat) : ENNReal) ≤
      (tubesPerPlank : ENNReal) *
        (Fintype.card (ActiveParentIndex S) : ENNReal) := by
  have hcard : plankCount U I ≤ Fintype.card (ActiveParentIndex S) :=
    maxWitnessSelectedOccurrenceCount_le_activeParentCard S U Y
      (selected U I)
  have hcardENN : (plankCount U I : ENNReal) ≤
      (Fintype.card (ActiveParentIndex S) : ENNReal) := by
    exact_mod_cast hcard
  calc
    (((plankCount U I) * tubesPerPlank : Nat) : ENNReal) =
        (plankCount U I : ENNReal) * (tubesPerPlank : ENNReal) := by
      norm_num
    _ ≤ (Fintype.card (ActiveParentIndex S) : ENNReal) *
        (tubesPerPlank : ENNReal) := mul_le_mul' hcardENN le_rfl
    _ = (tubesPerPlank : ENNReal) *
        (Fintype.card (ActiveParentIndex S) : ENNReal) := mul_comm _ _

/-! ## Transport from an actually all-active upper cover -/

section AllActiveUpper

variable {delta0 rho0 sigma0 : NNReal} {index0 : Type}
  [Fintype index0] [DecidableEq index0]
  {D0 : ActualTubeDatum delta0 index0}
  (S0 : StickyScaleCover D0.family rho0)

noncomputable def partitionOfAllAtActive
    (A0 : Finset (ActiveParentIndex S0))
    (hactive : A0 = (Finset.univ : Finset (ActiveParentIndex S0)))
    (P0 : GreedyDensityPartition S0.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S0)))
      (hullContainer S0.activeCoarseFamily) Finset.univ) :
    GreedyDensityPartition S0.activeCoarseFamily
      (hullCandidates A0) (hullContainer S0.activeCoarseFamily) A0 := by
  simpa only [hactive] using P0

theorem partitionOfAllAtActive_induced_averageMultiplicity_eq
    (A0 : Finset (ActiveParentIndex S0))
    (hactive : A0 = (Finset.univ : Finset (ActiveParentIndex S0)))
    (P0 : GreedyDensityPartition S0.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S0)))
      (hullContainer S0.activeCoarseFamily) Finset.univ)
    (Y0 : Shading S0.activeCoarseFamily) :
    ((convexFactorization S0.activeCoarseFamily
      (partitionOfAllAtActive S0 A0 hactive P0)).inducedShading Y0).averageMultiplicity =
      ((greedyParentFactorization S0 P0).inducedShading Y0).averageMultiplicity := by
  subst A0
  rfl

variable (U0 : StickyScaleCover (S0.coarse.restrictTo S0.activeCoarse) sigma0)

noncomputable abbrev upperPartitionOfAll
    (hactive : U0.activeFine = (Finset.univ : Finset (ActiveParentIndex S0)))
    (P0 : GreedyDensityPartition S0.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S0)))
      (hullContainer S0.activeCoarseFamily) Finset.univ) :=
  partitionOfAllAtActive S0 U0.activeFine hactive P0

theorem upperPartitionOfAll_induced_averageMultiplicity_eq
    (hactive : U0.activeFine = (Finset.univ : Finset (ActiveParentIndex S0)))
    (P0 : GreedyDensityPartition S0.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S0)))
      (hullContainer S0.activeCoarseFamily) Finset.univ)
    (Y0 : Shading S0.activeCoarseFamily) :
    ((convexFactorization S0.activeCoarseFamily
      (upperPartitionOfAll S0 U0 hactive P0)).inducedShading Y0).averageMultiplicity =
      ((greedyParentFactorization S0 P0).inducedShading Y0).averageMultiplicity :=
  partitionOfAllAtActive_induced_averageMultiplicity_eq
    S0 U0.activeFine hactive P0 Y0

theorem upperCover_activeFine_eq_univ :
    U0.activeFine = (Finset.univ : Finset (ActiveParentIndex S0)) := by
  calc
    U0.activeFine =
        (S0.coarse.restrictTo S0.activeCoarse).refinement.refined :=
      U0.activeFine_eq_refined
    _ = Finset.univ := S0.coarse.restrictTo_refined S0.activeCoarse

noncomputable abbrev canonicalUpperPartition
    (P0 : GreedyDensityPartition S0.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S0)))
      (hullContainer S0.activeCoarseFamily) Finset.univ) :=
  upperPartitionOfAll S0 U0 (upperCover_activeFine_eq_univ S0 U0) P0

end AllActiveUpper

/-! ## Same actual witness Equation (45) x Equation (46) endpoint -/

section SameObjectComposition

variable {delta1 rho1 sigma1 : NNReal} {index1 : Type}
  [Fintype index1] [DecidableEq index1]
  (D1 : ActualTubeDatum delta1 index1)
  (S1 : StickyScaleCover D1.family rho1)
  (U1 : StickyScaleCover (S1.coarse.restrictTo S1.activeCoarse) sigma1)
  (P1 : GreedyDensityPartition S1.activeCoarseFamily
    (hullCandidates (Finset.univ : Finset (ActiveParentIndex S1)))
    (hullContainer S1.activeCoarseFamily) Finset.univ)
  {assemblyLoss1 : Nat}
  (A1 : FactoringMultiplicityAssembly.ExactAssembly
    (greedyParentFactorization S1 P1)
    (parentAggregatedShading S1 D1.shading) assemblyLoss1)
  {conflictLoss1 : ENNReal}
  (W1 : DoubledParentConflictWeightedSelection U1
    (occurrenceMaxOwnerMass U1
      (canonicalUpperPartition S1 U1 P1)
      A1.refinement.shading Finset.univ) conflictLoss1)
  (I1 : PaperEq45MaxWitnessCommonScaleInput U1
    A1.refinement.shading Finset.univ conflictLoss1 W1)

theorem exists_family6Parameters_refinementAverage_le_witnessEq45_mul_eq46
    (hsource :
      (IndexedShadingRefinement.restrictTo
        (parentAggregatedShading S1 D1.shading)
        (greedyParentFactorization S1 P1).index.fine).shading.shadingMass ≠ 0)
    (tubesPerPlank : Nat)
    {beta : Real}
    (H : ConvexPlankFrostmanMultiplicityHypothesis
      {q // q ∈ selectedOccurrenceIndices
        (canonicalUpperPartition S1 U1 P1) (selected U1 I1)} beta)
    (lemmaEpsilon epsilon : Real) (hlemmaEpsilon : 0 < lemmaEpsilon)
    (habsorb : ScaleAbsorption U1 I1 rho1 lemmaEpsilon epsilon beta)
    (hrhoHalf : rho1 <= (2 : NNReal)⁻¹)
    (hbeta : 0 <= beta) (hbetaOne : beta <= 1)
    (hinner : ∀ k,
      k ∈ (greedyParentFactorization S1 P1).index.coarse →
      (sourceFineLevelShading A1 k).averageMultiplicity <=
        proposition66AInnerFactor rho1
          (maxWitnessCommonWidth rho1) (maxWitnessCommonWidth rho1)
          tubesPerPlank epsilon beta) :
    ∃ eta : Real, ∃ b0 : NNReal,
      0 < eta ∧ 0 < b0 ∧
      ∀ (_hw : 0 < maxWitnessCommonWidth rho1),
        maxWitnessCommonWidth rho1 <= b0 →
        (maxWitnessCommonWidth rho1 : ENNReal) ^ eta <=
          (datum U1 I1).shading.shadingDensity →
        A1.refinement.shading.averageMultiplicity <=
          ((((I1.fibreCardCap : ENNReal) * conflictLoss1) *
              (I1.fibreCardCap : ENNReal)) *
            (tubesPerPlank : ENNReal) ^ (1 - beta / 2)) *
          ((proposition66AFrostmanAspectGain
              (maxWitnessCommonWidth rho1) (maxWitnessCommonWidth rho1)
              I1.frostmanConstant beta *
              (2 : ENNReal) ^ (1 - beta / 2)) *
            frostmanMultiplicityRHS rho1
              (activeParentActualTubeDatum S1 D1.shading).actualFamilyVolume
              epsilon beta) := by
  obtain ⟨eta, b0, heta, hb0, hEq45⟩ :=
    exists_family6Parameters_sourceAverage_le_eq45 U1 I1 H rho1
      lemmaEpsilon epsilon hlemmaEpsilon habsorb
  refine ⟨eta, b0, heta, hb0, ?_⟩
  intro hw hwb0 hdensity
  have houterSelected := hEq45 hw hwb0 hdensity
  let outerLoss : ENNReal :=
    ((I1.fibreCardCap : ENNReal) * conflictLoss1) *
      (I1.fibreCardCap : ENNReal)
  have houterQ :
      ((convexFactorization S1.activeCoarseFamily
        (canonicalUpperPartition S1 U1 P1)).inducedShading
          A1.refinement.shading).averageMultiplicity <=
        outerLoss * proposition66AOuterFactor rho1
          (maxWitnessCommonWidth rho1) (maxWitnessCommonWidth rho1)
          (plankCount U1 I1) I1.frostmanConstant epsilon beta := by
    rw [← selectedOccurrenceOuterShading_univ_averageMultiplicity_eq_induced
      (canonicalUpperPartition S1 U1 P1) A1.refinement.shading]
    convert houterSelected using 1
    · congr 1
    · rfl
  have houter :
      ((greedyParentFactorization S1 P1).inducedShading
        A1.refinement.shading).averageMultiplicity <=
        outerLoss * proposition66AOuterFactor rho1
          (maxWitnessCommonWidth rho1) (maxWitnessCommonWidth rho1)
          (plankCount U1 I1) I1.frostmanConstant epsilon beta := by
    calc
      ((greedyParentFactorization S1 P1).inducedShading
        A1.refinement.shading).averageMultiplicity =
          ((convexFactorization S1.activeCoarseFamily
            (canonicalUpperPartition S1 U1 P1)).inducedShading
              A1.refinement.shading).averageMultiplicity :=
        (upperPartitionOfAll_induced_averageMultiplicity_eq
          S1 U1 (upperCover_activeFine_eq_univ S1 U1) P1 A1.refinement.shading).symm
      _ <= _ := houterQ
  obtain ⟨k, hk, _hvolume, hproduct⟩ :=
    refinement_averageMultiplicity_le_product_actualAverages A1 hsource
  have hcount :=
    maxWitnessCommonScale_uniformEq46Count S1 U1 I1 tubesPerPlank
  have hscalar :=
    proposition66AOuterFactor_mul_innerFactor_le_countLoss_mul_frostmanFactor
      (CF := I1.frostmanConstant)
      (countLoss := (tubesPerPlank : ENNReal))
      (epsilon := epsilon) (beta := beta)
      I1.delta_pos hw hw hbeta hbetaOne hcount
  have hactual := proposition66AFrostmanFactor_le_actualRHS_with_two_rpow
    (activeParentActualTubeDatum S1 D1.shading)
    (a := maxWitnessCommonWidth rho1) (b := maxWitnessCommonWidth rho1)
    (CF := I1.frostmanConstant) (epsilon := epsilon) (beta := beta)
    hrhoHalf (hbetaOne.trans (by norm_num))
  calc
    A1.refinement.shading.averageMultiplicity <=
        ((greedyParentFactorization S1 P1).inducedShading
          A1.refinement.shading).averageMultiplicity *
          (sourceFineLevelShading A1 k).averageMultiplicity := hproduct
    _ <= (outerLoss * proposition66AOuterFactor rho1
          (maxWitnessCommonWidth rho1) (maxWitnessCommonWidth rho1)
          (plankCount U1 I1) I1.frostmanConstant epsilon beta) *
        proposition66AInnerFactor rho1
          (maxWitnessCommonWidth rho1) (maxWitnessCommonWidth rho1)
          tubesPerPlank epsilon beta :=
      mul_le_mul' houter (hinner k hk)
    _ = outerLoss *
        (proposition66AOuterFactor rho1
          (maxWitnessCommonWidth rho1) (maxWitnessCommonWidth rho1)
          (plankCount U1 I1) I1.frostmanConstant epsilon beta *
        proposition66AInnerFactor rho1
          (maxWitnessCommonWidth rho1) (maxWitnessCommonWidth rho1)
          tubesPerPlank epsilon beta) := by ac_rfl
    _ <= outerLoss *
        ((tubesPerPlank : ENNReal) ^ (1 - beta / 2) *
          proposition66AFrostmanFactor rho1
            (maxWitnessCommonWidth rho1) (maxWitnessCommonWidth rho1)
            (Fintype.card (ActiveParentIndex S1)) I1.frostmanConstant
            epsilon beta) := mul_le_mul' le_rfl hscalar
    _ <= outerLoss *
        ((tubesPerPlank : ENNReal) ^ (1 - beta / 2) *
          ((proposition66AFrostmanAspectGain
              (maxWitnessCommonWidth rho1) (maxWitnessCommonWidth rho1)
              I1.frostmanConstant beta *
              (2 : ENNReal) ^ (1 - beta / 2)) *
            frostmanMultiplicityRHS rho1
              (activeParentActualTubeDatum S1 D1.shading).actualFamilyVolume
              epsilon beta)) := by
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hactual)
    _ = (outerLoss *
          (tubesPerPlank : ENNReal) ^ (1 - beta / 2)) *
          ((proposition66AFrostmanAspectGain
              (maxWitnessCommonWidth rho1) (maxWitnessCommonWidth rho1)
              I1.frostmanConstant beta *
              (2 : ENNReal) ^ (1 - beta / 2)) *
            frostmanMultiplicityRHS rho1
              (activeParentActualTubeDatum S1 D1.shading).actualFamilyVolume
              epsilon beta) := by ac_rfl

end SameObjectComposition

#print axioms upperCover_activeFine_eq_univ
#print axioms
  exists_family6Parameters_refinementAverage_le_witnessEq45_mul_eq46
#print axioms partitionOfAllAtActive_induced_averageMultiplicity_eq
#print axioms upperPartitionOfAll_induced_averageMultiplicity_eq
#print axioms selectedOccurrenceOuterShading_univ_averageMultiplicity_eq_induced
#print axioms maxWitnessSelectedOccurrenceCount_le_activeParentCard
#print axioms maxWitnessCommonScale_uniformEq46Count

end
end Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV13
