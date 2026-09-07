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

namespace Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV6

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
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
set_option maxHeartbeats 2000000

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

end AllActiveUpper

#print axioms partitionOfAllAtActive_induced_averageMultiplicity_eq
#print axioms upperPartitionOfAll_induced_averageMultiplicity_eq
#print axioms selectedOccurrenceOuterShading_univ_averageMultiplicity_eq_induced
#print axioms maxWitnessSelectedOccurrenceCount_le_activeParentCard
#print axioms maxWitnessCommonScale_uniformEq46Count

end
end Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV6
