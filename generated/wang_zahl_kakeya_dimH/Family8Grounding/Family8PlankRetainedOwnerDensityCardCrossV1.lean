import Family8Grounding.Family8PlankRetainedOwnerCubeWeightDensityCrossV1
import Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankRetainedOwnerDensityCardCrossV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Density/cardinality cross for the retained owner family

Every retained source plank keeps its certified body.  Thus its actual family
volume is at least retained cardinality times the certified lower body volume.
Source shading density and logarithmic mass retention then give a
division-free lower estimate for the retained mass.
-/

def plankCertifiedLowerVolume
    (D : ShadedConvexPlankFamily iota a b) : ENNReal :=
  (((D.comparisonConstant)⁻¹ : NNReal) : ENNReal) ^ 3 *
    ((a : ENNReal) * (b : ENNReal))

theorem retainedOwner_card_mul_certifiedLowerVolume_le_familyVolume
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    ((Fintype.card {i // i ∈ retainedOwnerSourceIndices C q} : Nat) : ENNReal) *
        plankCertifiedLowerVolume D ≤
      familyVolume (retainedOwnerPlankFamily D C q).family := by
  rw [show familyVolume (retainedOwnerPlankFamily D C q).family =
      ∑ i ∈ retainedOwnerSourceIndices C q,
        volume (D.family i : Set Space) by
    exact selectedCoarseFamily_volume D.family
      (retainedOwnerSourceIndices C q)]
  rw [Fintype.card_coe]
  calc
    (((retainedOwnerSourceIndices C q).card : Nat) : ENNReal) *
        plankCertifiedLowerVolume D =
      ∑ _i ∈ retainedOwnerSourceIndices C q,
        plankCertifiedLowerVolume D := by
      simp [nsmul_eq_mul]
    _ ≤ ∑ i ∈ retainedOwnerSourceIndices C q,
        volume (D.family i : Set Space) := by
      apply Finset.sum_le_sum
      intro i hi
      exact (D.all_isPlank i).volume_lower_bound

theorem retainedOwner_familyVolume_le_sourceFamilyVolume
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    familyVolume (retainedOwnerPlankFamily D C q).family ≤
      familyVolume D.family := by
  rw [show familyVolume (retainedOwnerPlankFamily D C q).family =
      ∑ i ∈ retainedOwnerSourceIndices C q,
        volume (D.family i : Set Space) by
    exact selectedCoarseFamily_volume D.family
      (retainedOwnerSourceIndices C q)]
  rw [familyVolume]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ => bot_le)

theorem retainedOwner_density_mul_card_mul_certifiedLowerVolume_le_mass
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (density loss : ENNReal)
    (hdensity : density ≤ D.shading.shadingDensity)
    (hretain : D.shading.shadingMass ≤
      loss * (retainedOwnerPlankFamily D C q).shading.shadingMass) :
    density *
        ((Fintype.card {i // i ∈ retainedOwnerSourceIndices C q} : Nat) : ENNReal) *
        plankCertifiedLowerVolume D ≤
      loss * (retainedOwnerPlankFamily D C q).shading.shadingMass := by
  calc
    density *
        ((Fintype.card {i // i ∈ retainedOwnerSourceIndices C q} : Nat) : ENNReal) *
        plankCertifiedLowerVolume D =
      density *
        (((Fintype.card {i // i ∈ retainedOwnerSourceIndices C q} : Nat) : ENNReal) *
          plankCertifiedLowerVolume D) := by ring
    _ ≤ density * familyVolume (retainedOwnerPlankFamily D C q).family := by
      gcongr
      exact retainedOwner_card_mul_certifiedLowerVolume_le_familyVolume D C q
    _ ≤ density * familyVolume D.family := by
      gcongr
      exact retainedOwner_familyVolume_le_sourceFamilyVolume D C q
    _ ≤ D.shading.shadingDensity * familyVolume D.family := by gcongr
    _ = D.shading.shadingMass := shadingDensity_mul_familyVolume D.shading
    _ ≤ loss * (retainedOwnerPlankFamily D C q).shading.shadingMass := hretain

#print axioms plankCertifiedLowerVolume
#print axioms retainedOwner_card_mul_certifiedLowerVolume_le_familyVolume
#print axioms retainedOwner_familyVolume_le_sourceFamilyVolume
#print axioms retainedOwner_density_mul_card_mul_certifiedLowerVolume_le_mass

end
end Family8PlankRetainedOwnerDensityCardCrossV1
