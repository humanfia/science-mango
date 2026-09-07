import Family8Grounding.Family8Prop51SelectedFineBlockDensityNormalizedFrostmanV1

/-!
# Exact volume of a selected occurrence outer family

This file identifies the `familyVolume` of the literal selected occurrence
family with the winning-body volume used by the downstream Prop. 5.1
normalization.  The only reindexing is `R.image some`; injectivity of
`Option.some` means that this step loses neither mass nor multiplicity.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceOuterFamilyVolumeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8Prop51SelectedFineBlockDensityNormalizedFrostmanV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-- The selected outer family has exactly the Prop. 5.1 subselected
winning-body volume.  In particular, the `Option` reindexing introduces no
duplicate-volume loss. -/
theorem selectedOccurrenceOuterFamily_familyVolume_eq_prop51SubselectedBodyVolume
    (P : GreedyDensityPartition F candidates container active)
    (R : Finset (Fin (blocks F P).length)) :
    familyVolume (selectedOccurrenceOuterFamily P R) =
      prop51SubselectedBodyVolume P R := by
  rw [selectedCoarseFamily_volume]
  unfold selectedOccurrenceIndices prop51SubselectedBodyVolume
  rw [Finset.sum_image]
  · rfl
  · intro k _hk l _hl hkl
    exact Option.some.inj hkl

#print axioms
  selectedOccurrenceOuterFamily_familyVolume_eq_prop51SubselectedBodyVolume

end

end Family8SelectedOccurrenceOuterFamilyVolumeV1
