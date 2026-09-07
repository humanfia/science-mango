import Family8Grounding.Family8PlankCanonicalUnitSlabIncidenceV5
import Family8Grounding.Family8PlankHeavyRetainedOwnerActualDatumV2
import «CubeWeightUniformization»
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankHeavyRetainedOwnerCellRestrictedCanonicalSlabV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.CubeWeightUniformization
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6CanonicalCertifiedPlankSlabIncidenceCoreV3
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankHeavyRetainedOwnerActualDatumV2
open Family8PlankCanonicalUnitSlabIncidenceV5

noncomputable section

universe u v

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# The heavy source datum after the common cell restriction

Both the fine heavy source shading and its induced thickened-owner shading
are restricted by exactly the same selected spatial cells.  Their shaded
unions remain equal, and the fine restriction is packaged as the literal
plank datum consumed by the canonical certified unit-slab API.
-/

theorem heavyRetainedOwner_commonCellRestriction_shadedUnion_eq
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex) :
    (restrictToCells (heavyRetainedOwnerPlankFamily D C q).shading
        cell hcell selected).shadedUnion =
      (restrictToCells (heavyRetainedOwnerThickenedShading D C q)
        cell hcell selected).shadedUnion := by
  rw [restrictToCells_shadedUnion, restrictToCells_shadedUnion,
    heavyRetainedOwnerThickenedShading_shadedUnion_eq]

def heavyRetainedOwnerCellRestrictedPlankDatum
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex) :
    ShadedConvexPlankFamily
      {i // i ∈ heavyRetainedOwnerSourceIndices C q} a b :=
  { heavyRetainedOwnerPlankFamily D C q with
      shading := restrictToCells
        (heavyRetainedOwnerPlankFamily D C q).shading cell hcell selected }

@[simp] theorem heavyRetainedOwnerCellRestrictedPlankDatum_family
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex) :
    (heavyRetainedOwnerCellRestrictedPlankDatum
      D C q cell hcell selected).family =
        (heavyRetainedOwnerPlankFamily D C q).family := rfl

@[simp] theorem heavyRetainedOwnerCellRestrictedPlankDatum_shading
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex) :
    (heavyRetainedOwnerCellRestrictedPlankDatum
      D C q cell hcell selected).shading =
        restrictToCells (heavyRetainedOwnerPlankFamily D C q).shading
          cell hcell selected := rfl

@[simp] theorem heavyRetainedOwnerCellRestrictedPlankDatum_comparisonConstant
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex) :
    (heavyRetainedOwnerCellRestrictedPlankDatum
      D C q cell hcell selected).comparisonConstant =
        D.comparisonConstant := rfl

theorem heavyRetainedOwnerCellRestrictedPlankDatum_shadedUnion_eq_coarse
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex) :
    (heavyRetainedOwnerCellRestrictedPlankDatum
      D C q cell hcell selected).shading.shadedUnion =
      (restrictToCells (heavyRetainedOwnerThickenedShading D C q)
        cell hcell selected).shadedUnion :=
  heavyRetainedOwner_commonCellRestriction_shadedUnion_eq
    D C q cell hcell selected

/-- The heavy cell-restricted datum inherits the canonical unit-slab
incidence.  Nonempty original retained mass makes the heavy source index
type nonempty through the proved factor-two retention. -/
noncomputable def heavyRetainedOwnerCellRestrictedCanonicalUnitSlabIncidence
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0) :
    CanonicalCertifiedPlankSlabIncidence
      {i // i ∈ heavyRetainedOwnerSourceIndices C q}
      {i // i ∈ heavyRetainedOwnerSourceIndices C q}
      (heavyRetainedOwnerCellRestrictedPlankDatum
        D C q cell hcell selected) 1 1 := by
  have hfin :=
    heavyRetainedOwnerSourceIndices_nonempty_of_retainedMass_ne_zero
      D C q hmass
  let hindex : Nonempty {i // i ∈ heavyRetainedOwnerSourceIndices C q} :=
    ⟨⟨hfin.choose, hfin.choose_spec⟩⟩
  exact canonicalUnitSlabIncidence
    (heavyRetainedOwnerCellRestrictedPlankDatum
      D C q cell hcell selected) hindex

#print axioms heavyRetainedOwner_commonCellRestriction_shadedUnion_eq
#print axioms heavyRetainedOwnerCellRestrictedPlankDatum
#print axioms heavyRetainedOwnerCellRestrictedPlankDatum_shadedUnion_eq_coarse
#print axioms heavyRetainedOwnerCellRestrictedCanonicalUnitSlabIncidence

end
end Family8PlankHeavyRetainedOwnerCellRestrictedCanonicalSlabV1
