import Family8Grounding.Family8PlankCanonicalUnitSlabIncidenceV5
import Family8Grounding.Family8PlankRetainedOwnerThickenedInducedShadingV2
import «CubeWeightUniformization»
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankRetainedOwnerCellRestrictedCanonicalSlabV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.CubeWeightUniformization
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6CanonicalCertifiedPlankSlabIncidenceCoreV3
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerThickenedInducedShadingV2
open Family8PlankCanonicalUnitSlabIncidenceV5

noncomputable section

universe u v

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# The literal cell-restricted retained datum and its canonical unit slab

The retained fine planks and their selected thickened owners have different
index types.  Their induced shaded unions are nevertheless exactly equal.
Restricting both shadings by the same selected cell region preserves that
equality.  The fine restriction is then packaged, without changing its
family, as the actual shaded plank datum consumed by the certified slab API.
-/

theorem retainedOwner_commonCellRestriction_shadedUnion_eq
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex) :
    (restrictToCells (retainedOwnerPlankFamily D C q).shading
        cell hcell selected).shadedUnion =
      (restrictToCells (retainedOwnerThickenedShading D C q)
        cell hcell selected).shadedUnion := by
  rw [restrictToCells_shadedUnion, restrictToCells_shadedUnion,
    retainedOwnerThickenedShading_shadedUnion_eq]

/-- Replace only the shading of the literal retained source plank datum by
its common-cell restriction.  All bodies, plank certificates, comparison
constant, and ambient data are inherited definitionally. -/
def retainedOwnerCellRestrictedPlankDatum
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex) :
    ShadedConvexPlankFamily {i // i ∈ retainedOwnerSourceIndices C q} a b :=
  { retainedOwnerPlankFamily D C q with
      shading := restrictToCells (retainedOwnerPlankFamily D C q).shading
        cell hcell selected }

@[simp] theorem retainedOwnerCellRestrictedPlankDatum_family
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex) :
    (retainedOwnerCellRestrictedPlankDatum D C q cell hcell selected).family =
      (retainedOwnerPlankFamily D C q).family := rfl

@[simp] theorem retainedOwnerCellRestrictedPlankDatum_shading
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex) :
    (retainedOwnerCellRestrictedPlankDatum D C q cell hcell selected).shading =
      restrictToCells (retainedOwnerPlankFamily D C q).shading
        cell hcell selected := rfl

@[simp] theorem retainedOwnerCellRestrictedPlankDatum_comparisonConstant
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex) :
    (retainedOwnerCellRestrictedPlankDatum D C q cell hcell selected).comparisonConstant =
      D.comparisonConstant := rfl

theorem retainedOwnerCellRestrictedPlankDatum_shadedUnion_eq_coarse
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex) :
    (retainedOwnerCellRestrictedPlankDatum D C q cell hcell selected).shading.shadedUnion =
      (restrictToCells (retainedOwnerThickenedShading D C q)
        cell hcell selected).shadedUnion :=
  retainedOwner_commonCellRestriction_shadedUnion_eq
    D C q cell hcell selected

/-- The exact cell-restricted fine datum carries the constructed certified
unit-slab incidence.  Positive retained mass supplies only the nonempty index
needed by the incidence structure; no multiplicity bound is assumed. -/
noncomputable def retainedOwnerCellRestrictedCanonicalUnitSlabIncidence
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0) :
    CanonicalCertifiedPlankSlabIncidence
      {i // i ∈ retainedOwnerSourceIndices C q}
      {i // i ∈ retainedOwnerSourceIndices C q}
      (retainedOwnerCellRestrictedPlankDatum D C q cell hcell selected) 1 1 := by
  have hfin := retainedOwnerSourceIndices_nonempty_of_mass_ne_zero
    D C q hmass
  let hindex : Nonempty {i // i ∈ retainedOwnerSourceIndices C q} :=
    ⟨⟨hfin.choose, hfin.choose_spec⟩⟩
  exact canonicalUnitSlabIncidence
    (retainedOwnerCellRestrictedPlankDatum D C q cell hcell selected) hindex

#print axioms retainedOwner_commonCellRestriction_shadedUnion_eq
#print axioms retainedOwnerCellRestrictedPlankDatum
#print axioms retainedOwnerCellRestrictedPlankDatum_shadedUnion_eq_coarse
#print axioms retainedOwnerCellRestrictedCanonicalUnitSlabIncidence

end
end Family8PlankRetainedOwnerCellRestrictedCanonicalSlabV1
