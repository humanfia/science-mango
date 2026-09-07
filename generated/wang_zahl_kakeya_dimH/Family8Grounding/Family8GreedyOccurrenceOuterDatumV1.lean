import Family8Grounding.Family8SelectedParentGreedyBlockFiberIdentityV2
import Family6Grounding.Family6AffinePlankAnalyticHypothesesStableV1
import Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing

/-!
# The honest occurrence-level outer datum for Family 8

The greedy convex factorization uses
`Option (Fin (blocks F P).length)` as its ambient coarse index type.  The
`none` index is only an empty-factorization placeholder; every genuine greedy
occurrence is a `some k`.  This file removes that placeholder and reindexes the
actual induced coarse shading by `Fin (blocks F P).length`.

The resulting family and shading have exactly the same carriers, total shaded
mass, shaded union, and average multiplicity as the original induced shading.
Its count is therefore the literal number of greedy occurrences.  No plank
geometry or analytic outer-multiplicity estimate is asserted here.  The final
constructor records the additional uniform plank and ambient certificates
that are still required before this honest convex datum can be supplied to
the Family 6 plank API.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8GreedyOccurrenceOuterDatumV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-- The genuine outer family, indexed only by actual greedy occurrences.
There is no inactive `Option.none` member. -/
abbrev greedyOccurrenceOuterFamily
    (P : GreedyDensityPartition F candidates container active) :
    ConvexFamily (Fin (blocks F P).length) :=
  occurrenceFamily F P

/-- The induced outer shading restricted and reindexed to actual greedy
occurrences. -/
def greedyOccurrenceOuterShading
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) : Shading (greedyOccurrenceOuterFamily P) where
  carrier k := ((convexFactorization F P).inducedShading Y).carrier (some k)
  measurable_carrier k :=
    ((convexFactorization F P).inducedShading Y).measurable_carrier (some k)
  carrier_subset k := by
    simpa [greedyOccurrenceOuterFamily, occurrenceFamily,
      coarseFamily] using
      ((convexFactorization F P).inducedShading Y).carrier_subset (some k)

/-- The honest outer count: the cardinality of the actual occurrence index
type, not an unrelated endpoint parameter. -/
def greedyOccurrenceOuterCount
    (P : GreedyDensityPartition F candidates container active) : Nat :=
  Fintype.card (Fin (blocks F P).length)

/-- One occurrence datum member is literally the winning body at that greedy
step. -/
@[simp] theorem greedyOccurrenceOuterFamily_apply
    (P : GreedyDensityPartition F candidates container active)
    (k : Fin (blocks F P).length) :
    greedyOccurrenceOuterFamily P k = (blockAt F P k).body :=
  rfl

/-- The reindexed carrier is the carrier of the corresponding genuine
`some k` coarse occurrence. -/
@[simp] theorem greedyOccurrenceOuterShading_carrier
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (k : Fin (blocks F P).length) :
    (greedyOccurrenceOuterShading P Y).carrier k =
      ((convexFactorization F P).inducedShading Y).carrier (some k) :=
  rfl

/-- More explicitly, an outer occurrence carrier is the union of the shaded
fine members in that literal greedy block. -/
theorem greedyOccurrenceOuterShading_carrier_eq_blockUnion
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (k : Fin (blocks F P).length) :
    (greedyOccurrenceOuterShading P Y).carrier k =
      ⋃ i : {i // i ∈ (blockAt F P k).fiber}, Y.carrier i.1 := by
  ext x
  rw [greedyOccurrenceOuterShading_carrier,
    (convexFactorization F P).mem_inducedShading_carrier_iff]
  have hcoarse :
      some k ∈ (convexFactorization F P).index.coarse := by
    change some k ∈ occurrenceIndices F P
    simp [occurrenceIndices]
  rw [and_iff_right hcoarse]
  rw [show (convexFactorization F P).index.fiber (some k) =
      (blockAt F P k).fiber from
    indexFactorization_fiber_eq_blockAt F P k]
  simp

/-- The honest outer count is exactly the recursive greedy length. -/
@[simp] theorem greedyOccurrenceOuterCount_eq_length
    (P : GreedyDensityPartition F candidates container active) :
    greedyOccurrenceOuterCount P = P.length := by
  simp [greedyOccurrenceOuterCount, blocks_length F P]

/-- Equivalently, the honest count equals the cardinality of the active
coarse finset in the original factorization. -/
theorem greedyOccurrenceOuterCount_eq_coarse_card
    (P : GreedyDensityPartition F candidates container active) :
    greedyOccurrenceOuterCount P =
      (convexFactorization F P).index.coarse.card := by
  rw [greedyOccurrenceOuterCount_eq_length P]
  exact (coarse_card_eq_length F P).symm

/-- Removing the inactive `none` placeholder preserves total shaded mass. -/
theorem greedyOccurrenceOuterShading_shadingMass_eq_induced
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) :
    (greedyOccurrenceOuterShading P Y).shadingMass =
      ((convexFactorization F P).inducedShading Y).shadingMass := by
  unfold Shading.shadingMass
  rw [Fintype.sum_option]
  have hnone : none ∉ (convexFactorization F P).index.coarse := by
    change none ∉ occurrenceIndices F P
    simp [occurrenceIndices]
  have hnoneCarrier :
      ((convexFactorization F P).inducedShading Y).carrier none = ∅ := by
    simp [ConvexFactorization.inducedShading, hnone]
  rw [hnoneCarrier]
  simp [greedyOccurrenceOuterShading]

/-- Removing the inactive `none` placeholder preserves the genuine shaded
union. -/
theorem greedyOccurrenceOuterShading_shadedUnion_eq_induced
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) :
    (greedyOccurrenceOuterShading P Y).shadedUnion =
      ((convexFactorization F P).inducedShading Y).shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨some k, hxk⟩
  · intro hx
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hq, _i, _hi, _hxi⟩ :=
      ((convexFactorization F P).mem_inducedShading_carrier_iff Y q x).1 hxq
    rw [show (convexFactorization F P).index.coarse =
        occurrenceIndices F P from rfl] at hq
    simp only [occurrenceIndices, Finset.mem_image, Finset.mem_univ,
      true_and] at hq
    obtain ⟨k, rfl⟩ := hq
    exact Set.mem_iUnion.mpr ⟨k, hxq⟩

/-- Consequently the genuine average multiplicity is unchanged. -/
theorem greedyOccurrenceOuterShading_averageMultiplicity_eq_induced
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) :
    (greedyOccurrenceOuterShading P Y).averageMultiplicity =
      ((convexFactorization F P).inducedShading Y).averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [greedyOccurrenceOuterShading_shadingMass_eq_induced P Y,
    greedyOccurrenceOuterShading_shadedUnion_eq_induced P Y]

/-- Exact packaging into the stable Family 6 plank datum, conditional on the
geometric information absent from a greedy `ConvexBody` factorization: one
common `a x b x 1` comparison, a unit-scale ambient body, and containment in
that ambient. -/
def greedyOccurrenceOuterPlankDatum
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (a b comparisonConstant : NNReal)
    (all_isPlank : forall k,
      IsPlank comparisonConstant a b (greedyOccurrenceOuterFamily P k))
    (ambient : ConvexBody Space) (ambientComparisonConstant : NNReal)
    (ambient_is_unit_scale :
      IsPlank ambientComparisonConstant 1 1 ambient)
    (contained_in_ambient : forall k,
      (greedyOccurrenceOuterFamily P k : Set Space) ⊆
        (ambient : Set Space)) :
    ShadedConvexPlankFamily (Fin (blocks F P).length) a b where
  family := greedyOccurrenceOuterFamily P
  shading := greedyOccurrenceOuterShading P Y
  comparisonConstant := comparisonConstant
  all_isPlank := all_isPlank
  ambient := ambient
  ambientComparisonConstant := ambientComparisonConstant
  ambient_is_unit_scale := ambient_is_unit_scale
  contained_in_ambient := contained_in_ambient

/-! ## The literal selected-parent specialization used by Family 8 -/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

variable (S : StickyScaleCover fine rho)
  (P : GreedyDensityPartition S.activeCoarseFamily
    (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
    (hullContainer S.activeCoarseFamily) Finset.univ)

/-- The literal Family 8 outer datum, still parameterized by the refined
active-parent shading to which the exact assembly is applied. -/
abbrev selectedParentGreedyOccurrenceOuterFamily :
    ConvexFamily (Fin (blocks S.activeCoarseFamily P).length) :=
  greedyOccurrenceOuterFamily P

def selectedParentGreedyOccurrenceOuterShading
    (Z : Shading S.activeCoarseFamily) :
    Shading (selectedParentGreedyOccurrenceOuterFamily S P) :=
  greedyOccurrenceOuterShading P Z

/-- The `plankCount` candidate supplied by the real Family 8 occurrence
object.  This theorem says only that it counts occurrences; it does not claim
those bodies already carry uniform plank certificates. -/
def selectedParentEq45OuterCount : Nat :=
  greedyOccurrenceOuterCount P

@[simp] theorem selectedParentEq45OuterCount_eq_length :
    selectedParentEq45OuterCount S P = P.length :=
  greedyOccurrenceOuterCount_eq_length P

theorem selectedParentGreedyOccurrenceOuterShading_shadingMass_eq_induced
    (Z : Shading S.activeCoarseFamily) :
    (selectedParentGreedyOccurrenceOuterShading S P Z).shadingMass =
      ((greedyParentFactorization S P).inducedShading Z).shadingMass :=
  greedyOccurrenceOuterShading_shadingMass_eq_induced P Z

theorem selectedParentGreedyOccurrenceOuterShading_shadedUnion_eq_induced
    (Z : Shading S.activeCoarseFamily) :
    (selectedParentGreedyOccurrenceOuterShading S P Z).shadedUnion =
      ((greedyParentFactorization S P).inducedShading Z).shadedUnion :=
  greedyOccurrenceOuterShading_shadedUnion_eq_induced P Z

theorem selectedParentGreedyOccurrenceOuterShading_averageMultiplicity_eq_induced
    (Z : Shading S.activeCoarseFamily) :
    (selectedParentGreedyOccurrenceOuterShading S P Z).averageMultiplicity =
      ((greedyParentFactorization S P).inducedShading Z).averageMultiplicity :=
  greedyOccurrenceOuterShading_averageMultiplicity_eq_induced P Z

#print axioms greedyOccurrenceOuterShading_carrier_eq_blockUnion
#print axioms greedyOccurrenceOuterCount_eq_length
#print axioms greedyOccurrenceOuterCount_eq_coarse_card
#print axioms greedyOccurrenceOuterShading_shadingMass_eq_induced
#print axioms greedyOccurrenceOuterShading_shadedUnion_eq_induced
#print axioms greedyOccurrenceOuterShading_averageMultiplicity_eq_induced
#print axioms selectedParentEq45OuterCount_eq_length
#print axioms selectedParentGreedyOccurrenceOuterShading_shadingMass_eq_induced
#print axioms selectedParentGreedyOccurrenceOuterShading_shadedUnion_eq_induced
#print axioms selectedParentGreedyOccurrenceOuterShading_averageMultiplicity_eq_induced

end

end Family8GreedyOccurrenceOuterDatumV1
