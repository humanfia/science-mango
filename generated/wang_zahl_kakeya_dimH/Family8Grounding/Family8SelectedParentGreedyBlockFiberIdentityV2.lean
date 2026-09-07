import Family8Grounding.Family8SelectedParentExactAssemblyInducedIdentityV2
import Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
import Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly

/-!
# A selected greedy parent block is an actual factorization fibre, V2

For the occurrence-indexed factorization extracted from the same greedy
partition used by V9, the selected parent block is literally the fibre over
that occurrence.  This module records the carrier, mass, union, and average
multiplicity identities between the subtype block shading and the ambient
`fiberShading`.

It also records the exact fine-level subtype object corresponding to an
`ExactAssembly.sourceFineLevelShading`.  The unrestricted block is not
identified with that level object: doing so requires the additional, genuine
statement that the whole block is saturated at the assembly's selected fine
level.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentGreedyBlockFiberIdentityV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.Uniformity
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8SelectedParentAffineShadingTransportV4
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

variable (S : StickyScaleCover fine rho)
  (Y : Shading fine.bodyFamily)
  (G : GreedyDensityPartition S.activeCoarseFamily
    (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
    (hullContainer S.activeCoarseFamily) Finset.univ)
  (k : Fin (blocks S.activeCoarseFamily G).length)

/-- The occurrence-indexed factorization extracted from the literal V9
greedy partition. -/
abbrev greedyParentFactorization :
    ConvexFactorization S.activeCoarseFamily
      (coarseFamily S.activeCoarseFamily G) :=
  convexFactorization S.activeCoarseFamily G

/-- Freeze the exact combinatorial identity once, so downstream data proofs
do not depend on definitional unfolding of `convexFactorization.index`. -/
theorem greedyParentFactorization_fiber_eq_block :
    (greedyParentFactorization S G).index.fiber (some k) =
      (blockAt S.activeCoarseFamily G k).fiber := by
  change (indexFactorization S.activeCoarseFamily G).fiber (some k) = _
  exact indexFactorization_fiber_eq_blockAt S.activeCoarseFamily G k

/-- The V9 block, regarded as a subtype shading of active parents. -/
abbrev greedyBlockShading :
    Shading (selectedCoarseFamily S.activeCoarseFamily
      (blockAt S.activeCoarseFamily G k).fiber) :=
  selectedParentActualShading S Y
    (blockAt S.activeCoarseFamily G k).fiber

/-- The same block as an ambient-index fibre shading. -/
def greedyBlockFiberShading : Shading S.activeCoarseFamily :=
  fiberShading (greedyParentFactorization S G)
    (parentAggregatedShading S Y) (some k)

/-- Every subtype block carrier is exactly its ambient fibre carrier. -/
theorem greedyBlockShading_carrier_eq_fiberShading
    (p : {p // p ∈ (blockAt S.activeCoarseFamily G k).fiber}) :
    (greedyBlockShading S Y G k).carrier p =
      (greedyBlockFiberShading S Y G k).carrier p.1 := by
  rw [greedyBlockFiberShading, fiberShading_carrier]
  have hp : p.1 ∈
      (greedyParentFactorization S G).index.fiber (some k) := by
    rw [greedyParentFactorization_fiber_eq_block S G k]
    exact p.2
  rw [if_pos hp]
  rfl

/-- Reindexing the selected block changes neither its multiplicity-counted
shading mass nor the actual source carrier pieces. -/
theorem greedyBlockShading_shadingMass_eq_fiberShading :
    (greedyBlockShading S Y G k).shadingMass =
      (greedyBlockFiberShading S Y G k).shadingMass := by
  rw [greedyBlockFiberShading, fiberShading_mass_eq_sum_fiber]
  change (selectedCoarseShading (parentAggregatedShading S Y)
      (blockAt S.activeCoarseFamily G k).fiber).shadingMass = _
  rw [selectedCoarseShading_mass,
    greedyParentFactorization_fiber_eq_block S G k]

/-- Reindexing the selected block also preserves its genuine shaded union. -/
theorem greedyBlockShading_shadedUnion_eq_fiberShading :
    (greedyBlockShading S Y G k).shadedUnion =
      (greedyBlockFiberShading S Y G k).shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr
      ⟨p.1, by
        rw [← greedyBlockShading_carrier_eq_fiberShading S Y G k p]
        exact hxp⟩
  · intro hx
    obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hx
    rw [greedyBlockFiberShading, fiberShading_carrier] at hxp
    by_cases hp : p ∈
        (greedyParentFactorization S G).index.fiber (some k)
    · rw [if_pos hp] at hxp
      have hpBlock : p ∈ (blockAt S.activeCoarseFamily G k).fiber := by
        rw [← greedyParentFactorization_fiber_eq_block S G k]
        exact hp
      let pp : {p // p ∈ (blockAt S.activeCoarseFamily G k).fiber} :=
        ⟨p, hpBlock⟩
      exact Set.mem_iUnion.mpr
        ⟨pp, by
          change x ∈ (parentAggregatedShading S Y).carrier pp.1
          exact hxp⟩
    · rw [if_neg hp] at hxp
      exact hxp.elim

/-- Consequently the genuine average multiplicity is unchanged by the block
subtype reindexing. -/
theorem greedyBlockShading_averageMultiplicity_eq_fiberShading :
    (greedyBlockShading S Y G k).averageMultiplicity =
      (greedyBlockFiberShading S Y G k).averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [greedyBlockShading_shadingMass_eq_fiberShading S Y G k,
    greedyBlockShading_shadedUnion_eq_fiberShading S Y G k]

/-- The exact subtype representative of one source fine-multiplicity level
inside the literal greedy block. -/
def greedyBlockFineLevelShading (n : Nat) :
    Shading (selectedCoarseFamily S.activeCoarseFamily
      (blockAt S.activeCoarseFamily G k).fiber) :=
  selectedCoarseShading
    (fiberLevelShading (greedyParentFactorization S G)
      (parentAggregatedShading S Y) (some k) n)
    (blockAt S.activeCoarseFamily G k).fiber

/-- The subtype fine-level carrier is exactly the ambient fibre-level carrier
at its underlying parent index. -/
theorem greedyBlockFineLevelShading_carrier
    (n : Nat)
    (p : {p // p ∈ (blockAt S.activeCoarseFamily G k).fiber}) :
    (greedyBlockFineLevelShading S Y G k n).carrier p =
      (fiberLevelShading (greedyParentFactorization S G)
        (parentAggregatedShading S Y) (some k) n).carrier p.1 := rfl

/-- Its mass is exactly the mass of the ambient source fine-level shading;
all carriers outside the actual occurrence fibre are empty. -/
theorem greedyBlockFineLevelShading_shadingMass (n : Nat) :
    (greedyBlockFineLevelShading S Y G k n).shadingMass =
      (fiberLevelShading (greedyParentFactorization S G)
        (parentAggregatedShading S Y) (some k) n).shadingMass := by
  rw [greedyBlockFineLevelShading, selectedCoarseShading_mass,
    fiberLevelShading_mass_eq_sum_fiber,
    greedyParentFactorization_fiber_eq_block S G k]

/-- For an ExactAssembly on this same occurrence factorization, the selected
block fine-level subtype has exactly the mass of the honest
`sourceFineLevelShading`; this is the strongest unconditional inner-object
identity. -/
theorem exactAssembly_greedyBlockFineLevelShading_shadingMass
    {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S G) (parentAggregatedShading S Y) loss) :
    (greedyBlockFineLevelShading S Y G k A.fineLevel).shadingMass =
      (sourceFineLevelShading A (some k)).shadingMass := by
  exact greedyBlockFineLevelShading_shadingMass S Y G k A.fineLevel

#print axioms greedyParentFactorization_fiber_eq_block
#print axioms greedyBlockShading_carrier_eq_fiberShading
#print axioms greedyBlockShading_shadingMass_eq_fiberShading
#print axioms greedyBlockShading_shadedUnion_eq_fiberShading
#print axioms greedyBlockShading_averageMultiplicity_eq_fiberShading
#print axioms greedyBlockFineLevelShading_carrier
#print axioms greedyBlockFineLevelShading_shadingMass
#print axioms exactAssembly_greedyBlockFineLevelShading_shadingMass

end

end Family8SelectedParentGreedyBlockFiberIdentityV2
