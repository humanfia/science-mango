import Family8Grounding.Family8SelectedParentGreedyBlockFiberIdentityV2
import Submission.Kakeya.ConvexFactoring.StatisticLevelRestriction

/-!
# Lift an actual greedy fibre level back to a fine Sticky shading, V2

Restrict the original fine shading by the common measurable set on which one
selected greedy fibre multiplicity equals `n`.  Parent aggregation commutes
with this restriction, so the selected parent block is exactly the subtype
form of the honest fibre-level shading.  The identity persists through the
actual V9 affine normalization and side-shape bucket.

No saturation premise, multiplicity estimate, or desired conclusion is
stored as an input.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentFineLevelLiftV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.StatisticLevelRestriction
open Submission.Kakeya.Uniformity
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentExactAssemblyInducedIdentityV2
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
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

def greedyBlockLevelSet (n : Nat) : Set Space :=
  {x | (greedyParentFactorization S G).fiberMultiplicity
    (parentAggregatedShading S Y) (some k) x = n}

theorem greedyBlockLevelSet_measurable (n : Nat) :
    MeasurableSet (greedyBlockLevelSet S Y G k n) := by
  exact measurableSet_fiberMultiplicity_eq
    (greedyParentFactorization S G) (parentAggregatedShading S Y)
      (some k) n

def fineShadingAtGreedyBlockLevel (n : Nat) : Shading fine.bodyFamily :=
  Y.restrictSet (greedyBlockLevelSet S Y G k n)
    (greedyBlockLevelSet_measurable S Y G k n)

theorem parentAggregatedShading_restrictSet_carrier
    (Omega : Set Space) (hOmega : MeasurableSet Omega)
    (p : ActiveParentIndex S) :
    (parentAggregatedShading S (Y.restrictSet Omega hOmega)).carrier p =
      (parentAggregatedShading S Y).carrier p ∩ Omega := by
  calc
    (parentAggregatedShading S (Y.restrictSet Omega hOmega)).carrier p =
        (activeInducedShading S (Y.restrictSet Omega hOmega)).carrier p :=
      (activeInducedShading_carrier_eq_parentAggregatedShading
        S (Y.restrictSet Omega hOmega) p).symm
    _ = ((Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover.toConvexFactorization S).inducedShading
          (Y.restrictSet Omega hOmega)).carrier p.1 := rfl
    _ = ((Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover.toConvexFactorization S).inducedShading
          Y).carrier p.1 ∩ Omega := by
      exact inducedShading_restrictSet_carrier
        (Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover.toConvexFactorization S)
          Y Omega hOmega p.1
    _ = (activeInducedShading S Y).carrier p ∩ Omega := rfl
    _ = (parentAggregatedShading S Y).carrier p ∩ Omega := by
      rw [activeInducedShading_carrier_eq_parentAggregatedShading S Y p]

theorem selectedParentFineLevel_carrier_eq_greedyBlockFineLevel
    (n : Nat)
    (p : {p // p ∈ (blockAt S.activeCoarseFamily G k).fiber}) :
    (selectedParentActualShading S
      (fineShadingAtGreedyBlockLevel S Y G k n)
      (blockAt S.activeCoarseFamily G k).fiber).carrier p =
        (greedyBlockFineLevelShading S Y G k n).carrier p := by
  rw [greedyBlockFineLevelShading_carrier]
  change (parentAggregatedShading S
      (fineShadingAtGreedyBlockLevel S Y G k n)).carrier p.1 = _
  rw [fineShadingAtGreedyBlockLevel,
    parentAggregatedShading_restrictSet_carrier]
  rw [fiberLevelShading_carrier]
  have hp : p.1 ∈
      (greedyParentFactorization S G).index.fiber (some k) := by
    rw [greedyParentFactorization_fiber_eq_block S G k]
    exact p.2
  rw [if_pos hp]
  rfl

theorem selectedParentFineLevel_shadingMass_eq (n : Nat) :
    (selectedParentActualShading S
      (fineShadingAtGreedyBlockLevel S Y G k n)
      (blockAt S.activeCoarseFamily G k).fiber).shadingMass =
        (greedyBlockFineLevelShading S Y G k n).shadingMass := by
  unfold Shading.shadingMass
  apply Finset.sum_congr rfl
  intro p _hp
  rw [selectedParentFineLevel_carrier_eq_greedyBlockFineLevel S Y G k n p]

theorem selectedParentFineLevel_shadedUnion_eq (n : Nat) :
    (selectedParentActualShading S
      (fineShadingAtGreedyBlockLevel S Y G k n)
      (blockAt S.activeCoarseFamily G k).fiber).shadedUnion =
        (greedyBlockFineLevelShading S Y G k n).shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨p, by
      rw [← selectedParentFineLevel_carrier_eq_greedyBlockFineLevel
        S Y G k n p]
      exact hp⟩
  · intro hx
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨p, by
      rw [selectedParentFineLevel_carrier_eq_greedyBlockFineLevel
        S Y G k n p]
      exact hp⟩

theorem selectedParentFineLevel_averageMultiplicity_eq (n : Nat) :
    (selectedParentActualShading S
      (fineShadingAtGreedyBlockLevel S Y G k n)
      (blockAt S.activeCoarseFamily G k).fiber).averageMultiplicity =
        (greedyBlockFineLevelShading S Y G k n).averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [selectedParentFineLevel_shadingMass_eq S Y G k n,
    selectedParentFineLevel_shadedUnion_eq S Y G k n]

theorem greedyBlockFineLevelShading_shadedUnion (n : Nat) :
    (greedyBlockFineLevelShading S Y G k n).shadedUnion =
      (fiberLevelShading (greedyParentFactorization S G)
        (parentAggregatedShading S Y) (some k) n).shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr
      ⟨p.1, by
        rw [← greedyBlockFineLevelShading_carrier S Y G k n p]
        exact hxp⟩
  · intro hx
    obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hx
    rw [fiberLevelShading_carrier] at hxp
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
          change x ∈ (fiberLevelShading (greedyParentFactorization S G)
            (parentAggregatedShading S Y) (some k) n).carrier pp.1
          rw [fiberLevelShading_carrier, if_pos hp]
          exact hxp⟩
    · rw [if_neg hp] at hxp
      exact hxp.elim

theorem greedyBlockFineLevelShading_averageMultiplicity (n : Nat) :
    (greedyBlockFineLevelShading S Y G k n).averageMultiplicity =
      (fiberLevelShading (greedyParentFactorization S G)
        (parentAggregatedShading S Y) (some k) n).averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [greedyBlockFineLevelShading_shadingMass S Y G k n,
    greedyBlockFineLevelShading_shadedUnion S Y G k n]

theorem exactAssembly_selectedParentFineLevel_averageMultiplicity_eq_source
    {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S G) (parentAggregatedShading S Y) loss) :
    (selectedParentActualShading S
      (fineShadingAtGreedyBlockLevel S Y G k A.fineLevel)
      (blockAt S.activeCoarseFamily G k).fiber).averageMultiplicity =
        (sourceFineLevelShading A (some k)).averageMultiplicity := by
  calc
    _ = (greedyBlockFineLevelShading S Y G k A.fineLevel).averageMultiplicity :=
      selectedParentFineLevel_averageMultiplicity_eq S Y G k A.fineLevel
    _ = (fiberLevelShading (greedyParentFactorization S G)
          (parentAggregatedShading S Y) (some k) A.fineLevel).averageMultiplicity :=
      greedyBlockFineLevelShading_averageMultiplicity S Y G k A.fineLevel
    _ = (sourceFineLevelShading A (some k)).averageMultiplicity := rfl

theorem exactAssembly_fineLevelPlankBucket_carrier
    {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S G) (parentAggregatedShading S Y) loss)
    (e : Space ≃ᵃ[Real] Space) (hrho : 0 < rho)
    (label : Fin 3 -> Int)
    (q : {p // p ∈ selectedParentPlankBucketIndices e S
      (blockAt S.activeCoarseFamily G k).fiber hrho label}) :
    (selectedParentPlankBucketShading e S
      (fineShadingAtGreedyBlockLevel S Y G k A.fineLevel)
      (blockAt S.activeCoarseFamily G k).fiber hrho label).carrier q =
        bucketNormalizedAffineEquiv e label ''
          (sourceFineLevelShading A (some k)).carrier q.1.1 := by
  change bucketNormalizedAffineEquiv e label ''
      (parentAggregatedShading S
        (fineShadingAtGreedyBlockLevel S Y G k A.fineLevel)).carrier q.1.1 = _
  apply congrArg (fun Omega : Set Space =>
    bucketNormalizedAffineEquiv e label '' Omega)
  calc
    _ = (greedyBlockFineLevelShading S Y G k A.fineLevel).carrier q.1 :=
      selectedParentFineLevel_carrier_eq_greedyBlockFineLevel
        S Y G k A.fineLevel q.1
    _ = (sourceFineLevelShading A (some k)).carrier q.1.1 := rfl

#print axioms greedyBlockLevelSet_measurable
#print axioms parentAggregatedShading_restrictSet_carrier
#print axioms selectedParentFineLevel_carrier_eq_greedyBlockFineLevel
#print axioms selectedParentFineLevel_shadingMass_eq
#print axioms selectedParentFineLevel_shadedUnion_eq
#print axioms selectedParentFineLevel_averageMultiplicity_eq
#print axioms greedyBlockFineLevelShading_shadedUnion
#print axioms greedyBlockFineLevelShading_averageMultiplicity
#print axioms
  exactAssembly_selectedParentFineLevel_averageMultiplicity_eq_source
#print axioms exactAssembly_fineLevelPlankBucket_carrier

end

end Family8SelectedParentFineLevelLiftV2
