import Family8Grounding.Family8ExactAssemblyActualAverageBridgeV1
import Family8Grounding.Family8SelectedOccurrenceDensityFrostmanV1
import Mathlib.Tactic

/-!
# Selected-occurrence source-fine block average bridge

The product theorem for a generic exact assembly returns an ambient-index
`sourceFineLevelShading`.  For a retained selected occurrence `q`, that shading
is supported on the literal greedy block at `q`.  This file merely reindexes
that same source-fine shading by the block subtype and records the three exact
equalities needed by the Eq. (46) consumer.

No equality of shadings with different index types is asserted, and the
source-fine shading is not replaced by the generally smaller final fibre.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceSourceFineLevelBlockAverageBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8SelectedOccurrenceDensityFrostmanV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-- The source fine-level factor returned by the exact-assembly product,
reindexed by the literal greedy block at the same selected occurrence. -/
def selectedOccurrenceSourceFineBlockShading
    (P : GreedyDensityPartition F candidates container active)
    (R : Finset (Fin (blocks F P).length)) {Y : Shading F} {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (selectedOccurrenceFactorization P R) Y loss)
    (q : Fin (blocks F P).length) :
    Shading (selectedCoarseFamily F (blockAt F P q).fiber) :=
  selectedCoarseShading (sourceFineLevelShading A (some q))
    (blockAt F P q).fiber

/-- Reindexing the retained source fine-level fibre by its literal block
subtype preserves its multiplicity-counted mass exactly. -/
theorem selectedOccurrenceSourceFineBlockShading_shadingMass_eq
    (P : GreedyDensityPartition F candidates container active)
    (R : Finset (Fin (blocks F P).length)) {Y : Shading F} {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (selectedOccurrenceFactorization P R) Y loss)
    (q : Fin (blocks F P).length) (hq : q ∈ R) :
    (selectedOccurrenceSourceFineBlockShading P R A q).shadingMass =
      (sourceFineLevelShading A (some q)).shadingMass := by
  classical
  rw [selectedOccurrenceSourceFineBlockShading, selectedCoarseShading_mass,
    sourceFineLevelShading, fiberLevelShading_mass_eq_sum_fiber,
    selectedOccurrenceFactorization_fiber P R q hq]

/-- Reindexing the retained source fine-level fibre by its literal block
subtype preserves its genuine shaded union exactly. -/
theorem selectedOccurrenceSourceFineBlockShading_shadedUnion_eq
    (P : GreedyDensityPartition F candidates container active)
    (R : Finset (Fin (blocks F P).length)) {Y : Shading F} {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (selectedOccurrenceFactorization P R) Y loss)
    (q : Fin (blocks F P).length) (hq : q ∈ R) :
    (selectedOccurrenceSourceFineBlockShading P R A q).shadedUnion =
      (sourceFineLevelShading A (some q)).shadedUnion := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨p.1, by
      change x ∈ (sourceFineLevelShading A (some q)).carrier p.1 at hxp
      exact hxp⟩
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    by_cases hi : i ∈
        (selectedOccurrenceFactorization P R).index.fiber (some q)
    · have hiBlock : i ∈ (blockAt F P q).fiber := by
        rw [← selectedOccurrenceFactorization_fiber P R q hq]
        exact hi
      let p : {i // i ∈ (blockAt F P q).fiber} := ⟨i, hiBlock⟩
      exact Set.mem_iUnion.mpr ⟨p, by
        change x ∈ (sourceFineLevelShading A (some q)).carrier p.1
        simpa only [p] using hxi⟩
    · have hempty :
          (sourceFineLevelShading A (some q)).carrier i = ∅ := by
        simpa only [sourceFineLevelShading] using
          (fiberLevelShading_carrier_eq_empty_of_not_mem
            (selectedOccurrenceFactorization P R) Y (some q)
            A.fineLevel i hi)
      rw [hempty] at hxi
      exact hxi.elim

/-- Consequently the actual average multiplicity of the same source-fine
factor is unchanged by the literal block-subtype reindexing. -/
theorem selectedOccurrenceSourceFineBlockShading_averageMultiplicity_eq
    (P : GreedyDensityPartition F candidates container active)
    (R : Finset (Fin (blocks F P).length)) {Y : Shading F} {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (selectedOccurrenceFactorization P R) Y loss)
    (q : Fin (blocks F P).length) (hq : q ∈ R) :
    (selectedOccurrenceSourceFineBlockShading P R A q).averageMultiplicity =
      (sourceFineLevelShading A (some q)).averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [selectedOccurrenceSourceFineBlockShading_shadingMass_eq P R A q hq,
    selectedOccurrenceSourceFineBlockShading_shadedUnion_eq P R A q hq]

#print axioms selectedOccurrenceSourceFineBlockShading_shadingMass_eq
#print axioms selectedOccurrenceSourceFineBlockShading_shadedUnion_eq
#print axioms selectedOccurrenceSourceFineBlockShading_averageMultiplicity_eq

end

end Family8SelectedOccurrenceSourceFineLevelBlockAverageBridgeV1
