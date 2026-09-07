import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import Family8Grounding.Family8SelectedOccurrenceDensityFrostmanV1
import Mathlib.Tactic

/-!
# Selected-occurrence frozen final-fibre block average bridge

The polylogarithmic frozen-comparable producer already returns an actual
`finalFiberShading` in its product.  For a retained selected occurrence `q`,
this file only reindexes that same final fibre by the literal greedy block at
`q` and exposes the exact average identity needed downstream.

It does not identify the final fibre with the whole source block shading and
does not assert equality between shadings with different index types.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceFrozenFinalFiberBlockAverageBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8SelectedOccurrenceDensityFrostmanV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-- The actual frozen final fibre, reindexed by the literal greedy block at
the same selected occurrence. -/
def selectedOccurrenceFrozenFinalFiberBlockShading
    (P : GreedyDensityPartition F candidates container active)
    (R : Finset (Fin (blocks F P).length)) {Y : Shading F} {r : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (selectedOccurrenceFactorization P R) Y r)
    (q : Fin (blocks F P).length) :
    Shading (selectedCoarseFamily F (blockAt F P q).fiber) :=
  selectedCoarseShading
    (Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading
      A (some q))
    (blockAt F P q).fiber

private theorem selectedOccurrenceFrozenFinalFiberBlockShading_shadingMass_eq
    (P : GreedyDensityPartition F candidates container active)
    (R : Finset (Fin (blocks F P).length)) {Y : Shading F} {r : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (selectedOccurrenceFactorization P R) Y r)
    (q : Fin (blocks F P).length) (hq : q ∈ R) :
    (selectedOccurrenceFrozenFinalFiberBlockShading P R A q).shadingMass =
      (Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading
        A (some q)).shadingMass := by
  classical
  rw [selectedOccurrenceFrozenFinalFiberBlockShading,
    selectedCoarseShading_mass]
  rw [Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading,
    fiberShading_mass_eq_sum_fiber,
    selectedOccurrenceFactorization_fiber P R q hq]
  apply Finset.sum_congr rfl
  intro i hi
  rw [fiberShading_carrier, if_pos]
  rw [selectedOccurrenceFactorization_fiber P R q hq]
  exact hi

private theorem selectedOccurrenceFrozenFinalFiberBlockShading_shadedUnion_eq
    (P : GreedyDensityPartition F candidates container active)
    (R : Finset (Fin (blocks F P).length)) {Y : Shading F} {r : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (selectedOccurrenceFactorization P R) Y r)
    (q : Fin (blocks F P).length) (hq : q ∈ R) :
    (selectedOccurrenceFrozenFinalFiberBlockShading P R A q).shadedUnion =
      (Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading
        A (some q)).shadedUnion := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨p.1, by
      change x ∈
        (Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading
          A (some q)).carrier p.1 at hxp
      exact hxp⟩
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    rw [Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading,
      fiberShading_carrier] at hxi
    by_cases hi : i ∈
        (selectedOccurrenceFactorization P R).index.fiber (some q)
    · rw [if_pos hi] at hxi
      have hiBlock : i ∈ (blockAt F P q).fiber := by
        rw [← selectedOccurrenceFactorization_fiber P R q hq]
        exact hi
      let p : {i // i ∈ (blockAt F P q).fiber} := ⟨i, hiBlock⟩
      exact Set.mem_iUnion.mpr ⟨p, by
        change x ∈
          (Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading
            A (some q)).carrier p.1
        rw [Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading,
          fiberShading_carrier, if_pos hi]
        exact hxi⟩
    · rw [if_neg hi] at hxi
      exact hxi.elim

/-- Reindexing the actual frozen final fibre by the literal block subtype
preserves its actual average multiplicity exactly. -/
theorem selectedOccurrenceFrozenFinalFiberBlockShading_averageMultiplicity_eq
    (P : GreedyDensityPartition F candidates container active)
    (R : Finset (Fin (blocks F P).length)) {Y : Shading F} {r : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (selectedOccurrenceFactorization P R) Y r)
    (q : Fin (blocks F P).length) (hq : q ∈ R) :
    (selectedOccurrenceFrozenFinalFiberBlockShading P R A q).averageMultiplicity =
      (Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading
        A (some q)).averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [selectedOccurrenceFrozenFinalFiberBlockShading_shadingMass_eq P R A q hq,
    selectedOccurrenceFrozenFinalFiberBlockShading_shadedUnion_eq P R A q hq]

#print axioms
  selectedOccurrenceFrozenFinalFiberBlockShading_averageMultiplicity_eq

end

end Family8SelectedOccurrenceFrozenFinalFiberBlockAverageBridgeV1
