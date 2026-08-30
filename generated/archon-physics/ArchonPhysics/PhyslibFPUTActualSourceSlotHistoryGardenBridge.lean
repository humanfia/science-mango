import ArchonPhysics.PhyslibFPUTActualDuhamelSourceHistoryExpansion

/-!
# Actual finite source-slot histories in the four garden sectors

The exact pointwise Duhamel source histories are transported through source
insertion and the finite weighted factorization defect.  This constructs
genuine `ClusterUnitSlotHistoryExpansion` objects for every actual unit
quadratic and quartic left/right slot, with explicit sector norm budgets.

The classification is conservative: the extracted Picard terms stay in the
bad-small-denominator sector until a separate gap theorem splits them, the
defect square is recorded as repeated history, and literal nonlinear
remainders stay in the truncation sector.  Thus the regular-good budget is
zero here rather than being asserted without proof.
-/

namespace ArchonPhysics.PhyslibFPUTActualSourceSlotHistoryGardenBridge

open scoped BigOperators
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualGardenHistoryDecomposition
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.PhyslibFPUTActualDuhamelSourceHistoryExpansion
open ArchonPhysics.PhyslibFPUTActualSourceSlotPotentialSplit
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy
open ArchonPhysics.PhyslibFPUTSourceInsertionClusterExpansion

noncomputable section

variable {I Omega : Type*}
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype Omega] [DecidableEq Omega]

/-- Source insertion distributes over an arbitrary fixed finite history
sum. -/
theorem sourceInsertedBlockObservable_sum_source
    {History : Type*} [DecidableEq History]
    (histories : Finset History)
    (path : Omega -> I -> Real -> Complex)
    (source : History -> Omega -> I -> Real -> Complex)
    (block : Finset I) (slot : I) (time : Real) :
    sourceInsertedBlockObservable path
        (fun omega i s => ∑ history ∈ histories, source history omega i s)
        block slot time =
      fun omega => ∑ history ∈ histories,
        sourceInsertedBlockObservable path (source history)
          block slot time omega := by
  funext omega
  simp [sourceInsertedBlockObservable, Finset.mul_sum]

/-- A finite weighted factorization defect is linear in a finite sum in its
left observable. -/
theorem finiteWeightedObservableFactorizationDefect_sum_left
    {History : Type*} [DecidableEq History]
    (histories : Finset History) (weight : Omega -> Real)
    (left : History -> Omega -> Complex) (right : Omega -> Complex) :
    finiteWeightedObservableFactorizationDefect weight
        (fun omega => ∑ history ∈ histories, left history omega) right =
      ∑ history ∈ histories,
        finiteWeightedObservableFactorizationDefect weight
          (left history) right := by
  induction histories using Finset.induction_on with
  | empty =>
      simp [finiteWeightedObservableFactorizationDefect,
        finiteWeightedObservableMoment]
  | @insert history histories hnot ih =>
      simp only [Finset.sum_insert hnot]
      rw [finiteWeightedObservableFactorizationDefect_add_left, ih]

/-- The corresponding finite-sum linearity in the right observable. -/
theorem finiteWeightedObservableFactorizationDefect_sum_right
    {History : Type*} [DecidableEq History]
    (histories : Finset History) (weight : Omega -> Real)
    (left : Omega -> Complex) (right : History -> Omega -> Complex) :
    finiteWeightedObservableFactorizationDefect weight left
        (fun omega => ∑ history ∈ histories, right history omega) =
      ∑ history ∈ histories,
        finiteWeightedObservableFactorizationDefect weight
          left (right history) := by
  induction histories using Finset.induction_on with
  | empty =>
      simp [finiteWeightedObservableFactorizationDefect,
        finiteWeightedObservableMoment]
  | @insert history histories hnot ih =>
      simp only [Finset.sum_insert hnot]
      rw [finiteWeightedObservableFactorizationDefect_add_right, ih]

def finiteLeftSourceHistorySlotContribution
    {History : Type*}
    (weight : Omega -> Real)
    (path : Omega -> I -> Real -> Complex)
    (source : History -> Omega -> I -> Real -> Complex)
    (left right : Finset I) (slot : I) (time : Real)
    (history : History) : Complex :=
  finiteWeightedObservableFactorizationDefect weight
    (sourceInsertedBlockObservable path (source history) left slot time)
    (pathBlockObservable path right time)

def finiteRightSourceHistorySlotContribution
    {History : Type*}
    (weight : Omega -> Real)
    (path : Omega -> I -> Real -> Complex)
    (source : History -> Omega -> I -> Real -> Complex)
    (left right : Finset I) (slot : I) (time : Real)
    (history : History) : Complex :=
  finiteWeightedObservableFactorizationDefect weight
    (pathBlockObservable path left time)
    (sourceInsertedBlockObservable path (source history) right slot time)

/-- Exact four-history expansion of each actual left unit-quadratic slot. -/
theorem actualLeftQuadraticUnitSourceSlotFactorizationDefect_eq_historySum
    {N : Nat} [NeZero N]
    (weight : Omega -> Real) (mass : Omega -> Lattice.PositiveMassConfig N)
    (entry : I -> PhaseSign × Lattice.Site N)
    (p q : Omega -> Time -> HilbertConfiguration N)
    (radius : Omega -> Lattice.Site N -> Real)
    (phase : Omega -> UnitAddTorus (Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    actualLeftQuadraticSourceSlotFactorizationDefect
        weight mass 1 1 entry p q left right slot time =
      ∑ history ∈ actualQuadraticSourceHistories,
        finiteLeftSourceHistorySlotContribution weight
          (actualFiniteCubicEnsemblePath mass entry p q)
          (actualFiniteQuadraticHistorySource mass entry q radius phase)
          left right slot time history := by
  unfold actualLeftQuadraticSourceSlotFactorizationDefect
    finiteLeftSourceHistorySlotContribution
  rw [actualFiniteQuadraticUnitSource_eq_historySum]
  rw [sourceInsertedBlockObservable_sum_source]
  exact finiteWeightedObservableFactorizationDefect_sum_left
    actualQuadraticSourceHistories weight _ _

/-- Exact four-history expansion of each actual right unit-quadratic slot. -/
theorem actualRightQuadraticUnitSourceSlotFactorizationDefect_eq_historySum
    {N : Nat} [NeZero N]
    (weight : Omega -> Real) (mass : Omega -> Lattice.PositiveMassConfig N)
    (entry : I -> PhaseSign × Lattice.Site N)
    (p q : Omega -> Time -> HilbertConfiguration N)
    (radius : Omega -> Lattice.Site N -> Real)
    (phase : Omega -> UnitAddTorus (Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    actualRightQuadraticSourceSlotFactorizationDefect
        weight mass 1 1 entry p q left right slot time =
      ∑ history ∈ actualQuadraticSourceHistories,
        finiteRightSourceHistorySlotContribution weight
          (actualFiniteCubicEnsemblePath mass entry p q)
          (actualFiniteQuadraticHistorySource mass entry q radius phase)
          left right slot time history := by
  unfold actualRightQuadraticSourceSlotFactorizationDefect
    finiteRightSourceHistorySlotContribution
  rw [actualFiniteQuadraticUnitSource_eq_historySum]
  rw [sourceInsertedBlockObservable_sum_source]
  exact finiteWeightedObservableFactorizationDefect_sum_right
    actualQuadraticSourceHistories weight _ _

/-- Exact two-history expansion of each actual left unit-quartic slot. -/
theorem actualLeftQuarticUnitSourceSlotFactorizationDefect_eq_historySum
    {N : Nat} [NeZero N]
    (weight : Omega -> Real) (mass : Omega -> Lattice.PositiveMassConfig N)
    (entry : I -> PhaseSign × Lattice.Site N)
    (p q : Omega -> Time -> HilbertConfiguration N)
    (radius : Omega -> Lattice.Site N -> Real)
    (phase : Omega -> UnitAddTorus (Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    actualLeftQuarticSourceSlotFactorizationDefect
        weight mass 1 1 entry p q left right slot time =
      ∑ history ∈ actualQuarticSourceHistories,
        finiteLeftSourceHistorySlotContribution weight
          (actualFiniteCubicEnsemblePath mass entry p q)
          (actualFiniteQuarticHistorySource mass entry q radius phase)
          left right slot time history := by
  unfold actualLeftQuarticSourceSlotFactorizationDefect
    finiteLeftSourceHistorySlotContribution
  rw [actualFiniteQuarticUnitSource_eq_historySum]
  rw [sourceInsertedBlockObservable_sum_source]
  exact finiteWeightedObservableFactorizationDefect_sum_left
    actualQuarticSourceHistories weight _ _

/-- Exact two-history expansion of each actual right unit-quartic slot. -/
theorem actualRightQuarticUnitSourceSlotFactorizationDefect_eq_historySum
    {N : Nat} [NeZero N]
    (weight : Omega -> Real) (mass : Omega -> Lattice.PositiveMassConfig N)
    (entry : I -> PhaseSign × Lattice.Site N)
    (p q : Omega -> Time -> HilbertConfiguration N)
    (radius : Omega -> Lattice.Site N -> Real)
    (phase : Omega -> UnitAddTorus (Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    actualRightQuarticSourceSlotFactorizationDefect
        weight mass 1 1 entry p q left right slot time =
      ∑ history ∈ actualQuarticSourceHistories,
        finiteRightSourceHistorySlotContribution weight
          (actualFiniteCubicEnsemblePath mass entry p q)
          (actualFiniteQuarticHistorySource mass entry q radius phase)
          left right slot time history := by
  unfold actualRightQuarticSourceSlotFactorizationDefect
    finiteRightSourceHistorySlotContribution
  rw [actualFiniteQuarticUnitSource_eq_historySum]
  rw [sourceInsertedBlockObservable_sum_source]
  exact finiteWeightedObservableFactorizationDefect_sum_right
    actualQuarticSourceHistories weight _ _

/-- Model-specific finite history data reconstructing every actual
unit-quadratic slot. -/
def actualFiniteQuadraticUnitSlotHistoryExpansion
    {N : Nat} [NeZero N]
    (weight : Omega -> Real) (mass : Omega -> Lattice.PositiveMassConfig N)
    (entry : I -> PhaseSign × Lattice.Site N)
    (p q : Omega -> Time -> HilbertConfiguration N)
    (radius : Omega -> Lattice.Site N -> Real)
    (phase : Omega -> UnitAddTorus (Lattice.Site N))
    (left right : Finset I) (time : Real) :
    ClusterUnitSlotHistoryExpansion ActualQuadraticSourceHistory I left right
      (fun slot => actualLeftQuadraticSourceSlotFactorizationDefect
        weight mass 1 1 entry p q left right slot time)
      (fun slot => actualRightQuadraticSourceSlotFactorizationDefect
        weight mass 1 1 entry p q left right slot time) where
  leftHistories := fun _ => actualQuadraticSourceHistories
  rightHistories := fun _ => actualQuadraticSourceHistories
  leftSector := fun _ => actualQuadraticHistorySector
  rightSector := fun _ => actualQuadraticHistorySector
  leftContribution := fun slot history =>
    finiteLeftSourceHistorySlotContribution weight
      (actualFiniteCubicEnsemblePath mass entry p q)
      (actualFiniteQuadraticHistorySource mass entry q radius phase)
      left right slot time history
  rightContribution := fun slot history =>
    finiteRightSourceHistorySlotContribution weight
      (actualFiniteCubicEnsemblePath mass entry p q)
      (actualFiniteQuadraticHistorySource mass entry q radius phase)
      left right slot time history
  left_reconstruct := by
    intro slot _hslot
    exact actualLeftQuadraticUnitSourceSlotFactorizationDefect_eq_historySum
      weight mass entry p q radius phase left right slot time
  right_reconstruct := by
    intro slot _hslot
    exact actualRightQuadraticUnitSourceSlotFactorizationDefect_eq_historySum
      weight mass entry p q radius phase left right slot time

/-- Model-specific finite history data reconstructing every actual
unit-quartic slot. -/
def actualFiniteQuarticUnitSlotHistoryExpansion
    {N : Nat} [NeZero N]
    (weight : Omega -> Real) (mass : Omega -> Lattice.PositiveMassConfig N)
    (entry : I -> PhaseSign × Lattice.Site N)
    (p q : Omega -> Time -> HilbertConfiguration N)
    (radius : Omega -> Lattice.Site N -> Real)
    (phase : Omega -> UnitAddTorus (Lattice.Site N))
    (left right : Finset I) (time : Real) :
    ClusterUnitSlotHistoryExpansion ActualQuarticSourceHistory I left right
      (fun slot => actualLeftQuarticSourceSlotFactorizationDefect
        weight mass 1 1 entry p q left right slot time)
      (fun slot => actualRightQuarticSourceSlotFactorizationDefect
        weight mass 1 1 entry p q left right slot time) where
  leftHistories := fun _ => actualQuarticSourceHistories
  rightHistories := fun _ => actualQuarticSourceHistories
  leftSector := fun _ => actualQuarticHistorySector
  rightSector := fun _ => actualQuarticHistorySector
  leftContribution := fun slot history =>
    finiteLeftSourceHistorySlotContribution weight
      (actualFiniteCubicEnsemblePath mass entry p q)
      (actualFiniteQuarticHistorySource mass entry q radius phase)
      left right slot time history
  rightContribution := fun slot history =>
    finiteRightSourceHistorySlotContribution weight
      (actualFiniteCubicEnsemblePath mass entry p q)
      (actualFiniteQuarticHistorySource mass entry q radius phase)
      left right slot time history
  left_reconstruct := by
    intro slot _hslot
    exact actualLeftQuarticUnitSourceSlotFactorizationDefect_eq_historySum
      weight mass entry p q radius phase left right slot time
  right_reconstruct := by
    intro slot _hslot
    exact actualRightQuarticUnitSourceSlotFactorizationDefect_eq_historySum
      weight mass entry p q radius phase left right slot time

/-- Explicit four-sector norm budget for all actual unit-quadratic slots. -/
theorem actualFiniteQuadraticUnitSlotNormSum_le_fourSectors
    {N : Nat} [NeZero N]
    (weight : Omega -> Real) (mass : Omega -> Lattice.PositiveMassConfig N)
    (entry : I -> PhaseSign × Lattice.Site N)
    (p q : Omega -> Time -> HilbertConfiguration N)
    (radius : Omega -> Lattice.Site N -> Real)
    (phase : Omega -> UnitAddTorus (Lattice.Site N))
    (left right : Finset I) (time : Real) :
    let expansion := actualFiniteQuadraticUnitSlotHistoryExpansion
      weight mass entry p q radius phase left right time
    (∑ slot ∈ left, ‖actualLeftQuadraticSourceSlotFactorizationDefect
        weight mass 1 1 entry p q left right slot time‖) +
      (∑ slot ∈ right, ‖actualRightQuadraticSourceSlotFactorizationDefect
        weight mass 1 1 entry p q left right slot time‖) <=
      expansion.sectorNormBudget .regularGoodGarden +
        expansion.sectorNormBudget .badSmallDenominator +
        expansion.sectorNormBudget .recollisionRepeatedHistory +
        expansion.sectorNormBudget .truncationRemainder := by
  dsimp only
  exact (actualFiniteQuadraticUnitSlotHistoryExpansion
    weight mass entry p q radius phase left right time).totalDefectNormSum_le_fourSectorBudgets

/-- Explicit four-sector norm budget for all actual unit-quartic slots. -/
theorem actualFiniteQuarticUnitSlotNormSum_le_fourSectors
    {N : Nat} [NeZero N]
    (weight : Omega -> Real) (mass : Omega -> Lattice.PositiveMassConfig N)
    (entry : I -> PhaseSign × Lattice.Site N)
    (p q : Omega -> Time -> HilbertConfiguration N)
    (radius : Omega -> Lattice.Site N -> Real)
    (phase : Omega -> UnitAddTorus (Lattice.Site N))
    (left right : Finset I) (time : Real) :
    let expansion := actualFiniteQuarticUnitSlotHistoryExpansion
      weight mass entry p q radius phase left right time
    (∑ slot ∈ left, ‖actualLeftQuarticSourceSlotFactorizationDefect
        weight mass 1 1 entry p q left right slot time‖) +
      (∑ slot ∈ right, ‖actualRightQuarticSourceSlotFactorizationDefect
        weight mass 1 1 entry p q left right slot time‖) <=
      expansion.sectorNormBudget .regularGoodGarden +
        expansion.sectorNormBudget .badSmallDenominator +
        expansion.sectorNormBudget .recollisionRepeatedHistory +
        expansion.sectorNormBudget .truncationRemainder := by
  dsimp only
  exact (actualFiniteQuarticUnitSlotHistoryExpansion
    weight mass entry p q radius phase left right time).totalDefectNormSum_le_fourSectorBudgets

end
end ArchonPhysics.PhyslibFPUTActualSourceSlotHistoryGardenBridge
