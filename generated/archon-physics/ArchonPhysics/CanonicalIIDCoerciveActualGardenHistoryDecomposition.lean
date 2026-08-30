import ArchonPhysics.CanonicalIIDCoerciveActualClusterSourceSlotCouplingScaling

/-!
# Exact four-sector garden/history decomposition of canonical unit slots

This module provides the deterministic bookkeeping layer between an actual
finite history expansion and the canonical iid quadratic/quartic unit-slot
budgets.  Every history term belongs to exactly one of four sectors:

* a regular good-garden term;
* a bad-small-denominator term;
* a recollision or repeated-history term;
* a truncation remainder term.

The expansion data contain only finite sets, sector labels, complex
contributions, and exact reconstruction identities for the actual canonical
unit-slot defects.  There is no probability estimate, small-o field, RPA
closure, cancellation assertion, or decay conclusion.  All bounds below are
finite-sum identities followed by the triangle inequality.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualGardenHistoryDecomposition

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualClusterSourceSlotCouplingScaling
open ArchonPhysics.CanonicalIIDCoerciveClusterExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveSourceSlotCouplingScalingExpectation
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.RandomMassPositiveCollisionData

noncomputable section

/-- The exhaustive four-way classification used after a finite garden or
history expansion of one source slot. -/
inductive GardenHistorySector where
  | regularGoodGarden
  | badSmallDenominator
  | recollisionRepeatedHistory
  | truncationRemainder
  deriving DecidableEq, Repr

/-- Signed finite contribution of one history sector. -/
def finiteHistorySectorContribution
    {History : Type*} [DecidableEq History]
    (histories : Finset History)
    (sector : History -> GardenHistorySector)
    (contribution : History -> Complex)
    (target : GardenHistorySector) : Complex :=
  ∑ history ∈ histories,
    if sector history = target then contribution history else 0

/-- Absolute finite budget of one history sector. -/
def finiteHistorySectorNormBudget
    {History : Type*} [DecidableEq History]
    (histories : Finset History)
    (sector : History -> GardenHistorySector)
    (contribution : History -> Complex)
    (target : GardenHistorySector) : Real :=
  ∑ history ∈ histories,
    if sector history = target then ‖contribution history‖ else 0

/-- Exact partition of a finite history sum into the four exhaustive
sectors. -/
theorem finiteHistorySum_eq_fourSectorContributions
    {History : Type*} [DecidableEq History]
    (histories : Finset History)
    (sector : History -> GardenHistorySector)
    (contribution : History -> Complex) :
    (∑ history ∈ histories, contribution history) =
      finiteHistorySectorContribution histories sector contribution
          .regularGoodGarden +
        finiteHistorySectorContribution histories sector contribution
          .badSmallDenominator +
        finiteHistorySectorContribution histories sector contribution
          .recollisionRepeatedHistory +
        finiteHistorySectorContribution histories sector contribution
          .truncationRemainder := by
  unfold finiteHistorySectorContribution
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro history _hhistory
  cases hsector : sector history <;> simp

/-- The sum of the term norms is exactly the sum of the four sector
budgets. -/
theorem finiteHistoryNormSum_eq_fourSectorNormBudgets
    {History : Type*} [DecidableEq History]
    (histories : Finset History)
    (sector : History -> GardenHistorySector)
    (contribution : History -> Complex) :
    (∑ history ∈ histories, ‖contribution history‖) =
      finiteHistorySectorNormBudget histories sector contribution
          .regularGoodGarden +
        finiteHistorySectorNormBudget histories sector contribution
          .badSmallDenominator +
        finiteHistorySectorNormBudget histories sector contribution
          .recollisionRepeatedHistory +
        finiteHistorySectorNormBudget histories sector contribution
          .truncationRemainder := by
  unfold finiteHistorySectorNormBudget
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro history _hhistory
  cases hsector : sector history <;> simp

/-- Direct triangle bound for one finite history expansion. -/
theorem norm_finiteHistorySum_le_fourSectorNormBudgets
    {History : Type*} [DecidableEq History]
    (histories : Finset History)
    (sector : History -> GardenHistorySector)
    (contribution : History -> Complex) :
    ‖∑ history ∈ histories, contribution history‖ <=
      finiteHistorySectorNormBudget histories sector contribution
          .regularGoodGarden +
        finiteHistorySectorNormBudget histories sector contribution
          .badSmallDenominator +
        finiteHistorySectorNormBudget histories sector contribution
          .recollisionRepeatedHistory +
        finiteHistorySectorNormBudget histories sector contribution
          .truncationRemainder := by
  exact (norm_sum_le histories contribution).trans_eq
    (finiteHistoryNormSum_eq_fourSectorNormBudgets
      histories sector contribution)

/-- Finite history data reconstructing every left/right slot in one
canonical channel.  The only proof fields are exact finite-sum identities;
in particular this structure has no asymptotic or smallness assumption. -/
structure ClusterUnitSlotHistoryExpansion
    (History I : Type*) [DecidableEq History] [DecidableEq I]
    (left right : Finset I)
    (leftDefect rightDefect : I -> Complex) where
  leftHistories : I -> Finset History
  rightHistories : I -> Finset History
  leftSector : I -> History -> GardenHistorySector
  rightSector : I -> History -> GardenHistorySector
  leftContribution : I -> History -> Complex
  rightContribution : I -> History -> Complex
  left_reconstruct : forall slot, slot ∈ left ->
    leftDefect slot =
      ∑ history ∈ leftHistories slot, leftContribution slot history
  right_reconstruct : forall slot, slot ∈ right ->
    rightDefect slot =
      ∑ history ∈ rightHistories slot, rightContribution slot history

namespace ClusterUnitSlotHistoryExpansion

variable {History I : Type*} [DecidableEq History] [DecidableEq I]
variable {left right : Finset I}
variable {leftDefect rightDefect : I -> Complex}

/-- Total left/right norm budget in one chosen history sector. -/
def sectorNormBudget
    (expansion : ClusterUnitSlotHistoryExpansion History I
      left right leftDefect rightDefect)
    (target : GardenHistorySector) : Real :=
  (∑ slot ∈ left,
      finiteHistorySectorNormBudget
        (expansion.leftHistories slot) (expansion.leftSector slot)
          (expansion.leftContribution slot) target) +
    ∑ slot ∈ right,
      finiteHistorySectorNormBudget
        (expansion.rightHistories slot) (expansion.rightSector slot)
          (expansion.rightContribution slot) target

/-- Exact four-sector identity for one reconstructed left slot. -/
theorem leftDefect_eq_fourSectorContributions
    (expansion : ClusterUnitSlotHistoryExpansion History I
      left right leftDefect rightDefect)
    {slot : I} (hslot : slot ∈ left) :
    leftDefect slot =
      finiteHistorySectorContribution
          (expansion.leftHistories slot) (expansion.leftSector slot)
          (expansion.leftContribution slot) .regularGoodGarden +
        finiteHistorySectorContribution
          (expansion.leftHistories slot) (expansion.leftSector slot)
          (expansion.leftContribution slot) .badSmallDenominator +
        finiteHistorySectorContribution
          (expansion.leftHistories slot) (expansion.leftSector slot)
          (expansion.leftContribution slot) .recollisionRepeatedHistory +
        finiteHistorySectorContribution
          (expansion.leftHistories slot) (expansion.leftSector slot)
          (expansion.leftContribution slot) .truncationRemainder := by
  rw [expansion.left_reconstruct slot hslot]
  exact finiteHistorySum_eq_fourSectorContributions
    (expansion.leftHistories slot) (expansion.leftSector slot)
      (expansion.leftContribution slot)

/-- Exact four-sector identity for one reconstructed right slot. -/
theorem rightDefect_eq_fourSectorContributions
    (expansion : ClusterUnitSlotHistoryExpansion History I
      left right leftDefect rightDefect)
    {slot : I} (hslot : slot ∈ right) :
    rightDefect slot =
      finiteHistorySectorContribution
          (expansion.rightHistories slot) (expansion.rightSector slot)
          (expansion.rightContribution slot) .regularGoodGarden +
        finiteHistorySectorContribution
          (expansion.rightHistories slot) (expansion.rightSector slot)
          (expansion.rightContribution slot) .badSmallDenominator +
        finiteHistorySectorContribution
          (expansion.rightHistories slot) (expansion.rightSector slot)
          (expansion.rightContribution slot) .recollisionRepeatedHistory +
        finiteHistorySectorContribution
          (expansion.rightHistories slot) (expansion.rightSector slot)
          (expansion.rightContribution slot) .truncationRemainder := by
  rw [expansion.right_reconstruct slot hslot]
  exact finiteHistorySum_eq_fourSectorContributions
    (expansion.rightHistories slot) (expansion.rightSector slot)
      (expansion.rightContribution slot)

/-- Summing the one-slot triangle bounds gives the total cluster budget
bound by the four explicitly separated sector budgets. -/
theorem totalDefectNormSum_le_fourSectorBudgets
    (expansion : ClusterUnitSlotHistoryExpansion History I
      left right leftDefect rightDefect) :
    (∑ slot ∈ left, ‖leftDefect slot‖) +
        (∑ slot ∈ right, ‖rightDefect slot‖) <=
      expansion.sectorNormBudget .regularGoodGarden +
        expansion.sectorNormBudget .badSmallDenominator +
        expansion.sectorNormBudget .recollisionRepeatedHistory +
        expansion.sectorNormBudget .truncationRemainder := by
  calc
    (∑ slot ∈ left, ‖leftDefect slot‖) +
          (∑ slot ∈ right, ‖rightDefect slot‖) <=
        (∑ slot ∈ left,
          (finiteHistorySectorNormBudget
              (expansion.leftHistories slot) (expansion.leftSector slot)
              (expansion.leftContribution slot) .regularGoodGarden +
            finiteHistorySectorNormBudget
              (expansion.leftHistories slot) (expansion.leftSector slot)
              (expansion.leftContribution slot) .badSmallDenominator +
            finiteHistorySectorNormBudget
              (expansion.leftHistories slot) (expansion.leftSector slot)
              (expansion.leftContribution slot) .recollisionRepeatedHistory +
            finiteHistorySectorNormBudget
              (expansion.leftHistories slot) (expansion.leftSector slot)
              (expansion.leftContribution slot) .truncationRemainder)) +
        (∑ slot ∈ right,
          (finiteHistorySectorNormBudget
              (expansion.rightHistories slot) (expansion.rightSector slot)
              (expansion.rightContribution slot) .regularGoodGarden +
            finiteHistorySectorNormBudget
              (expansion.rightHistories slot) (expansion.rightSector slot)
              (expansion.rightContribution slot) .badSmallDenominator +
            finiteHistorySectorNormBudget
              (expansion.rightHistories slot) (expansion.rightSector slot)
              (expansion.rightContribution slot) .recollisionRepeatedHistory +
            finiteHistorySectorNormBudget
              (expansion.rightHistories slot) (expansion.rightSector slot)
              (expansion.rightContribution slot) .truncationRemainder)) := by
      apply add_le_add <;> apply Finset.sum_le_sum
      · intro slot hslot
        rw [expansion.left_reconstruct slot hslot]
        exact norm_finiteHistorySum_le_fourSectorNormBudgets
          (expansion.leftHistories slot) (expansion.leftSector slot)
            (expansion.leftContribution slot)
      · intro slot hslot
        rw [expansion.right_reconstruct slot hslot]
        exact norm_finiteHistorySum_le_fourSectorNormBudgets
          (expansion.rightHistories slot) (expansion.rightSector slot)
            (expansion.rightContribution slot)
    _ = expansion.sectorNormBudget .regularGoodGarden +
        expansion.sectorNormBudget .badSmallDenominator +
        expansion.sectorNormBudget .recollisionRepeatedHistory +
        expansion.sectorNormBudget .truncationRemainder := by
      unfold sectorNormBudget
      simp only [Finset.sum_add_distrib]
      ring

end ClusterUnitSlotHistoryExpansion

variable {N : Nat} [NeZero N]
variable {I : Type*} [DecidableEq I]

/-- Concrete quadratic unit-slot budget bound from an exact finite history
expansion of the actual canonical quadratic slot defects. -/
theorem canonicalQuadraticUnitSlotBudget_le_fourGardenSectors
    {History : Type*} [DecidableEq History]
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I -> PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (time : Real)
    (expansion : ClusterUnitSlotHistoryExpansion History I left right
      (fun slot =>
        canonicalLeftUnitQuadraticSourceSlotFactorizationDefect (N := N)
          kappa beta g hbeta a entry left right slot time)
      (fun slot =>
        canonicalRightUnitQuadraticSourceSlotFactorizationDefect (N := N)
          kappa beta g hbeta a entry left right slot time)) :
    canonicalClusterUnitQuadraticSourceSlotNormSum (N := N)
        kappa beta g hbeta a entry left right time <=
      expansion.sectorNormBudget .regularGoodGarden +
        expansion.sectorNormBudget .badSmallDenominator +
        expansion.sectorNormBudget .recollisionRepeatedHistory +
        expansion.sectorNormBudget .truncationRemainder := by
  unfold canonicalClusterUnitQuadraticSourceSlotNormSum
  exact expansion.totalDefectNormSum_le_fourSectorBudgets

/-- Concrete quartic unit-slot budget bound from an exact finite history
expansion of the actual canonical quartic slot defects. -/
theorem canonicalQuarticUnitSlotBudget_le_fourGardenSectors
    {History : Type*} [DecidableEq History]
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I -> PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (time : Real)
    (expansion : ClusterUnitSlotHistoryExpansion History I left right
      (fun slot =>
        canonicalLeftUnitQuarticSourceSlotFactorizationDefect (N := N)
          kappa beta g hbeta a entry left right slot time)
      (fun slot =>
        canonicalRightUnitQuarticSourceSlotFactorizationDefect (N := N)
          kappa beta g hbeta a entry left right slot time)) :
    canonicalClusterUnitQuarticSourceSlotNormSum (N := N)
        kappa beta g hbeta a entry left right time <=
      expansion.sectorNormBudget .regularGoodGarden +
        expansion.sectorNormBudget .badSmallDenominator +
        expansion.sectorNormBudget .recollisionRepeatedHistory +
        expansion.sectorNormBudget .truncationRemainder := by
  unfold canonicalClusterUnitQuarticSourceSlotNormSum
  exact expansion.totalDefectNormSum_le_fourSectorBudgets

/-- Full actual canonical source bound with the quadratic and quartic
channels each resolved into the four finite garden/history sectors.  The
sector budgets are not asserted to decay. -/
theorem norm_canonicalClusterSource_le_fourGardenSectorBudgets
    [Finite I]
    {QuadraticHistory QuarticHistory : Type*}
    [DecidableEq QuadraticHistory] [DecidableEq QuarticHistory]
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    {left right : Finset I} (hindex : Disjoint left right)
    (time : Real)
    (quadraticExpansion :
      ClusterUnitSlotHistoryExpansion QuadraticHistory I left right
        (fun slot =>
          canonicalLeftUnitQuadraticSourceSlotFactorizationDefect (N := N)
            kappa beta g hbeta a entry left right slot time)
        (fun slot =>
          canonicalRightUnitQuadraticSourceSlotFactorizationDefect (N := N)
            kappa beta g hbeta a entry left right slot time))
    (quarticExpansion :
      ClusterUnitSlotHistoryExpansion QuarticHistory I left right
        (fun slot =>
          canonicalLeftUnitQuarticSourceSlotFactorizationDefect (N := N)
            kappa beta g hbeta a entry left right slot time)
        (fun slot =>
          canonicalRightUnitQuarticSourceSlotFactorizationDefect (N := N)
            kappa beta g hbeta a entry left right slot time)) :
    ‖canonicalCoerciveClusterFactorizationDefectSource (N := N)
        kappa beta g hbeta a entry left right time‖ <=
      |kappa * g| *
          (quadraticExpansion.sectorNormBudget .regularGoodGarden +
            quadraticExpansion.sectorNormBudget .badSmallDenominator +
            quadraticExpansion.sectorNormBudget .recollisionRepeatedHistory +
            quadraticExpansion.sectorNormBudget .truncationRemainder) +
        |beta * g ^ 2| *
          (quarticExpansion.sectorNormBudget .regularGoodGarden +
            quarticExpansion.sectorNormBudget .badSmallDenominator +
            quarticExpansion.sectorNormBudget .recollisionRepeatedHistory +
            quarticExpansion.sectorNormBudget .truncationRemainder) := by
  let _ := Fintype.ofFinite I
  apply
    (norm_canonicalCoerciveClusterFactorizationDefectSource_le_coupling_unitSlotNormSums
      hN ha0 ha1 kappa beta g hbeta entry hpositive hindex time).trans
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (canonicalQuadraticUnitSlotBudget_le_fourGardenSectors
        kappa beta g hbeta a entry left right time quadraticExpansion)
      (abs_nonneg _))
    (mul_le_mul_of_nonneg_left
      (canonicalQuarticUnitSlotBudget_le_fourGardenSectors
        kappa beta g hbeta a entry left right time quarticExpansion)
      (abs_nonneg _))

end

end ArchonPhysics.CanonicalIIDCoerciveActualGardenHistoryDecomposition
