import ArchonPhysics.CanonicalIIDCoerciveActualGardenHistoryDecomposition
import ArchonPhysics.ChildRepeatedAllEqualBroadeningDecay
import ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting
import ArchonPhysics.RepeatedParentChildPartitionFractionalBroadeningDecay

/-!
# Explicit kinetic bounds for the controlled repeated-history sectors

This file separates two statements which must not be conflated.

First, an actual finite history expansion has a literal finite number of
recollision/repeated terms.  Its norm budget is bounded by that cardinality
times a pointwise majorant.  For the existing fixed-root raw alpha-FPUT
histories the cardinality is exactly

`catalan order * 4 ^ order * N ^ order`.

Second, three concrete pieces of the decay-channel repeated-mode partition
already have volume-uniform `O(T^{-1/2})` bounds without RPA or a Markov
assumption: the two parent--child sectors and the all-three-equal part of the
child-repeated sector.  At kinetic time `T = tau / g^2` their joint ceiling is
linear in `|g|`.

The parent-distinct child-repeated sector and the map from an arbitrary
higher-order history contribution to these collision weights are *not*
silently asserted.  The final closure theorem exposes their sum as an
explicit residual sequence.  Thus the theorem identifies the exact remaining
estimate rather than storing a desired small-o conclusion in a structure.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveRepeatedHistoryKineticBound

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualGardenHistoryDecomposition
open ArchonPhysics.ChildRepeatedAllEqualBroadeningDecay
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RepeatedParentChildPartitionFractionalBroadeningDecay
open ArchonPhysics.UniformCollisionDensityTransfer
open Filter MeasureTheory

noncomputable section

/-! ## Literal finite-sector cardinality bounds -/

/-- Number of occurrences of one sector in an actual finite history list.
Multiplicity is retained at the `Finset` level used by the expansion. -/
def finiteHistorySectorCard
    {History : Type*} [DecidableEq History]
    (histories : Finset History)
    (sector : History -> GardenHistorySector)
    (target : GardenHistorySector) : Nat :=
  (histories.filter fun history => sector history = target).card

/-- The sector norm budget is exactly the norm sum over the filtered finite
history family. -/
theorem finiteHistorySectorNormBudget_eq_sum_filter
    {History : Type*} [DecidableEq History]
    (histories : Finset History)
    (sector : History -> GardenHistorySector)
    (contribution : History -> Complex)
    (target : GardenHistorySector) :
    finiteHistorySectorNormBudget histories sector contribution target =
      ∑ history ∈ histories.filter (fun history => sector history = target),
        ‖contribution history‖ := by
  classical
  simp [finiteHistorySectorNormBudget, Finset.sum_filter]

/-- A pointwise majorant gives the literal cardinality-times-majorant bound
for one finite sector. -/
theorem finiteHistorySectorNormBudget_le_card_mul
    {History : Type*} [DecidableEq History]
    (histories : Finset History)
    (sector : History -> GardenHistorySector)
    (contribution : History -> Complex)
    (target : GardenHistorySector)
    {majorant : Real}
    (hterm : forall history, history ∈ histories ->
      sector history = target -> ‖contribution history‖ <= majorant) :
    finiteHistorySectorNormBudget histories sector contribution target <=
      (finiteHistorySectorCard histories sector target : Real) * majorant := by
  rw [finiteHistorySectorNormBudget_eq_sum_filter]
  calc
    (∑ history ∈ histories.filter (fun history => sector history = target),
        ‖contribution history‖) <=
      ∑ _history ∈ histories.filter
          (fun history => sector history = target), majorant := by
        apply Finset.sum_le_sum
        intro history hhistory
        exact hterm history (Finset.mem_filter.mp hhistory).1
          (Finset.mem_filter.mp hhistory).2
    _ = (finiteHistorySectorCard histories sector target : Real) *
        majorant := by
      simp [finiteHistorySectorCard]

/-- Exact raw fixed-root history capacity at perturbative order `order`. -/
def fixedRootRawHistoryCapacity (N order : Nat) : Nat :=
  catalan order * 4 ^ order * N ^ order

/-- Every chosen sector of the actual fixed-root raw history family fits in
the exact Catalan/sign/momentum capacity. -/
theorem card_fixedRootRawHistorySector_le_capacity
    {N order : Nat} [NeZero N] (rootMomentum : Lattice.Site N)
    [DecidableEq (FixedRootRawHistoryIndex N order rootMomentum)]
    (histories : Finset (FixedRootRawHistoryIndex N order rootMomentum))
    (sector : FixedRootRawHistoryIndex N order rootMomentum ->
      GardenHistorySector)
    (target : GardenHistorySector) :
    finiteHistorySectorCard histories sector target <=
      fixedRootRawHistoryCapacity N order := by
  calc
    finiteHistorySectorCard histories sector target <= histories.card := by
      exact Finset.card_filter_le _ _
    _ <= Fintype.card (FixedRootRawHistoryIndex N order rootMomentum) :=
      Finset.card_le_univ _
    _ = fixedRootRawHistoryCapacity N order := by
      exact
        (card_fixedRootRawHistoryIndex rootMomentum).trans (by
          rfl)

variable {History I : Type*} [DecidableEq History] [DecidableEq I]
variable {left right : Finset I}
variable {leftDefect rightDefect : I -> Complex}

/-- Literal number of left/right history occurrences in one sector of a
cluster unit-slot expansion. -/
def clusterSectorOccurrenceCount
    (expansion : ClusterUnitSlotHistoryExpansion History I
      left right leftDefect rightDefect)
    (target : GardenHistorySector) : Nat :=
  (∑ slot ∈ left,
      finiteHistorySectorCard
        (expansion.leftHistories slot) (expansion.leftSector slot) target) +
    ∑ slot ∈ right,
      finiteHistorySectorCard
        (expansion.rightHistories slot) (expansion.rightSector slot) target

/-- The cluster sector budget is at most its literal occurrence count times
a uniform pointwise norm majorant. -/
theorem clusterSectorNormBudget_le_occurrenceCount_mul
    (expansion : ClusterUnitSlotHistoryExpansion History I
      left right leftDefect rightDefect)
    (target : GardenHistorySector)
    {majorant : Real}
    (hleft : forall slot, slot ∈ left -> forall history,
      history ∈ expansion.leftHistories slot ->
      expansion.leftSector slot history = target ->
      ‖expansion.leftContribution slot history‖ <= majorant)
    (hright : forall slot, slot ∈ right -> forall history,
      history ∈ expansion.rightHistories slot ->
      expansion.rightSector slot history = target ->
      ‖expansion.rightContribution slot history‖ <= majorant) :
    expansion.sectorNormBudget target <=
      (clusterSectorOccurrenceCount expansion target : Real) * majorant := by
  unfold ClusterUnitSlotHistoryExpansion.sectorNormBudget
    clusterSectorOccurrenceCount
  calc
    (∑ slot ∈ left,
        finiteHistorySectorNormBudget
          (expansion.leftHistories slot) (expansion.leftSector slot)
          (expansion.leftContribution slot) target) +
        ∑ slot ∈ right,
          finiteHistorySectorNormBudget
            (expansion.rightHistories slot) (expansion.rightSector slot)
            (expansion.rightContribution slot) target <=
      (∑ slot ∈ left,
        (finiteHistorySectorCard
          (expansion.leftHistories slot) (expansion.leftSector slot) target :
            Real) * majorant) +
        ∑ slot ∈ right,
          (finiteHistorySectorCard
            (expansion.rightHistories slot) (expansion.rightSector slot) target :
              Real) * majorant := by
      apply add_le_add <;> apply Finset.sum_le_sum
      · intro slot hslot
        exact finiteHistorySectorNormBudget_le_card_mul
          (expansion.leftHistories slot) (expansion.leftSector slot)
          (expansion.leftContribution slot) target
          (hleft slot hslot)
      · intro slot hslot
        exact finiteHistorySectorNormBudget_le_card_mul
          (expansion.rightHistories slot) (expansion.rightSector slot)
          (expansion.rightContribution slot) target
          (hright slot hslot)
    _ = (((∑ slot ∈ left,
          finiteHistorySectorCard
            (expansion.leftHistories slot) (expansion.leftSector slot) target) +
        ∑ slot ∈ right,
          finiteHistorySectorCard
            (expansion.rightHistories slot) (expansion.rightSector slot) target :
            Nat) : Real) * majorant := by
      simp only [Nat.cast_add, Nat.cast_sum]
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      ring

/-- When the history type is the actual order-`order` fixed-root raw FPUT
family, the complete cluster occurrence count has an explicit `N`/order
bound.  No decay estimate is used. -/
theorem fixedRootRaw_sectorOccurrenceCount_le
    {N order : Nat} [NeZero N] (rootMomentum : Lattice.Site N)
    [DecidableEq (FixedRootRawHistoryIndex N order rootMomentum)]
    (expansion : ClusterUnitSlotHistoryExpansion
      (FixedRootRawHistoryIndex N order rootMomentum) I
      left right leftDefect rightDefect)
    (target : GardenHistorySector) :
    clusterSectorOccurrenceCount expansion target <=
      (left.card + right.card) * fixedRootRawHistoryCapacity N order := by
  unfold clusterSectorOccurrenceCount
  calc
    (∑ slot ∈ left,
        finiteHistorySectorCard
          (expansion.leftHistories slot) (expansion.leftSector slot) target) +
        ∑ slot ∈ right,
          finiteHistorySectorCard
            (expansion.rightHistories slot) (expansion.rightSector slot) target <=
      (∑ _slot ∈ left, fixedRootRawHistoryCapacity N order) +
        ∑ _slot ∈ right, fixedRootRawHistoryCapacity N order := by
      apply Nat.add_le_add <;> apply Finset.sum_le_sum
      · intro slot _hslot
        exact card_fixedRootRawHistorySector_le_capacity rootMomentum
          (expansion.leftHistories slot) (expansion.leftSector slot) target
      · intro slot _hslot
        exact card_fixedRootRawHistorySector_le_capacity rootMomentum
          (expansion.rightHistories slot) (expansion.rightSector slot) target
    _ = (left.card + right.card) * fixedRootRawHistoryCapacity N order := by
      simp [Nat.add_mul]

/-- Explicit finite `N`/coupling/order bound for the actual raw-history
recollision sector.  The sole analytic input is the displayed pointwise
majorant, so the still-missing estimate cannot be hidden. -/
theorem fixedRootRaw_recollisionSectorNormBudget_le_explicit
    {N order : Nat} [NeZero N] (rootMomentum : Lattice.Site N)
    [DecidableEq (FixedRootRawHistoryIndex N order rootMomentum)]
    (expansion : ClusterUnitSlotHistoryExpansion
      (FixedRootRawHistoryIndex N order rootMomentum) I
      left right leftDefect rightDefect)
    (g amplitude : Real) (hamplitude : 0 <= amplitude)
    (hleft : forall slot, slot ∈ left -> forall history,
      history ∈ expansion.leftHistories slot ->
      expansion.leftSector slot history = .recollisionRepeatedHistory ->
      ‖expansion.leftContribution slot history‖ <= amplitude * |g|)
    (hright : forall slot, slot ∈ right -> forall history,
      history ∈ expansion.rightHistories slot ->
      expansion.rightSector slot history = .recollisionRepeatedHistory ->
      ‖expansion.rightContribution slot history‖ <= amplitude * |g|) :
    expansion.sectorNormBudget .recollisionRepeatedHistory <=
      (((left.card + right.card) *
          fixedRootRawHistoryCapacity N order : Nat) : Real) *
        (amplitude * |g|) := by
  have hmajorant : 0 <= amplitude * |g| :=
    mul_nonneg hamplitude (abs_nonneg g)
  calc
    expansion.sectorNormBudget .recollisionRepeatedHistory <=
        (clusterSectorOccurrenceCount expansion
          .recollisionRepeatedHistory : Real) *
          (amplitude * |g|) :=
      clusterSectorNormBudget_le_occurrenceCount_mul expansion
        .recollisionRepeatedHistory hleft hright
    _ <= (((left.card + right.card) *
          fixedRootRawHistoryCapacity N order : Nat) : Real) *
        (amplitude * |g|) := by
      have hcountNat := fixedRootRaw_sectorOccurrenceCount_le
        rootMomentum expansion GardenHistorySector.recollisionRepeatedHistory
      have hcountReal :
          (clusterSectorOccurrenceCount expansion
            GardenHistorySector.recollisionRepeatedHistory : Real) <=
          (((left.card + right.card) *
            fixedRootRawHistoryCapacity N order : Nat) : Real) := by
        exact_mod_cast hcountNat
      exact mul_le_mul_of_nonneg_right hcountReal hmajorant

/-! ## Three unconditionally controlled collision sub-sectors -/

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Sum of the two disjoint parent--child broadened weights per site and the
all-three-equal child-repeated broadened weight per site, at canonical volume
`N = n + 2`.  These are precisely the repeated collision sectors already
controlled without RPA/Markov assumptions. -/
def canonicalControlledRepeatedCollisionBudget
    (n : Nat) (omega : RandomEnsemble.SampleSpace) (T : Real) : Real :=
  let N := n + 2
  let m := canonicalIIDMassPhaseEnsemble.restrictPositiveMass
    (N := N) omega
  positiveParentChildOneRepeatedBroadenedInteractionWeight m T / (N : Real) +
    positiveParentChildTwoRepeatedBroadenedInteractionWeight m T / (N : Real) +
    ∫ mismatch : Real, normalizedFiniteTimeResonanceKernel mismatch T
      ∂(canonicalAllEqualPerSiteMismatchFiniteMeasure
        canonicalIIDMassPhaseEnsemble n omega : Measure Real)

/-- The controlled repeated collision budget is nonnegative at every real
observation time. -/
theorem canonicalControlledRepeatedCollisionBudget_nonneg
    (n : Nat) (omega : RandomEnsemble.SampleSpace) (T : Real) :
    0 <= canonicalControlledRepeatedCollisionBudget n omega T := by
  let N := n + 2
  let m := canonicalIIDMassPhaseEnsemble.restrictPositiveMass
    (N := N) omega
  have hone : 0 <=
      positiveParentChildOneRepeatedBroadenedInteractionWeight m T /
        (N : Real) :=
    div_nonneg
      (positiveParentChildOneRepeatedBroadenedInteractionWeight_nonneg m T)
      (Nat.cast_nonneg N)
  have htwo : 0 <=
      positiveParentChildTwoRepeatedBroadenedInteractionWeight m T /
        (N : Real) :=
    div_nonneg
      (positiveParentChildTwoRepeatedBroadenedInteractionWeight_nonneg m T)
      (Nat.cast_nonneg N)
  have hall : 0 <=
      ∫ mismatch : Real, normalizedFiniteTimeResonanceKernel mismatch T
        ∂(canonicalAllEqualPerSiteMismatchFiniteMeasure
          canonicalIIDMassPhaseEnsemble n omega : Measure Real) := by
    apply integral_nonneg_of_ae
    exact Eventually.of_forall fun mismatch =>
      normalizedFiniteTimeResonanceKernel_nonneg mismatch T
  dsimp [canonicalControlledRepeatedCollisionBudget, N, m]
  linarith

/-- Volume-uniform `O(T^{-1/2})` bound for the three controlled repeated
collision sub-sectors. -/
theorem canonicalControlledRepeatedCollisionBudget_le
    (n : Nat) (omega : RandomEnsemble.SampleSpace)
    {T : Real} (hT : 0 < T) :
    canonicalControlledRepeatedCollisionBudget n omega T <=
      3 * (5 / (2 * Real.pi * Real.sqrt T)) := by
  let N := n + 2
  let m := canonicalIIDMassPhaseEnsemble.restrictPositiveMass
    (N := N) omega
  have hone :=
    iid_positiveParentChildOneRepeatedBroadenedInteractionWeight_div_volume_le
      canonicalIIDMassPhaseEnsemble (N := N) omega hT
  have htwo :=
    iid_positiveParentChildTwoRepeatedBroadenedInteractionWeight_div_volume_le
      canonicalIIDMassPhaseEnsemble (N := N) omega hT
  have hall := integral_normalizedKernel_canonicalAllEqualPerSite_le
    canonicalIIDMassPhaseEnsemble omega n hT
  dsimp [canonicalControlledRepeatedCollisionBudget, N, m]
  linarith

/-- Exact square-root conversion from kinetic time to coupling size. -/
theorem fractionalCeiling_at_kineticTime
    {tau g : Real} (htau : 0 < tau) (hg : g ≠ 0) :
    5 / (2 * Real.pi * Real.sqrt (tau / g ^ 2)) =
      5 * |g| / (2 * Real.pi * Real.sqrt tau) := by
  rw [Real.sqrt_div htau.le, Real.sqrt_sq_eq_abs]
  field_simp

/-- At kinetic time, the three controlled sectors have a volume-uniform
ceiling linear in `|g|`. -/
theorem canonicalControlledRepeatedCollisionBudget_at_kineticTime_le
    (n : Nat) (omega : RandomEnsemble.SampleSpace)
    {tau g : Real} (htau : 0 < tau) (hg : g ≠ 0) :
    canonicalControlledRepeatedCollisionBudget n omega (tau / g ^ 2) <=
      3 * (5 * |g| / (2 * Real.pi * Real.sqrt tau)) := by
  have htime : 0 < tau / g ^ 2 := div_pos htau (sq_pos_of_ne_zero hg)
  calc
    canonicalControlledRepeatedCollisionBudget n omega (tau / g ^ 2) <=
        3 * (5 / (2 * Real.pi * Real.sqrt (tau / g ^ 2))) :=
      canonicalControlledRepeatedCollisionBudget_le n omega htime
    _ = 3 * (5 * |g| / (2 * Real.pi * Real.sqrt tau)) := by
      rw [fractionalCeiling_at_kineticTime htau hg]

/-- Uniform-in-volume kinetic convergence of the three controlled repeated
collision sectors along any nonzero coupling sequence tending to zero. -/
theorem canonicalControlledRepeatedCollisionBudget_at_kineticTime_tendsto_zero
    (size : Nat -> Nat) (omega : RandomEnsemble.SampleSpace)
    (tau : Real) (htau : 0 < tau)
    (g : Nat -> Real) (hg0 : forall n, g n ≠ 0)
    (hg : Tendsto g atTop (nhds 0)) :
    Tendsto
      (fun n => canonicalControlledRepeatedCollisionBudget
        (size n) omega (tau / (g n) ^ 2))
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n =>
      canonicalControlledRepeatedCollisionBudget_nonneg
        (size n) omega (tau / (g n) ^ 2)
  · exact Eventually.of_forall fun n =>
      canonicalControlledRepeatedCollisionBudget_at_kineticTime_le
        (size n) omega htau (hg0 n)
  · have habs : Tendsto (fun n => |g n|) atTop (nhds 0) := by
      simpa only [abs_zero] using hg.abs
    have hscaled : Tendsto
        (fun n => (3 * 5 / (2 * Real.pi * Real.sqrt tau)) * |g n|)
        atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul habs)
    convert hscaled using 1
    funext n
    ring

/-! ## Transparent residual closure -/

/-- A history-sector budget dominated by the three controlled collision
sectors plus an explicitly named residual.  In applications the residual is
exactly where the parent-distinct child-repeated sector and higher-order
recollision-to-collision comparison must be proved. -/
theorem repeatedHistoryBudget_at_kineticTime_le_controlled_add_residual
    (size : Nat -> Nat) (omega : RandomEnsemble.SampleSpace)
    (tau : Real) (htau : 0 < tau)
    (g : Nat -> Real) (hg0 : forall n, g n ≠ 0)
    (budget residual : Nat -> Real)
    (multiplicity : Nat)
    (hdominate : forall n,
      budget n <=
        (multiplicity : Real) *
            canonicalControlledRepeatedCollisionBudget
              (size n) omega (tau / (g n) ^ 2) +
          residual n) :
    forall n,
      budget n <=
        (multiplicity : Real) *
            (3 * (5 * |g n| / (2 * Real.pi * Real.sqrt tau))) +
          residual n := by
  intro n
  have hcontrol := mul_le_mul_of_nonneg_left
    (canonicalControlledRepeatedCollisionBudget_at_kineticTime_le
      (size n) omega htau (hg0 n))
    (Nat.cast_nonneg multiplicity)
  nlinarith [hdominate n, hcontrol]

/-- The repeated-history budget tends to zero once, and only once, the
explicit residual does.  The collision part of the proof is unconditional;
`hresidual` is the isolated remaining scientific estimate. -/
theorem repeatedHistoryBudget_at_kineticTime_tendsto_zero_of_residual
    (size : Nat -> Nat) (omega : RandomEnsemble.SampleSpace)
    (tau : Real) (htau : 0 < tau)
    (g : Nat -> Real) (hg0 : forall n, g n ≠ 0)
    (hg : Tendsto g atTop (nhds 0))
    (budget residual : Nat -> Real)
    (multiplicity : Nat)
    (hbudget_nonneg : forall n, 0 <= budget n)
    (hresidual : Tendsto residual atTop (nhds 0))
    (hdominate : forall n,
      budget n <=
        (multiplicity : Real) *
            canonicalControlledRepeatedCollisionBudget
              (size n) omega (tau / (g n) ^ 2) +
          residual n) :
    Tendsto budget atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall hbudget_nonneg
  · exact Eventually.of_forall hdominate
  · have hcontrolled :=
      canonicalControlledRepeatedCollisionBudget_at_kineticTime_tendsto_zero
        size omega tau htau g hg0 hg
    have hscaled : Tendsto
        (fun n => (multiplicity : Real) *
          canonicalControlledRepeatedCollisionBudget
            (size n) omega (tau / (g n) ^ 2))
        atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hcontrolled)
    simpa using hscaled.add hresidual

end

end ArchonPhysics.CanonicalIIDCoerciveRepeatedHistoryKineticBound
