import ArchonPhysics.ActualThreeMassRepeatedChildModeObstruction
import ArchonPhysics.DecayChannelModeEqualityPartition
import ArchonPhysics.RepeatedParentChildAcousticCumulativeBound

/-!
# Measure bridge for repeated parent--child sectors

The quadratic acoustic bounds are initially stated as explicit double sums
over tuples `[k,k,q]` and `[k,q,k]`.  The collision-limit pipeline, however,
uses predicate-restricted mismatch measures.  This module connects the two
representations without discarding the all-equal tuple: the exact partition
sectors are dominated by their complete equality planes, whose small-mismatch
mass is exactly the corresponding acoustic cumulative weight.
-/

namespace ArchonPhysics.RepeatedParentChildMismatchMeasureBridge

open ArchonPhysics
open ArchonPhysics.ActualThreeMassRepeatedChildModeObstruction
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.RepeatedParentChildAcousticCumulativeBound
open MeasureTheory Set

noncomputable section

/-- Coordinate equivalence used to reindex an ordered three-mode tuple. -/
def finThreeFunctionEquivTriple (alpha : Type*) :
    (Fin 3 -> alpha) ≃ alpha × (alpha × alpha) where
  toFun f := (f 0, (f 1, f 2))
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv f := by
    funext r
    fin_cases r <;> simp
  right_inv p := by
    rcases p with ⟨a, b, c⟩
    simp

/-- The complete equality plane `mode 0 = mode 1`, including the all-equal
tuple. -/
def ParentEqualsChildOne {N : Nat} [NeZero N]
    (modes : OrderedModeTriple N) : Prop :=
  modes 0 = modes 1

/-- The complete equality plane `mode 0 = mode 2`. -/
def ParentEqualsChildTwo {N : Nat} [NeZero N]
    (modes : OrderedModeTriple N) : Prop :=
  modes 0 = modes 2

/-- Restricting the tuple predicate is monotone at the measure level. -/
theorem positiveWeightedMismatchMeasureWhere_mono
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 -> InteractionSign)
    {keep₁ keep₂ : OrderedModeTriple N -> Prop}
    (hkeep : forall modes, keep₁ modes -> keep₂ modes) :
    positiveWeightedMismatchMeasureWhere m sign keep₁ <=
      positiveWeightedMismatchMeasureWhere m sign keep₂ := by
  classical
  unfold positiveWeightedMismatchMeasureWhere
  apply Finset.sum_le_sum
  intro modes _hmodes
  by_cases h₁ : IsPositiveOrderedTriple m modes ∧ keep₁ modes
  · have h₂ : IsPositiveOrderedTriple m modes ∧ keep₂ modes :=
      ⟨h₁.1, hkeep modes h₁.2⟩
    simp [h₁, h₂]
  · rw [if_neg h₁]
    exact bot_le

/-- Complete `0 = 1` equality-plane mismatch measure in its explicit
two-index parametrization. -/
def positiveRepeatedZeroOneMismatchMeasure
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) : Measure Real := by
  classical
  exact ∑ k, ∑ q,
    if IsPositiveOrderedTriple m ![k, k, q] then
      ENNReal.ofReal
          (harmonicOrderedNormalizedInteractionWeight m ![k, k, q]) •
        Measure.dirac
          (orderedThreeWaveMismatch m decayInteractionSign ![k, k, q])
    else 0

/-- Complete `0 = 2` equality-plane mismatch measure. -/
def positiveRepeatedZeroTwoMismatchMeasure
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) : Measure Real := by
  classical
  exact ∑ k, ∑ q,
    if IsPositiveOrderedTriple m ![k, q, k] then
      ENNReal.ofReal
          (harmonicOrderedNormalizedInteractionWeight m ![k, q, k]) •
        Measure.dirac
          (orderedThreeWaveMismatch m decayInteractionSign ![k, q, k])
    else 0

/-- Reindexing the predicate-restricted `0 = 1` plane gives the explicit
double-sum measure. -/
theorem positiveWeightedMismatchMeasureWhere_parentEqualsChildOne_eq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    positiveWeightedMismatchMeasureWhere
        m decayInteractionSign ParentEqualsChildOne =
      positiveRepeatedZeroOneMismatchMeasure m := by
  classical
  let summand : OrderedModeTriple N -> Measure Real := fun modes =>
    if IsPositiveOrderedTriple m modes ∧ ParentEqualsChildOne modes then
      ENNReal.ofReal
          (harmonicOrderedNormalizedInteractionWeight m modes) •
        Measure.dirac (orderedThreeWaveMismatch
          m decayInteractionSign modes)
    else 0
  change (∑ modes, summand modes) = _
  calc
    (∑ modes, summand modes) =
        ∑ p : OrderedModeIndex N ×
            (OrderedModeIndex N × OrderedModeIndex N),
          summand
            ((finThreeFunctionEquivTriple
              (OrderedModeIndex N)).symm p) :=
      (Equiv.sum_comp
        (finThreeFunctionEquivTriple (OrderedModeIndex N)).symm
        summand).symm
    _ = positiveRepeatedZeroOneMismatchMeasure m := by
      simp only [Fintype.sum_prod_type]
      simp only [summand, finThreeFunctionEquivTriple,
        positiveRepeatedZeroOneMismatchMeasure, ParentEqualsChildOne]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.sum_eq_single x]
      · simp
      · intro b _hb hbx
        simp [Ne.symm hbx]
      · simp

/-- Reindexing the `0 = 2` plane gives its explicit double sum. -/
theorem positiveWeightedMismatchMeasureWhere_parentEqualsChildTwo_eq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    positiveWeightedMismatchMeasureWhere
        m decayInteractionSign ParentEqualsChildTwo =
      positiveRepeatedZeroTwoMismatchMeasure m := by
  classical
  let summand : OrderedModeTriple N -> Measure Real := fun modes =>
    if IsPositiveOrderedTriple m modes ∧ ParentEqualsChildTwo modes then
      ENNReal.ofReal
          (harmonicOrderedNormalizedInteractionWeight m modes) •
        Measure.dirac (orderedThreeWaveMismatch
          m decayInteractionSign modes)
    else 0
  change (∑ modes, summand modes) = _
  calc
    (∑ modes, summand modes) =
        ∑ p : OrderedModeIndex N ×
            (OrderedModeIndex N × OrderedModeIndex N),
          summand
            ((finThreeFunctionEquivTriple
              (OrderedModeIndex N)).symm p) :=
      (Equiv.sum_comp
        (finThreeFunctionEquivTriple (OrderedModeIndex N)).symm
        summand).symm
    _ = positiveRepeatedZeroTwoMismatchMeasure m := by
      simp only [Fintype.sum_prod_type]
      simp only [summand, finThreeFunctionEquivTriple,
        positiveRepeatedZeroTwoMismatchMeasure, ParentEqualsChildTwo]
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro q _hq
      rw [Finset.sum_eq_single x]
      · simp
      · intro y _hy hyx
        simp [Ne.symm hyx]
      · simp

/-- The disjoint partition's first parent--child sector is dominated by its
complete equality plane. -/
theorem parentChildOneRepeated_mismatchMeasure_le_completePlane
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    positiveWeightedMismatchMeasureWhere
        m decayInteractionSign ParentChildOneRepeated <=
      positiveRepeatedZeroOneMismatchMeasure m := by
  rw [← positiveWeightedMismatchMeasureWhere_parentEqualsChildOne_eq]
  apply positiveWeightedMismatchMeasureWhere_mono
  intro modes hmodes
  exact hmodes.2

/-- The second parent--child partition sector is likewise dominated by the
complete `0 = 2` plane. -/
theorem parentChildTwoRepeated_mismatchMeasure_le_completePlane
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    positiveWeightedMismatchMeasureWhere
        m decayInteractionSign ParentChildTwoRepeated <=
      positiveRepeatedZeroTwoMismatchMeasure m := by
  rw [← positiveWeightedMismatchMeasureWhere_parentEqualsChildTwo_eq]
  apply positiveWeightedMismatchMeasureWhere_mono
  intro modes hmodes
  exact hmodes.2.2

end

end ArchonPhysics.RepeatedParentChildMismatchMeasureBridge
