import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open scoped BigOperators ENNReal NNReal

namespace Family8AllSlabUnionCancellationBudgetV1

/-!
# Finite all-slab union cancellation

The plank argument does not pass from one arbitrarily selected slab row back
to the source family.  It first pigeonholes a finite family of comparable
rows.  In normalized coordinates the row estimate contains the reciprocal
of the total reconstruction weight `|SS| * |S|`; summing the Jacobian-weighted
row unions supplies that same total weight and cancels it.

This file isolates exactly that finite aggregation.  It intentionally makes
no claim that the current certified-incidence construction supplies the row
catalogue, the Eq. (43) Frostman inheritance, or bounded-overlap assembly.
-/

noncomputable section

/-- The Eq. (43) coefficient before harmless absolute losses: original
Frostman constant times the total row/Jacobian reconstruction weight. -/
def eq43FrostmanEnvelope
    (sourceFrostmanConstant totalRowWeight : ENNReal) : ENNReal :=
  sourceFrostmanConstant * totalRowWeight

/-- An upper Eq. (43) bound gives the correct lower bound after the negative
Frostman power appearing in the union-volume formulation. -/
theorem eq43FrostmanEnvelope_negativePower_le
    (rowFrostmanConstant sourceFrostmanConstant totalRowWeight : ENNReal)
    (power : Real) (hpower : 0 <= power)
    (hEq43 : rowFrostmanConstant <=
      eq43FrostmanEnvelope sourceFrostmanConstant totalRowWeight) :
    eq43FrostmanEnvelope sourceFrostmanConstant totalRowWeight ^ (-power) <=
      rowFrostmanConstant ^ (-power) := by
  rw [ENNReal.rpow_neg, ENNReal.rpow_neg, ENNReal.inv_le_inv]
  exact ENNReal.rpow_le_rpow hEq43 hpower

/-- Weakest finite-row interface retaining the `|SS| * |S|` cancellation.

`rowWeight r` is the inverse-Jacobian reconstruction weight of row `r`
(constant `|S|` in the uniform paper situation).  `localCore / totalWeight`
is the row-independent scale after Eq. (43) and row-cardinality
pigeonholing.  Only its *aggregate* lower bound is required: no unnecessarily
strong pointwise estimate on every row is built into the interface.
`assemblyLoss` records only the finite overlap/comparability loss when the
weighted row unions are reassembled.
-/
structure AllSlabUnionCancellationBudget
    (rowIndex : Type*) [Fintype rowIndex] [DecidableEq rowIndex]
    (localCore globalUnion assemblyLoss : ENNReal) where
  rowWeight : rowIndex -> ENNReal
  normalizedRowUnion : rowIndex -> ENNReal
  totalWeight : ENNReal
  totalWeight_ne_zero : totalWeight ≠ 0
  totalWeight_ne_top : totalWeight ≠ ⊤
  weight_sum : (∑ r : rowIndex, rowWeight r) = totalWeight
  aggregate_rows_lower :
    totalWeight * (localCore / totalWeight) <=
      ∑ r : rowIndex, rowWeight r * normalizedRowUnion r
  weighted_rows_le_global :
    (∑ r : rowIndex, rowWeight r * normalizedRowUnion r) <=
      assemblyLoss * globalUnion

/-- Summing every normalized row estimate cancels the total row/Jacobian
weight exactly. -/
theorem AllSlabUnionCancellationBudget.localCore_le
    {rowIndex : Type*} [Fintype rowIndex] [DecidableEq rowIndex]
    {localCore globalUnion assemblyLoss : ENNReal}
    (B : AllSlabUnionCancellationBudget
      rowIndex localCore globalUnion assemblyLoss) :
    localCore <= assemblyLoss * globalUnion := by
  calc
    localCore = B.totalWeight * (localCore / B.totalWeight) :=
      (ENNReal.mul_div_cancel B.totalWeight_ne_zero
        B.totalWeight_ne_top).symm
    _ <= ∑ r : rowIndex,
        B.rowWeight r * B.normalizedRowUnion r := B.aggregate_rows_lower
    _ <= assemblyLoss * globalUnion := B.weighted_rows_le_global

/-- A pointwise lower bound on every row is one sufficient producer for the
weaker aggregate interface.  Lemma 6.13 may instead produce the aggregate
premise directly after refinement and comparability pigeonholing. -/
def AllSlabUnionCancellationBudget.ofPointwiseRowLower
    {rowIndex : Type*} [Fintype rowIndex] [DecidableEq rowIndex]
    (rowWeight : rowIndex -> ENNReal)
    (totalWeight localCore globalUnion assemblyLoss : ENNReal)
    (normalizedRowUnion : rowIndex -> ENNReal)
    (htotal0 : totalWeight ≠ 0) (htotalTop : totalWeight ≠ ⊤)
    (hweight : (∑ r : rowIndex, rowWeight r) = totalWeight)
    (hlocal : forall r : rowIndex,
      localCore / totalWeight <= normalizedRowUnion r)
    (hassembly :
      (∑ r : rowIndex, rowWeight r * normalizedRowUnion r) <=
        assemblyLoss * globalUnion) :
    AllSlabUnionCancellationBudget
      rowIndex localCore globalUnion assemblyLoss where
  rowWeight := rowWeight
  normalizedRowUnion := normalizedRowUnion
  totalWeight := totalWeight
  totalWeight_ne_zero := htotal0
  totalWeight_ne_top := htotalTop
  weight_sum := hweight
  aggregate_rows_lower := by
    calc
      totalWeight * (localCore / totalWeight) =
          (∑ r : rowIndex, rowWeight r) *
            (localCore / totalWeight) := by rw [hweight]
      _ = ∑ r : rowIndex,
          rowWeight r * (localCore / totalWeight) := by
        rw [Finset.sum_mul]
      _ <= ∑ r : rowIndex,
          rowWeight r * normalizedRowUnion r := by
        exact Finset.sum_le_sum fun r _hr =>
          mul_le_mul' le_rfl (hlocal r)
  weighted_rows_le_global := hassembly

/-- If the spare epsilon power also pays the fixed assembly loss, the target
core reaches the global union with no residual row-count or slab-volume
factor. -/
theorem AllSlabUnionCancellationBudget.target_le_global_of_reserve
    {rowIndex : Type*} [Fintype rowIndex] [DecidableEq rowIndex]
    {localCore targetCore globalUnion assemblyLoss : ENNReal}
    (B : AllSlabUnionCancellationBudget
      rowIndex localCore globalUnion assemblyLoss)
    (hassembly0 : assemblyLoss ≠ 0) (hassemblyTop : assemblyLoss ≠ ⊤)
    (hreserve : assemblyLoss * targetCore <= localCore) :
    targetCore <= globalUnion := by
  apply (ENNReal.mul_le_mul_iff_right hassembly0 hassemblyTop).mp
  exact hreserve.trans B.localCore_le

/-- Uniform-row constructor.  Here `totalWeight = |SS| * |S|` literally:
each of the `Fintype.card rowIndex` rows has the same slab/Jacobian weight. -/
def AllSlabUnionCancellationBudget.ofConstantSlabWeight
    {rowIndex : Type*} [Fintype rowIndex] [DecidableEq rowIndex]
    (slabWeight localCore globalUnion assemblyLoss : ENNReal)
    (normalizedRowUnion : rowIndex -> ENNReal)
    (htotal0 : (Fintype.card rowIndex : ENNReal) * slabWeight ≠ 0)
    (htotalTop : (Fintype.card rowIndex : ENNReal) * slabWeight ≠ ⊤)
    (hlocal : forall r : rowIndex,
      localCore / ((Fintype.card rowIndex : ENNReal) * slabWeight) <=
        normalizedRowUnion r)
    (hassembly :
      (∑ r : rowIndex, slabWeight * normalizedRowUnion r) <=
        assemblyLoss * globalUnion) :
    AllSlabUnionCancellationBudget
      rowIndex localCore globalUnion assemblyLoss :=
  AllSlabUnionCancellationBudget.ofPointwiseRowLower
    (fun _ => slabWeight)
    ((Fintype.card rowIndex : ENNReal) * slabWeight)
    localCore globalUnion assemblyLoss normalizedRowUnion
    htotal0 htotalTop (by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ])
    hlocal hassembly

/-- The uniform constructor exposes the paper cancellation without opening
the structure: a local `1 / (|SS|*|S|)` lower bound and bounded-overlap row
assembly imply the global bound. -/
theorem localCore_le_of_constantSlabWeight
    {rowIndex : Type*} [Fintype rowIndex] [DecidableEq rowIndex]
    (slabWeight localCore globalUnion assemblyLoss : ENNReal)
    (normalizedRowUnion : rowIndex -> ENNReal)
    (htotal0 : (Fintype.card rowIndex : ENNReal) * slabWeight ≠ 0)
    (htotalTop : (Fintype.card rowIndex : ENNReal) * slabWeight ≠ ⊤)
    (hlocal : forall r : rowIndex,
      localCore / ((Fintype.card rowIndex : ENNReal) * slabWeight) <=
        normalizedRowUnion r)
    (hassembly :
      (∑ r : rowIndex, slabWeight * normalizedRowUnion r) <=
        assemblyLoss * globalUnion) :
    localCore <= assemblyLoss * globalUnion :=
  (AllSlabUnionCancellationBudget.ofConstantSlabWeight
    slabWeight localCore globalUnion assemblyLoss normalizedRowUnion
      htotal0 htotalTop hlocal hassembly).localCore_le

#print axioms eq43FrostmanEnvelope_negativePower_le
#print axioms AllSlabUnionCancellationBudget.localCore_le
#print axioms AllSlabUnionCancellationBudget.ofPointwiseRowLower
#print axioms AllSlabUnionCancellationBudget.target_le_global_of_reserve
#print axioms AllSlabUnionCancellationBudget.ofConstantSlabWeight
#print axioms localCore_le_of_constantSlabWeight

end
end Family8AllSlabUnionCancellationBudgetV1
