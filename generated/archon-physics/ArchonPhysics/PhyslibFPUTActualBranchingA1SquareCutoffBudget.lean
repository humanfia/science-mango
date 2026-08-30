import ArchonPhysics.PhyslibFPUTActualBranchingA1CompactSmallBall
import ArchonPhysics.PhyslibFPUTActualGardenPowerScheduleRPAClosure

/-!
# Actual branching A1 square-cutoff bad budgets

This module converts the heterogeneous fixed-tree `ENNReal` fiber-law bound
into the real-valued exceptional budget consumed by the garden power
schedule.  At the cutoff `gamma = |g|^2`, the regular part is bounded by a
fixed coefficient times `|g|^2`.  A zero compact-complement mass, or an
explicit compact-tail bound of the same order, is absorbed into that
coefficient.

The result is conditional on the common scalar path encoded by
`ActualA1BranchingOccurrenceFiberFamily.realizes`, on the displayed compact
regularity domains, and on the genuine cumulative Jacobian lower bounds.
It does not derive those bounds from the random-mass law, and it proves no
good-set coupling powers, branching recollision decay, Markov closure, or
RPA renewal.
-/

namespace ArchonPhysics.PhyslibFPUTActualBranchingA1SquareCutoffBudget

open scoped BigOperators ENNReal

open Filter Topology
open ArchonPhysics
open ArchonPhysics.FiniteHistorySmallDenominatorUnionBound
open ArchonPhysics.PhyslibFPUTActualBranchingA1CompactSmallBall
open ArchonPhysics.PhyslibFPUTActualBranchingA1IntervalSelector
open ArchonPhysics.PhyslibFPUTArbitraryGardenCompactSmallBall
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTA1OrderedHistoryIntervalUnionBound
open ArchonPhysics.PhyslibFPUTExceptionalEventHigherOrderRPACriterion
open ArchonPhysics.PhyslibFPUTGardenPowerScheduleHigherOrderRPA
open ArchonPhysics.RandomEnsemble
open MeasureTheory Set

noncomputable section

/-- Real probability of the full fixed-tree branching near-denominator event
at the square coupling cutoff. -/
def actualA1BranchingSquareCutoffBadBudget
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (g : Real) : Real :=
  (massCoordinateLaw
    (actualA1BranchingSmallDenominatorEvent
      tree fiber (squareCouplingCutoff g))).toReal

/-- Real mass of the union of all occurrence-dependent compact exceptions. -/
def actualA1BranchingCompactTailBudget
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (K : ActualA1BranchingIntervalIndex tree → Set Real) : Real :=
  (massCoordinateLaw
    (actualA1BranchingOccurrenceCompactBadEvent tree K)).toReal

/-- The factorial-square `ENNReal` coefficient inherited from the finite
actual branching selector. -/
def actualA1BranchingFactorialSquareCoefficientENNReal
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (certificate : ∀ index : ActualA1BranchingIntervalIndex tree,
      OrdinaryGardenCoordinateCompactAtlas
        (actualA1BranchingOccurrenceFiberCoordinate tree fiber index)) :
    ENNReal :=
  (tree.shape.order.factorial *
      (tree.shape.order * tree.shape.order) : Nat) *
    actualA1BranchingCompactAtlasUniformBudget tree fiber certificate

/-- Real small-ball coefficient after substituting
`ENNReal.ofReal (2 * |g|^2)`. -/
def actualA1BranchingFactorialSquareRealCoefficient
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (certificate : ∀ index : ActualA1BranchingIntervalIndex tree,
      OrdinaryGardenCoordinateCompactAtlas
        (actualA1BranchingOccurrenceFiberCoordinate tree fiber index)) :
    Real :=
  2 *
    (actualA1BranchingFactorialSquareCoefficientENNReal
      tree fiber certificate).toReal

theorem ordinaryGardenCoordinateCompactAtlas_regularCoefficient_ne_top
    {coordinate : Real → Real}
    (certificate : OrdinaryGardenCoordinateCompactAtlas coordinate) :
    certificate.regularCoefficient ≠ ∞ := by
  have hjac : ENNReal.ofReal certificate.jacLower ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr certificate.jacLower_pos
  have hfiveHalf : (5 / 2 : ENNReal) ≠ ∞ :=
    ENNReal.div_ne_top (by simp) (by norm_num)
  exact ENNReal.mul_ne_top (by simp)
    (ENNReal.mul_ne_top hfiveHalf (ENNReal.inv_ne_top.mpr hjac))


theorem actualA1BranchingCompactAtlasUniformBudget_ne_top
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (certificate : ∀ index : ActualA1BranchingIntervalIndex tree,
      OrdinaryGardenCoordinateCompactAtlas
        (actualA1BranchingOccurrenceFiberCoordinate tree fiber index)) :
    actualA1BranchingCompactAtlasUniformBudget
      tree fiber certificate ≠ ∞ := by
  classical
  rw [← lt_top_iff_ne_top]
  unfold actualA1BranchingCompactAtlasUniformBudget
  rw [Finset.sup_lt_iff (by simp)]
  intro index _hindex
  exact (lt_top_iff_ne_top.mpr
    (ordinaryGardenCoordinateCompactAtlas_regularCoefficient_ne_top
      (certificate index)))

theorem actualA1BranchingFactorialSquareCoefficientENNReal_ne_top
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (certificate : ∀ index : ActualA1BranchingIntervalIndex tree,
      OrdinaryGardenCoordinateCompactAtlas
        (actualA1BranchingOccurrenceFiberCoordinate tree fiber index)) :
    actualA1BranchingFactorialSquareCoefficientENNReal
      tree fiber certificate ≠ ∞ := by
  unfold actualA1BranchingFactorialSquareCoefficientENNReal
  have hcount :
      ((tree.shape.order.factorial *
        (tree.shape.order * tree.shape.order) : Nat) : ENNReal) ≠ ∞ := by
    exact ENNReal.natCast_ne_top _
  exact ENNReal.mul_ne_top hcount
    (actualA1BranchingCompactAtlasUniformBudget_ne_top
      tree fiber certificate)

theorem actualA1BranchingSquareCutoffBadBudget_nonneg
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (g : Real) :
    0 ≤ actualA1BranchingSquareCutoffBadBudget tree fiber g :=
  ENNReal.toReal_nonneg

theorem actualA1BranchingCompactTailBudget_nonneg
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (K : ActualA1BranchingIntervalIndex tree → Set Real) :
    0 ≤ actualA1BranchingCompactTailBudget tree K :=
  ENNReal.toReal_nonneg

theorem actualA1BranchingFactorialSquareRealCoefficient_nonneg
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (certificate : ∀ index : ActualA1BranchingIntervalIndex tree,
      OrdinaryGardenCoordinateCompactAtlas
        (actualA1BranchingOccurrenceFiberCoordinate tree fiber index)) :
    0 ≤ actualA1BranchingFactorialSquareRealCoefficient
      tree fiber certificate := by
  unfold actualA1BranchingFactorialSquareRealCoefficient
  positivity

/-- Real-valued branching bound at the square cutoff.  The regular
coefficient contains the explicit order-factorial/order-squared selector
capacity.  The compact-complement probability remains a separate summand. -/
theorem actualA1BranchingSquareCutoffBadBudget_le_regular_add_tail
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (certificate : ∀ index : ActualA1BranchingIntervalIndex tree,
      OrdinaryGardenCoordinateCompactAtlas
        (actualA1BranchingOccurrenceFiberCoordinate tree fiber index))
    (K : ActualA1BranchingIntervalIndex tree → Set Real)
    (hcompact : ∀ index, (certificate index).compactSet = K index)
    (g : Real) :
    actualA1BranchingSquareCutoffBadBudget tree fiber g ≤
      actualA1BranchingFactorialSquareRealCoefficient
          tree fiber certificate * squareCouplingCutoff g +
        actualA1BranchingCompactTailBudget tree K := by
  have hmeasure :=
    measure_actualA1BranchingSmallDenominatorEvent_le_compactAtlas
      tree fiber certificate (squareCouplingCutoff g)
  have hbad :
      finiteCoordinateCompactAtlasBadEvent
          (actualA1BranchingOccurrenceFiberCoordinate tree fiber)
          certificate =
        actualA1BranchingOccurrenceCompactBadEvent tree K := by
    simp [finiteCoordinateCompactAtlasBadEvent,
      actualA1BranchingOccurrenceCompactBadEvent, hcompact]
  rw [hbad] at hmeasure
  have hcoefficient :
      finiteCoordinateCompactAtlasRegularCoefficient
          (actualA1BranchingOccurrenceFiberCoordinate tree fiber)
          certificate ≤
        actualA1BranchingFactorialSquareCoefficientENNReal
          tree fiber certificate := by
    simpa [actualA1BranchingFactorialSquareCoefficientENNReal] using
      actualA1BranchingCompactAtlasRegularCoefficient_le_factorial_sq
        tree fiber certificate
  have hmul :
      finiteCoordinateCompactAtlasRegularCoefficient
            (actualA1BranchingOccurrenceFiberCoordinate tree fiber)
            certificate *
          ENNReal.ofReal (2 * squareCouplingCutoff g) ≤
        actualA1BranchingFactorialSquareCoefficientENNReal
              tree fiber certificate *
            ENNReal.ofReal (2 * squareCouplingCutoff g) := by
    calc
      _ = ENNReal.ofReal (2 * squareCouplingCutoff g) *
          finiteCoordinateCompactAtlasRegularCoefficient
            (actualA1BranchingOccurrenceFiberCoordinate tree fiber)
            certificate := mul_comm _ _
      _ ≤ ENNReal.ofReal (2 * squareCouplingCutoff g) *
          actualA1BranchingFactorialSquareCoefficientENNReal
            tree fiber certificate :=
        mul_le_mul_right hcoefficient _
      _ = _ := mul_comm _ _
  have hENN :
      massCoordinateLaw
          (actualA1BranchingSmallDenominatorEvent tree fiber
            (squareCouplingCutoff g)) ≤
        actualA1BranchingFactorialSquareCoefficientENNReal
              tree fiber certificate *
            ENNReal.ofReal (2 * squareCouplingCutoff g) +
          massCoordinateLaw
            (actualA1BranchingOccurrenceCompactBadEvent tree K) :=
    hmeasure.trans (add_le_add hmul le_rfl)
  have hregularFinite :
      actualA1BranchingFactorialSquareCoefficientENNReal
            tree fiber certificate *
          ENNReal.ofReal (2 * squareCouplingCutoff g) ≠ ∞ :=
    ENNReal.mul_ne_top
      (actualA1BranchingFactorialSquareCoefficientENNReal_ne_top
        tree fiber certificate)
      ENNReal.ofReal_ne_top
  have htailFinite :
      massCoordinateLaw
          (actualA1BranchingOccurrenceCompactBadEvent tree K) ≠ ∞ :=
    measure_ne_top _ _
  have hupperFinite :
      actualA1BranchingFactorialSquareCoefficientENNReal
              tree fiber certificate *
            ENNReal.ofReal (2 * squareCouplingCutoff g) +
          massCoordinateLaw
            (actualA1BranchingOccurrenceCompactBadEvent tree K) ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hregularFinite, htailFinite⟩
  have htwoCutoff : 0 ≤ 2 * squareCouplingCutoff g := by
    unfold squareCouplingCutoff
    positivity
  have hreal := ENNReal.toReal_mono hupperFinite hENN
  rw [ENNReal.toReal_add hregularFinite htailFinite,
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal htwoCutoff] at hreal
  simpa [actualA1BranchingSquareCutoffBadBudget,
    actualA1BranchingCompactTailBudget,
    actualA1BranchingFactorialSquareRealCoefficient,
    mul_assoc, mul_left_comm, mul_comm] using hreal


/-- If the compact exception is null, the fixed-tree bad budget has exactly
the square-cutoff form consumed by the garden RPA closure. -/
theorem actualA1BranchingSquareCutoffBadBudget_le_of_compactTail_zero
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (certificate : ∀ index : ActualA1BranchingIntervalIndex tree,
      OrdinaryGardenCoordinateCompactAtlas
        (actualA1BranchingOccurrenceFiberCoordinate tree fiber index))
    (K : ActualA1BranchingIntervalIndex tree → Set Real)
    (hcompact : ∀ index, (certificate index).compactSet = K index)
    (htail :
      massCoordinateLaw
        (actualA1BranchingOccurrenceCompactBadEvent tree K) = 0)
    (g : Real) :
    actualA1BranchingSquareCutoffBadBudget tree fiber g ≤
      actualA1BranchingFactorialSquareRealCoefficient
        tree fiber certificate * squareCouplingCutoff g := by
  simpa [actualA1BranchingCompactTailBudget, htail] using
    actualA1BranchingSquareCutoffBadBudget_le_regular_add_tail
      tree fiber certificate K hcompact g

/-- A compact exception already controlled by B_tail times |g|^2 is absorbed
without changing the cutoff schedule. -/
theorem actualA1BranchingSquareCutoffBadBudget_le_of_compactTail
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (certificate : ∀ index : ActualA1BranchingIntervalIndex tree,
      OrdinaryGardenCoordinateCompactAtlas
        (actualA1BranchingOccurrenceFiberCoordinate tree fiber index))
    (K : ActualA1BranchingIntervalIndex tree → Set Real)
    (hcompact : ∀ index, (certificate index).compactSet = K index)
    (Btail g : Real)
    (htail : actualA1BranchingCompactTailBudget tree K ≤
      Btail * squareCouplingCutoff g) :
    actualA1BranchingSquareCutoffBadBudget tree fiber g ≤
      (actualA1BranchingFactorialSquareRealCoefficient
          tree fiber certificate + Btail) * squareCouplingCutoff g := by
  calc
    actualA1BranchingSquareCutoffBadBudget tree fiber g ≤
        actualA1BranchingFactorialSquareRealCoefficient
            tree fiber certificate * squareCouplingCutoff g +
          actualA1BranchingCompactTailBudget tree K :=
      actualA1BranchingSquareCutoffBadBudget_le_regular_add_tail
        tree fiber certificate K hcompact g
    _ ≤ actualA1BranchingFactorialSquareRealCoefficient
            tree fiber certificate * squareCouplingCutoff g +
          Btail * squareCouplingCutoff g :=
      add_le_add_right htail _
    _ = (actualA1BranchingFactorialSquareRealCoefficient
            tree fiber certificate + Btail) *
          squareCouplingCutoff g := by ring

/-- The actual cumulative-Jacobian hypotheses construct a certificate and a
real square-cutoff budget.  No transversality premise is discharged here. -/
theorem exists_actualA1BranchingSquareCutoffBadBudget_le_of_jacobian
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (K : ActualA1BranchingIntervalIndex tree → Set Real)
    (hK : ∀ index, IsCompact (K index))
    (hKregular : ∀ index second, second ∈ K index →
      (fiber.first index, second) ∈
        actualA1VertexIntervalDifferentiabilitySource
          (fiber.fixed index) (fiber.site₁ index) (fiber.site₂ index)
          ((randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).get
            index.1)
          index.2.toInterval)
    (j₀ : ActualA1BranchingIntervalIndex tree → Real)
    (hj₀ : ∀ index, 0 < j₀ index)
    (hjac : ∀ index second, second ∈ K index →
      j₀ index ≤
        |actualA1VertexIntervalVerticalJacobian
          (fiber.fixed index) (fiber.site₁ index) (fiber.site₂ index)
          ((randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).get
            index.1)
          index.2.toInterval (fiber.first index, second)|)
    (Btail g : Real)
    (htail : actualA1BranchingCompactTailBudget tree K ≤
      Btail * squareCouplingCutoff g) :
    ∃ certificate : ∀ index : ActualA1BranchingIntervalIndex tree,
        OrdinaryGardenCoordinateCompactAtlas
          (actualA1BranchingOccurrenceFiberCoordinate tree fiber index),
      (∀ index, (certificate index).compactSet = K index) ∧
      (∀ index, (certificate index).jacLower = j₀ index) ∧
      actualA1BranchingSquareCutoffBadBudget tree fiber g ≤
        (actualA1BranchingFactorialSquareRealCoefficient
            tree fiber certificate + Btail) * squareCouplingCutoff g := by
  obtain ⟨certificate, hcompact, hjacobian⟩ :=
    exists_actualA1BranchingOccurrenceCompactAtlasCertificates
      tree fiber K hK hKregular j₀ hj₀ hjac
  exact ⟨certificate, hcompact, hjacobian,
    actualA1BranchingSquareCutoffBadBudget_le_of_compactTail
      tree fiber certificate K hcompact Btail g htail⟩

/-- For a fixed finite tree and fixed atlas coefficient, the same bad-event
budget is o(|g|) in the quadratic channel and o(1) in the quartic channel.
A scale-dependent compact tail must be supplied explicitly. -/
theorem actualA1BranchingSquareCutoffBadBudget_quadratic_quartic_limits
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (certificate : ∀ index : ActualA1BranchingIntervalIndex tree,
      OrdinaryGardenCoordinateCompactAtlas
        (actualA1BranchingOccurrenceFiberCoordinate tree fiber index))
    (K : ActualA1BranchingIntervalIndex tree → Set Real)
    (hcompact : ∀ index, (certificate index).compactSet = K index)
    (g : Nat → Real)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : ∀ n, g n ≠ 0)
    (Btail : Real)
    (htail : ∀ n, actualA1BranchingCompactTailBudget tree K ≤
      Btail * squareCouplingCutoff (g n)) :
    Tendsto (fun n =>
        actualA1BranchingSquareCutoffBadBudget tree fiber (g n) /
          |g n|) atTop (nhds 0) ∧
      Tendsto (fun n =>
        actualA1BranchingSquareCutoffBadBudget tree fiber (g n))
          atTop (nhds 0) := by
  let bad : Nat → Real := fun n =>
    actualA1BranchingSquareCutoffBadBudget tree fiber (g n)
  have hbad0 : ∀ n, 0 ≤ bad n := by
    intro n
    exact actualA1BranchingSquareCutoffBadBudget_nonneg
      tree fiber (g n)
  have hsmall : ∀ n, bad n ≤
      (actualA1BranchingFactorialSquareRealCoefficient
          tree fiber certificate + Btail) *
        squareCouplingCutoff (g n) := by
    intro n
    exact actualA1BranchingSquareCutoffBadBudget_le_of_compactTail
      tree fiber certificate K hcompact Btail (g n) (htail n)
  have hquadratic :
      Tendsto (fun n => bad n / |g n|) atTop (nhds 0) :=
    badBudget_div_abs_tendsto_zero_of_linearSmallBall
      g (fun n => squareCouplingCutoff (g n)) bad
      (actualA1BranchingFactorialSquareRealCoefficient
        tree fiber certificate + Btail)
      hbad0 hsmall
      (squareCouplingCutoff_div_abs_tendsto_zero g hg hg0)
  have hquartic : Tendsto bad atTop (nhds 0) :=
    badBudget_tendsto_zero_of_linearSmallBall
      (fun n => squareCouplingCutoff (g n)) bad
      (actualA1BranchingFactorialSquareRealCoefficient
        tree fiber certificate + Btail)
      hbad0 hsmall (squareCouplingCutoff_tendsto_zero g hg)
  exact ⟨by simpa only [bad] using hquadratic,
    by simpa only [bad] using hquartic⟩

/-- Direct explicit endpoint from the genuine per-occurrence cumulative
Jacobian bounds.  The returned pointwise estimate has the precise form needed
for both bad-budget arguments of the actual finite coercive ordered-cluster
square-cutoff theorem.  It does not supply the separate good-garden or
recollision bounds. -/
theorem exists_actualA1BranchingSquareCutoffBudget_and_limits_of_jacobian
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (K : ActualA1BranchingIntervalIndex tree → Set Real)
    (hK : ∀ index, IsCompact (K index))
    (hKregular : ∀ index second, second ∈ K index →
      (fiber.first index, second) ∈
        actualA1VertexIntervalDifferentiabilitySource
          (fiber.fixed index) (fiber.site₁ index) (fiber.site₂ index)
          ((randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).get
            index.1)
          index.2.toInterval)
    (j₀ : ActualA1BranchingIntervalIndex tree → Real)
    (hj₀ : ∀ index, 0 < j₀ index)
    (hjac : ∀ index second, second ∈ K index →
      j₀ index ≤
        |actualA1VertexIntervalVerticalJacobian
          (fiber.fixed index) (fiber.site₁ index) (fiber.site₂ index)
          ((randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).get
            index.1)
          index.2.toInterval (fiber.first index, second)|)
    (g : Nat → Real)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : ∀ n, g n ≠ 0)
    (Btail : Real)
    (htail : ∀ n, actualA1BranchingCompactTailBudget tree K ≤
      Btail * squareCouplingCutoff (g n)) :
    ∃ certificate : ∀ index : ActualA1BranchingIntervalIndex tree,
        OrdinaryGardenCoordinateCompactAtlas
          (actualA1BranchingOccurrenceFiberCoordinate tree fiber index),
      (∀ index, (certificate index).compactSet = K index) ∧
      (∀ index, (certificate index).jacLower = j₀ index) ∧
      (∀ n, actualA1BranchingSquareCutoffBadBudget tree fiber (g n) ≤
        (actualA1BranchingFactorialSquareRealCoefficient
            tree fiber certificate + Btail) *
          squareCouplingCutoff (g n)) ∧
      Tendsto (fun n =>
        actualA1BranchingSquareCutoffBadBudget tree fiber (g n) /
          |g n|) atTop (nhds 0) ∧
      Tendsto (fun n =>
        actualA1BranchingSquareCutoffBadBudget tree fiber (g n))
          atTop (nhds 0) := by
  obtain ⟨certificate, hcompact, hjacobian⟩ :=
    exists_actualA1BranchingOccurrenceCompactAtlasCertificates
      tree fiber K hK hKregular j₀ hj₀ hjac
  have hsmall : ∀ n,
      actualA1BranchingSquareCutoffBadBudget tree fiber (g n) ≤
        (actualA1BranchingFactorialSquareRealCoefficient
            tree fiber certificate + Btail) *
          squareCouplingCutoff (g n) := by
    intro n
    exact actualA1BranchingSquareCutoffBadBudget_le_of_compactTail
      tree fiber certificate K hcompact Btail (g n) (htail n)
  obtain ⟨hquadratic, hquartic⟩ :=
    actualA1BranchingSquareCutoffBadBudget_quadratic_quartic_limits
      tree fiber certificate K hcompact g hg hg0 Btail htail
  exact ⟨certificate, hcompact, hjacobian, hsmall,
    hquadratic, hquartic⟩

end

end ArchonPhysics.PhyslibFPUTActualBranchingA1SquareCutoffBudget
