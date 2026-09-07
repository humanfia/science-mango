import Family8Grounding.Family8FrozenNeighborhoodAssemblyV1

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal

namespace Family8FrozenAssemblyImmediateJointP1P5V1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8ComparableMultiplicityBucketsV1
open Family8FrozenNeighborhoodAssemblyV1

noncomputable section

/-!
# Immediate P1--P5 consequences of a frozen assembly

This file records only the five pointwise and mass consequences already
carried by one `Family8FrozenNeighborhoodAssemblyV1.Assembly`.

Despite the name `ImmediateJointP1P5`, this is **not** a cellular joint
factoring theorem.  In particular, the structure below contains no spatial
cell family, no labelled parent--cell edge set, no positive edge weights, and
no whole-incidence retention or lifting statement.  It therefore cannot
replace a repaired cellular factoring construction.  Its purpose is to make
the exact strength of the existing frozen-assembly API explicit.
-/

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {W : ConvexFamily kappa}
  {P : ConvexFactorization F W} {Y : Shading F} {r : Real}

/-- The immediate mass, cover, two multiplicity-band, and product conclusions
of one frozen assembly.

The retained mass is relative to the active fine restriction stored in `P`,
not automatically to all of `Y`.  The two positive bands are stated only on
their respective unions, where positivity rules out the zero branch of
`ZeroOrComparable` without any global mass-positivity assumption. -/
structure ImmediateJointP1P5
    (A : Assembly P Y r) : Prop where
  activeFine_retained : WithinFactor A.loss
    (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass
    A.refinement.shading.shadingMass
  child_point_mem_frozenParent : forall i x,
    x ∈ A.refinement.shading.carrier i ->
      x ∈ A.frozenCoarse.carrier (P.index.parent i)
  fiber_band : forall k, k ∈ P.index.coarse -> forall x,
    x ∈ P.fiberShadedUnion A.refinement.shading k ->
      0 < comparableBase A.fiberLabel ∧
        comparableBase A.fiberLabel <=
          P.fiberMultiplicity A.refinement.shading k x ∧
        P.fiberMultiplicity A.refinement.shading k x <
          2 * comparableBase A.fiberLabel
  frozenOuter_band : forall x, x ∈ A.frozenCoarse.shadedUnion ->
    0 < comparableBase A.outerLabel ∧
      comparableBase A.outerLabel <= A.frozenCoarse.pointMultiplicity x ∧
      A.frozenCoarse.pointMultiplicity x <
        2 * comparableBase A.outerLabel
  pointMultiplicity_le_four_mul_bases : forall x,
    A.refinement.shading.pointMultiplicity x <=
      4 * comparableBase A.outerLabel * comparableBase A.fiberLabel

private theorem positiveBand_of_zeroOrComparable
    {B n : Nat} (hn : 0 < n) (h : ZeroOrComparable B n) :
    0 < B ∧ B <= n ∧ n < 2 * B := by
  rcases h with hzero | hpositive
  · exact (Nat.ne_of_gt hn hzero.2).elim
  · exact hpositive

/-- Every existing frozen assembly supplies the immediate P1--P5 package.

No positivity of the total shading mass is needed: membership in a fiber or
coarse shaded union gives the local positive multiplicity required to exclude
the zero bucket. -/
theorem immediateJointP1P5_of_assembly (A : Assembly P Y r) :
    ImmediateJointP1P5 A := by
  refine {
    activeFine_retained := A.retained
    child_point_mem_frozenParent := A.covers
    fiber_band := ?_
    frozenOuter_band := ?_
    pointMultiplicity_le_four_mul_bases := ?_ }
  · intro k hk x hx
    have hxInduced :
        x ∈ (P.inducedShading A.refinement.shading).carrier k := by
      rw [P.inducedShading_carrier_eq_fiberShadedUnion]
      exact hx
    have hpositive :
        0 < P.fiberMultiplicity A.refinement.shading k x :=
      (P.mem_inducedShading_iff_fiberMultiplicity_pos
        A.refinement.shading k x).1 hxInduced
    exact positiveBand_of_zeroOrComparable hpositive
      (A.fiber_comparable k hk x hx)
  · intro x hx
    have hpositive : 0 < A.frozenCoarse.pointMultiplicity x :=
      (A.frozenCoarse.pointMultiplicity_pos_iff_mem_shadedUnion x).2 hx
    exact positiveBand_of_zeroOrComparable hpositive
      (A.outer_comparable x hx)
  · intro x
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      A.pointMultiplicity_le_comparableProduct x

#print axioms ImmediateJointP1P5
#print axioms immediateJointP1P5_of_assembly

end

end Family8FrozenAssemblyImmediateJointP1P5V1
