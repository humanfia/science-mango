import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# Finite Boolean unit-twist cancellation

This file isolates the finite algebra behind a Boolean family of commuting
unit twists.  A finite set `twists` indexes the hypercube `twists.powerset`.
When `twists` is nonempty, an alternating main term with sign
`(-1) ^ chosen.card` cancels exactly over the whole hypercube.

More generally, if every contribution is an alternating main term plus a
displayed residual, the coherent hypercube sum is exactly the sum of those
residuals.  Its norm is therefore bounded by the sum of residual norms (or
by any supplied residual majorant).

This is only a model-independent finite-sum lemma.  It does **not** prove
that an FPUT diagram class is a Boolean orbit, that physical unit twists
commute, or that an actual diagram contribution obeys the required
alternating decomposition.  Those are separate model-specific obligations.
-/

namespace ArchonPhysics.FiniteUnitTwistHypercubeCancellation

open scoped BigOperators

noncomputable section

variable {Twist Value : Type*}

/-- The parity sign attached to a vertex of the Boolean twist hypercube. -/
def unitTwistParitySign (chosen : Finset Twist) : Int :=
  (-1 : Int) ^ chosen.card

/-- The coherent sum over all subsets of a finite admissible twist set. -/
def unitTwistHypercubeSum [AddCommMonoid Value]
    (twists : Finset Twist) (contribution : Finset Twist -> Value) : Value :=
  ∑ chosen ∈ twists.powerset, contribution chosen

/-- A fixed main value decorated by Boolean parity. -/
def unitTwistAlternatingMain [AddCommGroup Value]
    (main : Value) (chosen : Finset Twist) : Value :=
  unitTwistParitySign chosen • main

/-- Every nontrivial Boolean twist hypercube has zero alternating main sum.
This is the exact finite cancellation supplied by
`Finset.sum_powerset_neg_one_pow_card_of_nonempty`. -/
theorem unitTwistHypercubeSum_alternatingMain_eq_zero [AddCommGroup Value]
    (twists : Finset Twist) (main : Value) (htwists : twists.Nonempty) :
    unitTwistHypercubeSum twists (unitTwistAlternatingMain main) = 0 := by
  classical
  unfold unitTwistHypercubeSum unitTwistAlternatingMain unitTwistParitySign
  rw [← Finset.sum_smul]
  rw [Finset.sum_powerset_neg_one_pow_card_of_nonempty htwists]
  simp

/-- If every vertex contribution is an alternating main term plus a
residual, exact cancellation leaves precisely the coherent residual sum. -/
theorem unitTwistHypercubeSum_eq_residualSum_of_decomposition
    [AddCommGroup Value]
    (twists : Finset Twist) (contribution residual : Finset Twist -> Value)
    (main : Value) (htwists : twists.Nonempty)
    (hdecomposition : forall chosen, chosen ∈ twists.powerset ->
      contribution chosen = unitTwistAlternatingMain main chosen + residual chosen) :
    unitTwistHypercubeSum twists contribution =
      unitTwistHypercubeSum twists residual := by
  classical
  rw [unitTwistHypercubeSum]
  calc
    ∑ chosen ∈ twists.powerset, contribution chosen =
        (∑ chosen ∈ twists.powerset,
          unitTwistAlternatingMain main chosen) +
        ∑ chosen ∈ twists.powerset, residual chosen := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun chosen hchosen =>
        hdecomposition chosen hchosen
    _ = ∑ chosen ∈ twists.powerset, residual chosen := by
      rw [← unitTwistHypercubeSum]
      rw [unitTwistHypercubeSum_alternatingMain_eq_zero twists main htwists]
      simp

/-- The norm of a coherently cancelled twist class is controlled by the
residuals, not by the absolute sum of its alternating main terms. -/
theorem norm_unitTwistHypercubeSum_le_sum_norm_residual
    [NormedAddCommGroup Value]
    (twists : Finset Twist) (contribution residual : Finset Twist -> Value)
    (main : Value) (htwists : twists.Nonempty)
    (hdecomposition : forall chosen, chosen ∈ twists.powerset ->
      contribution chosen = unitTwistAlternatingMain main chosen + residual chosen) :
    ‖unitTwistHypercubeSum twists contribution‖ <=
      ∑ chosen ∈ twists.powerset, ‖residual chosen‖ := by
  rw [unitTwistHypercubeSum_eq_residualSum_of_decomposition
    twists contribution residual main htwists hdecomposition]
  exact norm_sum_le _ _

/-- A pointwise residual majorant gives a scalar bound on the whole
coherent twist class.  The model-specific analytic burden is explicit in
`hresidual`; the Boolean algebra alone supplies no such estimate. -/
theorem norm_unitTwistHypercubeSum_le_sum_residualMajorant
    [NormedAddCommGroup Value]
    (twists : Finset Twist) (contribution residual : Finset Twist -> Value)
    (main : Value) (residualMajorant : Finset Twist -> Real)
    (htwists : twists.Nonempty)
    (hdecomposition : forall chosen, chosen ∈ twists.powerset ->
      contribution chosen = unitTwistAlternatingMain main chosen + residual chosen)
    (hresidual : forall chosen, chosen ∈ twists.powerset ->
      ‖residual chosen‖ <= residualMajorant chosen) :
    ‖unitTwistHypercubeSum twists contribution‖ <=
      ∑ chosen ∈ twists.powerset, residualMajorant chosen := by
  exact (norm_unitTwistHypercubeSum_le_sum_norm_residual
    twists contribution residual main htwists hdecomposition).trans
      (Finset.sum_le_sum fun chosen hchosen => hresidual chosen hchosen)

/-- The product contribution attached to one Boolean vertex.  A selected
twist uses the `b` factor and contributes one minus sign; an unselected
twist uses the `a` factor. -/
def unitTwistAlternatingProductTerm {R : Type*} [CommRing R]
    [DecidableEq Twist]
    (twists : Finset Twist) (a b : Twist -> R)
    (chosen : Finset Twist) : R :=
  (-1 : R) ^ chosen.card *
    (∏ twist ∈ twists \ chosen, a twist) *
      ∏ twist ∈ chosen, b twist

/-- Boolean inclusion--exclusion turns the complete twist-class sum into
a product of finite differences.  This is the algebraic form of the gain
available when every admissible twist flips one smooth factor. -/
theorem unitTwistHypercubeSum_alternatingProduct_eq_prod_sub
    {R : Type*} [CommRing R] [DecidableEq Twist]
    (twists : Finset Twist) (a b : Twist -> R) :
    unitTwistHypercubeSum twists
        (unitTwistAlternatingProductTerm twists a b) =
      ∏ twist ∈ twists, (a twist - b twist) := by
  classical
  simpa [unitTwistHypercubeSum, unitTwistAlternatingProductTerm] using
    (Finset.prod_sub a b twists).symm

/-- The product-difference identity converts the coherent Boolean sum into
a multiplicative norm gain.  It still requires a model-specific theorem
identifying actual diagram factors with `a` and `b`. -/
theorem norm_unitTwistHypercubeSum_alternatingProduct_le
    {R : Type*} [NormedCommRing R] [NormOneClass R] [DecidableEq Twist]
    (twists : Finset Twist) (a b : Twist -> R) :
    ‖unitTwistHypercubeSum twists
        (unitTwistAlternatingProductTerm twists a b)‖ <=
      ∏ twist ∈ twists, ‖a twist - b twist‖ := by
  rw [unitTwistHypercubeSum_alternatingProduct_eq_prod_sub]
  exact Finset.norm_prod_le twists fun twist => a twist - b twist

end

end ArchonPhysics.FiniteUnitTwistHypercubeCancellation
