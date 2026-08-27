import ArchonPhysics.MeasurableOrderedModeCoupling

/-!
# Exact spectral-kernel factorization of summed interaction weights

The interaction vertex is indexed by several ordered modes.  Summing its
basis-free square against a product of one-leg weights factors exactly into a
product of weighted projected-bond kernels.  This is a finite Fubini identity:
it makes no simplicity, randomness, asymptotic, or kinetic-limit assumption.

The identity is useful for grounding collision measures because it replaces
an explicit sum over eigenvector triples by one-leg spectral projector kernels,
which can subsequently be estimated using resolvents, transfer matrices, or
integrated-density-of-states results.
-/

open scoped Matrix

namespace ArchonPhysics.OrderedInteractionSpectralFactorization

open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedSpectrum

noncomputable section

variable {iota bond : Type*}
variable [Fintype iota] [DecidableEq iota] [Fintype bond]

/-- Algebraic engine: finite mode Fubini plus distributivity of products over
sums.  Keeping it independent of spectral definitions makes the exact input
to the projector factorization explicit. -/
private theorem sum_doubleSum_prod_mul_prod
    {mode leg left right : Type*}
    [Fintype mode] [Fintype leg] [DecidableEq leg]
    [Fintype left] [Fintype right]
    (kernel : leg → mode → left → right → Real)
    (weight : leg → mode → Real) :
    (∑ modes : leg → mode,
        (∑ j, ∑ l, ∏ r, kernel r (modes r) j l) *
          ∏ r, weight r (modes r)) =
      ∑ j, ∑ l, ∏ r, ∑ k, weight r k * kernel r k j l := by
  calc
    (∑ modes : leg → mode,
        (∑ j, ∑ l, ∏ r, kernel r (modes r) j l) *
          ∏ r, weight r (modes r)) =
        ∑ modes : leg → mode, ∑ j, ∑ l,
          ∏ r, weight r (modes r) * kernel r (modes r) j l := by
      apply Finset.sum_congr rfl
      intro modes _hmodes
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _hl
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro r _hr
      exact mul_comm _ _
    _ = ∑ j, ∑ l, ∑ modes : leg → mode,
          ∏ r, weight r (modes r) * kernel r (modes r) j l := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.sum_comm]
    _ = ∑ j, ∑ l, ∏ r, ∑ k, weight r k * kernel r k j l := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro l _hl
      rw [Fintype.prod_sum]

/-- One-leg spectral projector kernel, weighted by an arbitrary scalar
function of the ordered mode. -/
def weightedProjectedBondKernel (B : Matrix bond iota Real)
    (A : HermitianMatrix iota)
    (weight : Fin (Fintype.card iota) → Real) : Matrix bond bond Real :=
  fun j l ↦ ∑ k, weight k * projectedBondKernel B A k j l

/-- Total order-`n` interaction moment against a product of one-leg weights. -/
def weightedInteractionMoment {n : Nat} (B : Matrix bond iota Real)
    (A : HermitianMatrix iota)
    (weight : Fin n → Fin (Fintype.card iota) → Real) : Real :=
  ∑ modes, orderedInteractionWeightSq B A modes * ∏ r, weight r (modes r)

/-- Exact factorization of a summed interaction moment into weighted one-leg
projector kernels.  In particular, no individual eigenvector choice appears
on the right-hand side. -/
theorem weightedInteractionMoment_eq_projectedKernelProduct {n : Nat}
    (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (weight : Fin n → Fin (Fintype.card iota) → Real) :
    weightedInteractionMoment B A weight =
      ∑ j, ∑ l, ∏ r, weightedProjectedBondKernel B A (weight r) j l := by
  unfold weightedInteractionMoment orderedInteractionWeightSq
    weightedProjectedBondKernel
  exact sum_doubleSum_prod_mul_prod
    (kernel := fun _r k j l ↦ projectedBondKernel B A k j l) weight

namespace Harmonic

open ArchonPhysics
open ArchonPhysics.ModeCoupling
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic

/-- The exact weighted interaction moment for one random-mass harmonic
realization, expressed without an eigenvector frame. -/
def harmonicWeightedInteractionMoment {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (weight : Fin n → Fin (Fintype.card (Lattice.Site N)) → Real) : Real :=
  weightedInteractionMoment (massWeightedDifferenceMatrix m)
    (harmonicHermitian m) weight

/-- Random-mass harmonic specialization of the exact factorization. -/
theorem harmonicWeightedInteractionMoment_eq_projectedKernelProduct
    {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (weight : Fin n → Fin (Fintype.card (Lattice.Site N)) → Real) :
    harmonicWeightedInteractionMoment m weight =
      ∑ j, ∑ l, ∏ r,
        weightedProjectedBondKernel (massWeightedDifferenceMatrix m)
          (harmonicHermitian m) (weight r) j l :=
  weightedInteractionMoment_eq_projectedKernelProduct _ _ weight

end Harmonic

end


end ArchonPhysics.OrderedInteractionSpectralFactorization
