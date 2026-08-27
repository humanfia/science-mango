import ArchonPhysics.ComplexPolynomialMarkedLegWindowStrongLaw
import ArchonPhysics.PeriodicPolynomialWindowRowSum

/-!
# Complex periodic polynomial-window row sums

Each large periodic leg is the complex combination of one cosine polynomial
kernel and one sine polynomial kernel.  The real exact window bridge is
applied separately to those two components and then combined leg by leg.
No expansion of the three-leg product into eight real summands is used.
-/

namespace ArchonPhysics.ComplexPeriodicPolynomialWindowRowSum

open ArchonPhysics
open ArchonPhysics.ComplexPolynomialMarkedLegWindowStrongLaw
open ArchonPhysics.PeriodicPolynomialWindowGeometricInterior
open ArchonPhysics.PeriodicPolynomialWindowReindex
open ArchonPhysics.PeriodicPolynomialWindowRowSum
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.PolynomialMarkedLegWindowStrongLaw
open ArchonPhysics.RegularizedMarkedLegPolynomialLocality

noncomputable section

/-- One complex polynomial leg of a finite periodic mass sample. -/
def complexPeriodicPolynomialLeg {N : Nat} [NeZero N]
    (x : Fin N → Real)
    (cosineDegree sineDegree : Nat)
    (cosineCoefficient sineCoefficient : Nat → Real)
    (i j : Fin N) : Complex :=
  (zeroConstantMatrixPolynomialUpTo cosineDegree cosineCoefficient
      (finWeightedCycleLaplacian (inverseClippedWindow x)) i j : Complex) +
    (zeroConstantMatrixPolynomialUpTo sineDegree sineCoefficient
      (finWeightedCycleLaplacian (inverseClippedWindow x)) i j : Complex) *
      Complex.I

/-- Every complex leg vanishes on a column of the translated-window
complement.  Both its cosine and sine components vanish there. -/
theorem complexPeriodicPolynomialLeg_eq_zero_on_centeredWindowComplement
    {m windowRadius : Nat} [NeZero m]
    (x : Fin ((2 * windowRadius + 1) + m) → Real)
    (target : Fin ((2 * windowRadius + 1) + m))
    (cosineDegree sineDegree : Nat)
    (cosineCoefficient sineCoefficient : Nat → Real)
    (hcosine : cosineDegree + 1 ≤ windowRadius)
    (hsine : sineDegree + 1 ≤ windowRadius)
    (j : Fin m) :
    let centerBig := Fin.castAdd m (centeredWindowIndex windowRadius)
    let shift := finCenteringShift centerBig target
    complexPeriodicPolynomialLeg x
      cosineDegree sineDegree cosineCoefficient sineCoefficient target
      (translatedSplitEquiv shift (Sum.inr j)) = 0 := by
  dsimp only
  unfold complexPeriodicPolynomialLeg
  rw [polynomialKernelEntry_eq_zero_on_centeredWindowComplement
      (inverseClippedWindow x) target cosineDegree cosineCoefficient hcosine j,
    polynomialKernelEntry_eq_zero_on_centeredWindowComplement
      (inverseClippedWindow x) target sineDegree sineCoefficient hsine j]
  simp

/-- At one translated-window column, a large periodic complex leg equals the
corresponding fixed-window complex leg. -/
theorem complexPeriodicPolynomialLeg_eq_centeredWindowLeg
    {m windowRadius : Nat} [NeZero m]
    (x : Fin ((2 * windowRadius + 1) + m) → Real)
    (target : Fin ((2 * windowRadius + 1) + m))
    (cosineDegree sineDegree : Nat)
    (cosineCoefficient sineCoefficient : Nat → Real)
    (hcosine : cosineDegree + 1 ≤ windowRadius)
    (hsine : sineDegree + 1 ≤ windowRadius)
    (b : Fin (2 * windowRadius + 1)) :
    let center := centeredWindowIndex windowRadius
    let centerBig := Fin.castAdd m center
    let shift := finCenteringShift centerBig target
    complexPeriodicPolynomialLeg x
        cosineDegree sineDegree cosineCoefficient sineCoefficient target
        (translatedSplitEquiv shift (Sum.inl b)) =
      (polynomialWindowKernelEntry cosineDegree cosineCoefficient center b
          (translatedMassWindow x shift) : Complex) +
        (polynomialWindowKernelEntry sineDegree sineCoefficient center b
          (translatedMassWindow x shift) : Complex) * Complex.I := by
  dsimp only
  unfold complexPeriodicPolynomialLeg
  simp only [translatedSplitEquiv_apply_inl]
  rw [periodicPolynomialKernelEntry_eq_centeredMassWindow_atSite
      x target cosineDegree cosineCoefficient hcosine b,
    periodicPolynomialKernelEntry_eq_centeredMassWindow_atSite
      x target sineDegree sineCoefficient hsine b]

/-- The product of three complex periodic legs at one translated-window
column equals the existing complex local observable, with one shared `b`. -/
theorem complexThreeLegPeriodicPolynomialProduct_eq_centeredWindowProduct
    {m windowRadius : Nat} [NeZero m]
    (x : Fin ((2 * windowRadius + 1) + m) → Real)
    (target : Fin ((2 * windowRadius + 1) + m))
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real)
    (hcosine : ∀ r, cosineDegree r + 1 ≤ windowRadius)
    (hsine : ∀ r, sineDegree r + 1 ≤ windowRadius)
    (b : Fin (2 * windowRadius + 1)) :
    let center := centeredWindowIndex windowRadius
    let centerBig := Fin.castAdd m center
    let shift := finCenteringShift centerBig target
    (∏ r : Fin 3,
      complexPeriodicPolynomialLeg x
        (cosineDegree r) (sineDegree r)
        (cosineCoefficient r) (sineCoefficient r) target
        (translatedSplitEquiv shift (Sum.inl b))) =
      complexThreeLegPolynomialWindowProduct
        cosineDegree sineDegree cosineCoefficient sineCoefficient
        (fun _ ↦ center) (fun _ ↦ b) (translatedMassWindow x shift) := by
  dsimp only
  unfold complexThreeLegPolynomialWindowProduct
  apply Finset.prod_congr rfl
  intro r _hr
  exact complexPeriodicPolynomialLeg_eq_centeredWindowLeg
    x target (cosineDegree r) (sineDegree r)
    (cosineCoefficient r) (sineCoefficient r)
    (hcosine r) (hsine r) b

/-- Exact complex row-sum reduction.  The same translated-window endpoint
`b` is used by all three complex legs. -/
theorem complexThreeLegPeriodicPolynomialRowSum_eq_centeredWindowSum
    {m windowRadius : Nat} [NeZero m]
    (x : Fin ((2 * windowRadius + 1) + m) → Real)
    (target : Fin ((2 * windowRadius + 1) + m))
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real)
    (hcosine : ∀ r, cosineDegree r + 1 ≤ windowRadius)
    (hsine : ∀ r, sineDegree r + 1 ≤ windowRadius) :
    let center := centeredWindowIndex windowRadius
    let centerBig := Fin.castAdd m center
    let shift := finCenteringShift centerBig target
    (∑ l : Fin ((2 * windowRadius + 1) + m),
      ∏ r : Fin 3,
        complexPeriodicPolynomialLeg x
          (cosineDegree r) (sineDegree r)
          (cosineCoefficient r) (sineCoefficient r) target l) =
      ∑ b : Fin (2 * windowRadius + 1),
        complexThreeLegPolynomialWindowProduct
          cosineDegree sineDegree cosineCoefficient sineCoefficient
          (fun _ ↦ center) (fun _ ↦ b)
          (translatedMassWindow x shift) := by
  dsimp only
  let shift := finCenteringShift
    (Fin.castAdd m (centeredWindowIndex windowRadius)) target
  let F : Fin ((2 * windowRadius + 1) + m) → Complex := fun l ↦
    ∏ r : Fin 3,
      complexPeriodicPolynomialLeg x
        (cosineDegree r) (sineDegree r)
        (cosineCoefficient r) (sineCoefficient r) target l
  calc
    (∑ l, F l) =
        ∑ u : Fin (2 * windowRadius + 1) ⊕ Fin m,
          F (translatedSplitEquiv shift u) := by
      exact (Equiv.sum_comp (translatedSplitEquiv shift) F).symm
    _ = (∑ b : Fin (2 * windowRadius + 1),
          F (translatedSplitEquiv shift (Sum.inl b))) +
        ∑ j : Fin m, F (translatedSplitEquiv shift (Sum.inr j)) := by
      exact Fintype.sum_sum_type _
    _ = (∑ b : Fin (2 * windowRadius + 1),
          complexThreeLegPolynomialWindowProduct
            cosineDegree sineDegree cosineCoefficient sineCoefficient
            (fun _ ↦ centeredWindowIndex windowRadius) (fun _ ↦ b)
            (translatedMassWindow x shift)) + 0 := by
      congr 1
      · apply Finset.sum_congr rfl
        intro b _hb
        exact
          complexThreeLegPeriodicPolynomialProduct_eq_centeredWindowProduct
            x target cosineDegree sineDegree
            cosineCoefficient sineCoefficient hcosine hsine b
      · apply Finset.sum_eq_zero
        intro j _hj
        unfold F
        have hzero (r : Fin 3) :
            complexPeriodicPolynomialLeg x
                (cosineDegree r) (sineDegree r)
                (cosineCoefficient r) (sineCoefficient r) target
                (translatedSplitEquiv shift (Sum.inr j)) = 0 := by
          exact complexPeriodicPolynomialLeg_eq_zero_on_centeredWindowComplement
            x target (cosineDegree r) (sineDegree r)
              (cosineCoefficient r) (sineCoefficient r)
              (hcosine r) (hsine r) j
        simp_rw [hzero]
        simp
    _ = ∑ b : Fin (2 * windowRadius + 1),
          complexThreeLegPolynomialWindowProduct
            cosineDegree sineDegree cosineCoefficient sineCoefficient
            (fun _ ↦ centeredWindowIndex windowRadius) (fun _ ↦ b)
            (translatedMassWindow x shift) := by
      rw [add_zero]

end
end ArchonPhysics.ComplexPeriodicPolynomialWindowRowSum
