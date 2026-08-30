import Mathlib.Algebra.MvPolynomial.PDeriv
import ArchonPhysics.FiniteExactDecayResonanceObstruction
import ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet

/-!
# Canonical characteristic-Jacobian resultant on a two-mass fiber

For a fixed finite random-mass background and two varied sites, this file
restricts the universal weighted-cycle characteristic polynomial to the two
inverse-mass variables `x` and `y` and removes its deterministic acoustic
factor `E`.  If the resulting positive-spectrum polynomial is denoted by
`P⁺(E,x,y)`, its canonical vertical critical-point eliminant is

`Res_E(P⁺, partial_y P⁺)`.

The reduction by `divX` is essential: the full characteristic polynomial is
always `E * P⁺`, hence its mass partial is `E * partial_y P⁺`.  The naive
full resultant therefore has the common acoustic root `E = 0` identically
and is the zero polynomial.  It cannot certify a non-acoustic ordinary
channel.  Only the reduced positive-spectrum resultant is named canonical
below, and specialization through `divX` is proved explicitly.

The resultant is taken with the symbolic degrees before specialization, so
evaluation remains functorial even when `partial_y P` loses degree at an
individual mass pair.  No nonvanishing claim is built into the definition.
-/

namespace ArchonPhysics.CanonicalPairCharacteristicJacobianResultant

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.FiniteExactDecayResonanceObstruction
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedCycleBridge
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassResultantBridge
open ArchonPhysics.TwoParameterSpectralPolynomialAvoidance
open Filter Set

noncomputable section

/-- The substitution homomorphism which freezes all inverse masses except the
two selected coordinates. -/
def twoSiteCharacteristicSliceHom
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) :
    MvPolynomial (Fin N) Real →+* MvPolynomial (Fin 2) Real :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (twoSiteRepeatedRootSliceSubstitution fixed site₁ site₂)

/-- The weighted-cycle matrix with entries in `Real[x,y]` on the selected
two-inverse-mass slice. -/
def twoSiteSymbolicWeightedCycleLaplacian
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) :
    Matrix (Lattice.Site N) (Lattice.Site N)
      (MvPolynomial (Fin 2) Real) :=
  (symbolicWeightedCycleLaplacian (N := N)).map
    (twoSiteCharacteristicSliceHom fixed site₁ site₂)

/-- `P⁺(E,x,y)`: the canonical two-inverse-mass positive-spectrum
characteristic polynomial, with the persistent acoustic factor removed. -/
def twoSitePositiveCharacteristicPolynomial
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) :
    Polynomial (MvPolynomial (Fin 2) Real) :=
  (twoSiteSymbolicWeightedCycleLaplacian fixed site₁ site₂).charpoly.divX

/-- Turn a polynomial in `E` with coefficients in `Real[x,y]` into one
multivariate polynomial whose `none` variable is `E`. -/
def energyMassPolynomial
    (p : Polynomial (MvPolynomial (Fin 2) Real)) :
    MvPolynomial (Option (Fin 2)) Real :=
  (MvPolynomial.optionEquivLeft Real (Fin 2)).symm p

/-- Coefficientwise partial derivative in the second inverse-mass variable.
The `Option` presentation makes this an ordinary `MvPolynomial.pderiv` while
leaving the energy variable untouched. -/
def verticalMassPartial
    (p : Polynomial (MvPolynomial (Fin 2) Real)) :
    Polynomial (MvPolynomial (Fin 2) Real) :=
  MvPolynomial.optionEquivLeft Real (Fin 2)
    (MvPolynomial.pderiv (some (1 : Fin 2)) (energyMassPolynomial p))

/-- The vertical mass partial is coefficientwise in the energy variable. -/
theorem coeff_verticalMassPartial
    (p : Polynomial (MvPolynomial (Fin 2) Real)) (n : Nat) :
    (verticalMassPartial p).coeff n =
      MvPolynomial.pderiv (1 : Fin 2) (p.coeff n) := by
  unfold verticalMassPartial
  ext d
  rw [MvPolynomial.optionEquivLeft_coeff_coeff,
    MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv]
  have hexponents :
      d.optionElim n + Finsupp.single (some (1 : Fin 2)) 1 =
        (d + Finsupp.single (1 : Fin 2) 1).optionElim n := by
    ext o
    cases o <;> simp [Finsupp.single_apply]
  rw [hexponents, ← MvPolynomial.optionEquivLeft_coeff_coeff]
  simp [energyMassPolynomial]

/-- Removing the acoustic energy factor commutes with the coefficientwise
vertical mass partial. -/
theorem verticalMassPartial_divX
    (p : Polynomial (MvPolynomial (Fin 2) Real)) :
    verticalMassPartial p.divX = (verticalMassPartial p).divX := by
  ext n
  simp [coeff_verticalMassPartial, Polynomial.coeff_divX]

/-- `partial_y P` for the canonical two-site characteristic polynomial. -/
def twoSitePositiveCharacteristicVerticalMassPartial
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) :
    Polynomial (MvPolynomial (Fin 2) Real) :=
  verticalMassPartial
    (twoSitePositiveCharacteristicPolynomial fixed site₁ site₂)

/-- The canonical Jacobian eliminant `Res_E(P, partial_y P)`.  The two
explicit bounds are the symbolic degrees, before any specialization. -/
def twoSitePositiveCharacteristicJacobianResultant
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) : MvPolynomial (Fin 2) Real :=
  let p := twoSitePositiveCharacteristicPolynomial fixed site₁ site₂
  let q := twoSitePositiveCharacteristicVerticalMassPartial fixed site₁ site₂
  Polynomial.resultant p q p.natDegree q.natDegree

/-- Evaluation of `partial_y p` at `(E,x,y)` is evaluation of the formal
partial derivative of the single multivariate presentation. -/
theorem eval_verticalMassPartial
    (p : Polynomial (MvPolynomial (Fin 2) Real))
    (coordinates : Fin 2 → Real) (energy : Real) :
    (Polynomial.map (MvPolynomial.eval coordinates)
        (verticalMassPartial p)).eval energy =
      MvPolynomial.eval (fun o ↦ o.elim energy coordinates)
        (MvPolynomial.pderiv (some (1 : Fin 2))
          (energyMassPolynomial p)) := by
  symm
  exact MvPolynomial.optionEquivLeft_elim_eval
    Real (Fin 2) coordinates energy _

/-- A calculus bridge for a multivariate polynomial along a curve for which
only one coordinate can have nonzero derivative. -/
theorem hasDerivAt_mvPolynomial_eval_of_single_coordinate
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (p : MvPolynomial sigma Real) (coordinate : sigma)
    (curve : Real → sigma → Real) (point derivative : Real)
    (hcurve : ∀ i, HasDerivAt (fun t ↦ curve t i)
      (if i = coordinate then derivative else 0) point) :
    HasDerivAt (fun t ↦ MvPolynomial.eval (curve t) p)
      (derivative * MvPolynomial.eval (curve point)
        (MvPolynomial.pderiv coordinate p)) point := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (hasDerivAt_const point a)
  | add p q hp hq =>
      refine ((hp.add hq).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t ↦ ?_)).congr_deriv ?_
      · exact MvPolynomial.eval_add
      · rw [map_add, MvPolynomial.eval_add]
        ring
  | mul_X p i hp =>
      have hproduct := hp.mul (hcurve i)
      by_cases hi : i = coordinate
      · subst i
        refine (hproduct.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun t ↦ ?_)).congr_deriv ?_
        · rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]
          rfl
        · rw [MvPolynomial.pderiv_mul,
            MvPolynomial.pderiv_X_self, MvPolynomial.eval_add,
            MvPolynomial.eval_mul, MvPolynomial.eval_mul,
            MvPolynomial.eval_X]
          simp only [map_one, mul_one, if_true]
          ring
      · refine (hproduct.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun t ↦ ?_)).congr_deriv ?_
        · rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]
          rfl
        · rw [MvPolynomial.pderiv_mul,
            MvPolynomial.pderiv_X_of_ne hi,
            MvPolynomial.eval_add, MvPolynomial.eval_mul,
            MvPolynomial.eval_mul, MvPolynomial.eval_X]
          simp only [map_zero, mul_zero, add_zero, if_neg hi]
          ring

/-- Specialization of the symbolic sliced matrix is the concrete weighted
cycle at the embedded inverse-mass coordinates. -/
theorem evaluate_twoSiteSymbolicWeightedCycleLaplacian
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (pair : Real × Real) :
    (twoSiteSymbolicWeightedCycleLaplacian fixed site₁ site₂).map
        (MvPolynomial.eval (iidInverseMassPairCoordinates pair)) =
      weightedCycleLaplacian
        (weightsOfCoordinates
          (twoSiteInverseMassSliceCoordinates fixed site₁ site₂ pair)) := by
  rw [twoSiteSymbolicWeightedCycleLaplacian, Matrix.map_map]
  have hhom :
      (MvPolynomial.eval (iidInverseMassPairCoordinates pair)).comp
          (twoSiteCharacteristicSliceHom fixed site₁ site₂) =
        MvPolynomial.eval
          (twoSiteInverseMassSliceCoordinates fixed site₁ site₂ pair) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [twoSiteCharacteristicSliceHom]
    · intro k
      simp [twoSiteCharacteristicSliceHom,
        twoSiteRepeatedRootSliceSubstitution,
        twoSiteInverseMassSliceCoordinates]
      split_ifs <;> simp
  change (symbolicWeightedCycleLaplacian (N := N)).map
      ⇑((MvPolynomial.eval (iidInverseMassPairCoordinates pair)).comp
        (twoSiteCharacteristicSliceHom fixed site₁ site₂)) = _
  rw [hhom]
  exact evaluate_symbolicWeightedCycleLaplacian _

/-- Exact specialization of `P⁺(E,x,y)` to the concrete sliced
positive-spectrum polynomial.  In particular, specialization is proved to
commute with `divX`; no degree-preservation shortcut is assumed. -/
theorem evaluate_twoSitePositiveCharacteristicPolynomial
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (pair : Real × Real) :
    Polynomial.map (MvPolynomial.eval (iidInverseMassPairCoordinates pair))
        (twoSitePositiveCharacteristicPolynomial fixed site₁ site₂) =
      (weightedCycleLaplacian
        (weightsOfCoordinates
          (twoSiteInverseMassSliceCoordinates fixed site₁ site₂ pair))).charpoly.divX := by
  unfold twoSitePositiveCharacteristicPolynomial
  have hdiv
      (q : Polynomial (MvPolynomial (Fin 2) Real)) :
      q.divX.map (MvPolynomial.eval (iidInverseMassPairCoordinates pair)) =
        (q.map
          (MvPolynomial.eval (iidInverseMassPairCoordinates pair))).divX := by
    ext n
    simp [Polynomial.coeff_divX]
  rw [hdiv, ← Matrix.charpoly_map]
  rw [evaluate_twoSiteSymbolicWeightedCycleLaplacian]

theorem twoSitePositiveCharacteristicPolynomial_monic
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) :
    (twoSitePositiveCharacteristicPolynomial fixed site₁ site₂).Monic := by
  apply monic_divX_of_one_le_natDegree (Matrix.charpoly_monic _)
  rw [Matrix.charpoly_natDegree_eq_dim, ZMod.card]
  exact Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)


/-- A monic polynomial and any polynomial with a common root have zero
fixed-size resultant, provided the supplied right size bounds the right
degree. -/
theorem fixedResultant_eq_zero_of_common_root
    {p q : Polynomial Real} (hp : p.Monic) {bound : Nat}
    (hqDegree : q.natDegree ≤ bound) {energy : Real}
    (hpRoot : p.eval energy = 0) (hqRoot : q.eval energy = 0) :
    Polynomial.resultant p q p.natDegree bound = 0 := by
  have hnotCoprime : ¬ IsCoprime p q := by
    intro hcoprime
    rcases hcoprime with ⟨a, b, hab⟩
    have heval := congrArg (Polynomial.eval energy) hab
    simp [hpRoot, hqRoot] at heval
  have hbase : Polynomial.resultant p q = 0 :=
    Polynomial.resultant_eq_zero_iff.mpr
      ⟨Or.inl hp.ne_zero, hnotCoprime⟩
  have hbound : bound = q.natDegree + (bound - q.natDegree) := by
    omega
  rw [hbound, Polynomial.resultant_add_right_deg p q p.natDegree
    q.natDegree (bound - q.natDegree) le_rfl, hbase, mul_zero]

/-- Evaluation of the canonical resultant vanishes whenever the specialized
`P` and `partial_y P` share an energy root.  This is the exact algebraic
elimination step; it makes no claim that the resultant polynomial is nonzero.
-/
theorem twoSitePositiveCharacteristicJacobianResultant_eval_eq_zero_of_common_energy
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (coordinates : Fin 2 → Real)
    (energy : Real)
    (hroot :
      (Polynomial.map (MvPolynomial.eval coordinates)
        (twoSitePositiveCharacteristicPolynomial fixed site₁ site₂)).eval
          energy = 0)
    (hpartial :
      (Polynomial.map (MvPolynomial.eval coordinates)
        (twoSitePositiveCharacteristicVerticalMassPartial fixed site₁ site₂)).eval
          energy = 0) :
    MvPolynomial.eval coordinates
      (twoSitePositiveCharacteristicJacobianResultant fixed site₁ site₂) = 0 := by
  let p := twoSitePositiveCharacteristicPolynomial fixed site₁ site₂
  let q := twoSitePositiveCharacteristicVerticalMassPartial fixed site₁ site₂
  have hp : p.Monic := twoSitePositiveCharacteristicPolynomial_monic fixed site₁ site₂
  have hzero := fixedResultant_eq_zero_of_common_root
    (hp.map (MvPolynomial.eval coordinates))
    (Polynomial.natDegree_map_le)
    (show (p.map (MvPolynomial.eval coordinates)).eval energy = 0 by
      simpa [p] using hroot)
    (show (q.map (MvPolynomial.eval coordinates)).eval energy = 0 by
      simpa [q] using hpartial)
  change MvPolynomial.eval coordinates
      (Polynomial.resultant p q p.natDegree q.natDegree) = 0
  rw [← Polynomial.resultant_map_map]
  simpa [hp.natDegree_map] using hzero

end

end ArchonPhysics.CanonicalPairCharacteristicJacobianResultant
