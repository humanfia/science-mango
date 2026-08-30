import ArchonPhysics.CanonicalPairCharacteristicJacobianResultant
import ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianFrozenFiber

/-!
# The canonical reduced characteristic-Jacobian resultant is nonzero at three sites

Fix three periodic sites, vary sites `0` and `1`, and freeze the mass at site
`2`.  In inverse-mass coordinates

`x = m₀⁻¹`, `y = m₁⁻¹`, `z = fixed.mass 2 ⁻¹`,

the canonical positive-spectrum polynomial and its vertical mass partial are

`P⁺(E) = E² - 2 (x + y + z) E + 3 (xy + xz + yz)`,

`∂y P⁺(E) = -2 E + 3 (x + z)`.

The canonical fixed-size resultant from
`CanonicalPairCharacteristicJacobianResultant` therefore has the exact value

`Res_E(P⁺, ∂y P⁺) = -3 (x - z)²`.

This proves polynomial nonvanishing for every positive frozen background and
identifies its zero set with the zero set of the previously constructed
frozen-fiber eliminant `X 0 - C z`.  It is a qualitative nonzero-polynomial
certificate.  The exact square identity gives pointwise values, but it does
not assert a positive uniform lower bound near the hypersurface `x = z`.
-/

open scoped Matrix

namespace ArchonPhysics.CanonicalThreeSiteCharacteristicJacobianResultantNonzero

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianFrozenFiber
open ArchonPhysics.CanonicalPairCharacteristicJacobianResultant
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.TwoParameterSpectralPolynomialAvoidance

noncomputable section

/-- The explicit reduced three-site characteristic polynomial in energy,
with coefficients in the two varied inverse-mass coordinates. -/
def threeSitePositiveCharacteristicPolynomialFormula
    (fixed : Lattice.PositiveMassConfig 3) :
    Polynomial (MvPolynomial (Fin 2) Real) :=
  Polynomial.X ^ 2 -
    Polynomial.C (2 * (MvPolynomial.X 0 + MvPolynomial.X 1 +
      MvPolynomial.C (frozenThirdInverseWeight fixed))) * Polynomial.X +
    Polynomial.C (3 * (MvPolynomial.X 0 * MvPolynomial.X 1 +
      MvPolynomial.X 0 * MvPolynomial.C (frozenThirdInverseWeight fixed) +
      MvPolynomial.X 1 * MvPolynomial.C (frozenThirdInverseWeight fixed)))

/-- A coefficient-normalized presentation of the same quadratic.  Keeping
the real constants visibly under `MvPolynomial.C` makes formal partial
differentiation coefficientwise. -/
private def threeSitePositiveCharacteristicPolynomialFormulaC
    (fixed : Lattice.PositiveMassConfig 3) :
    Polynomial (MvPolynomial (Fin 2) Real) :=
  Polynomial.X ^ 2 -
    Polynomial.C (MvPolynomial.C 2 *
      (MvPolynomial.X 0 + MvPolynomial.X 1 +
        MvPolynomial.C (frozenThirdInverseWeight fixed))) * Polynomial.X +
    Polynomial.C (MvPolynomial.C 3 *
      (MvPolynomial.X 0 * MvPolynomial.X 1 +
        MvPolynomial.X 0 * MvPolynomial.C (frozenThirdInverseWeight fixed) +
        MvPolynomial.X 1 * MvPolynomial.C (frozenThirdInverseWeight fixed)))

/-- The explicit coefficientwise partial derivative in the second varied
inverse-mass coordinate. -/
def threeSitePositiveCharacteristicVerticalMassPartialFormula
    (fixed : Lattice.PositiveMassConfig 3) :
    Polynomial (MvPolynomial (Fin 2) Real) :=
  Polynomial.C (-MvPolynomial.C 2) * Polynomial.X +
    Polynomial.C (MvPolynomial.C 3 *
      (MvPolynomial.X 0 +
        MvPolynomial.C (frozenThirdInverseWeight fixed)))

/-- The energy root of the explicit vertical mass partial. -/
def threeSiteCriticalEnergyPolynomial
    (fixed : Lattice.PositiveMassConfig 3) :
    MvPolynomial (Fin 2) Real :=
  MvPolynomial.C (3 / 2 : Real) *
    (MvPolynomial.X 0 +
      MvPolynomial.C (frozenThirdInverseWeight fixed))

/-- On sites `0,1`, the generic two-site slice coordinates are exactly the
explicit arbitrary-frozen three-site inverse weights. -/
theorem twoSiteInverseMassSliceCoordinates_zero_one_eq
    (fixed : Lattice.PositiveMassConfig 3) (pair : Real × Real) :
    twoSiteInverseMassSliceCoordinates fixed
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) pair =
      frozenFiberThreeSiteInverseWeights fixed pair := by
  funext k
  fin_cases k <;>
    norm_num +decide [twoSiteInverseMassSliceCoordinates,
      frozenFiberThreeSiteInverseWeights, frozenThirdInverseWeight,
      siteEquivFin]
  congr 1

/-- The concrete weighted-cycle characteristic polynomial on the generic
slice agrees with the explicit reindexed three-cycle calculation. -/
theorem weightedCycle_zero_one_charpoly_eq_explicitFrozenFiber
    (fixed : Lattice.PositiveMassConfig 3) (pair : Real × Real) :
    (weightedCycleLaplacian (weightsOfCoordinates
      (twoSiteInverseMassSliceCoordinates fixed
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) pair))).charpoly =
      (explicitFrozenFiberThreeCycleLaplacian fixed pair).charpoly := by
  rw [twoSiteInverseMassSliceCoordinates_zero_one_eq]
  rw [← Matrix.charpoly_reindex (siteEquivFin 3)]
  change (finWeightedCycleLaplacian
      (frozenFiberThreeSiteInverseWeights fixed pair)).charpoly = _
  rw [finWeightedCycleLaplacian_frozenFiberThreeSiteInverseWeights]

/-- The full explicit three-cycle characteristic polynomial is `X` times
the displayed positive-spectrum quadratic. -/
theorem explicitFrozenFiberThreeCycleLaplacian_charpoly_eq
    (fixed : Lattice.PositiveMassConfig 3) (pair : Real × Real) :
    (explicitFrozenFiberThreeCycleLaplacian fixed pair).charpoly =
      Polynomial.X *
        (Polynomial.X ^ 2 -
          Polynomial.C (2 * (pair.1⁻¹ + pair.2⁻¹ +
            frozenThirdInverseWeight fixed)) * Polynomial.X +
          Polynomial.C (3 * (pair.1⁻¹ * pair.2⁻¹ +
            pair.1⁻¹ * frozenThirdInverseWeight fixed +
            pair.2⁻¹ * frozenThirdInverseWeight fixed))) := by
  apply Polynomial.funext
  intro energy
  rw [explicitFrozenFiberThreeCycleLaplacian_charpoly_eval]
  simp

/-- Removing the acoustic factor from the explicit three-cycle gives the
displayed quadratic exactly. -/
theorem explicitFrozenFiberThreeCycleLaplacian_charpoly_divX_eq
    (fixed : Lattice.PositiveMassConfig 3) (pair : Real × Real) :
    (explicitFrozenFiberThreeCycleLaplacian fixed pair).charpoly.divX =
      Polynomial.X ^ 2 -
        Polynomial.C (2 * (pair.1⁻¹ + pair.2⁻¹ +
          frozenThirdInverseWeight fixed)) * Polynomial.X +
        Polynomial.C (3 * (pair.1⁻¹ * pair.2⁻¹ +
          pair.1⁻¹ * frozenThirdInverseWeight fixed +
          pair.2⁻¹ * frozenThirdInverseWeight fixed)) := by
  rw [explicitFrozenFiberThreeCycleLaplacian_charpoly_eq]
  ext n
  simp [Polynomial.coeff_divX]

/-- Exact symbolic specialization of the canonical reduced characteristic
polynomial at three sites and varied sites `0,1`. -/
theorem twoSitePositiveCharacteristicPolynomial_zero_one_eq_formula
    (fixed : Lattice.PositiveMassConfig 3) :
    twoSitePositiveCharacteristicPolynomial fixed
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) =
      threeSitePositiveCharacteristicPolynomialFormula fixed := by
  apply Polynomial.ext
  intro n
  apply MvPolynomial.funext
  intro coordinates
  let pair : Real × Real := ((coordinates 0)⁻¹, (coordinates 1)⁻¹)
  have hpairCoordinates : iidInverseMassPairCoordinates pair = coordinates := by
    funext i
    fin_cases i <;> simp [pair]
  have hmap := evaluate_twoSitePositiveCharacteristicPolynomial fixed
    (0 : Lattice.Site 3) (1 : Lattice.Site 3) pair
  rw [hpairCoordinates,
    weightedCycle_zero_one_charpoly_eq_explicitFrozenFiber,
    explicitFrozenFiberThreeCycleLaplacian_charpoly_divX_eq] at hmap
  have hformulaMap :
      Polynomial.map (MvPolynomial.eval coordinates)
          (threeSitePositiveCharacteristicPolynomialFormula fixed) =
        Polynomial.X ^ 2 -
          Polynomial.C (2 * (pair.1⁻¹ + pair.2⁻¹ +
            frozenThirdInverseWeight fixed)) * Polynomial.X +
          Polynomial.C (3 * (pair.1⁻¹ * pair.2⁻¹ +
            pair.1⁻¹ * frozenThirdInverseWeight fixed +
            pair.2⁻¹ * frozenThirdInverseWeight fixed)) := by
    simp [threeSitePositiveCharacteristicPolynomialFormula, pair]
  have hpmap :
      Polynomial.map (MvPolynomial.eval coordinates)
          (twoSitePositiveCharacteristicPolynomial fixed
            (0 : Lattice.Site 3) (1 : Lattice.Site 3)) =
        Polynomial.map (MvPolynomial.eval coordinates)
          (threeSitePositiveCharacteristicPolynomialFormula fixed) :=
    hmap.trans hformulaMap.symm
  have hcoeff := congrArg (fun p => p.coeff n) hpmap
  simpa using hcoeff

private theorem twoSitePositiveCharacteristicPolynomial_zero_one_eq_formulaC
    (fixed : Lattice.PositiveMassConfig 3) :
    twoSitePositiveCharacteristicPolynomial fixed
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) =
      threeSitePositiveCharacteristicPolynomialFormulaC fixed := by
  rw [twoSitePositiveCharacteristicPolynomial_zero_one_eq_formula]
  unfold threeSitePositiveCharacteristicPolynomialFormula
    threeSitePositiveCharacteristicPolynomialFormulaC
  have htwo : (2 : MvPolynomial (Fin 2) Real) = MvPolynomial.C 2 :=
    (MvPolynomial.C_eq_coe_nat 2).symm
  have hthree : (3 : MvPolynomial (Fin 2) Real) = MvPolynomial.C 3 :=
    (MvPolynomial.C_eq_coe_nat 3).symm
  rw [htwo, hthree]

private theorem threeSitePositiveCharacteristicPolynomialFormulaC_natDegree_le
    (fixed : Lattice.PositiveMassConfig 3) :
    (threeSitePositiveCharacteristicPolynomialFormulaC fixed).natDegree ≤ 2 := by
  unfold threeSitePositiveCharacteristicPolynomialFormulaC
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact Polynomial.natDegree_X_pow_le 2
    · exact (Polynomial.natDegree_C_mul_le _ _).trans
        (Polynomial.natDegree_X_le.trans (by omega))
  · rw [Polynomial.natDegree_C]
    omega

private theorem threeSitePositiveCharacteristicVerticalMassPartialFormula_natDegree_le
    (fixed : Lattice.PositiveMassConfig 3) :
    (threeSitePositiveCharacteristicVerticalMassPartialFormula fixed).natDegree ≤ 1 := by
  unfold threeSitePositiveCharacteristicVerticalMassPartialFormula
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact (Polynomial.natDegree_C_mul_le _ _).trans
      Polynomial.natDegree_X_le
  · rw [Polynomial.natDegree_C]
    omega

/-- The canonical vertical mass partial is exactly
`-2 E + 3 (x + z)` at three sites. -/
theorem twoSitePositiveCharacteristicVerticalMassPartial_zero_one_eq_formula
    (fixed : Lattice.PositiveMassConfig 3) :
    twoSitePositiveCharacteristicVerticalMassPartial fixed
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) =
      threeSitePositiveCharacteristicVerticalMassPartialFormula fixed := by
  rw [twoSitePositiveCharacteristicVerticalMassPartial,
    twoSitePositiveCharacteristicPolynomial_zero_one_eq_formulaC]
  have hleftDegree :
      (verticalMassPartial
        (threeSitePositiveCharacteristicPolynomialFormulaC fixed)).natDegree ≤ 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rw [coeff_verticalMassPartial]
    by_cases htwo : n = 2
    · subst n
      simp [threeSitePositiveCharacteristicPolynomialFormulaC]
    · have hlt : 2 < n := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        ((threeSitePositiveCharacteristicPolynomialFormulaC_natDegree_le fixed).trans_lt hlt)]
      exact map_zero (MvPolynomial.pderiv (1 : Fin 2))
  apply (Polynomial.ext_iff_natDegree_le hleftDegree
    (threeSitePositiveCharacteristicVerticalMassPartialFormula_natDegree_le fixed)).2
  intro n hn
  interval_cases n <;>
    simp [coeff_verticalMassPartial,
      threeSitePositiveCharacteristicPolynomialFormulaC,
      threeSitePositiveCharacteristicVerticalMassPartialFormula]

private theorem threeSitePositiveCharacteristicPolynomialFormulaC_natDegree_eq
    (fixed : Lattice.PositiveMassConfig 3) :
    (threeSitePositiveCharacteristicPolynomialFormulaC fixed).natDegree = 2 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (threeSitePositiveCharacteristicPolynomialFormulaC_natDegree_le fixed)
  simp [threeSitePositiveCharacteristicPolynomialFormulaC]

private theorem threeSitePositiveCharacteristicVerticalMassPartialFormula_natDegree_eq
    (fixed : Lattice.PositiveMassConfig 3) :
    (threeSitePositiveCharacteristicVerticalMassPartialFormula fixed).natDegree = 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (threeSitePositiveCharacteristicVerticalMassPartialFormula_natDegree_le fixed)
  simp [threeSitePositiveCharacteristicVerticalMassPartialFormula]

private theorem threeSitePositiveCharacteristicVerticalMassPartialFormula_factor
    (fixed : Lattice.PositiveMassConfig 3) :
    threeSitePositiveCharacteristicVerticalMassPartialFormula fixed =
      Polynomial.C (-MvPolynomial.C 2) *
        (Polynomial.X -
          Polynomial.C (threeSiteCriticalEnergyPolynomial fixed)) := by
  let a : MvPolynomial (Fin 2) Real :=
    MvPolynomial.X 0 + MvPolynomial.C (frozenThirdInverseWeight fixed)
  have hconstant :
      MvPolynomial.C 3 * a =
        -((-MvPolynomial.C 2) *
          (MvPolynomial.C (3 / 2 : Real) * a)) := by
    calc
      MvPolynomial.C 3 * a =
          MvPolynomial.C (2 * (3 / 2 : Real)) * a := by norm_num
      _ = (MvPolynomial.C 2 *
          MvPolynomial.C (3 / 2 : Real)) * a := by
        rw [MvPolynomial.C_mul]
      _ = -((-MvPolynomial.C 2) *
          (MvPolynomial.C (3 / 2 : Real) * a)) := by ring
  change
    Polynomial.C (-MvPolynomial.C 2) * Polynomial.X +
        Polynomial.C (MvPolynomial.C 3 * a) =
      Polynomial.C (-MvPolynomial.C 2) *
        (Polynomial.X -
          Polynomial.C (MvPolynomial.C (3 / 2 : Real) * a))
  rw [mul_sub, ← Polynomial.C_mul, sub_eq_add_neg,
    ← Polynomial.C_neg, hconstant]

/-- Exact computation of the canonical reduced characteristic-Jacobian
resultant at three sites. -/
theorem twoSitePositiveCharacteristicJacobianResultant_zero_one_eq
    (fixed : Lattice.PositiveMassConfig 3) :
    twoSitePositiveCharacteristicJacobianResultant fixed
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) =
      -MvPolynomial.C 3 *
        (MvPolynomial.X 0 -
          MvPolynomial.C (frozenThirdInverseWeight fixed)) ^ 2 := by
  unfold twoSitePositiveCharacteristicJacobianResultant
  dsimp only
  rw [twoSitePositiveCharacteristicPolynomial_zero_one_eq_formulaC,
    twoSitePositiveCharacteristicVerticalMassPartial_zero_one_eq_formula,
    threeSitePositiveCharacteristicPolynomialFormulaC_natDegree_eq,
    threeSitePositiveCharacteristicVerticalMassPartialFormula_natDegree_eq,
    threeSitePositiveCharacteristicVerticalMassPartialFormula_factor]
  rw [Polynomial.resultant_C_mul_right]
  rw [Polynomial.resultant_X_sub_C_right
    (threeSitePositiveCharacteristicPolynomialFormulaC fixed) 2
    (threeSiteCriticalEnergyPolynomial fixed)
    (threeSitePositiveCharacteristicPolynomialFormulaC_natDegree_le fixed)]
  apply MvPolynomial.funext
  intro coordinates
  simp [threeSitePositiveCharacteristicPolynomialFormulaC,
    threeSiteCriticalEnergyPolynomial]
  ring

/-- The canonical resultant is exactly `-3` times the square of the explicit
frozen-fiber outer-Jacobian eliminant. -/
theorem twoSitePositiveCharacteristicJacobianResultant_zero_one_eq_frozenFiber_sq
    (fixed : Lattice.PositiveMassConfig 3) :
    twoSitePositiveCharacteristicJacobianResultant fixed
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) =
      -MvPolynomial.C 3 *
        (frozenFiberThreeSiteOuterJacobianPolynomial fixed) ^ 2 := by
  simpa [frozenFiberThreeSiteOuterJacobianPolynomial] using
    twoSitePositiveCharacteristicJacobianResultant_zero_one_eq fixed

/-- Pointwise evaluation of the exact square identity. -/
@[simp] theorem twoSitePositiveCharacteristicJacobianResultant_zero_one_eval
    (fixed : Lattice.PositiveMassConfig 3)
    (coordinates : Fin 2 → Real) :
    MvPolynomial.eval coordinates
        (twoSitePositiveCharacteristicJacobianResultant fixed
          (0 : Lattice.Site 3) (1 : Lattice.Site 3)) =
      -3 * (coordinates 0 - frozenThirdInverseWeight fixed) ^ 2 := by
  rw [twoSitePositiveCharacteristicJacobianResultant_zero_one_eq]
  simp

/-- The exact zero set of the canonical three-site resultant is the affine
hyperplane `x = z`; the second inverse-mass coordinate is unrestricted. -/
@[simp] theorem twoSitePositiveCharacteristicJacobianResultant_zero_one_eval_eq_zero_iff
    (fixed : Lattice.PositiveMassConfig 3)
    (coordinates : Fin 2 → Real) :
    MvPolynomial.eval coordinates
        (twoSitePositiveCharacteristicJacobianResultant fixed
          (0 : Lattice.Site 3) (1 : Lattice.Site 3)) = 0 ↔
      coordinates 0 = frozenThirdInverseWeight fixed := by
  rw [twoSitePositiveCharacteristicJacobianResultant_zero_one_eval]
  simp [sub_eq_zero]

/-- The canonical resultant and the explicit outer-Jacobian eliminant have
identical evaluated zero sets. -/
theorem twoSitePositiveCharacteristicJacobianResultant_zero_one_eval_eq_zero_iff_frozenFiber
    (fixed : Lattice.PositiveMassConfig 3)
    (coordinates : Fin 2 → Real) :
    MvPolynomial.eval coordinates
        (twoSitePositiveCharacteristicJacobianResultant fixed
          (0 : Lattice.Site 3) (1 : Lattice.Site 3)) = 0 ↔
      MvPolynomial.eval coordinates
        (frozenFiberThreeSiteOuterJacobianPolynomial fixed) = 0 := by
  rw [twoSitePositiveCharacteristicJacobianResultant_zero_one_eval_eq_zero_iff]
  simp [frozenFiberThreeSiteOuterJacobianPolynomial, sub_eq_zero]

/-- A background-uniform algebraic evaluation witness: one unit away from
the affine zero hyperplane, the resultant evaluates to `-3`. -/
@[simp] theorem twoSitePositiveCharacteristicJacobianResultant_zero_one_eval_witness
    (fixed : Lattice.PositiveMassConfig 3) :
    MvPolynomial.eval
        (![frozenThirdInverseWeight fixed + 1, 0] : Fin 2 → Real)
        (twoSitePositiveCharacteristicJacobianResultant fixed
          (0 : Lattice.Site 3) (1 : Lattice.Site 3)) = -3 := by
  rw [twoSitePositiveCharacteristicJacobianResultant_zero_one_eval]
  norm_num

/-- For every arbitrary positive frozen background, the canonical reduced
characteristic-Jacobian resultant is a nonzero polynomial. -/
theorem twoSitePositiveCharacteristicJacobianResultant_zero_one_ne_zero
    (fixed : Lattice.PositiveMassConfig 3) :
    twoSitePositiveCharacteristicJacobianResultant fixed
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval
      (![frozenThirdInverseWeight fixed + 1, 0] : Fin 2 → Real)) hzero
  simp at heval

/-- Evaluation on a raw-mass pair, expressed in the inverse-mass coordinate
used by the canonical resultant API. -/
@[simp] theorem twoSitePositiveCharacteristicJacobianResultant_zero_one_eval_inverseMassPair
    (fixed : Lattice.PositiveMassConfig 3) (pair : Real × Real) :
    MvPolynomial.eval (iidInverseMassPairCoordinates pair)
        (twoSitePositiveCharacteristicJacobianResultant fixed
          (0 : Lattice.Site 3) (1 : Lattice.Site 3)) =
      -3 * (pair.1⁻¹ - frozenThirdInverseWeight fixed) ^ 2 := by
  rw [twoSitePositiveCharacteristicJacobianResultant_zero_one_eval]
  rfl

end

end ArchonPhysics.CanonicalThreeSiteCharacteristicJacobianResultantNonzero
