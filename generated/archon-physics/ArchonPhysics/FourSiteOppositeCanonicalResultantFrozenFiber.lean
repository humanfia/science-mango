import ArchonPhysics.CanonicalPairCharacteristicJacobianResultant

/-!
# Four-site opposite canonical resultant on an arbitrary frozen fiber

On the periodic four-cycle, vary the opposite sites `0` and `2` and freeze
sites `1` and `3`.  Write `x,y` for the varied inverse masses and `a,b` for
the two frozen inverse masses.  The reduced positive-spectrum characteristic
polynomial and its vertical partial are

`P(E) = E^3 - 2 (x+a+y+b) E^2
  + (3xa+4xy+3xb+3ay+4ab+3yb) E
  - 4 (xay+xab+xyb+ayb)`,

`partial_y P(E) = -2 E^2 + (4x+3a+3b) E - 4(xa+xb+ab)`.

Their canonical fixed-size resultant factors exactly as

`4 (a-b)^2 ((a+b)x - 2ab)^2`.

Consequently the resultant is a nonzero polynomial exactly when the two
positive frozen inverse masses differ.  When it is nonzero, its evaluated
zero set still contains the affine varied-mass hypersurface
`(a+b)x = 2ab`; no pointwise nonvanishing claim is made.
-/

open scoped Matrix

namespace ArchonPhysics.FourSiteOppositeCanonicalResultantFrozenFiber

open ArchonPhysics
open ArchonPhysics.CanonicalPairCharacteristicJacobianResultant
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.TwoParameterSpectralPolynomialAvoidance

noncomputable section

/-- The inverse mass frozen at site `1` of the opposite-site four-cycle
fiber. -/
def frozenInverseWeightOne (fixed : Lattice.PositiveMassConfig 4) : Real :=
  (fixed.mass (1 : Lattice.Site 4))⁻¹

/-- The inverse mass frozen at site `3` of the opposite-site four-cycle
fiber. -/
def frozenInverseWeightThree (fixed : Lattice.PositiveMassConfig 4) : Real :=
  (fixed.mass (3 : Lattice.Site 4))⁻¹

theorem frozenInverseWeightOne_pos (fixed : Lattice.PositiveMassConfig 4) :
    0 < frozenInverseWeightOne fixed := by
  exact inv_pos.mpr (fixed.mass_pos _)

theorem frozenInverseWeightThree_pos (fixed : Lattice.PositiveMassConfig 4) :
    0 < frozenInverseWeightThree fixed := by
  exact inv_pos.mpr (fixed.mass_pos _)

/-- The four inverse edge weights with opposite sites `0` and `2` varied. -/
def oppositeFrozenFiberInverseWeights
    (fixed : Lattice.PositiveMassConfig 4) (pair : Real × Real) :
    Fin 4 → Real :=
  ![pair.1⁻¹, frozenInverseWeightOne fixed, pair.2⁻¹,
    frozenInverseWeightThree fixed]

/-- Explicit finite matrix for the opposite-site four-cycle fiber. -/
def explicitOppositeFrozenFiberLaplacian
    (fixed : Lattice.PositiveMassConfig 4) (pair : Real × Real) :
    Matrix (Fin 4) (Fin 4) Real :=
  let x := pair.1⁻¹
  let y := pair.2⁻¹
  let a := frozenInverseWeightOne fixed
  let b := frozenInverseWeightThree fixed
  !![x + a, -a, 0, -x;
     -a, a + y, -y, 0;
     0, -y, y + b, -b;
     -x, 0, -b, b + x]

/-- Direct finite-matrix identification of the opposite-site frozen fiber. -/
theorem finWeightedCycleLaplacian_oppositeFrozenFiberInverseWeights
    (fixed : Lattice.PositiveMassConfig 4) (pair : Real × Real) :
    finWeightedCycleLaplacian
        (oppositeFrozenFiberInverseWeights fixed pair) =
      explicitOppositeFrozenFiberLaplacian fixed pair := by
  rw [finWeightedCycleLaplacian_eq_sum_rankOne]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, Fin.sum_univ_succ]
  <;> norm_num +decide [oppositeFrozenFiberInverseWeights,
    explicitOppositeFrozenFiberLaplacian, frozenInverseWeightOne,
    frozenInverseWeightThree, finCycleEdgeVector,
    SingleMassRankOnePerturbation.cycleMassPerturbationVector,
    differenceMatrix, siteEquivFin]
  <;> simp
  <;> ring

private theorem det_fin_four (M : Matrix (Fin 4) (Fin 4) Real) :
    M.det =
      M 0 0 *
          (M 1 1 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) -
            M 1 2 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) +
            M 1 3 * (M 2 1 * M 3 2 - M 2 2 * M 3 1)) -
        M 0 1 *
          (M 1 0 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) -
            M 1 2 * (M 2 0 * M 3 3 - M 2 3 * M 3 0) +
            M 1 3 * (M 2 0 * M 3 2 - M 2 2 * M 3 0)) +
        M 0 2 *
          (M 1 0 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) -
            M 1 1 * (M 2 0 * M 3 3 - M 2 3 * M 3 0) +
            M 1 3 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) -
        M 0 3 *
          (M 1 0 * (M 2 1 * M 3 2 - M 2 2 * M 3 1) -
            M 1 1 * (M 2 0 * M 3 2 - M 2 2 * M 3 0) +
            M 1 2 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) := by
  rw [Matrix.det_succ_row _ 0]
  simp only [Fin.sum_univ_succ, Matrix.det_fin_three]
  norm_num +decide [Fin.succAbove]
  rw [show Fin.succ (2 : Fin 3) = (3 : Fin 4) by decide]
  rw [show Fin.castSucc (2 : Fin 3) = (2 : Fin 4) by decide]
  ring

/-- Exact characteristic-polynomial evaluation of the explicit opposite-site
four-cycle. -/
theorem explicitOppositeFrozenFiberLaplacian_charpoly_eval
    (fixed : Lattice.PositiveMassConfig 4) (pair : Real × Real)
    (energy : Real) :
    (explicitOppositeFrozenFiberLaplacian fixed pair).charpoly.eval energy =
      energy * (energy ^ 3 -
        2 * (pair.1⁻¹ + frozenInverseWeightOne fixed + pair.2⁻¹ +
          frozenInverseWeightThree fixed) * energy ^ 2 +
        (3 * pair.1⁻¹ * frozenInverseWeightOne fixed +
          4 * pair.1⁻¹ * pair.2⁻¹ +
          3 * pair.1⁻¹ * frozenInverseWeightThree fixed +
          3 * frozenInverseWeightOne fixed * pair.2⁻¹ +
          4 * frozenInverseWeightOne fixed * frozenInverseWeightThree fixed +
          3 * pair.2⁻¹ * frozenInverseWeightThree fixed) * energy -
        4 * (pair.1⁻¹ * frozenInverseWeightOne fixed * pair.2⁻¹ +
          pair.1⁻¹ * frozenInverseWeightOne fixed *
            frozenInverseWeightThree fixed +
          pair.1⁻¹ * pair.2⁻¹ * frozenInverseWeightThree fixed +
          frozenInverseWeightOne fixed * pair.2⁻¹ *
            frozenInverseWeightThree fixed)) := by
  rw [Matrix.eval_charpoly, det_fin_four]
  simp [explicitOppositeFrozenFiberLaplacian, Matrix.scalar_apply]
  ring

/-- On sites `0,2`, the generic slice coordinates are exactly the explicit
opposite-site frozen-fiber weights. -/
theorem twoSiteInverseMassSliceCoordinates_zero_two_eq
    (fixed : Lattice.PositiveMassConfig 4) (pair : Real × Real) :
    twoSiteInverseMassSliceCoordinates fixed
        (0 : Lattice.Site 4) (2 : Lattice.Site 4) pair =
      oppositeFrozenFiberInverseWeights fixed pair := by
  funext k
  fin_cases k <;>
    norm_num +decide [twoSiteInverseMassSliceCoordinates,
      oppositeFrozenFiberInverseWeights, frozenInverseWeightOne,
      frozenInverseWeightThree, siteEquivFin]
  congr 1

/-- The concrete sliced weighted-cycle characteristic polynomial is the
characteristic polynomial of the displayed finite matrix. -/
theorem weightedCycle_zero_two_charpoly_eq_explicitOppositeFrozenFiber
    (fixed : Lattice.PositiveMassConfig 4) (pair : Real × Real) :
    (weightedCycleLaplacian (weightsOfCoordinates
      (twoSiteInverseMassSliceCoordinates fixed
        (0 : Lattice.Site 4) (2 : Lattice.Site 4) pair))).charpoly =
      (explicitOppositeFrozenFiberLaplacian fixed pair).charpoly := by
  rw [twoSiteInverseMassSliceCoordinates_zero_two_eq]
  rw [← Matrix.charpoly_reindex (siteEquivFin 4)]
  change (finWeightedCycleLaplacian
      (oppositeFrozenFiberInverseWeights fixed pair)).charpoly = _
  rw [finWeightedCycleLaplacian_oppositeFrozenFiberInverseWeights]

/-- The full explicit characteristic polynomial is `X` times the displayed
positive-spectrum cubic. -/
theorem explicitOppositeFrozenFiberLaplacian_charpoly_eq
    (fixed : Lattice.PositiveMassConfig 4) (pair : Real × Real) :
    (explicitOppositeFrozenFiberLaplacian fixed pair).charpoly =
      Polynomial.X *
        (Polynomial.X ^ 3 -
          Polynomial.C (2 * (pair.1⁻¹ + frozenInverseWeightOne fixed +
            pair.2⁻¹ + frozenInverseWeightThree fixed)) * Polynomial.X ^ 2 +
          Polynomial.C
            (3 * pair.1⁻¹ * frozenInverseWeightOne fixed +
              4 * pair.1⁻¹ * pair.2⁻¹ +
              3 * pair.1⁻¹ * frozenInverseWeightThree fixed +
              3 * frozenInverseWeightOne fixed * pair.2⁻¹ +
              4 * frozenInverseWeightOne fixed *
                frozenInverseWeightThree fixed +
              3 * pair.2⁻¹ * frozenInverseWeightThree fixed) * Polynomial.X -
          Polynomial.C
            (4 * (pair.1⁻¹ * frozenInverseWeightOne fixed * pair.2⁻¹ +
              pair.1⁻¹ * frozenInverseWeightOne fixed *
                frozenInverseWeightThree fixed +
              pair.1⁻¹ * pair.2⁻¹ * frozenInverseWeightThree fixed +
              frozenInverseWeightOne fixed * pair.2⁻¹ *
                frozenInverseWeightThree fixed))) := by
  apply Polynomial.funext
  intro energy
  rw [explicitOppositeFrozenFiberLaplacian_charpoly_eval]
  simp

/-- Removing the acoustic factor gives the displayed positive cubic. -/
theorem explicitOppositeFrozenFiberLaplacian_charpoly_divX_eq
    (fixed : Lattice.PositiveMassConfig 4) (pair : Real × Real) :
    (explicitOppositeFrozenFiberLaplacian fixed pair).charpoly.divX =
      Polynomial.X ^ 3 -
        Polynomial.C (2 * (pair.1⁻¹ + frozenInverseWeightOne fixed +
          pair.2⁻¹ + frozenInverseWeightThree fixed)) * Polynomial.X ^ 2 +
        Polynomial.C
          (3 * pair.1⁻¹ * frozenInverseWeightOne fixed +
            4 * pair.1⁻¹ * pair.2⁻¹ +
            3 * pair.1⁻¹ * frozenInverseWeightThree fixed +
            3 * frozenInverseWeightOne fixed * pair.2⁻¹ +
            4 * frozenInverseWeightOne fixed *
              frozenInverseWeightThree fixed +
            3 * pair.2⁻¹ * frozenInverseWeightThree fixed) * Polynomial.X -
        Polynomial.C
          (4 * (pair.1⁻¹ * frozenInverseWeightOne fixed * pair.2⁻¹ +
            pair.1⁻¹ * frozenInverseWeightOne fixed *
              frozenInverseWeightThree fixed +
            pair.1⁻¹ * pair.2⁻¹ * frozenInverseWeightThree fixed +
            frozenInverseWeightOne fixed * pair.2⁻¹ *
              frozenInverseWeightThree fixed)) := by
  rw [explicitOppositeFrozenFiberLaplacian_charpoly_eq]
  ext n
  simp [Polynomial.coeff_divX]

/-- The explicit reduced four-site characteristic polynomial over the two
varied inverse-mass coordinates. -/
def fourSiteOppositePositiveCharacteristicPolynomialFormula
    (fixed : Lattice.PositiveMassConfig 4) :
    Polynomial (MvPolynomial (Fin 2) Real) :=
  let x : MvPolynomial (Fin 2) Real := MvPolynomial.X 0
  let y : MvPolynomial (Fin 2) Real := MvPolynomial.X 1
  let a := MvPolynomial.C (frozenInverseWeightOne fixed)
  let b := MvPolynomial.C (frozenInverseWeightThree fixed)
  Polynomial.X ^ 3 -
    Polynomial.C (MvPolynomial.C 2 * (x + a + y + b)) * Polynomial.X ^ 2 +
    Polynomial.C (MvPolynomial.C 3 * x * a +
      MvPolynomial.C 4 * x * y + MvPolynomial.C 3 * x * b +
      MvPolynomial.C 3 * a * y + MvPolynomial.C 4 * a * b +
      MvPolynomial.C 3 * y * b) * Polynomial.X -
    Polynomial.C (MvPolynomial.C 4 *
      (x * a * y + x * a * b + x * y * b + a * y * b))

/-- Exact symbolic specialization of the canonical reduced characteristic
polynomial at opposite sites `0,2`. -/
theorem twoSitePositiveCharacteristicPolynomial_zero_two_eq_formula
    (fixed : Lattice.PositiveMassConfig 4) :
    twoSitePositiveCharacteristicPolynomial fixed
        (0 : Lattice.Site 4) (2 : Lattice.Site 4) =
      fourSiteOppositePositiveCharacteristicPolynomialFormula fixed := by
  apply Polynomial.ext
  intro n
  apply MvPolynomial.funext
  intro coordinates
  let pair : Real × Real := ((coordinates 0)⁻¹, (coordinates 1)⁻¹)
  have hpairCoordinates : iidInverseMassPairCoordinates pair = coordinates := by
    funext i
    fin_cases i <;> simp [pair, iidInverseMassPairCoordinates]
  have hmap := evaluate_twoSitePositiveCharacteristicPolynomial fixed
    (0 : Lattice.Site 4) (2 : Lattice.Site 4) pair
  rw [hpairCoordinates,
    weightedCycle_zero_two_charpoly_eq_explicitOppositeFrozenFiber,
    explicitOppositeFrozenFiberLaplacian_charpoly_divX_eq] at hmap
  have hformulaMap :
      Polynomial.map (MvPolynomial.eval coordinates)
          (fourSiteOppositePositiveCharacteristicPolynomialFormula fixed) =
        Polynomial.X ^ 3 -
          Polynomial.C (2 * (pair.1⁻¹ + frozenInverseWeightOne fixed +
            pair.2⁻¹ + frozenInverseWeightThree fixed)) * Polynomial.X ^ 2 +
          Polynomial.C
            (3 * pair.1⁻¹ * frozenInverseWeightOne fixed +
              4 * pair.1⁻¹ * pair.2⁻¹ +
              3 * pair.1⁻¹ * frozenInverseWeightThree fixed +
              3 * frozenInverseWeightOne fixed * pair.2⁻¹ +
              4 * frozenInverseWeightOne fixed *
                frozenInverseWeightThree fixed +
              3 * pair.2⁻¹ * frozenInverseWeightThree fixed) * Polynomial.X -
          Polynomial.C
            (4 * (pair.1⁻¹ * frozenInverseWeightOne fixed * pair.2⁻¹ +
              pair.1⁻¹ * frozenInverseWeightOne fixed *
                frozenInverseWeightThree fixed +
              pair.1⁻¹ * pair.2⁻¹ * frozenInverseWeightThree fixed +
              frozenInverseWeightOne fixed * pair.2⁻¹ *
                frozenInverseWeightThree fixed)) := by
    simp [fourSiteOppositePositiveCharacteristicPolynomialFormula, pair]
  have hpmap :
      Polynomial.map (MvPolynomial.eval coordinates)
          (twoSitePositiveCharacteristicPolynomial fixed
            (0 : Lattice.Site 4) (2 : Lattice.Site 4)) =
        Polynomial.map (MvPolynomial.eval coordinates)
          (fourSiteOppositePositiveCharacteristicPolynomialFormula fixed) :=
    hmap.trans hformulaMap.symm
  have hcoeff := congrArg (fun p => p.coeff n) hpmap
  simpa using hcoeff

/-- The explicit coefficientwise partial in the second varied inverse-mass
coordinate. -/
def fourSiteOppositePositiveCharacteristicVerticalMassPartialFormula
    (fixed : Lattice.PositiveMassConfig 4) :
    Polynomial (MvPolynomial (Fin 2) Real) :=
  let x : MvPolynomial (Fin 2) Real := MvPolynomial.X 0
  let a := MvPolynomial.C (frozenInverseWeightOne fixed)
  let b := MvPolynomial.C (frozenInverseWeightThree fixed)
  Polynomial.C (-MvPolynomial.C 2) * Polynomial.X ^ 2 +
    Polynomial.C (MvPolynomial.C 4 * x +
      MvPolynomial.C 3 * a + MvPolynomial.C 3 * b) * Polynomial.X +
    Polynomial.C (-MvPolynomial.C 4 * (x * a + x * b + a * b))

private theorem fourSiteOppositePositiveCharacteristicPolynomialFormula_natDegree_le
    (fixed : Lattice.PositiveMassConfig 4) :
    (fourSiteOppositePositiveCharacteristicPolynomialFormula fixed).natDegree ≤ 3 := by
  unfold fourSiteOppositePositiveCharacteristicPolynomialFormula
  dsimp only
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact Polynomial.natDegree_X_pow_le 3
      · exact (Polynomial.natDegree_C_mul_le _ _).trans
          ((Polynomial.natDegree_X_pow_le 2).trans (by omega))
    · exact (Polynomial.natDegree_C_mul_le _ _).trans
        (Polynomial.natDegree_X_le.trans (by omega))
  · rw [Polynomial.natDegree_C]
    omega

private theorem fourSiteOppositePositiveCharacteristicVerticalMassPartialFormula_natDegree_le
    (fixed : Lattice.PositiveMassConfig 4) :
    (fourSiteOppositePositiveCharacteristicVerticalMassPartialFormula fixed).natDegree ≤ 2 := by
  unfold fourSiteOppositePositiveCharacteristicVerticalMassPartialFormula
  dsimp only
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (Polynomial.natDegree_C_mul_le _ _).trans
        (Polynomial.natDegree_X_pow_le 2)
    · exact (Polynomial.natDegree_C_mul_le _ _).trans
        (Polynomial.natDegree_X_le.trans (by omega))
  · rw [Polynomial.natDegree_C]
    omega

private theorem fourSiteOppositePositiveCharacteristicPolynomialFormula_coeff_three
    (fixed : Lattice.PositiveMassConfig 4) :
    (fourSiteOppositePositiveCharacteristicPolynomialFormula fixed).coeff 3 = 1 := by
  simp only [fourSiteOppositePositiveCharacteristicPolynomialFormula,
    Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_C]
  norm_num

private theorem fourSiteOppositePositiveCharacteristicVerticalMassPartialFormula_coeff_two
    (fixed : Lattice.PositiveMassConfig 4) :
    (fourSiteOppositePositiveCharacteristicVerticalMassPartialFormula fixed).coeff 2 =
      -MvPolynomial.C 2 := by
  simp only [fourSiteOppositePositiveCharacteristicVerticalMassPartialFormula,
    Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
  norm_num

private theorem fourSiteOppositePositiveCharacteristicPolynomialFormula_natDegree_eq
    (fixed : Lattice.PositiveMassConfig 4) :
    (fourSiteOppositePositiveCharacteristicPolynomialFormula fixed).natDegree = 3 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (fourSiteOppositePositiveCharacteristicPolynomialFormula_natDegree_le fixed)
  rw [fourSiteOppositePositiveCharacteristicPolynomialFormula_coeff_three]
  exact one_ne_zero

private theorem fourSiteOppositePositiveCharacteristicVerticalMassPartialFormula_natDegree_eq
    (fixed : Lattice.PositiveMassConfig 4) :
    (fourSiteOppositePositiveCharacteristicVerticalMassPartialFormula fixed).natDegree = 2 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (fourSiteOppositePositiveCharacteristicVerticalMassPartialFormula_natDegree_le fixed)
  rw [fourSiteOppositePositiveCharacteristicVerticalMassPartialFormula_coeff_two]
  norm_num

/-- The canonical vertical partial is exactly
`-2 E^2 + (4x+3a+3b)E - 4(xa+xb+ab)`. -/
theorem twoSitePositiveCharacteristicVerticalMassPartial_zero_two_eq_formula
    (fixed : Lattice.PositiveMassConfig 4) :
    twoSitePositiveCharacteristicVerticalMassPartial fixed
        (0 : Lattice.Site 4) (2 : Lattice.Site 4) =
      fourSiteOppositePositiveCharacteristicVerticalMassPartialFormula fixed := by
  rw [twoSitePositiveCharacteristicVerticalMassPartial,
    twoSitePositiveCharacteristicPolynomial_zero_two_eq_formula]
  have hleftDegree :
      (verticalMassPartial
        (fourSiteOppositePositiveCharacteristicPolynomialFormula fixed)).natDegree ≤ 2 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rw [coeff_verticalMassPartial]
    by_cases hthree : n = 3
    · subst n
      rw [fourSiteOppositePositiveCharacteristicPolynomialFormula_coeff_three]
      simp
    · have hlt : 3 < n := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        ((fourSiteOppositePositiveCharacteristicPolynomialFormula_natDegree_le
          fixed).trans_lt hlt)]
      exact map_zero (MvPolynomial.pderiv (1 : Fin 2))
  apply (Polynomial.ext_iff_natDegree_le hleftDegree
    (fourSiteOppositePositiveCharacteristicVerticalMassPartialFormula_natDegree_le
      fixed)).2
  intro n hn
  interval_cases n <;>
    simp only [coeff_verticalMassPartial,
      fourSiteOppositePositiveCharacteristicPolynomialFormula,
      fourSiteOppositePositiveCharacteristicVerticalMassPartialFormula,
      Polynomial.coeff_sub, Polynomial.coeff_add,
      Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X, Polynomial.coeff_C] <;>
    simp <;> ring

private theorem resultant_linear_quadratic
    {R : Type*} [CommRing R] (l k q₂ q₁ q₀ : R) :
    Polynomial.resultant
        (Polynomial.C l * Polynomial.X + Polynomial.C k)
        (Polynomial.C q₂ * Polynomial.X ^ 2 +
          Polynomial.C q₁ * Polynomial.X + Polynomial.C q₀)
        1 2 =
      q₂ * k ^ 2 - q₁ * k * l + q₀ * l ^ 2 := by
  let f : Polynomial R := Polynomial.C l * Polynomial.X + Polynomial.C k
  let g : Polynomial R :=
    Polynomial.C q₂ * Polynomial.X ^ 2 +
      Polynomial.C q₁ * Polynomial.X + Polynomial.C q₀
  change (Polynomial.sylvester f g 1 2).det =
    q₂ * k ^ 2 - q₁ * k * l + q₀ * l ^ 2
  have hsylvester :
      Polynomial.sylvester f g 1 2 =
        !![q₀, k, 0;
           q₁, l, k;
           q₂, 0, l] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num +decide [f, g, Polynomial.sylvester,
        Fin.addCases, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
        Polynomial.coeff_X]
  rw [hsylvester, Matrix.det_fin_three]
  simp
  ring

private def fourSiteOppositeResultantQuotient
    (fixed : Lattice.PositiveMassConfig 4) :
    Polynomial (MvPolynomial (Fin 2) Real) :=
  let y : MvPolynomial (Fin 2) Real := MvPolynomial.X 1
  let a := MvPolynomial.C (frozenInverseWeightOne fixed)
  let b := MvPolynomial.C (frozenInverseWeightThree fixed)
  Polynomial.C (MvPolynomial.C (-1 / 2 : Real)) * Polynomial.X +
    Polynomial.C (y + MvPolynomial.C (1 / 4 : Real) * (a + b))

private def fourSiteOppositeResultantRemainder
    (fixed : Lattice.PositiveMassConfig 4) :
    Polynomial (MvPolynomial (Fin 2) Real) :=
  let x : MvPolynomial (Fin 2) Real := MvPolynomial.X 0
  let a := MvPolynomial.C (frozenInverseWeightOne fixed)
  let b := MvPolynomial.C (frozenInverseWeightThree fixed)
  let l := MvPolynomial.C (-1 / 4 : Real) *
    (MvPolynomial.C 3 * a ^ 2 - MvPolynomial.C 2 * a * b +
      MvPolynomial.C 3 * b ^ 2)
  let k := x * (a - b) ^ 2 + a * b * (a + b)
  Polynomial.C l * Polynomial.X + Polynomial.C k

private theorem fourSiteOppositeResultantQuotient_natDegree_le
    (fixed : Lattice.PositiveMassConfig 4) :
    (fourSiteOppositeResultantQuotient fixed).natDegree ≤ 1 := by
  unfold fourSiteOppositeResultantQuotient
  dsimp only
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact (Polynomial.natDegree_C_mul_le _ _).trans
      Polynomial.natDegree_X_le
  · rw [Polynomial.natDegree_C]
    omega

private theorem fourSiteOppositeResultantRemainder_natDegree_le
    (fixed : Lattice.PositiveMassConfig 4) :
    (fourSiteOppositeResultantRemainder fixed).natDegree ≤ 1 := by
  unfold fourSiteOppositeResultantRemainder
  dsimp only
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact (Polynomial.natDegree_C_mul_le _ _).trans
      Polynomial.natDegree_X_le
  · rw [Polynomial.natDegree_C]
    omega

private theorem fourSiteOppositePositiveCharacteristicPolynomial_decomposition
    (fixed : Lattice.PositiveMassConfig 4) :
    fourSiteOppositePositiveCharacteristicPolynomialFormula fixed =
      fourSiteOppositeResultantRemainder fixed +
        fourSiteOppositePositiveCharacteristicVerticalMassPartialFormula fixed *
          fourSiteOppositeResultantQuotient fixed := by
  apply Polynomial.funext
  intro energy
  apply MvPolynomial.funext
  intro coordinates
  simp [fourSiteOppositePositiveCharacteristicPolynomialFormula,
    fourSiteOppositePositiveCharacteristicVerticalMassPartialFormula,
    fourSiteOppositeResultantRemainder, fourSiteOppositeResultantQuotient]
  ring

/-- Exact factorization of the canonical four-site opposite-fiber
characteristic-Jacobian resultant. -/
theorem twoSitePositiveCharacteristicJacobianResultant_zero_two_eq
    (fixed : Lattice.PositiveMassConfig 4) :
    twoSitePositiveCharacteristicJacobianResultant fixed
        (0 : Lattice.Site 4) (2 : Lattice.Site 4) =
      MvPolynomial.C 4 *
        MvPolynomial.C
          (frozenInverseWeightOne fixed - frozenInverseWeightThree fixed) ^ 2 *
        (MvPolynomial.C
            (frozenInverseWeightOne fixed + frozenInverseWeightThree fixed) *
            MvPolynomial.X 0 -
          MvPolynomial.C
            (2 * frozenInverseWeightOne fixed *
              frozenInverseWeightThree fixed)) ^ 2 := by
  unfold twoSitePositiveCharacteristicJacobianResultant
  dsimp only
  rw [twoSitePositiveCharacteristicPolynomial_zero_two_eq_formula,
    twoSitePositiveCharacteristicVerticalMassPartial_zero_two_eq_formula,
    fourSiteOppositePositiveCharacteristicPolynomialFormula_natDegree_eq,
    fourSiteOppositePositiveCharacteristicVerticalMassPartialFormula_natDegree_eq,
    fourSiteOppositePositiveCharacteristicPolynomial_decomposition]
  let r := fourSiteOppositeResultantRemainder fixed
  let q :=
    fourSiteOppositePositiveCharacteristicVerticalMassPartialFormula fixed
  let s := fourSiteOppositeResultantQuotient fixed
  have hr : r.natDegree ≤ 1 :=
    fourSiteOppositeResultantRemainder_natDegree_le fixed
  have hq : q.natDegree ≤ 2 :=
    fourSiteOppositePositiveCharacteristicVerticalMassPartialFormula_natDegree_le fixed
  have hs : s.natDegree ≤ 1 :=
    fourSiteOppositeResultantQuotient_natDegree_le fixed
  calc
    Polynomial.resultant (r + q * s) q 3 2 =
        Polynomial.resultant r q 3 2 := by
      exact Polynomial.resultant_add_mul_left r q s 3 2 (by omega) hq
    _ = q.coeff 2 ^ 2 * Polynomial.resultant r q 1 2 := by
      have hadd :=
        Polynomial.resultant_add_left_deg r q 1 2 2 hr
      norm_num at hadd ⊢
      exact hadd
    _ = MvPolynomial.C 4 *
        MvPolynomial.C
          (frozenInverseWeightOne fixed - frozenInverseWeightThree fixed) ^ 2 *
        (MvPolynomial.C
            (frozenInverseWeightOne fixed + frozenInverseWeightThree fixed) *
            MvPolynomial.X 0 -
          MvPolynomial.C
            (2 * frozenInverseWeightOne fixed *
              frozenInverseWeightThree fixed)) ^ 2 := by
      rw [show q.coeff 2 = -MvPolynomial.C 2 by
        simpa [q] using
          fourSiteOppositePositiveCharacteristicVerticalMassPartialFormula_coeff_two
            fixed]
      simp only [neg_sq]
      unfold r q fourSiteOppositeResultantRemainder
        fourSiteOppositePositiveCharacteristicVerticalMassPartialFormula
      dsimp only
      rw [resultant_linear_quadratic]
      apply MvPolynomial.funext
      intro coordinates
      simp
      ring

/-- Pointwise form of the exact factorization. -/
@[simp] theorem twoSitePositiveCharacteristicJacobianResultant_zero_two_eval
    (fixed : Lattice.PositiveMassConfig 4) (coordinates : Fin 2 → Real) :
    MvPolynomial.eval coordinates
        (twoSitePositiveCharacteristicJacobianResultant fixed
          (0 : Lattice.Site 4) (2 : Lattice.Site 4)) =
      4 * (frozenInverseWeightOne fixed -
          frozenInverseWeightThree fixed) ^ 2 *
        ((frozenInverseWeightOne fixed + frozenInverseWeightThree fixed) *
            coordinates 0 -
          2 * frozenInverseWeightOne fixed *
            frozenInverseWeightThree fixed) ^ 2 := by
  rw [twoSitePositiveCharacteristicJacobianResultant_zero_two_eq]
  simp

/-- Evaluation at the zero varied coordinates is a legal nonvanishing
witness whenever the two frozen positive inverse masses differ. -/
@[simp] theorem twoSitePositiveCharacteristicJacobianResultant_zero_two_eval_zero
    (fixed : Lattice.PositiveMassConfig 4) :
    MvPolynomial.eval (fun _ : Fin 2 => 0)
        (twoSitePositiveCharacteristicJacobianResultant fixed
          (0 : Lattice.Site 4) (2 : Lattice.Site 4)) =
      16 * frozenInverseWeightOne fixed ^ 2 *
        frozenInverseWeightThree fixed ^ 2 *
        (frozenInverseWeightOne fixed -
          frozenInverseWeightThree fixed) ^ 2 := by
  rw [twoSitePositiveCharacteristicJacobianResultant_zero_two_eval]
  ring

/-- The exact frozen-background exceptional set: the resultant polynomial is
zero precisely when the two frozen inverse masses agree. -/
@[simp] theorem twoSitePositiveCharacteristicJacobianResultant_zero_two_eq_zero_iff
    (fixed : Lattice.PositiveMassConfig 4) :
    twoSitePositiveCharacteristicJacobianResultant fixed
        (0 : Lattice.Site 4) (2 : Lattice.Site 4) = 0 ↔
      frozenInverseWeightOne fixed = frozenInverseWeightThree fixed := by
  constructor
  · intro hzero
    have heval := congrArg
      (MvPolynomial.eval (fun _ : Fin 2 => 0)) hzero
    rw [twoSitePositiveCharacteristicJacobianResultant_zero_two_eval_zero] at heval
    simp only [map_zero] at heval
    have ha : frozenInverseWeightOne fixed ≠ 0 :=
      ne_of_gt (frozenInverseWeightOne_pos fixed)
    have hb : frozenInverseWeightThree fixed ≠ 0 :=
      ne_of_gt (frozenInverseWeightThree_pos fixed)
    rcases mul_eq_zero.mp heval with hleft | hdiff
    · rcases mul_eq_zero.mp hleft with hleft | hbzero
      · rcases mul_eq_zero.mp hleft with h16 | hazero
        · norm_num at h16
        · exact (ha (sq_eq_zero_iff.mp hazero)).elim
      · exact (hb (sq_eq_zero_iff.mp hbzero)).elim
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp hdiff)
  · intro hab
    rw [twoSitePositiveCharacteristicJacobianResultant_zero_two_eq, hab]
    simp

/-- For positive frozen weights, polynomial nonvanishing is equivalent to
inequality of those weights. -/
@[simp] theorem twoSitePositiveCharacteristicJacobianResultant_zero_two_ne_zero_iff
    (fixed : Lattice.PositiveMassConfig 4) :
    twoSitePositiveCharacteristicJacobianResultant fixed
        (0 : Lattice.Site 4) (2 : Lattice.Site 4) ≠ 0 ↔
      frozenInverseWeightOne fixed ≠ frozenInverseWeightThree fixed :=
  not_congr
    (twoSitePositiveCharacteristicJacobianResultant_zero_two_eq_zero_iff fixed)

/-- The requested frozen-fiber nonvanishing implication. -/
theorem twoSitePositiveCharacteristicJacobianResultant_zero_two_ne_zero
    (fixed : Lattice.PositiveMassConfig 4)
    (hfrozen :
      frozenInverseWeightOne fixed ≠ frozenInverseWeightThree fixed) :
    twoSitePositiveCharacteristicJacobianResultant fixed
        (0 : Lattice.Site 4) (2 : Lattice.Site 4) ≠ 0 :=
  (twoSitePositiveCharacteristicJacobianResultant_zero_two_ne_zero_iff
    fixed).2 hfrozen

/-- The full evaluated zero set includes the varied-coordinate affine
hypersurface; this is distinct from the frozen-background polynomial
exceptional set. -/
@[simp] theorem twoSitePositiveCharacteristicJacobianResultant_zero_two_eval_eq_zero_iff
    (fixed : Lattice.PositiveMassConfig 4) (coordinates : Fin 2 → Real) :
    MvPolynomial.eval coordinates
        (twoSitePositiveCharacteristicJacobianResultant fixed
          (0 : Lattice.Site 4) (2 : Lattice.Site 4)) = 0 ↔
      frozenInverseWeightOne fixed = frozenInverseWeightThree fixed ∨
        (frozenInverseWeightOne fixed + frozenInverseWeightThree fixed) *
            coordinates 0 =
          2 * frozenInverseWeightOne fixed *
            frozenInverseWeightThree fixed := by
  rw [twoSitePositiveCharacteristicJacobianResultant_zero_two_eval]
  norm_num [mul_eq_zero, sub_eq_zero]

end

end ArchonPhysics.FourSiteOppositeCanonicalResultantFrozenFiber
