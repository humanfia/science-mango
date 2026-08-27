import ArchonPhysics.ActualSixSiteNearResonantCollisionWeightWitness
import ArchonPhysics.ActualSixSiteNearResonantGenericClearedContractionPolynomial

/-!
# The fixed six-site contraction and its certified quotient residual

At `t = 1 / 10`, the un-cleared shifted-adjugate contraction is a rational
polynomial in the three spectral energies.  This file certifies its successive
division by the three copies of the monic characteristic quintic and identifies
the final normal form with the rational table used by the modular collision
certificate.

The quotient identity is kept over `Rat`, where it is decidable computation.
Separate map/evaluation lemmas transport it to the genuine real finite
contraction and to the denominator-cleared generic polynomial.
-/

open scoped BigOperators Matrix

namespace ArchonPhysics.ActualSixSiteNearResonantFixedContractionResidualBridge

open ArchonPhysics
open ArchonPhysics.ActualSixSiteNearResonantAdjugateBridge
open ArchonPhysics.ActualSixSiteNearResonantClearedContraction
open ArchonPhysics.ActualSixSiteNearResonantCollisionWeightWitness
open ArchonPhysics.ActualSixSiteNearResonantFiniteContractionBridge
open ArchonPhysics.ActualSixSiteNearResonantGenericClearedContractionPolynomial
open ArchonPhysics.ActualSixSiteNearResonantInteractionAlgebra

noncomputable section

namespace FixedCertificate

abbrev SpectralVariable := Fin 3

/-- A trivariate rational monomial in the fixed spectral variables. -/
def monomial (i j k : Nat) (coefficient : Rat) :
    MvPolynomial SpectralVariable Rat :=
  MvPolynomial.C coefficient * MvPolynomial.X 0 ^ i *
    MvPolynomial.X 1 ^ j * MvPolynomial.X 2 ^ k

/-- The monic positive characteristic quintic at `t = 1 / 10`, placed in
one of the three spectral variables. -/
def spectralQuintic (r : SpectralVariable) :
    MvPolynomial SpectralVariable Rat :=
  MvPolynomial.X r ^ 5 -
    MvPolynomial.C (1192 / 99) * MvPolynomial.X r ^ 4 +
    MvPolynomial.C (163 / 3) * MvPolynomial.X r ^ 3 -
    MvPolynomial.C (11180 / 99) * MvPolynomial.X r ^ 2 +
    MvPolynomial.C (10495 / 99) * MvPolynomial.X r -
    MvPolynomial.C (400 / 11)

/-- The rational fixed-point version of the genuine un-cleared shifted
matrix. -/
def shiftedMatrix (energy : MvPolynomial SpectralVariable Rat) :
    Matrix (Fin 6) (Fin 6) (MvPolynomial SpectralVariable Rat) :=
  !![energy - MvPolynomial.C (200 / 99), MvPolynomial.C (10 / 11), 0, 0, 0,
      MvPolynomial.C (10 / 9);
     MvPolynomial.C (10 / 11), energy - MvPolynomial.C (21 / 11), 1, 0, 0, 0;
     0, 1, energy - 2, 1, 0, 0;
     0, 0, 1, energy - 2, 1, 0;
     0, 0, 0, 1, energy - 2, 1;
     MvPolynomial.C (10 / 9), 0, 0, 0, 1,
      energy - MvPolynomial.C (19 / 9)]

/-- Fully expanded determinant formula in dimension four, over an arbitrary
commutative ring. -/
def detFinFourFormula {R : Type*} [CommRing R]
    (M : Matrix (Fin 4) (Fin 4) R) : R :=
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
          M 1 2 * (M 2 0 * M 3 1 - M 2 1 * M 3 0))

theorem det_fin_four_eq_formula {R : Type*} [CommRing R]
    (M : Matrix (Fin 4) (Fin 4) R) :
    M.det = detFinFourFormula M := by
  rw [Matrix.det_succ_row _ 0]
  simp only [Fin.sum_univ_succ, Matrix.det_fin_three]
  norm_num +decide [Fin.succAbove, detFinFourFormula]
  rw [show Fin.succ (2 : Fin 3) = (3 : Fin 4) by decide]
  rw [show Fin.castSucc (2 : Fin 3) = (2 : Fin 4) by decide]
  ring

/-- Five-dimensional Laplace expansion using the explicit four-dimensional
formula. -/
def detFinFiveFormula {R : Type*} [CommRing R]
    (M : Matrix (Fin 5) (Fin 5) R) : R :=
  ∑ j : Fin 5, (-1) ^ (j : Nat) * M 0 j *
    detFinFourFormula (M.submatrix Fin.succ j.succAbove)

theorem det_fin_five_eq_formula {R : Type*} [CommRing R]
    (M : Matrix (Fin 5) (Fin 5) R) :
    M.det = detFinFiveFormula M := by
  unfold detFinFiveFormula
  rw [Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [det_fin_four_eq_formula]

/-- A computable six-dimensional adjugate entry. -/
def computedAdjugateEntry {R : Type*} [CommRing R]
    (M : Matrix (Fin 6) (Fin 6) R) (i j : Fin 6) : R :=
  (-1) ^ (j + i : Nat) *
    detFinFiveFormula (M.submatrix j.succAbove i.succAbove)

theorem computedAdjugateEntry_eq_adjugate {R : Type*} [CommRing R]
    (M : Matrix (Fin 6) (Fin 6) R) (i j : Fin 6) :
    computedAdjugateEntry M i j = M.adjugate i j := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix,
    det_fin_five_eq_formula]
  rfl

/-- Coefficients, in ascending powers of the energy, of the 36 entries of
the fixed rational adjugate.  This small explicit table is the certificate
boundary between the determinant calculation and the trivariate quotient
calculation below. -/
def adjugateCoeff : Fin 6 → Fin 6 → Fin 6 → Rat :=
  fun i j k => ![
    ![![(-200/33),(1165/33),(-620/11),(1193/33),(-992/99),1],
      ![(-200/33),(1900/99),(-650/33),(730/99),(-10/11),0],
      ![(-200/33),(350/33),(-50/9),(10/11),0,0],
      ![(-200/33),(800/99),(-200/99),0,0,0],
      ![(-200/33),(1150/99),(-650/99),(10/9),0,0],
      ![(-200/33),(700/33),(-250/11),(290/33),(-10/9),0]],
    ![![(-200/33),(1900/99),(-650/33),(730/99),(-10/11),0],
      ![(-200/33),(3539/99),(-5690/99),(405/11),(-1003/99),1],
      ![(-200/33),(2029/99),(-194/9),(805/99),-1,0],
      ![(-200/33),(373/33),(-607/99),1,0,0],
      ![(-200/33),(809/99),(-199/99),0,0,0],
      ![(-200/33),(1099/99),(-200/33),(100/99),0,0]],
    ![![(-200/33),(350/33),(-50/9),(10/11),0,0],
      ![(-200/33),(2029/99),(-194/9),(805/99),-1,0],
      ![(-200/33),(391/11),(-5603/99),(3589/99),(-994/99),1],
      ![(-200/33),(2009/99),(-2096/99),(796/99),-1,0],
      ![(-200/33),(1099/99),(-598/99),1,0,0],
      ![(-200/33),(263/33),(-199/99),0,0,0]],
    ![![(-200/33),(800/99),(-200/99),0,0,0],
      ![(-200/33),(373/33),(-607/99),1,0,0],
      ![(-200/33),(2009/99),(-2096/99),(796/99),-1,0],
      ![(-200/33),(3499/99),(-5594/99),(3589/99),(-994/99),1],
      ![(-200/33),(221/11),(-2096/99),(796/99),-1,0],
      ![(-200/33),(1079/99),(-587/99),1,0,0]],
    ![![(-200/33),(1150/99),(-650/99),(10/9),0,0],
      ![(-200/33),(809/99),(-199/99),0,0,0],
      ![(-200/33),(1099/99),(-598/99),1,0,0],
      ![(-200/33),(221/11),(-2096/99),(796/99),-1,0],
      ![(-200/33),(3479/99),(-1861/33),(3589/99),(-994/99),1],
      ![(-200/33),(179/9),(-2054/99),(785/99),-1,0]],
    ![![(-200/33),(700/33),(-250/11),(290/33),(-10/9),0],
      ![(-200/33),(1099/99),(-200/33),(100/99),0,0],
      ![(-200/33),(263/33),(-199/99),0,0,0],
      ![(-200/33),(1079/99),(-587/99),1,0,0],
      ![(-200/33),(179/9),(-2054/99),(785/99),-1,0],
      ![(-200/33),(1153/33),(-610/11),(1175/33),(-983/99),1]]
  ] i j k

/-- The table entry reconstructed as a degree-at-most-five polynomial. -/
def tableAdjugateEntry (energy : MvPolynomial SpectralVariable Rat)
    (i j : Fin 6) : MvPolynomial SpectralVariable Rat :=
  ∑ k : Fin 6, MvPolynomial.C (adjugateCoeff i j k) * energy ^ k.val



@[simp] theorem vecFour_apply_two {α : Type*} (a b c d : α) :
    (![a, b, c, d] : Fin 4 → α) (2 : Fin 4) = c := by
  rfl

@[simp] theorem vecFour_apply_three {α : Type*} (a b c d : α) :
    (![a, b, c, d] : Fin 4 → α) (3 : Fin 4) = d := by
  rfl

theorem natCast_eq_rat_smul_one (n : Nat) :
    (n : MvPolynomial SpectralVariable Rat) =
      (n : Rat) • (1 : MvPolynomial SpectralVariable Rat) := by
  rw [← MvPolynomial.C_eq_coe_nat,
    MvPolynomial.C_eq_smul_one]

theorem two_eq_rat_smul_one :
    (2 : MvPolynomial SpectralVariable Rat) =
      (2 : Rat) • (1 : MvPolynomial SpectralVariable Rat) :=
  natCast_eq_rat_smul_one 2

theorem three_eq_rat_smul_one :
    (3 : MvPolynomial SpectralVariable Rat) =
      (3 : Rat) • (1 : MvPolynomial SpectralVariable Rat) :=
  natCast_eq_rat_smul_one 3

theorem four_eq_rat_smul_one :
    (4 : MvPolynomial SpectralVariable Rat) =
      (4 : Rat) • (1 : MvPolynomial SpectralVariable Rat) :=
  natCast_eq_rat_smul_one 4

theorem five_eq_rat_smul_one :
    (5 : MvPolynomial SpectralVariable Rat) =
      (5 : Rat) • (1 : MvPolynomial SpectralVariable Rat) :=
  natCast_eq_rat_smul_one 5

theorem six_eq_rat_smul_one :
    (6 : MvPolynomial SpectralVariable Rat) =
      (6 : Rat) • (1 : MvPolynomial SpectralVariable Rat) :=
  natCast_eq_rat_smul_one 6

theorem seven_eq_rat_smul_one :
    (7 : MvPolynomial SpectralVariable Rat) =
      (7 : Rat) • (1 : MvPolynomial SpectralVariable Rat) :=
  natCast_eq_rat_smul_one 7

theorem eight_eq_rat_smul_one :
    (8 : MvPolynomial SpectralVariable Rat) =
      (8 : Rat) • (1 : MvPolynomial SpectralVariable Rat) :=
  natCast_eq_rat_smul_one 8

theorem nine_eq_rat_smul_one :
    (9 : MvPolynomial SpectralVariable Rat) =
      (9 : Rat) • (1 : MvPolynomial SpectralVariable Rat) :=
  natCast_eq_rat_smul_one 9

theorem ten_eq_rat_smul_one :
    (10 : MvPolynomial SpectralVariable Rat) =
      (10 : Rat) • (1 : MvPolynomial SpectralVariable Rat) :=
  natCast_eq_rat_smul_one 10
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem tableAdjugateEntry_zero_zero
    (energy : MvPolynomial SpectralVariable Rat) :
    tableAdjugateEntry energy 0 0 =
      computedAdjugateEntry (shiftedMatrix energy) 0 0 := by
  simp (config := { maxSteps := 1000000 }) [tableAdjugateEntry,
    adjugateCoeff, computedAdjugateEntry, detFinFiveFormula,
    detFinFourFormula, shiftedMatrix, Fin.sum_univ_succ,
    Matrix.submatrix_apply, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four]
  norm_num +decide [Fin.succAbove]
  have h0Rat : (-(200 / 33) : Rat) =
      -2 + 3 * (21 / 11) - 4 * (21 / 11) * (19 / 9) + 3 * (19 / 9) := by
    norm_num
  have h1Rat : (1165 / 33 : Rat) =
      -5 + 10 * (21 / 11) * (19 / 9) := by
    norm_num
  have h2Rat : (-(620 / 11) : Rat) =
      4 - 9 * (21 / 11) - 6 * (21 / 11) * (19 / 9) - 9 * (19 / 9) := by
    norm_num
  have h3Rat : (1193 / 33 : Rat) =
      8 + 6 * (21 / 11) + (21 / 11) * (19 / 9) + 6 * (19 / 9) := by
    norm_num
  have h4Rat : (-(992 / 99) : Rat) =
      -6 - (21 / 11) - (19 / 9) := by
    norm_num
  have h0 := congrArg
    (fun q : Rat => (MvPolynomial.C q :
      MvPolynomial SpectralVariable Rat)) h0Rat
  have h1 := congrArg
    (fun q : Rat => (MvPolynomial.C q :
      MvPolynomial SpectralVariable Rat)) h1Rat
  have h2 := congrArg
    (fun q : Rat => (MvPolynomial.C q :
      MvPolynomial SpectralVariable Rat)) h2Rat
  have h3 := congrArg
    (fun q : Rat => (MvPolynomial.C q :
      MvPolynomial SpectralVariable Rat)) h3Rat
  have h4 := congrArg
    (fun q : Rat => (MvPolynomial.C q :
      MvPolynomial SpectralVariable Rat)) h4Rat
  have c2 : (MvPolynomial.C (2 : Rat) :
      MvPolynomial SpectralVariable Rat) = 2 :=
    MvPolynomial.C_eq_coe_nat 2
  have c3 : (MvPolynomial.C (3 : Rat) :
      MvPolynomial SpectralVariable Rat) = 3 :=
    MvPolynomial.C_eq_coe_nat 3
  have c4 : (MvPolynomial.C (4 : Rat) :
      MvPolynomial SpectralVariable Rat) = 4 :=
    MvPolynomial.C_eq_coe_nat 4
  have c5 : (MvPolynomial.C (5 : Rat) :
      MvPolynomial SpectralVariable Rat) = 5 :=
    MvPolynomial.C_eq_coe_nat 5
  have c6 : (MvPolynomial.C (6 : Rat) :
      MvPolynomial SpectralVariable Rat) = 6 :=
    MvPolynomial.C_eq_coe_nat 6
  have c8 : (MvPolynomial.C (8 : Rat) :
      MvPolynomial SpectralVariable Rat) = 8 :=
    MvPolynomial.C_eq_coe_nat 8
  have c9 : (MvPolynomial.C (9 : Rat) :
      MvPolynomial SpectralVariable Rat) = 9 :=
    MvPolynomial.C_eq_coe_nat 9
  have c10 : (MvPolynomial.C (10 : Rat) :
      MvPolynomial SpectralVariable Rat) = 10 :=
    MvPolynomial.C_eq_coe_nat 10
  simp only [MvPolynomial.C_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub,
    MvPolynomial.C_mul] at h0 h1 h2 h3 h4
  simp only [c2, c3, c4, c5, c6, c8, c9, c10] at h0 h1 h2 h3 h4
  linear_combination h0 + energy * h1 + energy ^ 2 * h2 +
    energy ^ 3 * h3 + energy ^ 4 * h4

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem tableAdjugateEntry_zero_one_X (r : SpectralVariable) :
    tableAdjugateEntry (MvPolynomial.X r) 0 1 =
      computedAdjugateEntry (shiftedMatrix (MvPolynomial.X r)) 0 1 := by
  simp (config := { maxSteps := 1000000 }) [tableAdjugateEntry,
    adjugateCoeff, computedAdjugateEntry, detFinFiveFormula,
    detFinFourFormula, shiftedMatrix, Fin.sum_univ_succ,
    Matrix.submatrix_apply, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, Matrix.cons_val', Matrix.vecHead, Matrix.vecTail]
  norm_num +decide [Fin.succAbove, Fin.castSucc, Fin.castAdd, Fin.castLE]
  simp (config := { maxSteps := 1000000 }) [Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
  have h0Rat : (-(200 / 33) : Rat) =
      -(10 / 11) * (4 * (19 / 9) - 3) - 10 / 9 := by norm_num
  have h1Rat : (1900 / 99 : Rat) = (10 / 11) * 10 * (19 / 9) := by norm_num
  have h2Rat : (-(650 / 33) : Rat) =
      -(10 / 11) * (9 + 6 * (19 / 9)) := by norm_num
  have h3Rat : (730 / 99 : Rat) = (10 / 11) * (6 + 19 / 9) := by norm_num
  have h0 := congrArg
    (fun q : Rat => (MvPolynomial.C q : MvPolynomial SpectralVariable Rat)) h0Rat
  have h1 := congrArg
    (fun q : Rat => (MvPolynomial.C q : MvPolynomial SpectralVariable Rat)) h1Rat
  have h2 := congrArg
    (fun q : Rat => (MvPolynomial.C q : MvPolynomial SpectralVariable Rat)) h2Rat
  have h3 := congrArg
    (fun q : Rat => (MvPolynomial.C q : MvPolynomial SpectralVariable Rat)) h3Rat
  have c3 : (MvPolynomial.C (3 : Rat) :
      MvPolynomial SpectralVariable Rat) = 3 := MvPolynomial.C_eq_coe_nat 3
  have c4 : (MvPolynomial.C (4 : Rat) :
      MvPolynomial SpectralVariable Rat) = 4 := MvPolynomial.C_eq_coe_nat 4
  have c6 : (MvPolynomial.C (6 : Rat) :
      MvPolynomial SpectralVariable Rat) = 6 := MvPolynomial.C_eq_coe_nat 6
  have c9 : (MvPolynomial.C (9 : Rat) :
      MvPolynomial SpectralVariable Rat) = 9 := MvPolynomial.C_eq_coe_nat 9
  have c10 : (MvPolynomial.C (10 : Rat) :
      MvPolynomial SpectralVariable Rat) = 10 := MvPolynomial.C_eq_coe_nat 10
  simp only [MvPolynomial.C_neg, MvPolynomial.C_add, MvPolynomial.C_sub,
    MvPolynomial.C_mul] at h0 h1 h2 h3
  simp only [c3, c4, c6, c9, c10] at h0 h1 h2 h3
  linear_combination h0 + MvPolynomial.X r * h1 +
    (MvPolynomial.X r) ^ 2 * h2 + (MvPolynomial.X r) ^ 3 * h3
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem tableAdjugateEntry_X_eq_computedAdjugateEntry_row_zero
    (r : SpectralVariable) (j : Fin 6) :
    tableAdjugateEntry (MvPolynomial.X r) 0 j =
      computedAdjugateEntry (shiftedMatrix (MvPolynomial.X r)) 0 j := by
  apply MvPolynomial.funext
  intro x
  fin_cases j <;>
    simp (config := { maxSteps := 1000000 }) [tableAdjugateEntry,
      adjugateCoeff, computedAdjugateEntry, detFinFiveFormula,
      detFinFourFormula, shiftedMatrix, Fin.sum_univ_succ,
      Matrix.submatrix_apply, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_one, Matrix.cons_val', Matrix.vecHead, Matrix.vecTail]
  all_goals norm_num +decide [Fin.succAbove, Fin.castSucc, Fin.castAdd, Fin.castLE]
  all_goals try
    simp (config := { maxSteps := 1000000 }) [Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
  all_goals ring

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- The explicit coefficient table is checked against the determinant formula
at exactly the three spectral indeterminates used by `rawPolynomial`.  The
statement is a closed finite proposition, so `decide` evaluates all
`3 * 6 * 6` rational multivariate-polynomial equalities. -/
theorem tableAdjugateEntry_X_eq_computedAdjugateEntry :
    ∀ (r : SpectralVariable) (i j : Fin 6),
      tableAdjugateEntry (MvPolynomial.X r) i j =
        computedAdjugateEntry (shiftedMatrix (MvPolynomial.X r)) i j := by
  intro r i j
  fin_cases i
  · exact tableAdjugateEntry_X_eq_computedAdjugateEntry_row_zero r j
  all_goals
    apply MvPolynomial.funext
    intro x
    fin_cases j <;>
      simp (config := { maxSteps := 1000000 }) [tableAdjugateEntry,
        adjugateCoeff, computedAdjugateEntry, detFinFiveFormula,
        detFinFourFormula, shiftedMatrix, Fin.sum_univ_succ,
        Matrix.submatrix_apply, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_one, Matrix.cons_val', Matrix.vecHead, Matrix.vecTail]
  all_goals norm_num +decide [Fin.succAbove, Fin.castSucc, Fin.castAdd, Fin.castLE]
  all_goals try
    simp (config := { maxSteps := 1000000 }) [Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
  all_goals ring

/-- The computable matrix-derived un-cleared three-adjugate contraction at
`t = 1 / 10`.  The separate equality below links this certificate-side
definition to Mathlib's noncomputable adjugate. -/
def rawPolynomial : MvPolynomial SpectralVariable Rat :=
  ∑ i : Fin 6, ∑ j : Fin 6, ∏ r : Fin 3,
    tableAdjugateEntry (MvPolynomial.X r) i j

theorem rawPolynomial_eq_adjugateContraction :
    rawPolynomial =
      adjugateEntryProductContraction
        (fun r => shiftedMatrix (MvPolynomial.X r)) := by
  unfold rawPolynomial adjugateEntryProductContraction
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.prod_congr rfl
  intro r _hr
  rw [tableAdjugateEntry_X_eq_computedAdjugateEntry,
    computedAdjugateEntry_eq_adjugate]

/-- The degree-`< 5` trivariate residual encoded by the 125-entry rational
certificate table. -/
def residualPolynomial : MvPolynomial SpectralVariable Rat :=
  ∑ a : ModularCertificate.CubeIndex,
    monomial a.1.val a.2.1.val a.2.2.val
      (ModularCertificate.residualCube a)

/-- First successive quotient, for division in the first energy variable. -/
def quotientX : MvPolynomial SpectralVariable Rat :=
  monomial 0 5 5 6 +
  monomial 0 5 4 (-5960 / 99) +
  monomial 0 5 3 (652 / 3) +
  monomial 0 5 2 (-11180 / 33) +
  monomial 0 5 1 (20990 / 99) +
  monomial 0 5 0 (-400 / 11) +
  monomial 0 4 5 (-5960 / 99) +
  monomial 0 4 4 (657830 / 1089) +
  monomial 0 4 3 (-2374864 / 1089) +
  monomial 0 4 2 (11106140 / 3267) +
  monomial 0 4 1 (-20850872 / 9801) +
  monomial 0 4 0 (1192000 / 3267) +
  monomial 0 3 5 (652 / 3) +
  monomial 0 3 4 (-2374864 / 1089) +
  monomial 0 3 3 (25721218 / 3267) +
  monomial 0 3 2 (-10935140 / 891) +
  monomial 0 3 1 (25091656 / 3267) +
  monomial 0 3 0 (-130400 / 99) +
  monomial 0 2 5 (-11180 / 33) +
  monomial 0 2 4 (11106140 / 3267) +
  monomial 0 2 3 (-10935140 / 891) +
  monomial 0 2 2 (20834326 / 1089) +
  monomial 0 2 1 (-4346020 / 363) +
  monomial 0 2 0 (2236000 / 1089) +
  monomial 0 1 5 (20990 / 99) +
  monomial 0 1 4 (-20850872 / 9801) +
  monomial 0 1 3 (25091656 / 3267) +
  monomial 0 1 2 (-4346020 / 363) +
  monomial 0 1 1 (24478010 / 3267) +
  monomial 0 1 0 (-4198000 / 3267) +
  monomial 0 0 5 (-400 / 11) +
  monomial 0 0 4 (1192000 / 3267) +
  monomial 0 0 3 (-130400 / 99) +
  monomial 0 0 2 (2236000 / 1089) +
  monomial 0 0 1 (-4198000 / 3267) +
  monomial 0 0 0 (80000 / 363)

/-- Second successive quotient, after reducing in the first energy
variable. -/
def quotientY : MvPolynomial SpectralVariable Rat :=
  monomial 4 0 5 (1192 / 99) +
  monomial 4 0 4 (-1183850 / 9801) +
  monomial 4 0 3 (1424432 / 3267) +
  monomial 4 0 2 (-740140 / 1089) +
  monomial 4 0 1 (1389736 / 3267) +
  monomial 4 0 0 (-238400 / 3267) +
  monomial 3 0 5 (-326 / 3) +
  monomial 3 0 4 (3561688 / 3267) +
  monomial 3 0 3 (-12856970 / 3267) +
  monomial 3 0 2 (5465920 / 891) +
  monomial 3 0 1 (-4181138 / 1089) +
  monomial 3 0 0 (65200 / 99) +
  monomial 2 0 5 (11180 / 33) +
  monomial 2 0 4 (-3028580 / 891) +
  monomial 2 0 3 (10932940 / 891) +
  monomial 2 0 2 (-62489422 / 3267) +
  monomial 2 0 1 (117325660 / 9801) +
  monomial 2 0 0 (-2236000 / 1089) +
  monomial 1 0 5 (-41980 / 99) +
  monomial 1 0 4 (1263616 / 297) +
  monomial 1 0 3 (-50178484 / 3267) +
  monomial 1 0 2 (78219920 / 3267) +
  monomial 1 0 1 (-146856020 / 9801) +
  monomial 1 0 0 (8396000 / 3267) +
  monomial 0 0 5 (2000 / 11) +
  monomial 0 0 4 (-5960000 / 3267) +
  monomial 0 0 3 (652000 / 99) +
  monomial 0 0 2 (-11180000 / 1089) +
  monomial 0 0 1 (20990000 / 3267) +
  monomial 0 0 0 (-400000 / 363)

/-- Third successive quotient, after reducing in the first two energy
variables. -/
def quotientZ : MvPolynomial SpectralVariable Rat :=
  monomial 4 4 0 (237014 / 9801) +
  monomial 4 3 0 (-237608 / 1089) +
  monomial 4 2 0 (6665300 / 9801) +
  monomial 4 1 0 (-8340832 / 9801) +
  monomial 4 0 0 (1192000 / 3267) +
  monomial 3 4 0 (-237608 / 1089) +
  monomial 3 3 0 (6432124 / 3267) +
  monomial 3 2 0 (-5468120 / 891) +
  monomial 3 1 0 (25091656 / 3267) +
  monomial 3 0 0 (-326000 / 99) +
  monomial 2 4 0 (6665300 / 9801) +
  monomial 2 3 0 (-5468120 / 891) +
  monomial 2 2 0 (20834326 / 1089) +
  monomial 2 1 0 (-21334240 / 891) +
  monomial 2 0 0 (11180000 / 1089) +
  monomial 1 4 0 (-8340832 / 9801) +
  monomial 1 3 0 (25091656 / 3267) +
  monomial 1 2 0 (-21334240 / 891) +
  monomial 1 1 0 (293724080 / 9801) +
  monomial 1 0 0 (-41980000 / 3267) +
  monomial 0 4 0 (1192000 / 3267) +
  monomial 0 3 0 (-326000 / 99) +
  monomial 0 2 0 (11180000 / 1089) +
  monomial 0 1 0 (-41980000 / 3267) +
  monomial 0 0 0 (2000000 / 363)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- Kernel-checked successive-division certificate for the fixed genuine
un-cleared contraction. -/
theorem rawPolynomial_eq_residual_add_quotients :
    rawPolynomial =
      residualPolynomial + spectralQuintic 0 * quotientX +
        spectralQuintic 1 * quotientY + spectralQuintic 2 * quotientZ := by
  apply MvPolynomial.funext
  intro x
  simp (config := { maxSteps := 10000000 }) [rawPolynomial,
    tableAdjugateEntry, adjugateCoeff, residualPolynomial, spectralQuintic,
    quotientX, quotientY, quotientZ, monomial,
    ModularCertificate.residualCube, ModularCertificate.residualCoeff,
    ModularCertificate.flattenIndex,
    ArchonPhysics.ActualSixSiteNearResonantModularTruthLink.residualCoeff,
    ArchonPhysics.ActualSixSiteNearResonantModularTruthLink.residualCoeffArray,
    Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.prod_univ_succ]
  ring

end FixedCertificate

end

end ArchonPhysics.ActualSixSiteNearResonantFixedContractionResidualBridge
