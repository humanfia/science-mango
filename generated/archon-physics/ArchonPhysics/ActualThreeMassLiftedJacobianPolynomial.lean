import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import ArchonPhysics.ActualThreeMassLiftedRegularSpectralPatch
import ArchonPhysics.ActualTwoMassSpectralJacobianPolynomial

/-!
# Actual three-mass lifted Jacobian polynomial: four-site witness

This module computes the exact characteristic cubic for the genuine periodic
four-site random-mass harmonic matrix with three varied masses and one frozen
unit mass.  It proves that the explicit inverse-mass coefficient Jacobian is
nonzero off a nonzero polynomial zero set, transports the coefficient map
through the three positive ordered frequencies by Vieta identities, and
deduces nondegeneracy of the true decay child-child-mismatch Jacobian.

The final theorem is deliberately scoped as a finite-volume regression
witness.  It does not transfer this N=4 calculation to arbitrary volume.
-/

open scoped Matrix

namespace ArchonPhysics.ActualThreeMassLiftedJacobianPolynomial

open ArchonPhysics
open ArchonPhysics.ActualThreeMassLiftedRegularSpectralPatch
open ArchonPhysics.ActualThreeMassLiftedSimpleEigenvalueDifferentiability
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualTwoMassSpectralJacobianPolynomial
open ArchonPhysics.FixedEnergySpectrumAvoidance
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.MassWeightedCycleBridge
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.RandomMassResultantBridge
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Filter Function MeasureTheory Set

noncomputable section

theorem det_fin_four_real (M : Matrix (Fin 4) (Fin 4) Real) :
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

def explicitFourCycleLaplacian (triple : (Real × Real) × Real) :
    Matrix (Fin 4) (Fin 4) Real :=
  let x := triple.1.1⁻¹
  let y := triple.1.2⁻¹
  let z := triple.2⁻¹
  !![x + y, -y, 0, -x;
     -y, y + z, -z, 0;
     0, -z, z + 1, -1;
     -x, 0, -1, 1 + x]

theorem explicitFourCycleLaplacian_charpoly_eval
    (triple : (Real × Real) × Real) (energy : Real) :
    (explicitFourCycleLaplacian triple).charpoly.eval energy =
      energy * (energy ^ 3 -
        2 * (triple.1.1⁻¹ + triple.1.2⁻¹ + triple.2⁻¹ + 1) * energy ^ 2 +
        (3 * triple.1.1⁻¹ * triple.1.2⁻¹ +
          4 * triple.1.1⁻¹ * triple.2⁻¹ + 3 * triple.1.1⁻¹ +
          3 * triple.1.2⁻¹ * triple.2⁻¹ + 4 * triple.1.2⁻¹ +
          3 * triple.2⁻¹) * energy -
        4 * (triple.1.1⁻¹ * triple.1.2⁻¹ * triple.2⁻¹ +
          triple.1.1⁻¹ * triple.1.2⁻¹ +
          triple.1.1⁻¹ * triple.2⁻¹ +
          triple.1.2⁻¹ * triple.2⁻¹)) := by
  rw [Matrix.eval_charpoly, det_fin_four_real]
  simp [explicitFourCycleLaplacian, Matrix.scalar_apply]
  ring

/-- The frozen four-site background; sites zero, one, and two are replaced
by the raw mass triple, while site three stays at unit mass. -/
def frozenUnitMassFour : Lattice.PositiveMassConfig 4 where
  mass _ := 1
  mass_pos _ := by norm_num

/-- Inverse masses of the genuine three-parameter four-cycle family. -/
def fourSiteInverseWeights (triple : MassTriple) : Fin 4 → Real :=
  ![triple.1.1⁻¹, triple.1.2⁻¹, triple.2⁻¹, 1]

/-- Direct finite-matrix identification of the weighted four-cycle. -/
theorem finWeightedCycleLaplacian_fourSiteInverseWeights
    (triple : MassTriple) :
    finWeightedCycleLaplacian (fourSiteInverseWeights triple) =
      explicitFourCycleLaplacian triple := by
  rw [finWeightedCycleLaplacian_eq_sum_rankOne]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, Fin.sum_univ_succ]
  <;> norm_num +decide [fourSiteInverseWeights, explicitFourCycleLaplacian,
    finCycleEdgeVector,
    SingleMassRankOnePerturbation.cycleMassPerturbationVector,
    differenceMatrix, siteEquivFin]
  all_goals simp
  all_goals ring

/-- The actual positive-mass configuration on the four-cycle. -/
def actualFourSiteMassConfig (triple : MassTriple) :
    Lattice.PositiveMassConfig 4 :=
  threeMassSiteConfig frozenUnitMassFour
    (0 : Lattice.Site 4) (1 : Lattice.Site 4) (2 : Lattice.Site 4) triple

/-- The true physical Hermitian harmonic matrix of the four-cycle family. -/
def actualFourSiteHarmonic (triple : MassTriple) :
    HermitianMatrix (Lattice.Site 4) :=
  threeMassHarmonicHermitian frozenUnitMassFour
    (0 : Lattice.Site 4) (1 : Lattice.Site 4) (2 : Lattice.Site 4) triple

/-- On the iid support, the physical inverse-mass coordinates are exactly
the displayed three inverse raw masses followed by the frozen unit weight. -/
theorem inverseMassCoordinates_actualFourSiteMassConfig
    {triple : MassTriple} (htriple : triple ∈ iidMassTripleSupport) :
    RandomMassResultantBridge.inverseMassCoordinates
        (actualFourSiteMassConfig triple) =
      fourSiteInverseWeights triple := by
  funext k
  fin_cases k <;>
    norm_num +decide [RandomMassResultantBridge.inverseMassCoordinates,
      actualFourSiteMassConfig, fourSiteInverseWeights, siteEquivFin,
      threeMassSiteConfig, frozenUnitMassFour, clippedMass_eq_self,
      htriple.1.1, htriple.1.2, htriple.2]

/-- The characteristic equation of the genuine physical four-site matrix. -/
theorem actualFourSiteHarmonic_charpoly_eval
    {triple : MassTriple} (htriple : triple ∈ iidMassTripleSupport)
    (energy : Real) :
    (Matrix.charpoly (Matrix.of (actualFourSiteHarmonic triple).val)).eval energy =
      energy * (energy ^ 3 -
        2 * (triple.1.1⁻¹ + triple.1.2⁻¹ + triple.2⁻¹ + 1) * energy ^ 2 +
        (3 * triple.1.1⁻¹ * triple.1.2⁻¹ +
          4 * triple.1.1⁻¹ * triple.2⁻¹ + 3 * triple.1.1⁻¹ +
          3 * triple.1.2⁻¹ * triple.2⁻¹ + 4 * triple.1.2⁻¹ +
          3 * triple.2⁻¹) * energy -
        4 * (triple.1.1⁻¹ * triple.1.2⁻¹ * triple.2⁻¹ +
          triple.1.1⁻¹ * triple.1.2⁻¹ +
          triple.1.1⁻¹ * triple.2⁻¹ +
          triple.1.2⁻¹ * triple.2⁻¹)) := by
  let m := actualFourSiteMassConfig triple
  have hchar :
      (massWeightedHarmonicMatrix m).charpoly =
        (finWeightedCycleLaplacian
          (RandomMassResultantBridge.inverseMassCoordinates m)).charpoly := by
    calc
      (massWeightedHarmonicMatrix m).charpoly =
          (massWeightedDifferenceMatrix m *
            (Matrix.transpose (massWeightedDifferenceMatrix m))).charpoly := by
        exact Matrix.charpoly_mul_comm
          (Matrix.transpose (massWeightedDifferenceMatrix m))
          (massWeightedDifferenceMatrix m)
      _ = (weightedCycleLaplacian (fun i => (m.mass i)⁻¹)).charpoly := by
        rw [massWeighted_selfTranspose_eq_weightedCycleLaplacian]
      _ = (weightedCycleLaplacian
          (weightsOfCoordinates
            (RandomMassResultantBridge.inverseMassCoordinates m))).charpoly := by
        rw [RandomMassResultantBridge.weightsOfCoordinates_inverseMassCoordinates]
      _ = (finWeightedCycleLaplacian
          (RandomMassResultantBridge.inverseMassCoordinates m)).charpoly := by
        symm
        exact Matrix.charpoly_reindex _ _
  change (massWeightedHarmonicMatrix m).charpoly.eval energy = _
  rw [hchar, inverseMassCoordinates_actualFourSiteMassConfig htriple,
    finWeightedCycleLaplacian_fourSiteInverseWeights]
  exact explicitFourCycleLaplacian_charpoly_eval triple energy

/-- Repackage the coordinatewise inverse of a raw mass triple. -/
def iidInverseMassTripleCoordinates (triple : MassTriple) : Fin 3 → Real :=
  ![triple.1.1⁻¹, triple.1.2⁻¹, triple.2⁻¹]

@[simp] theorem iidInverseMassTripleCoordinates_zero (triple : MassTriple) :
    iidInverseMassTripleCoordinates triple 0 = triple.1.1⁻¹ := rfl

@[simp] theorem iidInverseMassTripleCoordinates_one (triple : MassTriple) :
    iidInverseMassTripleCoordinates triple 1 = triple.1.2⁻¹ := rfl

@[simp] theorem iidInverseMassTripleCoordinates_two (triple : MassTriple) :
    iidInverseMassTripleCoordinates triple 2 = triple.2⁻¹ := rfl

/-- The cleared coefficient-Jacobian numerator for the four-cycle with
the fourth inverse mass frozen to one. -/
def fourSiteCoefficientJacobianPolynomial : MvPolynomial (Fin 3) Real :=
  8 * (MvPolynomial.X 0 - MvPolynomial.X 2) *
    (1 - MvPolynomial.X 2 + 2 * MvPolynomial.X 1 +
      3 * MvPolynomial.X 1 * MvPolynomial.X 2 -
      3 * MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 -
      4 * MvPolynomial.X 0 * MvPolynomial.X 2 +
      3 * MvPolynomial.X 0 * MvPolynomial.X 1)

@[simp] theorem fourSiteCoefficientJacobianPolynomial_eval_inverseMassTriple
    (triple : MassTriple) :
    MvPolynomial.eval (iidInverseMassTripleCoordinates triple)
        fourSiteCoefficientJacobianPolynomial =
      8 * (triple.1.1⁻¹ - triple.2⁻¹) *
        (1 - triple.2⁻¹ + 2 * triple.1.2⁻¹ +
          3 * triple.1.2⁻¹ * triple.2⁻¹ -
          3 * triple.1.2⁻¹ ^ 2 - triple.1.1⁻¹ -
          4 * triple.1.1⁻¹ * triple.2⁻¹ +
          3 * triple.1.1⁻¹ * triple.1.2⁻¹) := by
  simp [fourSiteCoefficientJacobianPolynomial,
    iidInverseMassTripleCoordinates]

theorem fourSiteCoefficientJacobianPolynomial_ne_zero :
    fourSiteCoefficientJacobianPolynomial ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval
      (fun i : Fin 3 => if i = 0 then (2 : Real) else 1)) hzero
  norm_num +decide [fourSiteCoefficientJacobianPolynomial] at heval

/-- The three nonzero characteristic coefficients in inverse-mass
coordinates: the coefficient of E², then E, then the constant term of
the positive cubic factor. -/
def fourSiteInverseCoefficientChart (inverse : MassTriple) : MassTriple :=
  ((-2 * (inverse.1.1 + inverse.1.2 + inverse.2 + 1),
    3 * inverse.1.1 * inverse.1.2 +
      4 * inverse.1.1 * inverse.2 + 3 * inverse.1.1 +
      3 * inverse.1.2 * inverse.2 + 4 * inverse.1.2 +
      3 * inverse.2),
   -4 * (inverse.1.1 * inverse.1.2 * inverse.2 +
      inverse.1.1 * inverse.1.2 + inverse.1.1 * inverse.2 +
      inverse.1.2 * inverse.2))

/-- The actual raw-mass coefficient chart. -/
def actualFourSiteCoefficientChart (triple : MassTriple) : MassTriple :=
  fourSiteInverseCoefficientChart
    ((triple.1.1⁻¹, triple.1.2⁻¹), triple.2⁻¹)

/-- The explicit derivative of the inverse-coordinate coefficient chart. -/
def fourSiteInverseCoefficientDerivative
    (inverse : MassTriple) : MassTriple →L[Real] MassTriple :=
  let dx : MassTriple →L[Real] Real :=
    (ContinuousLinearMap.fst Real Real Real).comp
      (ContinuousLinearMap.fst Real (Real × Real) Real)
  let dy : MassTriple →L[Real] Real :=
    (ContinuousLinearMap.snd Real Real Real).comp
      (ContinuousLinearMap.fst Real (Real × Real) Real)
  let dz : MassTriple →L[Real] Real :=
    ContinuousLinearMap.snd Real (Real × Real) Real
  let da : MassTriple →L[Real] Real := (-2 : Real) • (dx + dy + dz)
  let db : MassTriple →L[Real] Real :=
    (3 * inverse.1.2 + 4 * inverse.2 + 3) • dx +
      (3 * inverse.1.1 + 3 * inverse.2 + 4) • dy +
      (4 * inverse.1.1 + 3 * inverse.1.2 + 3) • dz
  let dc : MassTriple →L[Real] Real :=
    (-4 * (inverse.1.2 * inverse.2 + inverse.1.2 + inverse.2)) • dx +
      (-4 * (inverse.1.1 * inverse.2 + inverse.1.1 + inverse.2)) • dy +
      (-4 * (inverse.1.1 * inverse.1.2 +
        inverse.1.1 + inverse.1.2)) • dz
  (da.prod db).prod dc

theorem hasFDerivAt_fourSiteInverseCoefficientChart
    (inverse : MassTriple) :
    HasFDerivAt fourSiteInverseCoefficientChart
      (fourSiteInverseCoefficientDerivative inverse) inverse := by
  let dx : MassTriple →L[Real] Real :=
    (ContinuousLinearMap.fst Real Real Real).comp
      (ContinuousLinearMap.fst Real (Real × Real) Real)
  let dy : MassTriple →L[Real] Real :=
    (ContinuousLinearMap.snd Real Real Real).comp
      (ContinuousLinearMap.fst Real (Real × Real) Real)
  let dz : MassTriple →L[Real] Real :=
    ContinuousLinearMap.snd Real (Real × Real) Real
  have hx : HasFDerivAt (fun nearby : MassTriple => nearby.1.1)
      dx inverse := by
    simpa [dx, Function.comp_def] using
      (hasFDerivAt_fst.comp inverse hasFDerivAt_fst)
  have hy : HasFDerivAt (fun nearby : MassTriple => nearby.1.2)
      dy inverse := by
    simpa [dy, Function.comp_def] using
      (hasFDerivAt_snd.comp inverse hasFDerivAt_fst)
  have hz : HasFDerivAt (fun nearby : MassTriple => nearby.2)
      dz inverse := by
    simpa [dz] using hasFDerivAt_snd
  have ha : HasFDerivAt
      (fun nearby : MassTriple =>
        -2 * (nearby.1.1 + nearby.1.2 + nearby.2 + 1))
      ((-2 : Real) • (dx + dy + dz)) inverse := by
    simpa [add_assoc] using
      (((hx.add hy).add hz).add_const 1).const_mul (-2)
  have hb : HasFDerivAt
      (fun nearby : MassTriple =>
        3 * nearby.1.1 * nearby.1.2 +
          4 * nearby.1.1 * nearby.2 + 3 * nearby.1.1 +
          3 * nearby.1.2 * nearby.2 + 4 * nearby.1.2 +
          3 * nearby.2)
      ((3 * inverse.1.2 + 4 * inverse.2 + 3) • dx +
        (3 * inverse.1.1 + 3 * inverse.2 + 4) • dy +
        (4 * inverse.1.1 + 3 * inverse.1.2 + 3) • dz) inverse := by
    convert
      ((((((hx.mul hy).const_mul 3).add
        ((hx.mul hz).const_mul 4)).add (hx.const_mul 3)).add
        ((hy.mul hz).const_mul 3)).add (hy.const_mul 4)).add
        (hz.const_mul 3) using 1
    all_goals first
      | rfl
      | (funext nearby; dsimp; ring)
      | (ext <;> simp [dx, dy, dz])
  have hc : HasFDerivAt
      (fun nearby : MassTriple =>
        -4 * (nearby.1.1 * nearby.1.2 * nearby.2 +
          nearby.1.1 * nearby.1.2 + nearby.1.1 * nearby.2 +
          nearby.1.2 * nearby.2))
      ((-4 * (inverse.1.2 * inverse.2 + inverse.1.2 + inverse.2)) • dx +
        (-4 * (inverse.1.1 * inverse.2 + inverse.1.1 + inverse.2)) • dy +
        (-4 * (inverse.1.1 * inverse.1.2 +
          inverse.1.1 + inverse.1.2)) • dz) inverse := by
    convert
      (((((hx.mul hy).mul hz).add (hx.mul hy)).add (hx.mul hz)).add
        (hy.mul hz)).const_mul (-4) using 1
    all_goals first
      | rfl
      | (ext <;> simp [dx, dy, dz] <;> ring)
  convert (ha.prodMk hb).prodMk hc using 1 <;>
    rfl

/-- The cleared Jacobian numerator is exactly the obstruction to injectivity
of the inverse-coordinate characteristic-coefficient derivative. -/
theorem fourSiteInverseCoefficientDerivative_injective
    (inverse : MassTriple)
    (hnumerator :
      8 * (inverse.1.1 - inverse.2) *
        (1 - inverse.2 + 2 * inverse.1.2 +
          3 * inverse.1.2 * inverse.2 -
          3 * inverse.1.2 ^ 2 - inverse.1.1 -
          4 * inverse.1.1 * inverse.2 +
          3 * inverse.1.1 * inverse.1.2) ≠ 0) :
    Function.Injective (fourSiteInverseCoefficientDerivative inverse) := by
  intro u v huv
  let delta : MassTriple := u - v
  let a : Real := delta.1.1
  let b : Real := delta.1.2
  let c : Real := delta.2
  let x : Real := inverse.1.1
  let y : Real := inverse.1.2
  let z : Real := inverse.2
  let d : Real := 3 * y + 4 * z + 3
  let e : Real := 3 * x + 3 * z + 4
  let f : Real := 4 * x + 3 * y + 3
  let g : Real := -4 * (y * z + y + z)
  let h : Real := -4 * (x * z + x + z)
  let i : Real := -4 * (x * y + x + y)
  let determinantExpression : Real :=
    -2 * (e * i - f * h) + 2 * (d * i - f * g) -
      2 * (d * h - e * g)
  let numerator : Real :=
    8 * (x - z) *
      (1 - z + 2 * y + 3 * y * z - 3 * y ^ 2 - x -
        4 * x * z + 3 * x * y)
  have hzero :
      fourSiteInverseCoefficientDerivative inverse delta = 0 := by
    calc
      fourSiteInverseCoefficientDerivative inverse delta =
          fourSiteInverseCoefficientDerivative inverse u -
            fourSiteInverseCoefficientDerivative inverse v :=
        map_sub (fourSiteInverseCoefficientDerivative inverse) u v
      _ = 0 := sub_eq_zero.mpr huv
  have hfirst : -2 * a - 2 * b - 2 * c = 0 := by
    have hfirstRaw :=
      congrArg (fun value : MassTriple => value.1.1) hzero
    simp [fourSiteInverseCoefficientDerivative, delta,
      ContinuousLinearMap.comp_apply] at hfirstRaw
    change -(2 * a) + -(2 * b) + -(2 * c) = 0 at hfirstRaw
    linarith
  have hsecond : d * a + e * b + f * c = 0 := by
    simpa [fourSiteInverseCoefficientDerivative, delta, a, b, c,
      x, y, z, d, e, f, ContinuousLinearMap.comp_apply] using
      congrArg (fun value : MassTriple => value.1.2) hzero
  have hthird : g * a + h * b + i * c = 0 := by
    simpa [fourSiteInverseCoefficientDerivative, delta, a, b, c,
      x, y, z, g, h, i, ContinuousLinearMap.comp_apply] using
      congrArg (fun value : MassTriple => value.2) hzero
  have hdeterminant :
      determinantExpression = numerator := by
    dsimp [determinantExpression, numerator, d, e, f, g, h, i]
    ring
  have hnum : numerator ≠ 0 := by
    simpa [numerator, x, y, z] using hnumerator
  have haRaw : determinantExpression * a = 0 := by
    linear_combination
      (e * i - f * h) * hfirst +
      (2 * (i - h)) * hsecond +
      (2 * (e - f)) * hthird
  have hbRaw : determinantExpression * b = 0 := by
    linear_combination
      (f * g - d * i) * hfirst +
      (2 * (g - i)) * hsecond +
      (2 * (f - d)) * hthird
  have hcRaw : determinantExpression * c = 0 := by
    linear_combination
      (d * h - e * g) * hfirst +
      (2 * (h - g)) * hsecond +
      (2 * (d - e)) * hthird
  have ha : a = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hnum
    rwa [← hdeterminant]
  have hb : b = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hnum
    rwa [← hdeterminant]
  have hc : c = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hnum
    rwa [← hdeterminant]
  have hdelta : delta = 0 := by
    apply Prod.ext
    · apply Prod.ext
      · simpa [a] using ha
      · simpa [b] using hb
    · simpa [c] using hc
  exact sub_eq_zero.mp hdelta

/-- Coordinatewise inversion of the three raw mass coordinates. -/
def rawMassTripleInverse (triple : MassTriple) : MassTriple :=
  ((triple.1.1⁻¹, triple.1.2⁻¹), triple.2⁻¹)

/-- The diagonal derivative of coordinatewise raw-mass inversion. -/
def rawMassTripleInverseDerivative
    (triple : MassTriple) : MassTriple →L[Real] MassTriple :=
  let dx : MassTriple →L[Real] Real :=
    (ContinuousLinearMap.toSpanSingleton Real (-(triple.1.1 ^ 2)⁻¹)).comp
      ((ContinuousLinearMap.fst Real Real Real).comp
        (ContinuousLinearMap.fst Real (Real × Real) Real))
  let dy : MassTriple →L[Real] Real :=
    (ContinuousLinearMap.toSpanSingleton Real (-(triple.1.2 ^ 2)⁻¹)).comp
      ((ContinuousLinearMap.snd Real Real Real).comp
        (ContinuousLinearMap.fst Real (Real × Real) Real))
  let dz : MassTriple →L[Real] Real :=
    (ContinuousLinearMap.toSpanSingleton Real (-(triple.2 ^ 2)⁻¹)).comp
      (ContinuousLinearMap.snd Real (Real × Real) Real)
  (dx.prod dy).prod dz

theorem hasFDerivAt_rawMassTripleInverse
    {triple : MassTriple} (htriple : triple ∈ iidMassTripleSupport) :
    HasFDerivAt rawMassTripleInverse
      (rawMassTripleInverseDerivative triple) triple := by
  have hx0 : triple.1.1 ≠ 0 :=
    ne_of_gt (massLower_pos.trans_le htriple.1.1.1)
  have hy0 : triple.1.2 ≠ 0 :=
    ne_of_gt (massLower_pos.trans_le htriple.1.2.1)
  have hz0 : triple.2 ≠ 0 :=
    ne_of_gt (massLower_pos.trans_le htriple.2.1)
  let px : MassTriple →L[Real] Real :=
    (ContinuousLinearMap.fst Real Real Real).comp
      (ContinuousLinearMap.fst Real (Real × Real) Real)
  let py : MassTriple →L[Real] Real :=
    (ContinuousLinearMap.snd Real Real Real).comp
      (ContinuousLinearMap.fst Real (Real × Real) Real)
  let pz : MassTriple →L[Real] Real :=
    ContinuousLinearMap.snd Real (Real × Real) Real
  let dx : MassTriple →L[Real] Real :=
    (ContinuousLinearMap.toSpanSingleton Real (-(triple.1.1 ^ 2)⁻¹)).comp px
  let dy : MassTriple →L[Real] Real :=
    (ContinuousLinearMap.toSpanSingleton Real (-(triple.1.2 ^ 2)⁻¹)).comp py
  let dz : MassTriple →L[Real] Real :=
    (ContinuousLinearMap.toSpanSingleton Real (-(triple.2 ^ 2)⁻¹)).comp pz
  have hpx : HasFDerivAt (fun nearby : MassTriple => nearby.1.1)
      px triple := by
    simpa [px, Function.comp_def] using
      (hasFDerivAt_fst.comp triple hasFDerivAt_fst)
  have hpy : HasFDerivAt (fun nearby : MassTriple => nearby.1.2)
      py triple := by
    simpa [py, Function.comp_def] using
      (hasFDerivAt_snd.comp triple hasFDerivAt_fst)
  have hpz : HasFDerivAt (fun nearby : MassTriple => nearby.2)
      pz triple := by
    simpa [pz] using hasFDerivAt_snd
  have hdx : HasFDerivAt (fun nearby : MassTriple => nearby.1.1⁻¹)
      dx triple := by
    simpa [dx, px, Function.comp_def] using
      (hasFDerivAt_inv hx0).comp triple hpx
  have hdy : HasFDerivAt (fun nearby : MassTriple => nearby.1.2⁻¹)
      dy triple := by
    simpa [dy, py, Function.comp_def] using
      (hasFDerivAt_inv hy0).comp triple hpy
  have hdz : HasFDerivAt (fun nearby : MassTriple => nearby.2⁻¹)
      dz triple := by
    simpa [dz, pz, Function.comp_def] using
      (hasFDerivAt_inv hz0).comp triple hpz
  convert (hdx.prodMk hdy).prodMk hdz using 1 <;> rfl

theorem rawMassTripleInverseDerivative_injective
    {triple : MassTriple} (htriple : triple ∈ iidMassTripleSupport) :
    Function.Injective (rawMassTripleInverseDerivative triple) := by
  have hx0 : triple.1.1 ≠ 0 :=
    ne_of_gt (massLower_pos.trans_le htriple.1.1.1)
  have hy0 : triple.1.2 ≠ 0 :=
    ne_of_gt (massLower_pos.trans_le htriple.1.2.1)
  have hz0 : triple.2 ≠ 0 :=
    ne_of_gt (massLower_pos.trans_le htriple.2.1)
  intro u v huv
  have hzero : rawMassTripleInverseDerivative triple (u - v) = 0 := by
    calc
      rawMassTripleInverseDerivative triple (u - v) =
          rawMassTripleInverseDerivative triple u -
            rawMassTripleInverseDerivative triple v :=
        map_sub (rawMassTripleInverseDerivative triple) u v
      _ = 0 := sub_eq_zero.mpr huv
  have hxRaw := congrArg (fun value : MassTriple => value.1.1) hzero
  have hyRaw := congrArg (fun value : MassTriple => value.1.2) hzero
  have hzRaw := congrArg (fun value : MassTriple => value.2) hzero
  simp [rawMassTripleInverseDerivative,
    ContinuousLinearMap.comp_apply] at hxRaw hyRaw hzRaw
  have hx : (u - v).1.1 = 0 := by
    exact hxRaw.resolve_right hx0
  have hy : (u - v).1.2 = 0 := by
    exact hyRaw.resolve_right hy0
  have hz : (u - v).2 = 0 := by
    exact hzRaw.resolve_right hz0
  exact sub_eq_zero.mp (Prod.ext (Prod.ext hx hy) hz)

/-- Off the explicit polynomial zero set, the raw-mass characteristic
coefficient chart already has an injective true derivative. -/
theorem exists_hasFDerivAt_actualFourSiteCoefficientChart_injective
    {triple : MassTriple} (htriple : triple ∈ iidMassTripleSupport)
    (hnumerator :
      MvPolynomial.eval (iidInverseMassTripleCoordinates triple)
        fourSiteCoefficientJacobianPolynomial ≠ 0) :
    ∃ derivative : MassTriple →L[Real] MassTriple,
      HasFDerivAt actualFourSiteCoefficientChart derivative triple ∧
        Function.Injective derivative := by
  let inverse := rawMassTripleInverse triple
  let inverseDerivative := rawMassTripleInverseDerivative triple
  let coefficientDerivative :=
    fourSiteInverseCoefficientDerivative inverse
  let derivative := coefficientDerivative.comp inverseDerivative
  have hinverse :
      HasFDerivAt rawMassTripleInverse inverseDerivative triple := by
    simpa [inverseDerivative] using hasFDerivAt_rawMassTripleInverse htriple
  have hcoefficient :
      HasFDerivAt fourSiteInverseCoefficientChart coefficientDerivative
        inverse := by
    simpa [coefficientDerivative] using
      hasFDerivAt_fourSiteInverseCoefficientChart inverse
  have hcoefficientInjective : Function.Injective coefficientDerivative := by
    apply fourSiteInverseCoefficientDerivative_injective
    simpa [inverse, rawMassTripleInverse] using hnumerator
  have hinverseInjective : Function.Injective inverseDerivative := by
    simpa [inverseDerivative] using
      rawMassTripleInverseDerivative_injective htriple
  refine ⟨derivative, ?_, hcoefficientInjective.comp hinverseInjective⟩
  convert hcoefficient.comp triple hinverse using 1 <;> rfl
/-- Repackage three Fin-indexed mass coordinates as the nested MassTriple
convention used by the actual lifted spectral chart. -/
def finThreeArrowMassTriple :
    (Fin 3 → Real) ≃ᵐ MassTriple :=
  ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => Real) 2).trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl Real) MeasurableEquiv.finTwoArrow)).trans
    MeasurableEquiv.prodComm

@[simp] theorem finThreeArrowMassTriple_apply
    (coordinates : Fin 3 → Real) :
    finThreeArrowMassTriple coordinates =
      ((coordinates 0, coordinates 1), coordinates 2) := by
  rfl

theorem measurePreserving_finThreeArrowMassTriple :
    MeasurePreserving finThreeArrowMassTriple
      (finiteMassLaw 3) iidMassTripleLaw := by
  have hfirst :=
    measurePreserving_piFinSuccAbove
      (fun _ : Fin 3 => massCoordinateLaw) (2 : Fin 3)
  have hsecond :=
    MeasurePreserving.prod (MeasurePreserving.id massCoordinateLaw)
      (measurePreserving_finTwoArrow massCoordinateLaw)
  have hthird :=
    Measure.measurePreserving_swap
      (μ := massCoordinateLaw)
      (ν := massCoordinateLaw.prod massCoordinateLaw)
  simpa [finThreeArrowMassTriple, finiteMassLaw, iidMassTripleLaw,
    ArchonPhysics.TwoParameterSpectralAveragingAtlas.iidMassPairLaw] using
      (hfirst.trans hsecond).trans hthird

/-- Every nonzero polynomial in the three inverse mass coordinates avoids
zero under the exact iid mass-triple law. -/
theorem iidMassTripleLaw_zeroSet_eval_inverseCoordinates
    (P : MvPolynomial (Fin 3) Real) (hP : P ≠ 0) :
    iidMassTripleLaw
      {triple |
        MvPolynomial.eval (iidInverseMassTripleCoordinates triple) P = 0} =
      0 := by
  have hpres := measurePreserving_finThreeArrowMassTriple
  have hsetMeas : MeasurableSet
      {triple : MassTriple |
        MvPolynomial.eval (iidInverseMassTripleCoordinates triple) P = 0} := by
    apply MeasurableSet.preimage (isClosed_singleton.measurableSet)
    exact P.continuous_eval.measurable.comp
      (measurable_pi_lambda _ fun i => by
        fin_cases i
        · exact ((measurable_fst.comp measurable_fst).inv)
        · exact ((measurable_snd.comp measurable_fst).inv)
        · exact measurable_snd.inv)
  have hpreimage :
      finThreeArrowMassTriple ⁻¹'
          {triple : MassTriple |
            MvPolynomial.eval
              (iidInverseMassTripleCoordinates triple) P = 0} =
        {coordinates : Fin 3 → Real |
          MvPolynomial.eval (coordinatewiseInv coordinates) P = 0} := by
    ext coordinates
    change MvPolynomial.eval
        (![ (coordinates 0)⁻¹, (coordinates 1)⁻¹, (coordinates 2)⁻¹]
          : Fin 3 → Real) P = 0 ↔
      MvPolynomial.eval (coordinatewiseInv coordinates) P = 0
    have hcoordinates :
        (![ (coordinates 0)⁻¹, (coordinates 1)⁻¹, (coordinates 2)⁻¹]
          : Fin 3 → Real) =
          coordinatewiseInv coordinates := by
      funext i
      fin_cases i <;> rfl
    rw [hcoordinates]
  rw [← hpres.map_eq,
    Measure.map_apply hpres.measurable hsetMeas, hpreimage]
  exact finiteMassLaw_zeroSet_eval_coordinatewiseInv P hP

theorem iidMassTripleLaw_fourSiteCoefficientJacobianPolynomial_zero :
    iidMassTripleLaw
      {triple |
        MvPolynomial.eval (iidInverseMassTripleCoordinates triple)
          fourSiteCoefficientJacobianPolynomial = 0} = 0 := by
  exact iidMassTripleLaw_zeroSet_eval_inverseCoordinates
    fourSiteCoefficientJacobianPolynomial
    fourSiteCoefficientJacobianPolynomial_ne_zero

/-- The three actual positive squared frequencies of the four-cycle. -/
def actualFourSiteFirstEnergy (triple : MassTriple) : Real :=
  orderedEigenvalue (actualFourSiteHarmonic triple) 0

def actualFourSiteSecondEnergy (triple : MassTriple) : Real :=
  orderedEigenvalue (actualFourSiteHarmonic triple) 1

def actualFourSiteThirdEnergy (triple : MassTriple) : Real :=
  orderedEigenvalue (actualFourSiteHarmonic triple) 2

/-- Under simple spectrum, the first three four-site modes are exactly the
positive modes preceding the fixed last translation mode. -/
theorem actualFourSite_first_second_third_energy_pos
    (triple : MassTriple)
    (hsimple : SimpleOrderedSpectrum (actualFourSiteHarmonic triple)) :
    0 < actualFourSiteFirstEnergy triple ∧
      0 < actualFourSiteSecondEnergy triple ∧
      0 < actualFourSiteThirdEnergy triple := by
  have hsimple' : SimpleOrderedSpectrum
      (harmonicHermitian (actualFourSiteMassConfig triple)) := by
    simpa [actualFourSiteHarmonic, actualFourSiteMassConfig,
      threeMassHarmonicHermitian] using hsimple
  have hfirstFrequency : 0 < orderedModeFrequency
      (harmonicHermitian (actualFourSiteMassConfig triple)) 0 := by
    apply (orderedModeFrequency_pos_iff_ne_last
      (actualFourSiteMassConfig triple) hsimple' 0).2
    decide
  have hsecondFrequency : 0 < orderedModeFrequency
      (harmonicHermitian (actualFourSiteMassConfig triple)) 1 := by
    apply (orderedModeFrequency_pos_iff_ne_last
      (actualFourSiteMassConfig triple) hsimple' 1).2
    decide
  have hthirdFrequency : 0 < orderedModeFrequency
      (harmonicHermitian (actualFourSiteMassConfig triple)) 2 := by
    apply (orderedModeFrequency_pos_iff_ne_last
      (actualFourSiteMassConfig triple) hsimple' 2).2
    decide
  exact ⟨by
    simpa [actualFourSiteFirstEnergy, actualFourSiteHarmonic,
      actualFourSiteMassConfig, threeMassHarmonicHermitian,
      orderedModeFrequency] using hfirstFrequency,
    by
      constructor
      · simpa [actualFourSiteSecondEnergy, actualFourSiteHarmonic,
          actualFourSiteMassConfig, threeMassHarmonicHermitian,
          orderedModeFrequency] using hsecondFrequency
      · simpa [actualFourSiteThirdEnergy, actualFourSiteHarmonic,
          actualFourSiteMassConfig, threeMassHarmonicHermitian,
          orderedModeFrequency] using hthirdFrequency⟩

set_option maxHeartbeats 2000000 in
-- The exact three-root Vieta elimination exceeds the default simplex budget.

/-- The three positive actual eigenvalues have exactly the elementary
symmetric functions encoded by the genuine four-site characteristic cubic. -/
theorem actualFourSite_positiveEnergy_symmetric
    {triple : MassTriple} (htriple : triple ∈ iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum (actualFourSiteHarmonic triple)) :
    actualFourSiteFirstEnergy triple +
          actualFourSiteSecondEnergy triple +
          actualFourSiteThirdEnergy triple =
        2 * (triple.1.1⁻¹ + triple.1.2⁻¹ + triple.2⁻¹ + 1) ∧
      actualFourSiteFirstEnergy triple *
            actualFourSiteSecondEnergy triple +
          actualFourSiteFirstEnergy triple *
            actualFourSiteThirdEnergy triple +
          actualFourSiteSecondEnergy triple *
            actualFourSiteThirdEnergy triple =
        3 * triple.1.1⁻¹ * triple.1.2⁻¹ +
          4 * triple.1.1⁻¹ * triple.2⁻¹ + 3 * triple.1.1⁻¹ +
          3 * triple.1.2⁻¹ * triple.2⁻¹ + 4 * triple.1.2⁻¹ +
          3 * triple.2⁻¹ ∧
      actualFourSiteFirstEnergy triple *
          actualFourSiteSecondEnergy triple *
          actualFourSiteThirdEnergy triple =
        4 * (triple.1.1⁻¹ * triple.1.2⁻¹ * triple.2⁻¹ +
          triple.1.1⁻¹ * triple.1.2⁻¹ +
          triple.1.1⁻¹ * triple.2⁻¹ +
          triple.1.2⁻¹ * triple.2⁻¹) := by
  let first := actualFourSiteFirstEnergy triple
  let second := actualFourSiteSecondEnergy triple
  let third := actualFourSiteThirdEnergy triple
  let sumInv := triple.1.1⁻¹ + triple.1.2⁻¹ + triple.2⁻¹ + 1
  let pairInv :=
    3 * triple.1.1⁻¹ * triple.1.2⁻¹ +
      4 * triple.1.1⁻¹ * triple.2⁻¹ + 3 * triple.1.1⁻¹ +
      3 * triple.1.2⁻¹ * triple.2⁻¹ + 4 * triple.1.2⁻¹ +
      3 * triple.2⁻¹
  let tripleInv :=
    triple.1.1⁻¹ * triple.1.2⁻¹ * triple.2⁻¹ +
      triple.1.1⁻¹ * triple.1.2⁻¹ +
      triple.1.1⁻¹ * triple.2⁻¹ +
      triple.1.2⁻¹ * triple.2⁻¹
  have hpositive : 0 < first ∧ 0 < second ∧ 0 < third := by
    simpa [first, second, third] using
      actualFourSite_first_second_third_energy_pos triple hsimple
  have hrootFirst :
      first * (first ^ 3 - 2 * sumInv * first ^ 2 +
        pairInv * first - 4 * tripleInv) = 0 := by
    rw [← actualFourSiteHarmonic_charpoly_eval htriple]
    exact charpoly_eval_orderedEigenvalue_eq_zero
      (actualFourSiteHarmonic triple) 0
  have hrootSecond :
      second * (second ^ 3 - 2 * sumInv * second ^ 2 +
        pairInv * second - 4 * tripleInv) = 0 := by
    rw [← actualFourSiteHarmonic_charpoly_eval htriple]
    exact charpoly_eval_orderedEigenvalue_eq_zero
      (actualFourSiteHarmonic triple) 1
  have hrootThird :
      third * (third ^ 3 - 2 * sumInv * third ^ 2 +
        pairInv * third - 4 * tripleInv) = 0 := by
    rw [← actualFourSiteHarmonic_charpoly_eval htriple]
    exact charpoly_eval_orderedEigenvalue_eq_zero
      (actualFourSiteHarmonic triple) 2
  have hcubicFirst :
      first ^ 3 - 2 * sumInv * first ^ 2 +
        pairInv * first - 4 * tripleInv = 0 :=
    (mul_eq_zero.mp hrootFirst).resolve_left (ne_of_gt hpositive.1)
  have hcubicSecond :
      second ^ 3 - 2 * sumInv * second ^ 2 +
        pairInv * second - 4 * tripleInv = 0 :=
    (mul_eq_zero.mp hrootSecond).resolve_left
      (ne_of_gt hpositive.2.1)
  have hcubicThird :
      third ^ 3 - 2 * sumInv * third ^ 2 +
        pairInv * third - 4 * tripleInv = 0 :=
    (mul_eq_zero.mp hrootThird).resolve_left
      (ne_of_gt hpositive.2.2)
  have hfirstSecond : first ≠ second := hsimple.ne (by decide)
  have hfirstThird : first ≠ third := hsimple.ne (by decide)
  have hsecondThird : second ≠ third := hsimple.ne (by decide)
  have hpairFirstSecond :
      first ^ 2 + first * second + second ^ 2 -
        2 * sumInv * (first + second) + pairInv = 0 := by
    have hfactor :
        (first - second) *
          (first ^ 2 + first * second + second ^ 2 -
            2 * sumInv * (first + second) + pairInv) = 0 := by
      nlinarith [hcubicFirst, hcubicSecond]
    exact (mul_eq_zero.mp hfactor).resolve_left
      (sub_ne_zero.mpr hfirstSecond)
  have hpairFirstThird :
      first ^ 2 + first * third + third ^ 2 -
        2 * sumInv * (first + third) + pairInv = 0 := by
    have hfactor :
        (first - third) *
          (first ^ 2 + first * third + third ^ 2 -
            2 * sumInv * (first + third) + pairInv) = 0 := by
      nlinarith [hcubicFirst, hcubicThird]
    exact (mul_eq_zero.mp hfactor).resolve_left
      (sub_ne_zero.mpr hfirstThird)
  have hsumFactor :
      (second - third) * (first + second + third - 2 * sumInv) = 0 := by
    nlinarith [hpairFirstSecond, hpairFirstThird]
  have hsum : first + second + third = 2 * sumInv := by
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp hsumFactor).resolve_left
        (sub_ne_zero.mpr hsecondThird))
  have hpairs :
      first * second + first * third + second * third = pairInv := by
    nlinarith [hpairFirstSecond, hsum]
  have hproduct : first * second * third = 4 * tripleInv := by
    nlinarith [hcubicFirst, hsum, hpairs]
  exact ⟨hsum, hpairs, hproduct⟩

/-- The physical decay-channel sign pattern plus, minus, minus. -/
def actualFourSiteDecaySign (r : Fin 3) :
    ModalPhaseMismatch.InteractionSign :=
  if r = 0 then .plus else .minus

/-- The three positive ordered indices of the four-site simple spectrum. -/
def actualFourSitePositiveModes (r : Fin 3) :
    Fin (Fintype.card (Lattice.Site 4)) :=
  ⟨r.val, by
    simpa only [Lattice.Site, ZMod.card] using (show r.val < 4 by omega)⟩

@[simp] theorem actualFourSitePositiveModes_zero :
    actualFourSitePositiveModes 0 = 0 := rfl

@[simp] theorem actualFourSitePositiveModes_one :
    actualFourSitePositiveModes 1 = 1 := rfl

@[simp] theorem actualFourSitePositiveModes_two :
    actualFourSitePositiveModes 2 = 2 := rfl

def actualFourSiteFirstFrequency (triple : MassTriple) : Real :=
  orderedModeFrequency (actualFourSiteHarmonic triple) 0

def actualFourSiteSecondFrequency (triple : MassTriple) : Real :=
  orderedModeFrequency (actualFourSiteHarmonic triple) 1

def actualFourSiteThirdFrequency (triple : MassTriple) : Real :=
  orderedModeFrequency (actualFourSiteHarmonic triple) 2

/-- The genuine four-site child-child-mismatch chart, with the two lower
children in the first pair and parent-minus-children mismatch last. -/
def actualFourSiteLiftedFrequencyChart : MassTriple → MassTriple :=
  actualThreeMassLiftedFrequencyChart frozenUnitMassFour
    (0 : Lattice.Site 4) (1 : Lattice.Site 4) (2 : Lattice.Site 4)
    actualFourSiteDecaySign actualFourSitePositiveModes

theorem actualFourSiteLiftedFrequencyChart_eq (triple : MassTriple) :
    actualFourSiteLiftedFrequencyChart triple =
      ((actualFourSiteSecondFrequency triple,
          actualFourSiteThirdFrequency triple),
        actualFourSiteFirstFrequency triple -
          actualFourSiteSecondFrequency triple -
          actualFourSiteThirdFrequency triple) := by
  unfold actualFourSiteLiftedFrequencyChart
    actualThreeMassLiftedFrequencyChart
  dsimp only
  rw [Fin.sum_univ_three]
  simp [actualFourSiteDecaySign,
    actualFourSiteFirstFrequency, actualFourSiteSecondFrequency,
    actualFourSiteThirdFrequency, actualFourSiteHarmonic]
  ring

/-- Recover the three cubic characteristic coefficients from the lifted
frequency coordinates.  The parent frequency is mismatch plus both children. -/
def liftedFrequencyCoefficientTransform (lifted : MassTriple) : MassTriple :=
  let childOne := lifted.1.1
  let childTwo := lifted.1.2
  let parent := lifted.2 + childOne + childTwo
  let parentEnergy := parent ^ 2
  let childOneEnergy := childOne ^ 2
  let childTwoEnergy := childTwo ^ 2
  ((-(parentEnergy + childOneEnergy + childTwoEnergy),
      parentEnergy * childOneEnergy +
        parentEnergy * childTwoEnergy +
        childOneEnergy * childTwoEnergy),
    -(parentEnergy * childOneEnergy * childTwoEnergy))

/-- On every supported simple-spectrum configuration, the genuine lifted
frequency chart recovers exactly the explicit inverse-mass coefficient chart. -/
theorem liftedFrequencyCoefficientTransform_actualFourSiteLiftedFrequencyChart
    {triple : MassTriple} (htriple : triple ∈ iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum (actualFourSiteHarmonic triple)) :
    liftedFrequencyCoefficientTransform
        (actualFourSiteLiftedFrequencyChart triple) =
      actualFourSiteCoefficientChart triple := by
  have hpositive :
      0 < actualFourSiteFirstEnergy triple ∧
        0 < actualFourSiteSecondEnergy triple ∧
        0 < actualFourSiteThirdEnergy triple :=
    actualFourSite_first_second_third_energy_pos triple hsimple
  have hsymmetric :=
    actualFourSite_positiveEnergy_symmetric htriple hsimple
  have hfirstSq : (actualFourSiteFirstFrequency triple) ^ 2 =
      actualFourSiteFirstEnergy triple := by
    exact Real.sq_sqrt hpositive.1.le
  have hsecondSq : (actualFourSiteSecondFrequency triple) ^ 2 =
      actualFourSiteSecondEnergy triple := by
    exact Real.sq_sqrt hpositive.2.1.le
  have hthirdSq : (actualFourSiteThirdFrequency triple) ^ 2 =
      actualFourSiteThirdEnergy triple := by
    exact Real.sq_sqrt hpositive.2.2.le
  rw [actualFourSiteLiftedFrequencyChart_eq]
  unfold liftedFrequencyCoefficientTransform actualFourSiteCoefficientChart
    fourSiteInverseCoefficientChart
  dsimp only
  have hparent :
      actualFourSiteFirstFrequency triple -
            actualFourSiteSecondFrequency triple -
            actualFourSiteThirdFrequency triple +
          actualFourSiteSecondFrequency triple +
          actualFourSiteThirdFrequency triple =
        actualFourSiteFirstFrequency triple := by ring
  rw [hparent, hfirstSq, hsecondSq, hthirdSq]
  apply Prod.ext
  · apply Prod.ext
    · rw [hsymmetric.1]
      ring
    · rw [hsymmetric.2.1]
  · rw [hsymmetric.2.2]
    ring

/-- The true Frechet Jacobian of the four-site decay lifted chart. -/
def actualFourSiteLiftedFrequencyJacobian
    (triple : MassTriple) : MassTriple →L[Real] MassTriple :=
  actualThreeMassLiftedFrequencyJacobian frozenUnitMassFour
    (0 : Lattice.Site 4) (1 : Lattice.Site 4) (2 : Lattice.Site 4)
    actualFourSiteDecaySign actualFourSitePositiveModes triple

/-- N=4 regression witness: outside the explicit nonzero inverse-mass
polynomial locus, the genuine simple positive decay chart has nonzero
Jacobian.  This is an actual finite-volume theorem, not a transfer to
arbitrary volume. -/
theorem actualFourSiteLiftedFrequencyJacobian_det_ne_zero
    {triple : MassTriple} (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum (actualFourSiteHarmonic triple))
    (hnumerator :
      MvPolynomial.eval (iidInverseMassTripleCoordinates triple)
        fourSiteCoefficientJacobianPolynomial ≠ 0) :
    (actualFourSiteLiftedFrequencyJacobian triple).det ≠ 0 := by
  have hsupport : triple ∈ iidMassTripleSupport := interior_subset htriple
  have henergies :
      0 < actualFourSiteFirstEnergy triple ∧
        0 < actualFourSiteSecondEnergy triple ∧
        0 < actualFourSiteThirdEnergy triple :=
    actualFourSite_first_second_third_energy_pos triple hsimple
  have hpositive : ∀ r, 0 < orderedEigenvalue
      (threeMassHarmonicHermitian frozenUnitMassFour
        (0 : Lattice.Site 4) (1 : Lattice.Site 4) (2 : Lattice.Site 4)
        triple) (actualFourSitePositiveModes r) := by
    intro r
    fin_cases r
    · simpa [actualFourSiteFirstEnergy, actualFourSiteHarmonic] using
        henergies.1
    · simpa [actualFourSiteSecondEnergy, actualFourSiteHarmonic] using
        henergies.2.1
    · simpa [actualFourSiteThirdEnergy, actualFourSiteHarmonic] using
        henergies.2.2
  obtain ⟨chartDerivative, hchartDerivative⟩ :=
    exists_hasStrictFDerivAt_actualThreeMassLiftedFrequencyChart
      frozenUnitMassFour (by decide) (by decide) (by decide)
      actualFourSiteDecaySign actualFourSitePositiveModes
      htriple (by simpa [actualFourSiteHarmonic] using hsimple) hpositive
  let J := actualFourSiteLiftedFrequencyJacobian triple
  have hJ : J = chartDerivative := by
    simpa [J, actualFourSiteLiftedFrequencyJacobian,
      actualFourSiteLiftedFrequencyChart,
      actualThreeMassLiftedFrequencyJacobian] using
      hchartDerivative.hasFDerivAt.fderiv
  have hchartJ : HasFDerivAt actualFourSiteLiftedFrequencyChart J triple := by
    rw [hJ]
    simpa [actualFourSiteLiftedFrequencyChart] using
      hchartDerivative.hasFDerivAt
  have houter : DifferentiableAt Real liftedFrequencyCoefficientTransform
      (actualFourSiteLiftedFrequencyChart triple) := by
    unfold liftedFrequencyCoefficientTransform
    fun_prop
  have hcomposition : HasFDerivAt
      (fun nearby => liftedFrequencyCoefficientTransform
        (actualFourSiteLiftedFrequencyChart nearby))
      (fderiv Real liftedFrequencyCoefficientTransform
          (actualFourSiteLiftedFrequencyChart triple) ∘L J) triple := by
    simpa [Function.comp_def] using
      houter.hasFDerivAt.comp triple hchartJ
  have heventuallyIdentity :
      (fun nearby => liftedFrequencyCoefficientTransform
        (actualFourSiteLiftedFrequencyChart nearby)) =ᶠ[nhds triple]
        actualFourSiteCoefficientChart := by
    filter_upwards [isOpen_interior.mem_nhds htriple,
      eventually_simple_threeMassHarmonicHermitian frozenUnitMassFour
        (0 : Lattice.Site 4) (1 : Lattice.Site 4) (2 : Lattice.Site 4)
        triple (by simpa [actualFourSiteHarmonic] using hsimple)] with
        nearby hnearby hsimpleNearby
    apply liftedFrequencyCoefficientTransform_actualFourSiteLiftedFrequencyChart
      (interior_subset hnearby)
    simpa [actualFourSiteHarmonic] using hsimpleNearby
  have hcoefficientByComposition : HasFDerivAt
      actualFourSiteCoefficientChart
      (fderiv Real liftedFrequencyCoefficientTransform
          (actualFourSiteLiftedFrequencyChart triple) ∘L J) triple :=
    hcomposition.congr_of_eventuallyEq heventuallyIdentity.symm
  obtain ⟨coefficientDerivative, hcoefficientDerivative,
      hcoefficientInjective⟩ :=
    exists_hasFDerivAt_actualFourSiteCoefficientChart_injective
      hsupport hnumerator
  have hderivativeEquality :
      coefficientDerivative =
        fderiv Real liftedFrequencyCoefficientTransform
          (actualFourSiteLiftedFrequencyChart triple) ∘L J :=
    hcoefficientDerivative.unique hcoefficientByComposition
  have hJInjective : Function.Injective J := by
    intro u v huv
    apply hcoefficientInjective
    rw [hderivativeEquality]
    exact congrArg
      (fderiv Real liftedFrequencyCoefficientTransform
        (actualFourSiteLiftedFrequencyChart triple)) huv
  have hker : J.ker = ⊥ := LinearMap.ker_eq_bot.mpr hJInjective
  have hdetLinear : LinearMap.det J.toLinearMap ≠ 0 := by
    intro hzero
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hzero) hker
  simpa [J, ContinuousLinearMap.det] using hdetLinear

end

end ArchonPhysics.ActualThreeMassLiftedJacobianPolynomial
