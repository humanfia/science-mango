import ArchonPhysics.ActualProjectorAdjugateSaturationLocalization
import ArchonPhysics.ActualThreeMassLiftedJacobianDeterminantIdentity
import ArchonPhysics.ActualThreeMassLiftedJacobianPolynomial

/-!
# An explicit actual four-site positive-mode projector witness

The Vandermonde-saturated spectral system still permits the translation zero
mode.  Before strengthening that saturation, this module supplies a fully
physical regression point for the intended positive sector.  At raw masses
`(1, 1, 40 / 49)` with the fourth mass frozen to one, the three positive
energies are exactly `2`, `11 / 5`, and `17 / 4`.  The actual coefficient
Jacobian numerator is `81 / 100`, so the true three-frequency Jacobian and
the associated dual-cycle projector minor are nonzero.

This is deliberately an `N = 4` witness.  It is not a general-volume
nondegeneracy theorem.
-/

namespace ArchonPhysics.ActualFourSitePositiveProjectorWitness

open ArchonPhysics
open ArchonPhysics.ActualProjectorAdjugatePolynomial
open ArchonPhysics.ActualProjectorAdjugateSaturatedSpectralSystem
open ArchonPhysics.ActualThreeMassHellmannFeynmanJacobian
open ArchonPhysics.ActualThreeMassLiftedJacobianDeterminantIdentity
open ArchonPhysics.ActualThreeMassLiftedJacobianPolynomial
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Set

noncomputable section

/-- A separable characteristic polynomial makes the decreasing Hermitian
eigenvalue enumeration injective. -/
theorem simpleOrderedSpectrum_of_charpoly_separable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) (hseparable : (Matrix.charpoly A.1).Separable) :
    SimpleOrderedSpectrum A := by
  intro i j hij
  have hroots := Polynomial.nodup_roots hseparable
  rw [A.2.roots_charpoly_eq_eigenvalues₀] at hroots
  apply Multiset.inj_on_of_nodup_map hroots i (by simp) j (by simp)
  simpa [orderedEigenvalue, Function.comp_def] using hij

/-- The explicit raw-mass point, strictly inside `[4/5, 6/5]^3`. -/
def actualFourSiteWitnessTriple : MassTriple :=
  (((1 : Real), (1 : Real)), (40 : Real) / 49)

/-- The complete distinct spectrum at the witness point. -/
def actualFourSiteWitnessEnergy : Fin 4 → Real :=
  ![(0 : Real), (2 : Real), (11 : Real) / 5, (17 : Real) / 4]

theorem actualFourSiteWitnessTriple_mem_interior :
    actualFourSiteWitnessTriple ∈ interior iidMassTripleSupport := by
  rw [iidMassTripleSupport, interior_prod_eq]
  constructor
  · rw [TwoParameterSpectralAveragingAtlas.iidMassPairSupport,
      interior_prod_eq]
    constructor <;>
      simp [actualFourSiteWitnessTriple, massSupport, massLower, massUpper] <;>
        norm_num
  · norm_num [actualFourSiteWitnessTriple, massSupport, massLower, massUpper]

theorem actualFourSiteWitnessEnergy_injective :
    Function.Injective actualFourSiteWitnessEnergy := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals simp_all [actualFourSiteWitnessEnergy]
  all_goals norm_num at hij

/-- Exact factorization of the genuine physical four-site characteristic
polynomial at the witness masses. -/
theorem actualFourSiteWitness_charpoly :
    Matrix.charpoly
        (Matrix.of (actualFourSiteHarmonic actualFourSiteWitnessTriple).val) =
      ∏ r : Fin 4,
        (Polynomial.X - Polynomial.C (actualFourSiteWitnessEnergy r)) := by
  apply Polynomial.funext
  intro energy
  rw [actualFourSiteHarmonic_charpoly_eval
    (interior_subset actualFourSiteWitnessTriple_mem_interior)]
  simp [actualFourSiteWitnessTriple, actualFourSiteWitnessEnergy,
    Fin.prod_univ_succ]; norm_num
  ring; simp

theorem actualFourSiteWitness_charpoly_separable :
    (Matrix.charpoly
      (Matrix.of (actualFourSiteHarmonic actualFourSiteWitnessTriple).val)).Separable := by
  rw [actualFourSiteWitness_charpoly]
  exact Polynomial.separable_prod_X_sub_C_iff.mpr
    actualFourSiteWitnessEnergy_injective

/-- The actual physical harmonic matrix at the rational witness has simple
spectrum, with no genericity premise. -/
theorem actualFourSiteWitness_simple :
    SimpleOrderedSpectrum
      (actualFourSiteHarmonic actualFourSiteWitnessTriple) := by
  apply simpleOrderedSpectrum_of_charpoly_separable
  have hmatrix :
      Matrix.of (actualFourSiteHarmonic actualFourSiteWitnessTriple).val =
        (actualFourSiteHarmonic actualFourSiteWitnessTriple).1 := by
    ext i j
    rfl
  rw [← hmatrix]
  exact actualFourSiteWitness_charpoly_separable

/-- Exact nonzero value of the already constructed coefficient-Jacobian
polynomial at the physical witness. -/
theorem actualFourSiteWitness_coefficientJacobianPolynomial_eval :
    MvPolynomial.eval
        (iidInverseMassTripleCoordinates actualFourSiteWitnessTriple)
        fourSiteCoefficientJacobianPolynomial = (81 : Real) / 100 := by
  rw [fourSiteCoefficientJacobianPolynomial_eval_inverseMassTriple]
  norm_num [actualFourSiteWitnessTriple]

theorem actualFourSiteWitness_coefficientJacobianPolynomial_ne_zero :
    MvPolynomial.eval
        (iidInverseMassTripleCoordinates actualFourSiteWitnessTriple)
        fourSiteCoefficientJacobianPolynomial ≠ 0 := by
  rw [actualFourSiteWitness_coefficientJacobianPolynomial_eval]
  norm_num

/-- The genuine lifted child-child-mismatch Jacobian is nondegenerate at the
explicit physical witness. -/
theorem actualFourSiteWitness_liftedFrequencyJacobian_det_ne_zero :
    (actualFourSiteLiftedFrequencyJacobian
      actualFourSiteWitnessTriple).det ≠ 0 :=
  actualFourSiteLiftedFrequencyJacobian_det_ne_zero
    actualFourSiteWitnessTriple_mem_interior
    actualFourSiteWitness_simple
    actualFourSiteWitness_coefficientJacobianPolynomial_ne_zero

theorem actualFourSiteWitness_positiveModes_injective :
    Function.Injective actualFourSitePositiveModes := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

theorem actualFourSiteWitness_positiveModes_energy_pos :
    ∀ r, 0 < orderedEigenvalue
      (actualFourSiteHarmonic actualFourSiteWitnessTriple)
      (actualFourSitePositiveModes r) := by
  have henergies := actualFourSite_first_second_third_energy_pos
    actualFourSiteWitnessTriple actualFourSiteWitness_simple
  intro r
  fin_cases r
  · simpa [actualFourSiteFirstEnergy] using henergies.1
  · simpa [actualFourSiteSecondEnergy] using henergies.2.1
  · simpa [actualFourSiteThirdEnergy] using henergies.2.2

/-- Actual dual-cycle projector-weight minor nondegeneracy at the witness.
This is the exact minor occurring in the general-N Hellmann--Feynman
factorization. -/
theorem actualFourSiteWitness_projectorWeightMatrix_det_ne_zero :
    (actualThreeMassProjectorWeightMatrix frozenUnitMassFour
      (0 : Lattice.Site 4) (1 : Lattice.Site 4) (2 : Lattice.Site 4)
      actualFourSitePositiveModes actualFourSiteWitnessTriple).det ≠ 0 := by
  have hlifted :
      (actualThreeMassLiftedFrequencyJacobian frozenUnitMassFour
        (0 : Lattice.Site 4) (1 : Lattice.Site 4) (2 : Lattice.Site 4)
        actualFourSiteDecaySign actualFourSitePositiveModes
        actualFourSiteWitnessTriple).det ≠ 0 := by
    simpa [actualFourSiteLiftedFrequencyJacobian] using
      actualFourSiteWitness_liftedFrequencyJacobian_det_ne_zero
  have hidentity :=
    actualThreeMassLiftedFrequencyJacobian_det_eq_frequencyProjector
      frozenUnitMassFour (by decide) (by decide) (by decide)
      actualFourSiteDecaySign actualFourSitePositiveModes
      actualFourSiteWitnessTriple_mem_interior
      actualFourSiteWitness_simple
      actualFourSiteWitness_positiveModes_energy_pos
  rw [hidentity] at hlifted
  have hfrequency :
      (actualThreeMassFrequencyProjectorJacobianMatrix frozenUnitMassFour
        (0 : Lattice.Site 4) (1 : Lattice.Site 4) (2 : Lattice.Site 4)
        actualFourSitePositiveModes actualFourSiteWitnessTriple).det ≠ 0 :=
    (mul_ne_zero_iff.mp hlifted).2
  exact (actualThreeMassFrequencyProjectorJacobianMatrix_det_ne_zero_iff
    frozenUnitMassFour
    (0 : Lattice.Site 4) (1 : Lattice.Site 4) (2 : Lattice.Site 4)
    actualFourSitePositiveModes actualFourSiteWitnessTriple_mem_interior
    actualFourSiteWitness_positiveModes_energy_pos).mp hfrequency

/-- The explicit joint inverse-mass/eigenvalue adjugate numerator itself is
nonzero at the physical witness. -/
theorem actualFourSiteWitness_adjugateSpectralPolynomial_eval_ne_zero :
    MvPolynomial.eval
        (adjugateSpectralEvaluation
          (RandomMassResultantBridge.inverseMassCoordinates
            (threeMassSiteConfig frozenUnitMassFour
              (0 : Lattice.Site 4) (1 : Lattice.Site 4)
              (2 : Lattice.Site 4) actualFourSiteWitnessTriple))
          (fun r => orderedEigenvalue
            (actualThreeMassDualHermitian frozenUnitMassFour
              (0 : Lattice.Site 4) (1 : Lattice.Site 4)
              (2 : Lattice.Site 4) actualFourSiteWitnessTriple)
            (actualFourSitePositiveModes r)))
        (actualThreeMassAdjugateSpectralPolynomial
          (0 : Lattice.Site 4) (1 : Lattice.Site 4)
          (2 : Lattice.Site 4)) ≠ 0 := by
  have hsimpleDual := simple_actualThreeMassDualHermitian_of_simple
    frozenUnitMassFour (0 : Lattice.Site 4) (1 : Lattice.Site 4)
    (2 : Lattice.Site 4) actualFourSiteWitnessTriple
    actualFourSiteWitness_simple
  intro hzero
  exact actualFourSiteWitness_projectorWeightMatrix_det_ne_zero
    ((actualThreeMassProjectorMinor_eq_zero_iff_adjugateSpectralPolynomial
      frozenUnitMassFour
      (0 : Lattice.Site 4) (1 : Lattice.Site 4) (2 : Lattice.Site 4)
      actualFourSitePositiveModes actualFourSiteWitnessTriple
      hsimpleDual).mpr hzero)

/-- The five actual Vandermonde-saturated equations do not all vanish at the
explicit positive-mode point. -/
theorem actualFourSiteWitness_not_saturatedSpectralSystem :
    ¬ ∀ q : Fin 5,
      MvPolynomial.eval
        (actualThreeMassSaturatedAdjugateSpectralPoint frozenUnitMassFour
          (0 : Lattice.Site 4) (1 : Lattice.Site 4)
          (2 : Lattice.Site 4) actualFourSitePositiveModes
          actualFourSiteWitnessTriple)
        (actualThreeMassSaturatedAdjugateSpectralSystem
          (0 : Lattice.Site 4) (1 : Lattice.Site 4)
          (2 : Lattice.Site 4) q) = 0 := by
  have hsimpleDual := simple_actualThreeMassDualHermitian_of_simple
    frozenUnitMassFour (0 : Lattice.Site 4) (1 : Lattice.Site 4)
    (2 : Lattice.Site 4) actualFourSiteWitnessTriple
    actualFourSiteWitness_simple
  intro hsystem
  exact actualFourSiteWitness_projectorWeightMatrix_det_ne_zero
    ((actualThreeMassProjectorMinor_eq_zero_iff_saturatedSpectralSystem
      frozenUnitMassFour
      (0 : Lattice.Site 4) (1 : Lattice.Site 4) (2 : Lattice.Site 4)
      actualFourSitePositiveModes actualFourSiteWitnessTriple hsimpleDual
      actualFourSiteWitness_positiveModes_injective).mpr hsystem)

end

end ArchonPhysics.ActualFourSitePositiveProjectorWitness
