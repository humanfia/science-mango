import ArchonPhysics.ActualThreeSiteIteratedA2OuterCompactAtlas
import ArchonPhysics.UniformRandomMassHarmonicSpectrumBound

/-!
# Explicit determinant lower bound for the three-site outer mismatch

For the concrete outer channel whose mismatch is `-omega_2`, write
`x = m0⁻¹`, `y = m1⁻¹`, `z = m2⁻¹`, `E = omega_2²`, and `S = x+y+z`.
The true derivative `J` in the middle raw mass satisfies

`4 omega_2 (S-E) J = y² (-2E + 3(x+z))`.

At the selected root of the explicit characteristic quadratic, the vertical
factor has the exact rationalization

`(-2E + 3(x+z)) (x+4y+z-2E) = 3(x-z)²`.

On the iid support, these identities and elementary uniform bounds give
`|J| >= delta² / 4000` whenever `|x-z| >= delta > 0`.  Since the augmented
chart determinant is `-J`, the same explicit bound holds for it.

This is a pointwise/local quantitative result.  The existing global compact
small-ball proof still chooses the number of inverse-function patches by an
existential finite subcover.  Nothing here controls that atlas cardinal as a
function of `delta`, so this module deliberately makes no global epsilon-rate
claim.
-/

open scoped Matrix

namespace ArchonPhysics.ActualThreeSiteIteratedA2OuterExplicitDeterminantLower

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2OuterCompactAtlas
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualTwoMassSimpleEigenvalueDifferentiability
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeBridges
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianFrozenFiber
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianEliminant
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.ThreeParameterProjectorWeightJacobian
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open Filter Set

noncomputable section

private theorem factor_identity {x y z energy : Real}
    (hresidual : energy ^ 2 - 2 * (x + y + z) * energy +
      3 * (x * y + x * z + y * z) = 0) :
    (-2 * energy + 3 * (x + z)) *
        (x + 4 * y + z - 2 * energy) =
      3 * (x - z) ^ 2 := by
  nlinarith [hresidual]

private theorem inverse_mem_bounds {mass : Real}
    (hmass : mass ∈ massSupport) :
    (5 / 6 : Real) ≤ mass⁻¹ ∧ mass⁻¹ ≤ 5 / 4 := by
  have hpos : 0 < mass := massLower_pos.trans_le hmass.1
  constructor
  · calc
      (5 / 6 : Real) = 1 / massUpper := by norm_num [massUpper]
      _ ≤ 1 / mass := one_div_le_one_div_of_le hpos hmass.2
      _ = mass⁻¹ := by simp [one_div]
  · calc
      mass⁻¹ = 1 / mass := by simp [one_div]
      _ ≤ 1 / massLower := one_div_le_one_div_of_le massLower_pos hmass.1
      _ = 5 / 4 := by norm_num [massLower]

private theorem frequency_lt_three (triple : MassTriple) :
    orderedModeFrequency (threeSiteOuterTripleHarmonic triple) 1 < 3 := by
  let mass := threeSiteOuterTripleMassConfig triple
  have hmassLower : ∀ site, massLower ≤ mass.mass site := by
    intro site
    fin_cases site <;>
      simp [mass, threeSiteOuterTripleMassConfig, threeMassSiteConfig]
      <;> exact (clippedMass_mem_support _).1
  have hband := orderedModeFrequency_harmonic_le_sqrt_four_div_massLower
    mass massLower massLower_pos hmassLower (1 : Fin 3)
  have hsqrtSq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsqrtNonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hsqrt : Real.sqrt 5 < 3 := by nlinarith
  change orderedModeFrequency (harmonicHermitian mass) 1 < 3
  norm_num [massLower] at hband
  exact hband.trans_lt hsqrt


private theorem frozen_vertical_identity
    (fixed : Lattice.PositiveMassConfig 3)
    {pair : Real × Real} (hpair : pair ∈ interior iidMassPairSupport)
    (hsimple : SimpleOrderedSpectrum
      (frozenFiberThreeSiteHarmonic fixed pair)) :
    let energy := orderedEigenvalue
      (frozenFiberThreeSiteHarmonic fixed pair) 1
    let frequency := orderedModeFrequency
      (frozenFiberThreeSiteHarmonic fixed pair) 1
    let jacobian := physlibIteratedA2PairMismatchVerticalJacobian fixed
      (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
      firstPositivePhysicalModeThree threeSiteSingleFrequencyOuterTerm pair
    4 * frequency *
        (pair.1⁻¹ + pair.2⁻¹ + frozenThirdInverseWeight fixed - energy) *
        jacobian =
      pair.2⁻¹ ^ 2 *
        (-2 * energy + 3 * (pair.1⁻¹ + frozenThirdInverseWeight fixed)) := by
  dsimp only
  let frequency : Real × Real → Real := fun nearby =>
    orderedModeFrequency (frozenFiberThreeSiteHarmonic fixed nearby) 1
  let energy : Real × Real → Real := fun nearby =>
    orderedEigenvalue (frozenFiberThreeSiteHarmonic fixed nearby) 1
  let jacobian := physlibIteratedA2PairMismatchVerticalJacobian fixed
    (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
    firstPositivePhysicalModeThree threeSiteSingleFrequencyOuterTerm pair
  have hpositive : 0 < orderedEigenvalue
      (frozenFiberThreeSiteHarmonic fixed pair) 1 :=
    frozenFiberThreeSite_secondEnergy_pos_of_simple fixed pair hsimple
  obtain ⟨Dfrequency, hfrequency⟩ :=
    exists_hasStrictFDerivAt_actualTwoMassOrderedModeFrequency
      fixed (by decide) hpair hsimple 1 hpositive
  have hfrequencyStrict : HasStrictFDerivAt frequency Dfrequency pair := by
    simpa [frequency, frozenFiberThreeSiteHarmonic] using hfrequency
  have hnegative : HasFDerivAt (fun nearby => -frequency nearby)
      (-Dfrequency) pair := hfrequencyStrict.hasFDerivAt.neg
  have hjacobianEq :
      fderiv Real (fun nearby => -frequency nearby) pair (0, 1) =
        jacobian := by
    dsimp [jacobian, physlibIteratedA2PairMismatchVerticalJacobian]
    rw [frozenFiberThreeSite_outerMismatchChart_eq]
  have hDfrequencyVertical : Dfrequency (0, 1) = -jacobian := by
    rw [hnegative.fderiv] at hjacobianEq
    have hneg := congrArg Neg.neg hjacobianEq
    simpa using hneg
  have hinclusion : HasFDerivAt (fun second : Real => (pair.1, second))
      (ContinuousLinearMap.inr Real Real Real) pair.2 :=
    hasFDerivAt_prodMk_right pair.1 pair.2
  have hfrequencyLine : HasDerivAt
      (fun second => frequency (pair.1, second)) (-jacobian) pair.2 := by
    have hcomp := hfrequencyStrict.hasFDerivAt.comp pair.2 hinclusion
    simpa [Function.comp_def, ContinuousLinearMap.comp_apply,
      hDfrequencyVertical] using hcomp.hasDerivAt
  have henergyLine : HasDerivAt
      (fun second => energy (pair.1, second))
      (-2 * frequency pair * jacobian) pair.2 := by
    have hsquare := hfrequencyLine.pow 2
    have heventually :
        (fun second => energy (pair.1, second)) =ᶠ[nhds pair.2]
          (fun second => frequency (pair.1, second)) ^ 2 :=
      Filter.Eventually.of_forall fun second =>
        (orderedModeFrequency_sq_eq_orderedEigenvalue
          (frozenFiberThreeSiteMassConfig fixed (pair.1, second)) 1).symm
    have hsquareEnergy := hsquare.congr_of_eventuallyEq heventually
    apply hsquareEnergy.congr_deriv
    ring
  have hsecondNe : pair.2 ≠ 0 := ne_of_gt
    (massLower_pos.trans_le (interior_subset hpair).2.1)
  let inverseDerivative : Real := -(pair.2 ^ 2)⁻¹
  have hinverse : HasDerivAt (fun second : Real => second⁻¹)
      inverseDerivative pair.2 := by
    simpa [inverseDerivative] using hasDerivAt_inv hsecondNe
  let residualLine : Real → Real := fun second =>
    energy (pair.1, second) ^ 2 -
      2 * (pair.1⁻¹ + second⁻¹ + frozenThirdInverseWeight fixed) *
        energy (pair.1, second) +
      3 * (pair.1⁻¹ * second⁻¹ +
        pair.1⁻¹ * frozenThirdInverseWeight fixed +
        second⁻¹ * frozenThirdInverseWeight fixed)
  have hsum : HasDerivAt
      (fun second : Real =>
        pair.1⁻¹ + second⁻¹ + frozenThirdInverseWeight fixed)
      inverseDerivative pair.2 := by
    simpa [Pi.add_apply, add_assoc] using
      ((hasDerivAt_const pair.2 pair.1⁻¹).add hinverse).add_const
        (frozenThirdInverseWeight fixed)
  have hpairProduct : HasDerivAt
      (fun second : Real => pair.1⁻¹ * second⁻¹)
      (pair.1⁻¹ * inverseDerivative) pair.2 := by
    simpa using hinverse.const_mul pair.1⁻¹
  have hfrozenProduct : HasDerivAt
      (fun second : Real => second⁻¹ * frozenThirdInverseWeight fixed)
      (inverseDerivative * frozenThirdInverseWeight fixed) pair.2 :=
    hinverse.mul_const _
  have hcalc :=
    (henergyLine.pow 2).sub
      ((hsum.const_mul 2).mul henergyLine) |>.add
      (((hpairProduct.add_const
        (pair.1⁻¹ * frozenThirdInverseWeight fixed)).add
          hfrozenProduct).const_mul 3)
  have hresidualEventuallyZero :
      residualLine =ᶠ[nhds pair.2] fun _ => 0 := by
    have hinteriorEventually : ∀ᶠ second in nhds pair.2,
        (pair.1, second) ∈ interior iidMassPairSupport := by
      have htendsto : Tendsto (fun second : Real => (pair.1, second))
          (nhds pair.2) (nhds pair) := hinclusion.continuousAt
      exact htendsto.eventually (isOpen_interior.mem_nhds hpair)
    have hsimpleEventually : ∀ᶠ second in nhds pair.2,
        SimpleOrderedSpectrum
          (frozenFiberThreeSiteHarmonic fixed (pair.1, second)) := by
      have hglobal := eventually_simple_twoSiteHarmonicHermitian fixed
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) pair hsimple
      have htendsto : Tendsto (fun second : Real => (pair.1, second))
          (nhds pair.2) (nhds pair) := hinclusion.continuousAt
      simpa [frozenFiberThreeSiteHarmonic] using htendsto.eventually hglobal
    filter_upwards [hinteriorEventually, hsimpleEventually]
      with second hinterior hsimpleSecond
    simpa [residualLine, energy] using
      frozenFiberThreeSite_secondEnergy_residual_eq_zero fixed
        (interior_subset hinterior) hsimpleSecond
  have hderivativeEquation :
      (2 * energy pair -
          2 * (pair.1⁻¹ + pair.2⁻¹ + frozenThirdInverseWeight fixed)) *
          (-2 * frequency pair * jacobian) +
        inverseDerivative *
          (-2 * energy pair +
            3 * (pair.1⁻¹ + frozenThirdInverseWeight fixed)) = 0 := by
    have hzeroDerivative : HasDerivAt (fun _ : Real => (0 : Real)) 0 pair.2 :=
      hasDerivAt_const pair.2 0
    have hcalcDerivativeZero :=
      (hcalc.congr_of_eventuallyEq
        (show (fun _ : Real => (0 : Real)) =ᶠ[nhds pair.2] _ from by
          filter_upwards [hresidualEventuallyZero] with second hzero
          calc
            0 = residualLine second := hzero.symm
            _ = _ := by
              dsimp [residualLine, energy])).unique hzeroDerivative
    convert hcalcDerivativeZero using 1 <;> ring
  dsimp [inverseDerivative] at hderivativeEquation
  calc
    4 * frequency pair *
          (pair.1⁻¹ + pair.2⁻¹ + frozenThirdInverseWeight fixed - energy pair) *
          jacobian =
        (pair.2 ^ 2)⁻¹ *
          (-2 * energy pair +
            3 * (pair.1⁻¹ + frozenThirdInverseWeight fixed)) := by
      linarith
    _ = pair.2⁻¹ ^ 2 *
          (-2 * energy pair +
            3 * (pair.1⁻¹ + frozenThirdInverseWeight fixed)) := by
      rw [inv_pow]


private theorem algebraic_abs_jacobian_lower
    {x y z energy frequency jacobian delta : Real}
    (hx0 : 0 ≤ x) (hx2 : x ≤ 2)
    (hy0 : 0 ≤ y) (hy2 : y ≤ 2) (hySq : (1 / 2 : Real) ≤ y ^ 2)
    (hz0 : 0 ≤ z) (hz2 : z ≤ 2)
    (henergy0 : 0 ≤ energy) (henergy9 : energy ≤ 9)
    (hfrequency0 : 0 ≤ frequency) (hfrequency3 : frequency ≤ 3)
    (hderivative :
      4 * frequency * (x + y + z - energy) * jacobian =
        y ^ 2 * (-2 * energy + 3 * (x + z)))
    (hfactor :
      (-2 * energy + 3 * (x + z)) *
          (x + 4 * y + z - 2 * energy) =
        3 * (x - z) ^ 2)
    (hdelta : 0 ≤ delta) (hseparated : delta ≤ |x - z|) :
    delta ^ 2 / 4000 ≤ |jacobian| := by
  let q := -2 * energy + 3 * (x + z)
  let partner := x + 4 * y + z - 2 * energy
  have hsum0 : 0 ≤ x + y + z := by linarith
  have hsum6 : x + y + z ≤ 6 := by linarith
  have henergyAbs : |energy| = energy := abs_of_nonneg henergy0
  have hsumAbs : |x + y + z| = x + y + z := abs_of_nonneg hsum0
  have hsumEnergyAbs : |x + y + z - energy| ≤ 15 := by
    calc
      |x + y + z - energy| ≤ |x + y + z| + |energy| := abs_sub _ _
      _ = (x + y + z) + energy := by rw [hsumAbs, henergyAbs]
      _ ≤ 15 := by linarith
  have hpartnerAbs : |partner| ≤ 30 := by
    dsimp [partner]
    calc
      |x + 4 * y + z - 2 * energy| ≤
          |x + 4 * y + z| + |2 * energy| := abs_sub _ _
      _ = (x + 4 * y + z) + 2 * energy := by
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by positivity)]
      _ ≤ 30 := by linarith
  have hcoefficient :
      4 * frequency * |x + y + z - energy| ≤ 180 := by
    calc
      4 * frequency * |x + y + z - energy| ≤ 4 * 3 * 15 := by
        gcongr
      _ = 180 := by norm_num
  have hderivativeAbs :
      4 * frequency * |x + y + z - energy| * |jacobian| =
        y ^ 2 * |q| := by
    have habs := congrArg abs hderivative
    simpa [q, abs_mul, abs_of_nonneg hfrequency0,
      abs_of_nonneg (sq_nonneg y), mul_assoc] using habs
  have hyqLe : y ^ 2 * |q| ≤ 180 * |jacobian| := by
    calc
      y ^ 2 * |q| =
          (4 * frequency * |x + y + z - energy|) * |jacobian| :=
        hderivativeAbs.symm
      _ ≤ 180 * |jacobian| :=
        mul_le_mul_of_nonneg_right hcoefficient (abs_nonneg jacobian)
  have hqLe : |q| ≤ 360 * |jacobian| := by
    have hhalf : (1 / 2 : Real) * |q| ≤ y ^ 2 * |q| :=
      mul_le_mul_of_nonneg_right hySq (abs_nonneg q)
    nlinarith
  have hfactorAbs : |q| * |partner| = 3 * (x - z) ^ 2 := by
    calc
      |q| * |partner| = |q * partner| := (abs_mul q partner).symm
      _ = |3 * (x - z) ^ 2| := by rw [hfactor]
      _ = 3 * (x - z) ^ 2 := abs_of_nonneg (by positivity)
  have hdeltaSq : delta ^ 2 ≤ |x - z| ^ 2 :=
    (sq_le_sq₀ hdelta (abs_nonneg (x - z))).2 hseparated
  have hfactorLower : 3 * delta ^ 2 ≤ 30 * |q| := by
    calc
      3 * delta ^ 2 ≤ 3 * |x - z| ^ 2 := by gcongr
      _ = 3 * (x - z) ^ 2 := by rw [sq_abs]
      _ = |q| * |partner| := hfactorAbs.symm
      _ ≤ |q| * 30 :=
        mul_le_mul_of_nonneg_left hpartnerAbs (abs_nonneg q)
      _ = 30 * |q| := by ring
  have hcombined : 3 * delta ^ 2 ≤ 10800 * |jacobian| := by
    calc
      3 * delta ^ 2 ≤ 30 * |q| := hfactorLower
      _ ≤ 30 * (360 * |jacobian|) := by gcongr
      _ = 10800 * |jacobian| := by ring
  have hjacobian0 : 0 ≤ |jacobian| := abs_nonneg jacobian
  nlinarith


private theorem threeSiteOuterTriple_secondEnergy_residual
    {triple : MassTriple} (htriple : triple ∈ iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeSiteOuterTripleHarmonic triple)) :
    let energy := orderedEigenvalue (threeSiteOuterTripleHarmonic triple) 1
    energy ^ 2 -
        2 * (triple.1.1⁻¹ + triple.1.2⁻¹ + triple.2⁻¹) * energy +
        3 * (triple.1.1⁻¹ * triple.1.2⁻¹ +
          triple.1.1⁻¹ * triple.2⁻¹ + triple.1.2⁻¹ * triple.2⁻¹) = 0 := by
  dsimp only
  let fixed := threeSiteOuterFrozenThirdBackground triple.2
  have hsimpleFiber : SimpleOrderedSpectrum
      (frozenFiberThreeSiteHarmonic fixed triple.1) := by
    rw [frozenFiberThreeSiteHarmonic_outerBackground_eq]
    exact hsimple
  have hresidual := frozenFiberThreeSite_secondEnergy_residual_eq_zero
    fixed htriple.1 hsimpleFiber
  rw [frozenFiberThreeSiteHarmonic_outerBackground_eq] at hresidual
  simpa [fixed, frozenThirdInverseWeight,
    threeSiteOuterFrozenThirdBackground, clippedMass_eq_self htriple.2]
    using hresidual

/-- Exact implicit-differentiation identity for the true middle raw-mass
partial of the concrete mismatch `-omega_2`. -/
theorem threeSiteOuterTripleMismatchDerivative_second_identity
    {triple : MassTriple} (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeSiteOuterTripleHarmonic triple)) :
    let energy := orderedEigenvalue (threeSiteOuterTripleHarmonic triple) 1
    let frequency := orderedModeFrequency
      (threeSiteOuterTripleHarmonic triple) 1
    let jacobian := threeSiteOuterTripleMismatchDerivative triple
      (massTripleBasis 1)
    4 * frequency *
        (triple.1.1⁻¹ + triple.1.2⁻¹ + triple.2⁻¹ - energy) * jacobian =
      triple.1.2⁻¹ ^ 2 *
        (-2 * energy + 3 * (triple.1.1⁻¹ + triple.2⁻¹)) := by
  dsimp only
  let fixed := threeSiteOuterFrozenThirdBackground triple.2
  have hsupport := interior_subset htriple
  have hpairInterior : triple.1 ∈ interior iidMassPairSupport := by
    rw [iidMassTripleSupport, interior_prod_eq] at htriple
    exact htriple.1
  have hsimpleFiber : SimpleOrderedSpectrum
      (frozenFiberThreeSiteHarmonic fixed triple.1) := by
    rw [frozenFiberThreeSiteHarmonic_outerBackground_eq]
    exact hsimple
  have hidentity := frozen_vertical_identity fixed hpairInterior hsimpleFiber
  have hbridge :=
    threeSiteOuterTripleMismatchDerivative_second_eq_pairVerticalJacobian
      htriple hsimple
  rw [← hbridge] at hidentity
  rw [frozenFiberThreeSiteHarmonic_outerBackground_eq] at hidentity
  simpa [fixed, frozenThirdInverseWeight,
    threeSiteOuterFrozenThirdBackground, clippedMass_eq_self hsupport.2]
    using hidentity

/-- The vertical factor at the selected positive energy has an exact
conjugate-factor product equal to `3 (m0_inv - m2_inv)^2`. -/
theorem threeSiteOuterTriple_verticalFactor_mul_conjugate
    {triple : MassTriple} (htriple : triple ∈ iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeSiteOuterTripleHarmonic triple)) :
    let energy := orderedEigenvalue (threeSiteOuterTripleHarmonic triple) 1
    (-2 * energy + 3 * (triple.1.1⁻¹ + triple.2⁻¹)) *
        (triple.1.1⁻¹ + 4 * triple.1.2⁻¹ + triple.2⁻¹ - 2 * energy) =
      3 * (triple.1.1⁻¹ - triple.2⁻¹) ^ 2 := by
  dsimp only
  apply factor_identity
  exact threeSiteOuterTriple_secondEnergy_residual htriple hsimple


/-- On the interior iid support, inverse-mass separation by `delta` gives the
explicit quadratic lower bound for the actual augmented determinant. -/
theorem abs_det_threeSiteOuterAugmentedDerivative_ge_delta_sq_div_fourThousand
    {delta : Real} (hdelta : 0 < delta)
    {triple : MassTriple} (htriple : triple ∈ interior iidMassTripleSupport)
    (hseparated : delta ≤ |triple.1.1⁻¹ - triple.2⁻¹|) :
    delta ^ 2 / 4000 ≤
      |(threeSiteOuterAugmentedDerivative triple).det| := by
  have hsupport := interior_subset htriple
  have habsPos : 0 < |triple.1.1⁻¹ - triple.2⁻¹| :=
    hdelta.trans_le hseparated
  have hne : triple.1.1⁻¹ ≠ triple.2⁻¹ :=
    sub_ne_zero.mp (abs_pos.mp habsPos)
  have hsimple := threeSiteOuterTripleHarmonic_simple_of_inverse_separated
    hsupport hne
  let x := triple.1.1⁻¹
  let y := triple.1.2⁻¹
  let z := triple.2⁻¹
  let energy := orderedEigenvalue (threeSiteOuterTripleHarmonic triple) 1
  let frequency := orderedModeFrequency (threeSiteOuterTripleHarmonic triple) 1
  let jacobian := threeSiteOuterTripleMismatchDerivative triple
    (massTripleBasis 1)
  have hx := inverse_mem_bounds hsupport.1.1
  have hy := inverse_mem_bounds hsupport.1.2
  have hz := inverse_mem_bounds hsupport.2
  have hx0 : 0 ≤ x := by dsimp [x]; linarith [hx.1]
  have hx2 : x ≤ 2 := by dsimp [x]; linarith [hx.2]
  have hy0 : 0 ≤ y := by dsimp [y]; linarith [hy.1]
  have hy2 : y ≤ 2 := by dsimp [y]; linarith [hy.2]
  have hySq : (1 / 2 : Real) ≤ y ^ 2 := by
    dsimp [y]
    nlinarith [hy.1, sq_nonneg (triple.1.2⁻¹ - 5 / 6)]
  have hz0 : 0 ≤ z := by dsimp [z]; linarith [hz.1]
  have hz2 : z ≤ 2 := by dsimp [z]; linarith [hz.2]
  have hfrequency0 : 0 ≤ frequency := by
    dsimp [frequency]
    exact Real.sqrt_nonneg _
  have hfrequency3 : frequency ≤ 3 := by
    exact (frequency_lt_three triple).le
  have hfrequencySq : frequency ^ 2 = energy := by
    dsimp [frequency, energy, orderedModeFrequency]
    exact Real.sq_sqrt
      (threeSiteOuterTriple_secondEnergy_pos_of_simple triple hsimple).le
  have henergy0 : 0 ≤ energy := by
    rw [← hfrequencySq]
    positivity
  have henergy9 : energy ≤ 9 := by
    have hsquare : frequency ^ 2 ≤ (3 : Real) ^ 2 :=
      (sq_le_sq₀ hfrequency0 (by norm_num)).2 hfrequency3
    nlinarith [hfrequencySq]
  have hderivative :
      4 * frequency * (x + y + z - energy) * jacobian =
        y ^ 2 * (-2 * energy + 3 * (x + z)) := by
    simpa [x, y, z, energy, frequency, jacobian] using
      threeSiteOuterTripleMismatchDerivative_second_identity htriple hsimple
  have hfactor :
      (-2 * energy + 3 * (x + z)) *
          (x + 4 * y + z - 2 * energy) =
        3 * (x - z) ^ 2 := by
    simpa [x, y, z, energy] using
      threeSiteOuterTriple_verticalFactor_mul_conjugate hsupport hsimple
  have hlower : delta ^ 2 / 4000 ≤ |jacobian| :=
    algebraic_abs_jacobian_lower hx0 hx2 hy0 hy2 hySq hz0 hz2
      henergy0 henergy9 hfrequency0 hfrequency3 hderivative hfactor
      hdelta.le (by simpa [x, z] using hseparated)
  rw [det_threeSiteOuterAugmentedDerivative, abs_neg]
  exact hlower

end
end ArchonPhysics.ActualThreeSiteIteratedA2OuterExplicitDeterminantLower
