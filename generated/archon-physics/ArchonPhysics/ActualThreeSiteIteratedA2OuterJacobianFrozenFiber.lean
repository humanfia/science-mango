import ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianEliminant

/-!
# Frozen-fiber three-site actual A2 Jacobian elimination

The unit-background calculation is upgraded here to an arbitrary positive
frozen background.  Sites `0` and `1` are the two raw iid coordinates and
site `2` is frozen.  Writing

`x = m_0^{-1}`, `y = m_1^{-1}`, `z = m_2^{-1}`,

the full characteristic polynomial is

`E * (E^2 - 2 (x+y+z) E + 3 (xy+xz+yz))`.

For the concrete ordinary outer history from the imported module, the
mismatch is the negative second positive frequency.  If its derivative in
the second raw mass vanishes, implicit differentiation of the displayed
quadratic gives `2 E = 3 (x+z)`.  Combining this with the characteristic
equation gives `(x-z)^2=0`.  Hence the explicit nonzero polynomial
`X 0 - C z` is a genuine Jacobian eliminant on every frozen fiber.
-/

open scoped Matrix

namespace ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianFrozenFiber

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianEliminant
open ArchonPhysics.ActualTwoMassSimpleEigenvalueDifferentiability
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.FixedEnergySpectrumAvoidance
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.MassWeightedCycleBridge
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassResultantBridge
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.TwoParameterSpectralPolynomialAvoidance
open Filter Set

noncomputable section

/-- The inverse weight of the one site not varied in the three-site fiber. -/
def frozenThirdInverseWeight (fixed : Lattice.PositiveMassConfig 3) : Real :=
  (fixed.mass (2 : Lattice.Site 3))⁻¹

/-- The three inverse edge weights with sites zero and one varied. -/
def frozenFiberThreeSiteInverseWeights
    (fixed : Lattice.PositiveMassConfig 3) (pair : Real × Real) :
    Fin 3 → Real :=
  ![pair.1⁻¹, pair.2⁻¹, frozenThirdInverseWeight fixed]

/-- Explicit reindexing of the arbitrary-frozen-weight three-cycle. -/
def explicitFrozenFiberThreeCycleLaplacian
    (fixed : Lattice.PositiveMassConfig 3) (pair : Real × Real) :
    Matrix (Fin 3) (Fin 3) Real :=
  let x := pair.1⁻¹
  let y := pair.2⁻¹
  let z := frozenThirdInverseWeight fixed
  !![x + y, -y, -x;
     -y, y + z, -z;
     -x, -z, x + z]

/-- Direct finite-matrix identification for arbitrary frozen third mass. -/
theorem finWeightedCycleLaplacian_frozenFiberThreeSiteInverseWeights
    (fixed : Lattice.PositiveMassConfig 3) (pair : Real × Real) :
    finWeightedCycleLaplacian (frozenFiberThreeSiteInverseWeights fixed pair) =
      explicitFrozenFiberThreeCycleLaplacian fixed pair := by
  rw [finWeightedCycleLaplacian_eq_sum_rankOne]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, Fin.sum_univ_succ]
  <;> norm_num +decide [frozenFiberThreeSiteInverseWeights,
    explicitFrozenFiberThreeCycleLaplacian, frozenThirdInverseWeight,
    finCycleEdgeVector,
    SingleMassRankOnePerturbation.cycleMassPerturbationVector,
    differenceMatrix, siteEquivFin]
  <;> simp
  <;> ring

/-- Evaluation of the arbitrary-frozen three-cycle characteristic
polynomial. -/
theorem explicitFrozenFiberThreeCycleLaplacian_charpoly_eval
    (fixed : Lattice.PositiveMassConfig 3) (pair : Real × Real)
    (energy : Real) :
    (explicitFrozenFiberThreeCycleLaplacian fixed pair).charpoly.eval energy =
      energy * (energy ^ 2 -
        2 * (pair.1⁻¹ + pair.2⁻¹ + frozenThirdInverseWeight fixed) * energy +
        3 * (pair.1⁻¹ * pair.2⁻¹ +
          pair.1⁻¹ * frozenThirdInverseWeight fixed +
          pair.2⁻¹ * frozenThirdInverseWeight fixed)) := by
  rw [Matrix.eval_charpoly, Matrix.det_fin_three]
  simp [explicitFrozenFiberThreeCycleLaplacian, Matrix.scalar_apply]
  ring

/-- The genuine physical mass configuration on the frozen fiber. -/
def frozenFiberThreeSiteMassConfig
    (fixed : Lattice.PositiveMassConfig 3) (pair : Real × Real) :
    Lattice.PositiveMassConfig 3 :=
  twoSiteMassConfig fixed (0 : Lattice.Site 3) (1 : Lattice.Site 3) pair

/-- Its genuine physical harmonic Hermitian matrix. -/
def frozenFiberThreeSiteHarmonic
    (fixed : Lattice.PositiveMassConfig 3) (pair : Real × Real) :
    HermitianMatrix (Lattice.Site 3) :=
  twoSiteHarmonicHermitian fixed
    (0 : Lattice.Site 3) (1 : Lattice.Site 3) pair

/-- On the physical support, the inverse coordinates are exactly the two raw
inverse masses followed by the arbitrary frozen inverse mass. -/
theorem inverseMassCoordinates_frozenFiberThreeSiteMassConfig
    (fixed : Lattice.PositiveMassConfig 3)
    {pair : Real × Real} (hpair : pair ∈ iidMassPairSupport) :
    inverseMassCoordinates (frozenFiberThreeSiteMassConfig fixed pair) =
      frozenFiberThreeSiteInverseWeights fixed pair := by
  funext k
  fin_cases k <;>
    simp [inverseMassCoordinates, frozenFiberThreeSiteMassConfig,
      frozenFiberThreeSiteInverseWeights, frozenThirdInverseWeight,
      siteEquivFin, twoSiteMassConfig, clippedMass_eq_self, hpair.1, hpair.2]
  <;> try { congr 1 <;> decide }

/-- The genuine arbitrary-frozen physical characteristic equation has the
displayed inverse-mass quadratic factor. -/
theorem frozenFiberThreeSiteHarmonic_charpoly_eval
    (fixed : Lattice.PositiveMassConfig 3)
    {pair : Real × Real} (hpair : pair ∈ iidMassPairSupport)
    (energy : Real) :
    (Matrix.charpoly
      (Matrix.of (frozenFiberThreeSiteHarmonic fixed pair).val)).eval energy =
      energy * (energy ^ 2 -
        2 * (pair.1⁻¹ + pair.2⁻¹ + frozenThirdInverseWeight fixed) * energy +
        3 * (pair.1⁻¹ * pair.2⁻¹ +
          pair.1⁻¹ * frozenThirdInverseWeight fixed +
          pair.2⁻¹ * frozenThirdInverseWeight fixed)) := by
  let m := frozenFiberThreeSiteMassConfig fixed pair
  have hchar :
      (massWeightedHarmonicMatrix m).charpoly =
        (finWeightedCycleLaplacian (inverseMassCoordinates m)).charpoly := by
    calc
      (massWeightedHarmonicMatrix m).charpoly =
          (massWeightedDifferenceMatrix m *
            Matrix.transpose (massWeightedDifferenceMatrix m)).charpoly :=
        Matrix.charpoly_mul_comm
          (Matrix.transpose (massWeightedDifferenceMatrix m))
          (massWeightedDifferenceMatrix m)
      _ = (weightedCycleLaplacian (fun i => (m.mass i)⁻¹)).charpoly := by
        rw [massWeighted_selfTranspose_eq_weightedCycleLaplacian]
      _ = (weightedCycleLaplacian
          (weightsOfCoordinates (inverseMassCoordinates m))).charpoly := by
        rw [weightsOfCoordinates_inverseMassCoordinates]
      _ = (finWeightedCycleLaplacian
          (inverseMassCoordinates m)).charpoly := by
        symm
        exact Matrix.charpoly_reindex _ _
  change (massWeightedHarmonicMatrix m).charpoly.eval energy = _
  rw [hchar, inverseMassCoordinates_frozenFiberThreeSiteMassConfig
    fixed hpair,
    finWeightedCycleLaplacian_frozenFiberThreeSiteInverseWeights]
  exact explicitFrozenFiberThreeCycleLaplacian_charpoly_eval fixed pair energy

/-- The second ordered mode is positive whenever the three-site spectrum is
simple; index two is the deterministic acoustic mode. -/
theorem frozenFiberThreeSite_secondEnergy_pos_of_simple
    (fixed : Lattice.PositiveMassConfig 3) (pair : Real × Real)
    (hsimple : SimpleOrderedSpectrum
      (frozenFiberThreeSiteHarmonic fixed pair)) :
    0 < orderedEigenvalue (frozenFiberThreeSiteHarmonic fixed pair) 1 := by
  have hfrequency : 0 < orderedModeFrequency
      (frozenFiberThreeSiteHarmonic fixed pair) 1 := by
    apply (orderedModeFrequency_pos_iff_ne_last
      (frozenFiberThreeSiteMassConfig fixed pair) hsimple 1).2
    decide
  exact Real.sqrt_pos.mp hfrequency

/-- The selected positive energy satisfies the explicit quadratic factor. -/
theorem frozenFiberThreeSite_secondEnergy_residual_eq_zero
    (fixed : Lattice.PositiveMassConfig 3)
    {pair : Real × Real} (hpair : pair ∈ iidMassPairSupport)
    (hsimple : SimpleOrderedSpectrum
      (frozenFiberThreeSiteHarmonic fixed pair)) :
    let energy := orderedEigenvalue
      (frozenFiberThreeSiteHarmonic fixed pair) 1
    energy ^ 2 -
        2 * (pair.1⁻¹ + pair.2⁻¹ + frozenThirdInverseWeight fixed) * energy +
        3 * (pair.1⁻¹ * pair.2⁻¹ +
          pair.1⁻¹ * frozenThirdInverseWeight fixed +
          pair.2⁻¹ * frozenThirdInverseWeight fixed) = 0 := by
  dsimp only
  have hroot :
      orderedEigenvalue (frozenFiberThreeSiteHarmonic fixed pair) 1 *
        (orderedEigenvalue (frozenFiberThreeSiteHarmonic fixed pair) 1 ^ 2 -
          2 * (pair.1⁻¹ + pair.2⁻¹ + frozenThirdInverseWeight fixed) *
            orderedEigenvalue (frozenFiberThreeSiteHarmonic fixed pair) 1 +
          3 * (pair.1⁻¹ * pair.2⁻¹ +
            pair.1⁻¹ * frozenThirdInverseWeight fixed +
            pair.2⁻¹ * frozenThirdInverseWeight fixed)) = 0 := by
    rw [← frozenFiberThreeSiteHarmonic_charpoly_eval fixed hpair]
    exact charpoly_eval_orderedEigenvalue_eq_zero
      (frozenFiberThreeSiteHarmonic fixed pair) 1
  exact (mul_eq_zero.mp hroot).resolve_left
    (ne_of_gt (frozenFiberThreeSite_secondEnergy_pos_of_simple
      fixed pair hsimple))

@[simp] theorem orderedIndexEquiv_symm_firstPositivePhysicalModeThree :
    orderedIndexEquiv.symm firstPositivePhysicalModeThree =
      (0 : Fin (Fintype.card (Lattice.Site 3))) := by
  change orderedIndexEquiv.symm
      (orderedIndexEquiv
        (0 : Fin (Fintype.card (Lattice.Site 3)))) = 0
  exact orderedIndexEquiv.symm_apply_apply _

@[simp] theorem orderedIndexEquiv_symm_secondPositivePhysicalModeThree :
    orderedIndexEquiv.symm secondPositivePhysicalModeThree =
      (1 : Fin (Fintype.card (Lattice.Site 3))) := by
  change orderedIndexEquiv.symm
      (orderedIndexEquiv
        (1 : Fin (Fintype.card (Lattice.Site 3)))) = 1
  exact orderedIndexEquiv.symm_apply_apply _

/-- The actual mismatch chart for the concrete history is exactly the
negative second positive ordered-frequency branch. -/
theorem frozenFiberThreeSite_outerMismatchChart_eq
    (fixed : Lattice.PositiveMassConfig 3) :
    physlibIteratedA2PairMismatchChart fixed
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
        firstPositivePhysicalModeThree threeSiteSingleFrequencyOuterTerm =
      fun pair => -orderedModeFrequency
        (frozenFiberThreeSiteHarmonic fixed pair) 1 := by
  funext pair
  rw [show physlibIteratedA2PairMismatchChart fixed
      (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
      firstPositivePhysicalModeThree threeSiteSingleFrequencyOuterTerm pair =
      iteratedQuadraticOuterMismatch
        (frozenFiberThreeSiteMassConfig fixed pair)
        firstPositivePhysicalModeThree
        threeSiteSingleFrequencyOuterTerm by rfl]
  rw [threeSiteSingleFrequency_outerMismatch_eq]
  rw [← orderedPullbackFrequency_eq_modeFrequency]
  unfold orderedPullbackFrequency
  rw [orderedIndexEquiv_symm_secondPositivePhysicalModeThree]
  rfl

/-- Jacobian-only elimination on every positive frozen fiber.  This is the
substantive channel-specific theorem: no polynomial implication is assumed. -/
theorem frozenFiberThreeSite_outerVerticalJacobian_zero_forces_inverse_eq
    (fixed : Lattice.PositiveMassConfig 3)
    {pair : Real × Real} (hpair : pair ∈ interior iidMassPairSupport)
    (hsimple : SimpleOrderedSpectrum
      (frozenFiberThreeSiteHarmonic fixed pair))
    (hjacobian : physlibIteratedA2PairMismatchVerticalJacobian fixed
      (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
      firstPositivePhysicalModeThree threeSiteSingleFrequencyOuterTerm pair = 0) :
    pair.1⁻¹ = frozenThirdInverseWeight fixed := by
  let frequency : Real × Real → Real := fun nearby =>
    orderedModeFrequency (frozenFiberThreeSiteHarmonic fixed nearby) 1
  let energy : Real × Real → Real := fun nearby =>
    orderedEigenvalue (frozenFiberThreeSiteHarmonic fixed nearby) 1
  have hpositive : 0 < orderedEigenvalue
      (frozenFiberThreeSiteHarmonic fixed pair) 1 :=
    frozenFiberThreeSite_secondEnergy_pos_of_simple fixed pair hsimple
  obtain ⟨Dfrequency, hfrequency⟩ :=
    exists_hasStrictFDerivAt_actualTwoMassOrderedModeFrequency
      fixed (by decide) hpair hsimple 1 hpositive
  have hfrequency' : HasStrictFDerivAt frequency Dfrequency pair := by
    simpa [frequency, frozenFiberThreeSiteHarmonic] using hfrequency
  have hnegative : HasFDerivAt (fun nearby => -frequency nearby)
      (-Dfrequency) pair := by
    exact hfrequency'.hasFDerivAt.neg
  have hjacobian' :
      fderiv Real (fun nearby => -frequency nearby) pair (0, 1) = 0 := by
    simpa [physlibIteratedA2PairMismatchVerticalJacobian,
      frozenFiberThreeSite_outerMismatchChart_eq, frequency] using hjacobian
  have hDfrequencyVertical : Dfrequency (0, 1) = 0 := by
    rw [hnegative.fderiv] at hjacobian'
    simpa using hjacobian'
  have hinclusion : HasFDerivAt (fun second : Real => (pair.1, second))
      (ContinuousLinearMap.inr Real Real Real) pair.2 :=
    hasFDerivAt_prodMk_right pair.1 pair.2
  have hfrequencyLine : HasDerivAt
      (fun second => frequency (pair.1, second)) 0 pair.2 := by
    have hcomp := hfrequency'.hasFDerivAt.comp pair.2 hinclusion
    simpa [Function.comp_def, ContinuousLinearMap.comp_apply,
      hDfrequencyVertical] using hcomp.hasDerivAt
  have henergyLine : HasDerivAt
      (fun second => energy (pair.1, second)) 0 pair.2 := by
    have hsquare := hfrequencyLine.pow 2
    have heventually :
        (fun second => energy (pair.1, second)) =ᶠ[nhds pair.2]
          (fun second => frequency (pair.1, second)) ^ 2 :=
      Filter.Eventually.of_forall fun second =>
        (orderedModeFrequency_sq_eq_orderedEigenvalue
          (frozenFiberThreeSiteMassConfig fixed (pair.1, second)) 1).symm
    simpa using hsquare.congr_of_eventuallyEq heventually
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
          (nhds pair.2) (nhds pair) := by
        exact hinclusion.continuousAt
      exact htendsto.eventually (isOpen_interior.mem_nhds hpair)
    have hsimpleEventually : ∀ᶠ second in nhds pair.2,
        SimpleOrderedSpectrum
          (frozenFiberThreeSiteHarmonic fixed (pair.1, second)) := by
      have hglobal := eventually_simple_twoSiteHarmonicHermitian fixed
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) pair hsimple
      have htendsto : Tendsto (fun second : Real => (pair.1, second))
          (nhds pair.2) (nhds pair) := by
        exact hinclusion.continuousAt
      simpa [frozenFiberThreeSiteHarmonic] using htendsto.eventually hglobal
    filter_upwards [hinteriorEventually, hsimpleEventually]
      with second hinterior hsimpleSecond
    simpa [residualLine, energy] using
      frozenFiberThreeSite_secondEnergy_residual_eq_zero fixed
        (interior_subset hinterior) hsimpleSecond
  have hderivativeEquation :
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
  have hinverseDerivativeNe : inverseDerivative ≠ 0 := by
    simp [inverseDerivative, hsecondNe]
  have hlinear :
      -2 * energy pair +
        3 * (pair.1⁻¹ + frozenThirdInverseWeight fixed) = 0 :=
    (mul_eq_zero.mp hderivativeEquation).resolve_left hinverseDerivativeNe
  have hresidual := frozenFiberThreeSite_secondEnergy_residual_eq_zero
    fixed (interior_subset hpair) hsimple
  have hlinearMul :
      (-2 * energy pair +
        3 * (pair.1⁻¹ + frozenThirdInverseWeight fixed)) * pair.2⁻¹ = 0 := by
    rw [hlinear, zero_mul]
  have hsquare :
      (pair.1⁻¹ - frozenThirdInverseWeight fixed) ^ 2 = 0 := by
    dsimp only at hresidual
    nlinarith [hresidual, hlinear, hlinearMul]
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)

/-- The explicit mass-only Jacobian eliminant on an arbitrary frozen fiber. -/
def frozenFiberThreeSiteOuterJacobianPolynomial
    (fixed : Lattice.PositiveMassConfig 3) : MvPolynomial (Fin 2) Real :=
  MvPolynomial.X 0 - MvPolynomial.C (frozenThirdInverseWeight fixed)

@[simp] theorem frozenFiberThreeSiteOuterJacobianPolynomial_eval
    (fixed : Lattice.PositiveMassConfig 3) (pair : Real × Real) :
    MvPolynomial.eval (iidInverseMassPairCoordinates pair)
        (frozenFiberThreeSiteOuterJacobianPolynomial fixed) =
      pair.1⁻¹ - frozenThirdInverseWeight fixed := by
  simp [frozenFiberThreeSiteOuterJacobianPolynomial]

/-- The frozen-fiber eliminant is genuinely nonzero for every background. -/
theorem frozenFiberThreeSiteOuterJacobianPolynomial_ne_zero
    (fixed : Lattice.PositiveMassConfig 3) :
    frozenFiberThreeSiteOuterJacobianPolynomial fixed ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval
      (![frozenThirdInverseWeight fixed + 1, 0] : Fin 2 → Real)) hzero
  simp [frozenFiberThreeSiteOuterJacobianPolynomial] at heval

/-- Exact polynomial implication needed by the algebraic bad-set API. -/
theorem frozenFiberThreeSite_outerVerticalJacobian_zero_forces_polynomial_zero
    (fixed : Lattice.PositiveMassConfig 3)
    (pair : Real × Real) (hpair : pair ∈ interior iidMassPairSupport)
    (hsimple : SimpleOrderedSpectrum
      (twoSiteHarmonicHermitian fixed
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) pair))
    (hjacobian : physlibIteratedA2PairMismatchVerticalJacobian fixed
      (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
      firstPositivePhysicalModeThree threeSiteSingleFrequencyOuterTerm pair = 0) :
    MvPolynomial.eval (iidInverseMassPairCoordinates pair)
      (frozenFiberThreeSiteOuterJacobianPolynomial fixed) = 0 := by
  rw [frozenFiberThreeSiteOuterJacobianPolynomial_eval]
  exact sub_eq_zero.mpr
    (frozenFiberThreeSite_outerVerticalJacobian_zero_forces_inverse_eq
      fixed hpair hsimple hjacobian)

/-- The concrete ordinary channel contains only ordered modes zero and one,
so it avoids the deterministic ordered acoustic mode two. -/
theorem threeSiteSingleFrequencyOuter_avoidsAcoustic :
    IteratedA2ChannelAvoidsAcoustic .outer firstPositivePhysicalModeThree
      threeSiteSingleFrequencyOuterTerm := by
  intro mode hmode
  simp [iteratedA2ChannelParticipatingModes, iteratedA2ChannelActiveTerm,
    threeSiteSingleFrequencyOuterTerm, iteratedQuadraticFreeMode,
    iteratedQuadraticFirstPicardMode, iteratedQuadraticInnerEntry,
    iteratedQuadraticOuterModes, iteratedQuadraticFirstPicardSlot,
    iteratedQuadraticFreeSign, otherQuadraticSlot,
    quadraticCollisionModes] at hmode
  rcases hmode with rfl | ⟨r, rfl⟩
  · rw [orderedIndexEquiv_symm_firstPositivePhysicalModeThree]
    change (0 : Fin 3) ≠ 2
    decide
  · fin_cases r
    · change orderedIndexEquiv.symm secondPositivePhysicalModeThree ≠
        lastOrderedIndex
      rw [orderedIndexEquiv_symm_secondPositivePhysicalModeThree]
      change (1 : Fin 3) ≠ 2
      decide
    · change orderedIndexEquiv.symm firstPositivePhysicalModeThree ≠
        lastOrderedIndex
      rw [orderedIndexEquiv_symm_firstPositivePhysicalModeThree]
      change (0 : Fin 3) ≠ 2
      decide
    · change orderedIndexEquiv.symm firstPositivePhysicalModeThree ≠
        lastOrderedIndex
      rw [orderedIndexEquiv_symm_firstPositivePhysicalModeThree]
      change (0 : Fin 3) ≠ 2
      decide

end

end ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianFrozenFiber
