import ArchonPhysics.ActualThreeMassHellmannFeynmanJacobian
import ArchonPhysics.ActualThreeMassLiftedJacobianContinuity
import ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianFrozenFiber

/-!
# Quantitative bridges for the actual three-site outer A2 channel

This module supplies the two pointwise facts needed before a quantitative
compact-atlas argument can use the explicit eliminant `X 0 - C z`.

First, the genuine derivative of the full three-mass mismatch ∈ the second
raw mass is identified with the already audited pair-fiber vertical
Jacobian.  The full derivative is the Hellmann--Feynman projector row, so it
is locally continuous throughout the interior simple-positive locus.

Second, the elementary three-cycle characteristic polynomial is used with
an arbitrary frozen third inverse mass.  A repeated positive root forces all
three inverse masses to agree.  In particular every nonsimple point is
contained ∈ the same inverse-mass diagonal detected by the Jacobian
eliminant.  No almost-everywhere or external simplicity hypothesis is used.
-/

open scoped Matrix

namespace ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeBridges

open ArchonPhysics
open ArchonPhysics.ActualThreeMassHellmannFeynmanJacobian
open ArchonPhysics.ActualThreeMassLiftedJacobianContinuity
open ArchonPhysics.ActualThreeMassLiftedSimpleEigenvalueDifferentiability
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianEliminant
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianFrozenFiber
open ArchonPhysics.ActualTwoMassSimpleEigenvalueDifferentiability
open ArchonPhysics.ActualTwoMassSpectralJacobianPolynomial
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.RandomMassSimpleSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.ThreeParameterProjectorWeightJacobian
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open Filter Function Set

noncomputable section

/-! ## The full three-mass chart and its true second-mass derivative -/

/-- A harmless positive background.  All three sites are replaced by the
raw coordinates ∈ the full three-mass family, so its numerical values do
not affect the resulting configuration. -/
def threeSiteOuterTripleBackground : Lattice.PositiveMassConfig 3 where
  mass _ := 1
  mass_pos _ := by norm_num

/-- The genuine three-site configuration associated with the nested raw
mass triple `((m0,m1),m2)`. -/
def threeSiteOuterTripleMassConfig (triple : MassTriple) :
    Lattice.PositiveMassConfig 3 :=
  threeMassSiteConfig threeSiteOuterTripleBackground
    (0 : Lattice.Site 3) (1 : Lattice.Site 3) (2 : Lattice.Site 3) triple

/-- The genuine harmonic matrix of the full three-mass family. -/
def threeSiteOuterTripleHarmonic (triple : MassTriple) :
    HermitianMatrix (Lattice.Site 3) :=
  threeMassHarmonicHermitian threeSiteOuterTripleBackground
    (0 : Lattice.Site 3) (1 : Lattice.Site 3) (2 : Lattice.Site 3) triple

/-- The actual ordinary outer mismatch, written on all three iid raw mass
coordinates.  It is the negative second positive ordered frequency. -/
def threeSiteOuterTripleMismatch (triple : MassTriple) : Real :=
  -orderedModeFrequency (threeSiteOuterTripleHarmonic triple) 1

/-- Repeat the selected second positive mode ∈ the three-row
Hellmann--Feynman interface; only row zero is used below. -/
def threeSiteOuterRepeatedSecondMode :
    Fin 3 → Fin (Fintype.card (Lattice.Site 3)) :=
  fun _ => 1

/-- The explicit true derivative field of the full three-mass mismatch. -/
def threeSiteOuterTripleMismatchDerivative (triple : MassTriple) :
    MassTriple →L[Real] Real :=
  -massTripleLinearFunctional
    ((actualThreeMassFrequencyProjectorJacobianMatrix
      threeSiteOuterTripleBackground
      (0 : Lattice.Site 3) (1 : Lattice.Site 3) (2 : Lattice.Site 3)
      threeSiteOuterRepeatedSecondMode triple) 0)

/-- A background which freezes precisely the third raw mass. -/
def threeSiteOuterFrozenThirdBackground (third : Real) :
    Lattice.PositiveMassConfig 3 where
  mass site := if site = (2 : Lattice.Site 3) then clippedMass third else 1
  mass_pos site := by
    split_ifs
    · exact clippedMass_pos third
    · norm_num

@[simp] theorem threeSiteOuterFrozenThirdBackground_mass_two
    (third : Real) :
    (threeSiteOuterFrozenThirdBackground third).mass
        (2 : Lattice.Site 3) = clippedMass third := by
  simp [threeSiteOuterFrozenThirdBackground]

/-- Replacing the first two masses after freezing the third is exactly the
same configuration as replacing all three at once. -/
theorem frozenFiberThreeSiteMassConfig_outerBackground_eq
    (triple : MassTriple) :
    frozenFiberThreeSiteMassConfig
        (threeSiteOuterFrozenThirdBackground triple.2) triple.1 =
      threeSiteOuterTripleMassConfig triple := by
  rw [Lattice.PositiveMassConfig.mk.injEq]
  funext site
  fin_cases site <;>
    simp [frozenFiberThreeSiteMassConfig, twoSiteMassConfig,
      threeSiteOuterFrozenThirdBackground, threeSiteOuterTripleMassConfig,
      threeMassSiteConfig, threeSiteOuterTripleBackground]

/-- Consequently the frozen-pair and full-triple harmonic matrices agree
pointwise, including outside the iid support (both sides use clipping). -/
theorem frozenFiberThreeSiteHarmonic_outerBackground_eq
    (triple : MassTriple) :
    frozenFiberThreeSiteHarmonic
        (threeSiteOuterFrozenThirdBackground triple.2) triple.1 =
      threeSiteOuterTripleHarmonic triple := by
  exact congrArg harmonicHermitian
    (frozenFiberThreeSiteMassConfig_outerBackground_eq triple)

/-- Restricting the full triple mismatch to its second-mass line gives the
existing audited pair-fiber chart exactly. -/
theorem threeSiteOuterTripleMismatch_secondMassLine_eq_pairChart
    (triple : MassTriple) (second : Real) :
    threeSiteOuterTripleMismatch ((triple.1.1, second), triple.2) =
      physlibIteratedA2PairMismatchChart
        (threeSiteOuterFrozenThirdBackground triple.2)
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
        firstPositivePhysicalModeThree threeSiteSingleFrequencyOuterTerm
        (triple.1.1, second) := by
  rw [frozenFiberThreeSite_outerMismatchChart_eq]
  unfold threeSiteOuterTripleMismatch
  rw [← frozenFiberThreeSiteHarmonic_outerBackground_eq]

/-- The second ordered energy is positive at every simple point of the full
three-site family. -/
theorem threeSiteOuterTriple_secondEnergy_pos_of_simple
    (triple : MassTriple)
    (hsimple : SimpleOrderedSpectrum
      (threeSiteOuterTripleHarmonic triple)) :
    0 < orderedEigenvalue (threeSiteOuterTripleHarmonic triple) 1 := by
  have hfrequency : 0 < orderedModeFrequency
      (threeSiteOuterTripleHarmonic triple) 1 := by
    apply (orderedModeFrequency_pos_iff_ne_last
      (threeSiteOuterTripleMassConfig triple) hsimple 1).2
    decide
  exact Real.sqrt_pos.mp hfrequency

/-- The explicit projector-row field is the strict derivative of the
actual full-triple outer mismatch. -/
theorem hasStrictFDerivAt_threeSiteOuterTripleMismatch
    {triple : MassTriple} (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeSiteOuterTripleHarmonic triple)) :
    HasStrictFDerivAt threeSiteOuterTripleMismatch
      (threeSiteOuterTripleMismatchDerivative triple) triple := by
  have hpositive : ∀ r : Fin 3,
      0 < orderedEigenvalue (threeSiteOuterTripleHarmonic triple)
        (threeSiteOuterRepeatedSecondMode r) := by
    intro r
    exact threeSiteOuterTriple_secondEnergy_pos_of_simple triple hsimple
  obtain ⟨derivative, hderivative, hrow⟩ :=
    exists_actualThreeMassFrequencyDerivative_eq_projectorRow
      threeSiteOuterTripleBackground (by decide) (by decide) (by decide)
      threeSiteOuterRepeatedSecondMode htriple hsimple hpositive 0
  rw [hrow] at hderivative
  change HasStrictFDerivAt
    (-(fun nearby : MassTriple => orderedModeFrequency
      (threeMassHarmonicHermitian threeSiteOuterTripleBackground
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) (2 : Lattice.Site 3) nearby) 1))
    (-massTripleLinearFunctional
      ((actualThreeMassFrequencyProjectorJacobianMatrix
        threeSiteOuterTripleBackground
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) (2 : Lattice.Site 3)
        threeSiteOuterRepeatedSecondMode triple) 0)) triple
  simpa [threeSiteOuterRepeatedSecondMode] using hderivative.neg

/-- The genuine full-triple derivative field is locally continuous on the
interior simple locus. -/
theorem continuousAt_threeSiteOuterTripleMismatchDerivative
    {triple : MassTriple} (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeSiteOuterTripleHarmonic triple)) :
    ContinuousAt threeSiteOuterTripleMismatchDerivative triple := by
  have hpositive : ∀ r : Fin 3,
      0 < orderedEigenvalue (threeSiteOuterTripleHarmonic triple)
        (threeSiteOuterRepeatedSecondMode r) := by
    intro r
    exact threeSiteOuterTriple_secondEnergy_pos_of_simple triple hsimple
  have hmatrix :=
    continuousAt_actualThreeMassFrequencyProjectorJacobianMatrix
      threeSiteOuterTripleBackground
      (0 : Lattice.Site 3) (1 : Lattice.Site 3) (2 : Lattice.Site 3)
      threeSiteOuterRepeatedSecondMode htriple hsimple hpositive
  let matrix := fun nearby =>
    actualThreeMassFrequencyProjectorJacobianMatrix
      threeSiteOuterTripleBackground
      (0 : Lattice.Site 3) (1 : Lattice.Site 3) (2 : Lattice.Site 3)
      threeSiteOuterRepeatedSecondMode nearby
  have hentry (s : Fin 3) : ContinuousAt (fun nearby => matrix nearby 0 s) triple :=
    (continuous_apply s).continuousAt.comp
      ((continuous_apply (0 : Fin 3)).continuousAt.comp hmatrix)
  have hzero : ContinuousAt (fun nearby =>
      matrix nearby 0 0 • massTripleCoordinateZero) triple :=
    (hentry 0).smul continuousAt_const
  have hone : ContinuousAt (fun nearby =>
      matrix nearby 0 1 • massTripleCoordinateOne) triple :=
    (hentry 1).smul continuousAt_const
  have htwo : ContinuousAt (fun nearby =>
      matrix nearby 0 2 • massTripleCoordinateTwo) triple :=
    (hentry 2).smul continuousAt_const
  change ContinuousAt (fun nearby =>
    -((matrix nearby 0 0 • massTripleCoordinateZero +
      matrix nearby 0 1 • massTripleCoordinateOne) +
      matrix nearby 0 2 • massTripleCoordinateTwo)) triple
  exact ((hzero.add hone).add htwo).neg

/-- Exact bridge requested by the quantitative fiber argument: evaluating
the true full-three-mass derivative ∈ the `m1` direction is the pair-fiber
vertical Jacobian already used by the eliminant theorem. -/
theorem threeSiteOuterTripleMismatchDerivative_second_eq_pairVerticalJacobian
    {triple : MassTriple} (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeSiteOuterTripleHarmonic triple)) :
    threeSiteOuterTripleMismatchDerivative triple (massTripleBasis 1) =
      physlibIteratedA2PairMismatchVerticalJacobian
        (threeSiteOuterFrozenThirdBackground triple.2)
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
        firstPositivePhysicalModeThree threeSiteSingleFrequencyOuterTerm
        triple.1 := by
  let line : Real → MassTriple := fun second =>
    ((triple.1.1, second), triple.2)
  have hline : HasDerivAt line (massTripleBasis 1) triple.1.2 := by
    simpa [line] using
      (((hasDerivAt_const triple.1.2 triple.1.1).prodMk (hasDerivAt_id triple.1.2)).prodMk
        (hasDerivAt_const triple.1.2 triple.2))
  have hfull : HasDerivAt (fun second =>
      threeSiteOuterTripleMismatch ((triple.1.1, second), triple.2))
      (threeSiteOuterTripleMismatchDerivative triple (massTripleBasis 1))
      triple.1.2 := by
    have hcomp :=
      (hasStrictFDerivAt_threeSiteOuterTripleMismatch htriple hsimple).hasFDerivAt.comp
        triple.1.2 hline.hasFDerivAt
    simpa [line, ContinuousLinearMap.comp_apply, Function.comp_def] using
      hcomp.hasDerivAt
  let fixed := threeSiteOuterFrozenThirdBackground triple.2
  let pairChart := physlibIteratedA2PairMismatchChart fixed
    (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
    firstPositivePhysicalModeThree threeSiteSingleFrequencyOuterTerm
  have hpairInterior : triple.1 ∈ interior iidMassPairSupport := by
    rw [iidMassTripleSupport, interior_prod_eq] at htriple
    exact htriple.1
  have hsimpleFiber : SimpleOrderedSpectrum
      (frozenFiberThreeSiteHarmonic fixed triple.1) := by
    rw [frozenFiberThreeSiteHarmonic_outerBackground_eq]
    exact hsimple
  obtain ⟨frequencyDerivative, hfrequency⟩ :=
    exists_hasStrictFDerivAt_actualTwoMassOrderedModeFrequency
      fixed (by decide) hpairInterior hsimpleFiber 1
        (frozenFiberThreeSite_secondEnergy_pos_of_simple
          fixed triple.1 hsimpleFiber)
  have hpairStrict : HasStrictFDerivAt pairChart (-frequencyDerivative)
      triple.1 := by
    rw [show pairChart = fun pair => -orderedModeFrequency
      (frozenFiberThreeSiteHarmonic fixed pair) 1 by
        simpa [pairChart] using frozenFiberThreeSite_outerMismatchChart_eq fixed]
    change HasStrictFDerivAt
      (-(fun pair : Real × Real => orderedModeFrequency
        (twoSiteHarmonicHermitian fixed (0 : Lattice.Site 3)
          (1 : Lattice.Site 3) pair) 1)) (-frequencyDerivative) triple.1
    exact hfrequency.neg
  have hpairLine : HasDerivAt (fun second => pairChart (triple.1.1, second))
      (physlibIteratedA2PairMismatchVerticalJacobian fixed
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
        firstPositivePhysicalModeThree threeSiteSingleFrequencyOuterTerm
        triple.1) triple.1.2 := by
    have hinclusion : HasFDerivAt (fun second : Real =>
        (triple.1.1, second))
        (ContinuousLinearMap.inr Real Real Real) triple.1.2 :=
      hasFDerivAt_prodMk_right triple.1.1 triple.1.2
    have hcomp := hpairStrict.hasFDerivAt.comp triple.1.2 hinclusion
    have hfderiv : fderiv Real pairChart triple.1 = -frequencyDerivative :=
      hpairStrict.hasFDerivAt.fderiv
    simpa [physlibIteratedA2PairMismatchVerticalJacobian, pairChart,
      hfderiv, ContinuousLinearMap.comp_apply, Function.comp_def] using hcomp.hasDerivAt
  have heq : (fun second =>
      threeSiteOuterTripleMismatch ((triple.1.1, second), triple.2)) =
      fun second => pairChart (triple.1.1, second) := by
    funext second
    exact threeSiteOuterTripleMismatch_secondMassLine_eq_pairChart
      triple second
  exact hfull.unique (by simpa [heq] using hpairLine)

/-! ## Arbitrary-third-mass spectrum degeneracy is ∈ the same diagonal -/

/-- The characteristic polynomial with arbitrary frozen inverse mass. -/
def frozenFiberThreeSiteCharacteristicPolynomial
    (fixed : Lattice.PositiveMassConfig 3) (pair : Real × Real) :
    Polynomial Real :=
  Polynomial.X *
    (Polynomial.X ^ 2 -
      Polynomial.C (2 * (pair.1⁻¹ + pair.2⁻¹ +
        frozenThirdInverseWeight fixed)) * Polynomial.X +
      Polynomial.C (3 * (pair.1⁻¹ * pair.2⁻¹ +
        pair.1⁻¹ * frozenThirdInverseWeight fixed +
        pair.2⁻¹ * frozenThirdInverseWeight fixed)))

/-- Polynomial identity underlying the arbitrary-frozen simplicity audit. -/
theorem frozenFiberThreeSiteHarmonic_charpoly
    (fixed : Lattice.PositiveMassConfig 3)
    {pair : Real × Real} (hpair : pair ∈ iidMassPairSupport) :
    Matrix.charpoly (Matrix.of
      (frozenFiberThreeSiteHarmonic fixed pair).val) =
        frozenFiberThreeSiteCharacteristicPolynomial fixed pair := by
  apply Polynomial.funext
  intro energy
  rw [frozenFiberThreeSiteHarmonic_charpoly_eval fixed hpair]
  simp [frozenFiberThreeSiteCharacteristicPolynomial]

/-- If the first inverse mass differs from the frozen third inverse mass,
the complete three-site ordered spectrum is simple.  Contrapositively every
spectral degeneracy lies ∈ `m0⁻¹ = m2⁻¹` (indeed the proof forces all
three inverse masses to agree). -/
theorem frozenFiberThreeSiteHarmonic_simple_of_firstInverse_ne_frozenThird
    (fixed : Lattice.PositiveMassConfig 3)
    {pair : Real × Real} (hpair : pair ∈ iidMassPairSupport)
    (hne : pair.1⁻¹ ≠ frozenThirdInverseWeight fixed) :
    SimpleOrderedSpectrum (frozenFiberThreeSiteHarmonic fixed pair) := by
  apply simpleOrderedSpectrum_of_not_orderedPositiveDuplicate
    (frozenFiberThreeSiteMassConfig fixed pair)
  intro hduplicate
  have hrepeated :=
    repeatedPositiveHarmonic_of_orderedPositiveDuplicate
      (frozenFiberThreeSiteMassConfig fixed pair) hduplicate
  rcases hrepeated with ⟨lambda, hlambda, v, hv, heigen⟩
  let A := massWeightedHarmonicMatrix
    (frozenFiberThreeSiteMassConfig fixed pair)
  have hmultiple : 1 < A.charpoly.rootMultiplicity lambda :=
    rootMultiplicity_charpoly_gt_one_of_two_eigenvectors_at A v hv heigen
  have hrootDerivative :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot
      (Matrix.charpoly_monic A).ne_zero).1 hmultiple
  have hcharSource := frozenFiberThreeSiteHarmonic_charpoly fixed hpair
  have hmatrixOf :
      Matrix.of (frozenFiberThreeSiteHarmonic fixed pair).val = A := by
    ext i j
    rfl
  rw [hmatrixOf] at hcharSource
  have hchar : A.charpoly =
      frozenFiberThreeSiteCharacteristicPolynomial fixed pair := hcharSource
  have hrootThree :
      (frozenFiberThreeSiteCharacteristicPolynomial fixed pair).IsRoot
        lambda := by
    rw [← hchar]
    exact hrootDerivative.1
  let x := pair.1⁻¹
  let y := pair.2⁻¹
  let z := frozenThirdInverseWeight fixed
  have hroot : lambda = 0 ∨
      lambda ^ 2 - 2 * (x + y + z) * lambda +
        3 * (x * y + x * z + y * z) = 0 := by
    simpa [Polynomial.IsRoot.def,
      frozenFiberThreeSiteCharacteristicPolynomial, x, y, z] using hrootThree
  have hderivativeThree :
      (frozenFiberThreeSiteCharacteristicPolynomial fixed pair).derivative.eval
        lambda = 0 := by
    rw [← hchar]
    exact hrootDerivative.2
  have hderivative :
      3 * lambda ^ 2 - 4 * (x + y + z) * lambda +
        3 * (x * y + x * z + y * z) = 0 := by
    convert hderivativeThree using 1
    simp [frozenFiberThreeSiteCharacteristicPolynomial, x, y, z]
    ring
  have hquadratic :
      lambda ^ 2 - 2 * (x + y + z) * lambda +
        3 * (x * y + x * z + y * z) = 0 :=
    hroot.resolve_left hlambda.ne'
  have hlambdaSum : lambda = x + y + z := by
    nlinarith [hquadratic, hderivative]
  have hdiscriminant :
      (x - y) ^ 2 + (x - z) ^ 2 + (y - z) ^ 2 = 0 := by
    nlinarith [hquadratic]
  have hxz : x = z := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - z),
      sq_nonneg (y - z)]
  exact hne (by simpa [x, z] using hxz)

/-- Full-triple form: outside the inverse-mass diagonal, the actual
three-site spectrum is simple. -/
theorem threeSiteOuterTripleHarmonic_simple_of_inverse_separated
    {triple : MassTriple} (htriple : triple ∈ iidMassTripleSupport)
    (hne : triple.1.1⁻¹ ≠ triple.2⁻¹) :
    SimpleOrderedSpectrum (threeSiteOuterTripleHarmonic triple) := by
  let fixed := threeSiteOuterFrozenThirdBackground triple.2
  have hfrozen : frozenThirdInverseWeight fixed = triple.2⁻¹ := by
    simp [fixed, frozenThirdInverseWeight,
      threeSiteOuterFrozenThirdBackground, clippedMass_eq_self htriple.2]
  have hsimple :=
    frozenFiberThreeSiteHarmonic_simple_of_firstInverse_ne_frozenThird
      fixed htriple.1 (by simpa [hfrozen] using hne)
  rw [frozenFiberThreeSiteHarmonic_outerBackground_eq] at hsimple
  exact hsimple

/-- The full-triple true second-mass derivative can vanish only on the same
inverse-mass diagonal.  This combines the exact derivative bridge with the
already proved eliminant. -/
theorem threeSiteOuterTripleMismatchDerivative_second_zero_forces_inverse_eq
    {triple : MassTriple} (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeSiteOuterTripleHarmonic triple))
    (hzero : threeSiteOuterTripleMismatchDerivative triple
      (massTripleBasis 1) = 0) :
    triple.1.1⁻¹ = triple.2⁻¹ := by
  let fixed := threeSiteOuterFrozenThirdBackground triple.2
  have hpairInterior : triple.1 ∈ interior iidMassPairSupport := by
    rw [iidMassTripleSupport, interior_prod_eq] at htriple
    exact htriple.1
  have hsimpleFiber : SimpleOrderedSpectrum
      (frozenFiberThreeSiteHarmonic fixed triple.1) := by
    rw [frozenFiberThreeSiteHarmonic_outerBackground_eq]
    exact hsimple
  have hjacobian : physlibIteratedA2PairMismatchVerticalJacobian fixed
      (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
      firstPositivePhysicalModeThree threeSiteSingleFrequencyOuterTerm
      triple.1 = 0 := by
    rw [← threeSiteOuterTripleMismatchDerivative_second_eq_pairVerticalJacobian
      htriple hsimple]
    exact hzero
  have hinverse := frozenFiberThreeSite_outerVerticalJacobian_zero_forces_inverse_eq
    fixed hpairInterior hsimpleFiber hjacobian
  simpa [fixed, frozenThirdInverseWeight,
    threeSiteOuterFrozenThirdBackground,
    clippedMass_eq_self (interior_subset htriple).2] using hinverse

end

end ActualThreeSiteIteratedA2OuterQuantitativeBridges
end ArchonPhysics
