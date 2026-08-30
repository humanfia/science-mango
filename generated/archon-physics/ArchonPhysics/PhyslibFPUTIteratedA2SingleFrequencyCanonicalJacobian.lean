import ArchonPhysics.CanonicalPairCharacteristicJacobianResultant
import ArchonPhysics.PhyslibFPUTIteratedA2PairFiberSpectrumNonvanishing

/-!
# Canonical Jacobian elimination for a single-frequency A2 channel

Suppose an ordinary iterated-`A2` pair-fiber mismatch is identically a
nonzero signed multiple of one positive simple ordered mode frequency.  At a
zero of its vertical raw-mass Jacobian, the corresponding ordered energy has
zero derivative in that raw mass.  Differentiating the characteristic
identity after the change of variable `y = mass₂⁻¹` gives

`P⁺(E,x,y) = 0` and `partial_y P⁺(E,x,y) = 0`.

Consequently the canonical eliminant `Res_E(P⁺, partial_y P⁺)` vanishes.  The
last theorem constructs the existing algebraic-regularity certificate from
this canonical polynomial; its only algebraic premise is the honestly named
nonvanishing statement for this very resultant.
-/

namespace ArchonPhysics.PhyslibFPUTIteratedA2SingleFrequencyCanonicalJacobian

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSimpleEigenvalueDifferentiability
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.CanonicalPairCharacteristicJacobianResultant
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.FixedEnergySpectrumAvoidance
open ArchonPhysics.FiniteExactDecayResonanceObstruction
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.MassWeightedCycleBridge
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberSpectrumNonvanishing
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassResultantBridge
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.TwoParameterSpectralPolynomialAvoidance
open Filter Set

noncomputable section

/-- The canonical sliced positive-spectrum polynomial vanishes at every
strictly positive actual ordered energy on the physical two-mass support. -/
theorem twoSitePositiveCharacteristicPolynomial_orderedEnergy_root
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    {pair : Real × Real} (hpair : pair ∈ iidMassPairSupport)
    (mode : Fin (Fintype.card (Lattice.Site N)))
    (hpositive : 0 < orderedEigenvalue
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair) mode) :
    (Polynomial.map (MvPolynomial.eval (iidInverseMassPairCoordinates pair))
      (twoSitePositiveCharacteristicPolynomial fixed site₁ site₂)).eval
        (orderedEigenvalue
          (twoSiteHarmonicHermitian fixed site₁ site₂ pair) mode) = 0 := by
  let m := twoSiteMassConfig fixed site₁ site₂ pair
  rw [evaluate_twoSitePositiveCharacteristicPolynomial]
  rw [← inverseMassCoordinates_twoSiteMassConfig_of_mem_support
    fixed hsite hpair]
  apply weightedCycle_divX_eval_orderedEigenvalue_eq_zero m mode
  have hpositivePhysical :
      0 < orderedEigenvalue (harmonicHermitian m) mode := by
    simpa [m, twoSiteHarmonicHermitian] using hpositive
  simpa [orderedModeFrequency] using Real.sqrt_pos.2 hpositivePhysical

/-- If a pair-fiber mismatch is one nonzero signed positive ordered
frequency, a zero vertical Jacobian forces `partial_y P-positive` to vanish at the
same ordered energy. -/
theorem verticalJacobian_zero_forces_positiveCharacteristicVerticalMassPartial_zero
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (mode : Fin (Fintype.card (Lattice.Site N)))
    (sign : Real) (hsign : sign ≠ 0)
    (hmismatch :
      physlibIteratedA2PairMismatchChart fixed site₁ site₂
          channel observed term =
        fun nearby ↦ sign * orderedModeFrequency
          (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) mode)
    {pair : Real × Real} (hpair : pair ∈ interior iidMassPairSupport)
    (hsimple : SimpleOrderedSpectrum
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair))
    (hpositive : 0 < orderedEigenvalue
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair) mode)
    (hjacobian : physlibIteratedA2PairMismatchVerticalJacobian fixed
      site₁ site₂ channel observed term pair = 0) :
    (Polynomial.map (MvPolynomial.eval (iidInverseMassPairCoordinates pair))
      (twoSitePositiveCharacteristicVerticalMassPartial fixed site₁ site₂)).eval
        (orderedEigenvalue
          (twoSiteHarmonicHermitian fixed site₁ site₂ pair) mode) = 0 := by
  let frequency : Real × Real → Real := fun nearby ↦
    orderedModeFrequency
      (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) mode
  let energy : Real × Real → Real := fun nearby ↦
    orderedEigenvalue
      (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) mode
  obtain ⟨Dfrequency, hfrequency⟩ :=
    exists_hasStrictFDerivAt_actualTwoMassOrderedModeFrequency
      fixed hsite hpair hsimple mode hpositive
  have hfrequency' : HasStrictFDerivAt frequency Dfrequency pair := by
    simpa [frequency] using hfrequency
  have hsigned : HasFDerivAt (fun nearby ↦ sign * frequency nearby)
      (sign • Dfrequency) pair :=
    hfrequency'.hasFDerivAt.const_mul sign
  have hjacobian' :
      fderiv Real (fun nearby ↦ sign * frequency nearby) pair (0, 1) = 0 := by
    unfold physlibIteratedA2PairMismatchVerticalJacobian at hjacobian
    rw [hmismatch] at hjacobian
    simpa [frequency] using hjacobian
  have hDfrequencyVertical : Dfrequency (0, 1) = 0 := by
    rw [hsigned.fderiv] at hjacobian'
    have hproduct : sign * Dfrequency (0, 1) = 0 := by
      simpa using hjacobian'
    exact (mul_eq_zero.mp hproduct).resolve_left hsign
  have hinclusion : HasFDerivAt (fun second : Real ↦ (pair.1, second))
      (ContinuousLinearMap.inr Real Real Real) pair.2 :=
    hasFDerivAt_prodMk_right pair.1 pair.2
  have hfrequencyLine : HasDerivAt
      (fun second ↦ frequency (pair.1, second)) 0 pair.2 := by
    have hcomp := hfrequency'.hasFDerivAt.comp pair.2 hinclusion
    simpa [Function.comp_def, ContinuousLinearMap.comp_apply,
      hDfrequencyVertical] using hcomp.hasDerivAt
  have henergyLine : HasDerivAt
      (fun second ↦ energy (pair.1, second)) 0 pair.2 := by
    have hsquare := hfrequencyLine.pow 2
    have heventually :
        (fun second ↦ energy (pair.1, second)) =ᶠ[nhds pair.2]
          (fun second ↦ frequency (pair.1, second)) ^ 2 :=
      Filter.Eventually.of_forall fun second ↦
        (orderedModeFrequency_sq_eq_orderedEigenvalue
          (twoSiteMassConfig fixed site₁ site₂ (pair.1, second))
          mode).symm
    simpa [energy, frequency] using
      hsquare.congr_of_eventuallyEq heventually
  have hsecondNe : pair.2 ≠ 0 := ne_of_gt
    (massLower_pos.trans_le (interior_subset hpair).2.1)
  let inverseDerivative : Real := -(pair.2 ^ 2)⁻¹
  have hinverse : HasDerivAt (fun second : Real ↦ second⁻¹)
      inverseDerivative pair.2 := by
    simpa [inverseDerivative] using hasDerivAt_inv hsecondNe
  let p := twoSitePositiveCharacteristicPolynomial fixed site₁ site₂
  let lifted := energyMassPolynomial p
  let curve : Real → Option (Fin 2) → Real := fun second o ↦
    o.elim (energy (pair.1, second))
      (iidInverseMassPairCoordinates (pair.1, second))
  have hcurve : ∀ o, HasDerivAt (fun second ↦ curve second o)
      (if o = some (1 : Fin 2) then inverseDerivative else 0) pair.2 := by
    intro o
    cases o with
    | none =>
        simpa [curve] using henergyLine
    | some i =>
        fin_cases i
        · simpa [curve] using
            (hasDerivAt_const pair.2 pair.1⁻¹)
        · simpa [curve] using hinverse
  have hresidualDerivative : HasDerivAt
      (fun second ↦ MvPolynomial.eval (curve second) lifted)
      (inverseDerivative * MvPolynomial.eval (curve pair.2)
        (MvPolynomial.pderiv (some (1 : Fin 2)) lifted)) pair.2 :=
    hasDerivAt_mvPolynomial_eval_of_single_coordinate
      lifted (some (1 : Fin 2)) curve pair.2 inverseDerivative hcurve
  have hresidualEventuallyZero :
      (fun second ↦ MvPolynomial.eval (curve second) lifted) =ᶠ[nhds pair.2]
        fun _ ↦ 0 := by
    have hinteriorEventually : ∀ᶠ second in nhds pair.2,
        (pair.1, second) ∈ interior iidMassPairSupport := by
      exact hinclusion.continuousAt.eventually
        (isOpen_interior.mem_nhds hpair)
    have hpositiveEventually : ∀ᶠ second in nhds pair.2,
        0 < energy (pair.1, second) :=
      henergyLine.continuousAt.eventually (Ioi_mem_nhds hpositive)
    filter_upwards [hinteriorEventually, hpositiveEventually] with
      second hinterior hpositiveSecond
    have hroot := twoSitePositiveCharacteristicPolynomial_orderedEnergy_root
      fixed hsite (interior_subset hinterior) mode (by
        simpa [energy] using hpositiveSecond)
    calc
      MvPolynomial.eval (curve second) lifted =
          (Polynomial.map
            (MvPolynomial.eval
              (iidInverseMassPairCoordinates (pair.1, second))) p).eval
            (energy (pair.1, second)) := by
              simpa [curve, lifted, energyMassPolynomial] using
                MvPolynomial.optionEquivLeft_elim_eval
                  Real (Fin 2)
                  (iidInverseMassPairCoordinates (pair.1, second))
                  (energy (pair.1, second)) lifted
      _ = 0 := by simpa [p, energy] using hroot
  have hzeroDerivative : HasDerivAt (fun _ : Real ↦ (0 : Real)) 0 pair.2 :=
    hasDerivAt_const pair.2 0
  have hderivativeEquation :
      inverseDerivative * MvPolynomial.eval (curve pair.2)
        (MvPolynomial.pderiv (some (1 : Fin 2)) lifted) = 0 :=
    (hresidualDerivative.congr_of_eventuallyEq
      hresidualEventuallyZero.symm).unique hzeroDerivative
  have hinverseDerivativeNe : inverseDerivative ≠ 0 := by
    simp [inverseDerivative, hsecondNe]
  have hpartial : MvPolynomial.eval (curve pair.2)
      (MvPolynomial.pderiv (some (1 : Fin 2)) lifted) = 0 :=
    (mul_eq_zero.mp hderivativeEquation).resolve_left hinverseDerivativeNe
  rw [twoSitePositiveCharacteristicVerticalMassPartial, eval_verticalMassPartial]
  simpa [curve, lifted, p, energy] using hpartial

/-- Main general-`N` single-frequency elimination theorem.  The Jacobian-zero
locus is contained in the zero set of the canonical characteristic
resultant, with no supplied channel polynomial. -/
theorem verticalJacobian_zero_forces_positiveCharacteristicJacobianResultant_zero
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (mode : Fin (Fintype.card (Lattice.Site N)))
    (sign : Real) (hsign : sign ≠ 0)
    (hmismatch :
      physlibIteratedA2PairMismatchChart fixed site₁ site₂
          channel observed term =
        fun nearby ↦ sign * orderedModeFrequency
          (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) mode)
    {pair : Real × Real} (hpair : pair ∈ interior iidMassPairSupport)
    (hsimple : SimpleOrderedSpectrum
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair))
    (hpositive : 0 < orderedEigenvalue
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair) mode)
    (hjacobian : physlibIteratedA2PairMismatchVerticalJacobian fixed
      site₁ site₂ channel observed term pair = 0) :
    MvPolynomial.eval (iidInverseMassPairCoordinates pair)
      (twoSitePositiveCharacteristicJacobianResultant fixed site₁ site₂) = 0 := by
  apply
    twoSitePositiveCharacteristicJacobianResultant_eval_eq_zero_of_common_energy
      fixed site₁ site₂ (iidInverseMassPairCoordinates pair)
        (orderedEigenvalue
          (twoSiteHarmonicHermitian fixed site₁ site₂ pair) mode)
  · exact twoSitePositiveCharacteristicPolynomial_orderedEnergy_root
      fixed hsite (interior_subset hpair) mode hpositive
  · exact
      verticalJacobian_zero_forces_positiveCharacteristicVerticalMassPartial_zero
        fixed hsite channel observed term mode sign hsign hmismatch hpair
          hsimple hpositive hjacobian

/-- A non-acoustic ordered mode has positive energy at every simple-spectrum
pair. -/
theorem orderedEnergy_pos_of_simple_of_ne_last
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (mode : Fin (Fintype.card (Lattice.Site N)))
    (hmode : mode ≠ lastOrderedIndex)
    {pair : Real × Real}
    (hsimple : SimpleOrderedSpectrum
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair)) :
    0 < orderedEigenvalue
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair) mode := by
  let m := twoSiteMassConfig fixed site₁ site₂ pair
  have hfrequency : 0 < orderedModeFrequency (harmonicHermitian m) mode :=
    (orderedModeFrequency_pos_iff_ne_last m (by
      simpa [m, twoSiteHarmonicHermitian] using hsimple) mode).2 hmode
  exact Real.sqrt_pos.mp hfrequency

/-- Sharp certificate reduction for an ordinary single-frequency channel.
The spectrum resultant is already discharged by the positive-path theorem.
The only remaining algebraic proposition is precisely
`twoSitePositiveCharacteristicJacobianResultant ... ≠ 0`; it is not renamed as an
abstract polynomial premise. -/
def algebraicRegularityCertificateOfSingleFrequencyCanonicalResultant
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (mode : Fin (Fintype.card (Lattice.Site N)))
    (hmode : mode ≠ lastOrderedIndex)
    (sign : Real) (hsign : sign ≠ 0)
    (hmismatch :
      physlibIteratedA2PairMismatchChart fixed site₁ site₂
          channel observed term =
        fun nearby ↦ sign * orderedModeFrequency
          (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) mode)
    (hresultant :
      twoSitePositiveCharacteristicJacobianResultant fixed site₁ site₂ ≠ 0) :
    IteratedA2PairAlgebraicRegularityCertificate
      fixed site₁ site₂ channel observed term :=
  algebraicRegularityCertificateOfJacobian fixed channel observed term hsite
    (twoSitePositiveCharacteristicJacobianResultant fixed site₁ site₂)
    hresultant (fun _pair hpair hsimple hjacobian ↦
      verticalJacobian_zero_forces_positiveCharacteristicJacobianResultant_zero
        fixed hsite channel observed term mode sign hsign hmismatch hpair
          hsimple
          (orderedEnergy_pos_of_simple_of_ne_last
            fixed site₁ site₂ mode hmode hsimple)
          hjacobian)

end

end ArchonPhysics.PhyslibFPUTIteratedA2SingleFrequencyCanonicalJacobian
