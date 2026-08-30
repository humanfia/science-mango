import ArchonPhysics.OrderedTranslationLastMode
import ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
import ArchonPhysics.RandomMassResultantBridge
import ArchonPhysics.TwoParameterSpectralPolynomialAvoidance

/-!
# Algebraic audit of the actual iterated-A2 pair-fiber bad set

At fixed finite volume, the local transversality atlas leaves four possible
sources of bad mass pairs: the boundary of the iid square, nonsimple harmonic
spectrum, a participating acoustic mode, and a zero vertical mismatch
Jacobian.  This file separates them without hiding any of them in a generic
regularity premise.

* The boundary is contained in the zero set of an explicit nonzero four-factor
  polynomial in the two raw masses.
* Nonsimple spectrum is contained in the zero set of the explicit restriction
  of the finite weighted-cycle characteristic resultant to the two varied
  inverse masses.  Only nonvanishing of this concrete finite polynomial is
  left as a checkable specialization certificate.
* A participating acoustic mode is a structural obstruction, not a null bad
  set.  If the finite participating-mode set avoids the deterministic last
  ordered mode, positivity follows from simple spectrum; if it contains that
  mode, the differentiability source is empty on every such fiber point.
* The remaining zero-Jacobian locus is reduced to one supplied nonzero
  two-variable inverse-mass polynomial together with a pointwise elimination
  implication.  Thus the complete regularity target is reduced to two finite,
  computable polynomial obligations: nonvanishing of the resultant slice and
  the channel-specific Jacobian eliminant.

The charge-matched total channel is deliberately not covered: its mismatch
and vertical Jacobian are identically zero by the exact obstruction theorem
in the imported atlas.
-/

namespace ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.RandomMassResultantBridge
open ArchonPhysics.RandomMassSimpleSpectrum
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.TwoParameterSpectralPolynomialAvoidance
open Filter MeasureTheory Set

noncomputable section

/-! ## The support boundary is one explicit algebraic null set -/

/-- A raw-mass polynomial whose zero set contains all four boundary faces of
the compact iid mass square. -/
def iidMassPairBoundaryPolynomial : MvPolynomial (Fin 2) Real :=
  (MvPolynomial.X 0 - MvPolynomial.C massLower) *
    (MvPolynomial.X 0 - MvPolynomial.C massUpper) *
    (MvPolynomial.X 1 - MvPolynomial.C massLower) *
    (MvPolynomial.X 1 - MvPolynomial.C massUpper)

@[simp] theorem iidMassPairBoundaryPolynomial_eval (pair : Real × Real) :
    MvPolynomial.eval (iidMassPairCoordinates pair)
        iidMassPairBoundaryPolynomial =
      (pair.1 - massLower) * (pair.1 - massUpper) *
        (pair.2 - massLower) * (pair.2 - massUpper) := by
  simp [iidMassPairBoundaryPolynomial]

theorem iidMassPairBoundaryPolynomial_ne_zero :
    iidMassPairBoundaryPolynomial ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval (![1, (11 / 10 : Real)] : Fin 2 → Real)) hzero
  norm_num [iidMassPairBoundaryPolynomial, massLower, massUpper] at heval

/-- Inside the closed support square, failure to be interior forces the
explicit boundary polynomial to vanish. -/
theorem iidMassPairBoundaryPolynomial_vanishes
    {pair : Real × Real} (hpair : pair ∈ iidMassPairSupport)
    (hnotInterior : pair ∉ interior iidMassPairSupport) :
    MvPolynomial.eval (iidMassPairCoordinates pair)
        iidMassPairBoundaryPolynomial = 0 := by
  rw [iidMassPairBoundaryPolynomial_eval]
  rw [iidMassPairSupport, massSupport] at hpair
  by_cases hfirstLower : pair.1 = massLower
  · simp [hfirstLower]
  by_cases hfirstUpper : pair.1 = massUpper
  · simp [hfirstUpper]
  by_cases hsecondLower : pair.2 = massLower
  · simp [hsecondLower]
  by_cases hsecondUpper : pair.2 = massUpper
  · simp [hsecondUpper]
  exfalso
  apply hnotInterior
  rw [iidMassPairSupport, interior_prod_eq, massSupport, interior_Icc]
  exact
    ⟨⟨lt_of_le_of_ne hpair.1.1 (Ne.symm hfirstLower),
        lt_of_le_of_ne hpair.1.2 hfirstUpper⟩,
      ⟨lt_of_le_of_ne hpair.2.1 (Ne.symm hsecondLower),
        lt_of_le_of_ne hpair.2.2 hsecondUpper⟩⟩

/-- The iid pair belongs to the open support square almost everywhere.  The
proof records the explicit polynomial certificate rather than merely deleting
the two endpoint atoms coordinatewise. -/
theorem iidMassPair_mem_interior_ae :
    ∀ᵐ pair ∂iidMassPairLaw, pair ∈ interior iidMassPairSupport := by
  have hsupport : ∀ᵐ pair ∂iidMassPairLaw,
      pair ∈ iidMassPairSupport := by
    rw [iidMassPairLaw, Measure.ae_prod_mem_iff_ae_ae_mem]
    · filter_upwards [massCoordinate_mem_support_ae] with first hfirst
      filter_upwards [massCoordinate_mem_support_ae] with second hsecond
      exact ⟨hfirst, hsecond⟩
    · exact (measurableSet_Icc.prod measurableSet_Icc)
  have hpolynomial : ∀ᵐ pair ∂iidMassPairLaw,
      MvPolynomial.eval (iidMassPairCoordinates pair)
        iidMassPairBoundaryPolynomial ≠ 0 := by
    have hzero := iidMassPairLaw_zeroSet_mvPolynomial_eval
      iidMassPairBoundaryPolynomial iidMassPairBoundaryPolynomial_ne_zero
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero]
      with pair hpair
    simpa only [mem_ofPred_eq] using hpair
  filter_upwards [hsupport, hpolynomial] with pair hpair hpolynomial
  by_contra hnotInterior
  exact hpolynomial
    (iidMassPairBoundaryPolynomial_vanishes hpair hnotInterior)

/-! ## The full spectral discriminant restricted to the pair fiber -/

/-- The inverse-mass vector obtained by varying precisely two sites in a
fixed background. -/
def twoSiteInverseMassSliceCoordinates
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (pair : Real × Real) : Fin N → Real :=
  fun k =>
    let site := (siteEquivFin N).symm k
    if site = site₁ then pair.1⁻¹
    else if site = site₂ then pair.2⁻¹
    else (fixed.mass site)⁻¹

/-- Polynomial substitution that leaves the two selected inverse masses free
and freezes every other inverse mass at its actual background value. -/
def twoSiteRepeatedRootSliceSubstitution
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) :
    Fin N → MvPolynomial (Fin 2) Real :=
  fun k =>
    let site := (siteEquivFin N).symm k
    if site = site₁ then MvPolynomial.X 0
    else if site = site₂ then MvPolynomial.X 1
    else MvPolynomial.C ((fixed.mass site)⁻¹)

/-- The concrete fixed-volume repeated-root resultant restricted to the two
varied inverse masses.  It is a finite multivariate polynomial computable from
`N`, the two sites, and the frozen background. -/
def twoSiteRepeatedRootSlicePolynomial
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) : MvPolynomial (Fin 2) Real :=
  MvPolynomial.eval₂
    (MvPolynomial.C : Real →+* MvPolynomial (Fin 2) Real)
    (twoSiteRepeatedRootSliceSubstitution fixed site₁ site₂)
    (symbolicRepeatedRootCertificate (N := N))

/-- Evaluation of the restricted polynomial agrees exactly with evaluation
of the full finite-volume resultant on the embedded inverse-mass slice. -/
theorem evaluate_twoSiteRepeatedRootSlicePolynomial
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (pair : Real × Real) :
    MvPolynomial.eval (iidInverseMassPairCoordinates pair)
        (twoSiteRepeatedRootSlicePolynomial fixed site₁ site₂) =
      MvPolynomial.eval
        (twoSiteInverseMassSliceCoordinates fixed site₁ site₂ pair)
        (symbolicRepeatedRootCertificate (N := N)) := by
  unfold twoSiteRepeatedRootSlicePolynomial
  rw [MvPolynomial.eval_eval₂]
  have hcoeff :
      (MvPolynomial.eval (iidInverseMassPairCoordinates pair)).comp
          (MvPolynomial.C : Real →+* MvPolynomial (Fin 2) Real) =
        RingHom.id Real := by
    ext a
    simp
  rw [hcoeff, MvPolynomial.eval₂_id]
  apply congrArg
    (fun coordinates => MvPolynomial.eval coordinates
      (symbolicRepeatedRootCertificate (N := N)))
  funext k
  simp only [twoSiteRepeatedRootSliceSubstitution,
    twoSiteInverseMassSliceCoordinates]
  split_ifs <;> simp

/-- On the physical support, the actual two-site mass configuration has
exactly the displayed inverse-mass slice coordinates. -/
theorem inverseMassCoordinates_twoSiteMassConfig_of_mem_support
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    {pair : Real × Real} (hpair : pair ∈ iidMassPairSupport) :
    inverseMassCoordinates (twoSiteMassConfig fixed site₁ site₂ pair) =
      twoSiteInverseMassSliceCoordinates fixed site₁ site₂ pair := by
  funext k
  let site := (siteEquivFin N).symm k
  by_cases hfirst : site = site₁
  · simp [inverseMassCoordinates, twoSiteInverseMassSliceCoordinates,
      twoSiteMassConfig, site, hfirst, clippedMass_eq_self hpair.1]
  by_cases hsecond : site = site₂
  · simp [inverseMassCoordinates, twoSiteInverseMassSliceCoordinates,
      twoSiteMassConfig, site, hsecond, hsite.symm,
      clippedMass_eq_self hpair.2]
  · simp [inverseMassCoordinates, twoSiteInverseMassSliceCoordinates,
      twoSiteMassConfig, site, hfirst, hsecond]

/-- Failure of actual ordered simplicity on the supported pair fiber forces
the explicit restricted characteristic resultant to vanish. -/
theorem twoSiteRepeatedRootSlicePolynomial_vanishes_of_not_simple
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    {pair : Real × Real} (hpair : pair ∈ iidMassPairSupport)
    (hnonsimple : ¬ SimpleOrderedSpectrum
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair)) :
    MvPolynomial.eval (iidInverseMassPairCoordinates pair)
      (twoSiteRepeatedRootSlicePolynomial fixed site₁ site₂) = 0 := by
  rw [evaluate_twoSiteRepeatedRootSlicePolynomial]
  rw [← inverseMassCoordinates_twoSiteMassConfig_of_mem_support
    fixed hsite hpair]
  apply certificate_vanishes_of_repeatedPositiveHarmonic
  apply repeatedPositiveHarmonic_of_orderedPositiveDuplicate
  by_contra hnotDuplicate
  apply hnonsimple
  simpa [twoSiteHarmonicHermitian, harmonicHermitian] using
    simpleOrderedSpectrum_of_not_orderedPositiveDuplicate
      (twoSiteMassConfig fixed site₁ site₂ pair) hnotDuplicate

/-- Once its directly computable two-variable resultant restriction is proved
nonzero, nonsimple spectrum has zero iid pair mass on this exact fiber. -/
theorem iidMassPairLaw_twoSite_not_simple_eq_zero
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (hspectrum :
      twoSiteRepeatedRootSlicePolynomial fixed site₁ site₂ ≠ 0) :
    iidMassPairLaw
      {pair |
        pair ∈ iidMassPairSupport ∧
        ¬ SimpleOrderedSpectrum
          (twoSiteHarmonicHermitian fixed site₁ site₂ pair)} = 0 := by
  apply measure_mono_null (t :=
    {pair |
      MvPolynomial.eval (iidInverseMassPairCoordinates pair)
        (twoSiteRepeatedRootSlicePolynomial fixed site₁ site₂) = 0})
  · intro pair hpair
    exact twoSiteRepeatedRootSlicePolynomial_vanishes_of_not_simple
      fixed hsite hpair.1 hpair.2
  · exact iidMassPairLaw_zeroSet_eval_inverseCoordinates
      (twoSiteRepeatedRootSlicePolynomial fixed site₁ site₂) hspectrum

/-! ## The acoustic-mode obstruction is structural -/

/-- The selected A2 channel avoids the deterministic translation/acoustic
mode in its finite participating-mode set. -/
def IteratedA2ChannelAvoidsAcoustic
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Prop :=
  ∀ mode ∈ iteratedA2ChannelParticipatingModes channel observed term,
    orderedIndexEquiv.symm mode ≠
      lastOrderedIndex (ι := Lattice.Site N)

/-- If the finite channel support avoids the last ordered mode, simple
spectrum supplies every positivity hypothesis needed by the A2 atlas. -/
theorem participatingMode_energy_pos_of_simple_of_avoidsAcoustic
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (havoid : IteratedA2ChannelAvoidsAcoustic channel observed term)
    {pair : Real × Real}
    (hsimple : SimpleOrderedSpectrum
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair)) :
    ∀ mode ∈ iteratedA2ChannelParticipatingModes channel observed term,
      0 < orderedEigenvalue
        (twoSiteHarmonicHermitian fixed site₁ site₂ pair)
        (orderedIndexEquiv.symm mode) := by
  intro mode hmode
  let m := twoSiteMassConfig fixed site₁ site₂ pair
  have hsimple' : SimpleOrderedSpectrum (harmonicHermitian m) := by
    simpa [m, twoSiteHarmonicHermitian] using hsimple
  have hfrequency : 0 < orderedModeFrequency (harmonicHermitian m)
      (orderedIndexEquiv.symm mode) :=
    (orderedModeFrequency_pos_iff_ne_last m hsimple'
      (orderedIndexEquiv.symm mode)).2 (havoid mode hmode)
  change 0 < orderedEigenvalue (harmonicHermitian m)
    (orderedIndexEquiv.symm mode)
  exact Real.sqrt_pos.mp hfrequency

/-- Conversely, if the acoustic mode participates, its positivity requirement
fails identically; this is not an exceptional set that polynomial avoidance
could delete. -/
theorem not_mem_differentiabilitySource_of_acoustic_participates
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hacoustic :
      orderedIndexEquiv (lastOrderedIndex (ι := Lattice.Site N)) ∈
        iteratedA2ChannelParticipatingModes channel observed term)
    (pair : Real × Real) :
    pair ∉ physlibIteratedA2PairMismatchDifferentiabilitySource
      fixed site₁ site₂ channel observed term := by
  intro hsource
  have hpositive := hsource.2.2
    (orderedIndexEquiv (lastOrderedIndex (ι := Lattice.Site N))) hacoustic
  simp only [Equiv.symm_apply_apply] at hpositive
  change 0 < orderedEigenvalue
    (harmonicHermitian (twoSiteMassConfig fixed site₁ site₂ pair))
      (lastOrderedIndex (ι := Lattice.Site N)) at hpositive
  rw [harmonic_lastOrderedEigenvalue_eq_zero] at hpositive
  exact lt_irrefl 0 hpositive

/-! ## A finite algebraic certificate for the complete regular bad set -/

/-- The remaining finite algebraic data for one fixed actual A2 channel.
The spectrum polynomial is canonical and computable above.  The supplied
Jacobian polynomial is a channel-specific eliminant: its pointwise implication
is the exact finite symbolic calculation still required from the mismatch
formula. -/
structure IteratedA2PairAlgebraicRegularityCertificate
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) where
  site_ne : site₁ ≠ site₂
  spectrumPolynomial_ne_zero :
    twoSiteRepeatedRootSlicePolynomial fixed site₁ site₂ ≠ 0
  jacobianPolynomial : MvPolynomial (Fin 2) Real
  jacobianPolynomial_ne_zero : jacobianPolynomial ≠ 0
  jacobian_zero_forces_polynomial_zero :
    ∀ pair ∈ interior iidMassPairSupport,
      SimpleOrderedSpectrum
          (twoSiteHarmonicHermitian fixed site₁ site₂ pair) →
      physlibIteratedA2PairMismatchVerticalJacobian
          fixed site₁ site₂ channel observed term pair = 0 →
      MvPolynomial.eval (iidInverseMassPairCoordinates pair)
          jacobianPolynomial = 0

/-- The exact actual regular/noncritical set certified by the finite
polynomial data. -/
def IteratedA2PairAlgebraicRegularityCertificate.regularSet
    {N : Nat} [NeZero N] {fixed : Lattice.PositiveMassConfig N}
    {site₁ site₂ : Lattice.Site N} {channel : IteratedA2MismatchChannel}
    {observed : Lattice.Site N}
    {term : IteratedQuadraticSecondPicardCharacterTerm N}
    (_certificate : IteratedA2PairAlgebraicRegularityCertificate
      fixed site₁ site₂ channel observed term) : Set (Real × Real) :=
  {pair |
    pair ∈ physlibIteratedA2PairMismatchDifferentiabilitySource
      fixed site₁ site₂ channel observed term ∧
    physlibIteratedA2PairMismatchVerticalJacobian
      fixed site₁ site₂ channel observed term pair ≠ 0}

/-- Pointwise reduction: on the physical support, every failure of actual
regular/noncritical transversality lies in one of exactly three displayed
polynomial zero sets (boundary, spectrum resultant slice, Jacobian eliminant).
-/
theorem IteratedA2PairAlgebraicRegularityCertificate.badSet_subset_three_zeroSets
    {N : Nat} [NeZero N] {fixed : Lattice.PositiveMassConfig N}
    {site₁ site₂ : Lattice.Site N} {channel : IteratedA2MismatchChannel}
    {observed : Lattice.Site N}
    {term : IteratedQuadraticSecondPicardCharacterTerm N}
    (certificate : IteratedA2PairAlgebraicRegularityCertificate
      fixed site₁ site₂ channel observed term)
    (havoid : IteratedA2ChannelAvoidsAcoustic channel observed term) :
    certificate.regularSetᶜ ∩ iidMassPairSupport ⊆
      {pair |
        MvPolynomial.eval (iidMassPairCoordinates pair)
          iidMassPairBoundaryPolynomial = 0} ∪
      {pair |
        MvPolynomial.eval (iidInverseMassPairCoordinates pair)
          (twoSiteRepeatedRootSlicePolynomial fixed site₁ site₂) = 0} ∪
      {pair |
        MvPolynomial.eval (iidInverseMassPairCoordinates pair)
          certificate.jacobianPolynomial = 0} := by
  intro pair hbad
  by_cases hinterior : pair ∈ interior iidMassPairSupport
  · by_cases hsimple : SimpleOrderedSpectrum
        (twoSiteHarmonicHermitian fixed site₁ site₂ pair)
    · have hpositive :=
        participatingMode_energy_pos_of_simple_of_avoidsAcoustic
          fixed site₁ site₂ channel observed term havoid hsimple
      have hsource : pair ∈
          physlibIteratedA2PairMismatchDifferentiabilitySource
            fixed site₁ site₂ channel observed term :=
        ⟨hinterior, hsimple, hpositive⟩
      have hjac : physlibIteratedA2PairMismatchVerticalJacobian
          fixed site₁ site₂ channel observed term pair = 0 := by
        by_contra hjac
        exact hbad.1 ⟨hsource, hjac⟩
      exact Or.inr (certificate.jacobian_zero_forces_polynomial_zero
        pair hinterior hsimple hjac)
    · exact Or.inl (Or.inr
        (twoSiteRepeatedRootSlicePolynomial_vanishes_of_not_simple
          fixed certificate.site_ne hbad.2 hsimple))
  · exact Or.inl (Or.inl
      (iidMassPairBoundaryPolynomial_vanishes hbad.2 hinterior))

/-- The union of the three explicit certified bad loci has zero iid pair
mass. -/
theorem IteratedA2PairAlgebraicRegularityCertificate.three_zeroSets_null
    {N : Nat} [NeZero N] {fixed : Lattice.PositiveMassConfig N}
    {site₁ site₂ : Lattice.Site N} {channel : IteratedA2MismatchChannel}
    {observed : Lattice.Site N}
    {term : IteratedQuadraticSecondPicardCharacterTerm N}
    (certificate : IteratedA2PairAlgebraicRegularityCertificate
      fixed site₁ site₂ channel observed term) :
    iidMassPairLaw
      ({pair |
        MvPolynomial.eval (iidMassPairCoordinates pair)
          iidMassPairBoundaryPolynomial = 0} ∪
       {pair |
        MvPolynomial.eval (iidInverseMassPairCoordinates pair)
          (twoSiteRepeatedRootSlicePolynomial fixed site₁ site₂) = 0} ∪
       {pair |
        MvPolynomial.eval (iidInverseMassPairCoordinates pair)
          certificate.jacobianPolynomial = 0}) = 0 := by
  apply measure_union_null
  · apply measure_union_null
    · exact iidMassPairLaw_zeroSet_mvPolynomial_eval
        iidMassPairBoundaryPolynomial iidMassPairBoundaryPolynomial_ne_zero
    · exact iidMassPairLaw_zeroSet_eval_inverseCoordinates
        (twoSiteRepeatedRootSlicePolynomial fixed site₁ site₂)
        certificate.spectrumPolynomial_ne_zero
  · exact iidMassPairLaw_zeroSet_eval_inverseCoordinates
      certificate.jacobianPolynomial
      certificate.jacobianPolynomial_ne_zero

/-- Final fixed-volume conclusion: a channel avoiding the structural
acoustic obstruction is regular and noncritical at almost every iid mass
pair, once the two finite algebraic certificate obligations are supplied. -/
theorem IteratedA2PairAlgebraicRegularityCertificate.regularSet_ae
    {N : Nat} [NeZero N] {fixed : Lattice.PositiveMassConfig N}
    {site₁ site₂ : Lattice.Site N} {channel : IteratedA2MismatchChannel}
    {observed : Lattice.Site N}
    {term : IteratedQuadraticSecondPicardCharacterTerm N}
    (certificate : IteratedA2PairAlgebraicRegularityCertificate
      fixed site₁ site₂ channel observed term)
    (havoid : IteratedA2ChannelAvoidsAcoustic channel observed term) :
    ∀ᵐ pair ∂iidMassPairLaw, pair ∈ certificate.regularSet := by
  have hsupport : ∀ᵐ pair ∂iidMassPairLaw,
      pair ∈ iidMassPairSupport := by
    filter_upwards [iidMassPair_mem_interior_ae] with pair hpair
    exact interior_subset hpair
  have hzero := certificate.three_zeroSets_null
  have hnotZero := measure_eq_zero_iff_ae_notMem.mp hzero
  filter_upwards [hsupport, hnotZero] with pair hsupport hnotZero
  by_contra hnotRegular
  apply hnotZero
  exact certificate.badSet_subset_three_zeroSets havoid
    ⟨hnotRegular, hsupport⟩

/-- Equivalent zero-measure formulation of the complete certified bad set. -/
theorem IteratedA2PairAlgebraicRegularityCertificate.badSet_eq_zero
    {N : Nat} [NeZero N] {fixed : Lattice.PositiveMassConfig N}
    {site₁ site₂ : Lattice.Site N} {channel : IteratedA2MismatchChannel}
    {observed : Lattice.Site N}
    {term : IteratedQuadraticSecondPicardCharacterTerm N}
    (certificate : IteratedA2PairAlgebraicRegularityCertificate
      fixed site₁ site₂ channel observed term)
    (havoid : IteratedA2ChannelAvoidsAcoustic channel observed term) :
    iidMassPairLaw certificate.regularSetᶜ = 0 := by
  exact mem_ae_iff.mp (certificate.regularSet_ae havoid)

end

end ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
