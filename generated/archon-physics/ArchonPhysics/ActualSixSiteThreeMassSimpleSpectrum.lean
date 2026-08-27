import ArchonPhysics.ActualSixSiteCleanDecayResonancePatch
import ArchonPhysics.ActualThreeMassWeightedProjectorMinorScaleBound
import ArchonPhysics.OrderedTranslationLastMode
import ArchonPhysics.PathLaplacianResultant
import ArchonPhysics.RandomMassOrderedProjectorBridge

/-!
# Simple spectrum inside the six-site near-resonance patch

Only three masses vary in the six-site family, so the full-iid simple-spectrum
theorem does not apply directly.  We instead specialize the six-variable
repeated-root resultant by leaving inverse-mass coordinates zero, one, and two
free and setting the other three coordinates to one.

At the algebraic point `(0, 1, 1)` this specialization is exactly the
broken-cycle path witness.  Hence the restricted resultant is nonzero.  The
three-dimensional inverse-mass polynomial-avoidance theorem then makes the
positive-spectrum duplicate event null under the genuine iid mass-triple law.
The deterministic one-dimensional translation kernel upgrades this to full
ordered-spectrum simplicity almost surely.

Removing that null exceptional set from the positive-mass six-site
near-resonance patch preserves its strictly positive probability.  This module
does not claim that the lifted Jacobian is nonzero on that patch.
-/

open scoped BigOperators Matrix

namespace ArchonPhysics.ActualSixSiteThreeMassSimpleSpectrum

open ArchonPhysics
open ArchonPhysics.ActualSixSiteCleanDecayResonancePatch
open ArchonPhysics.ActualThreeMassLiftedJacobianPolynomial
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassWeightedProjectorMinorScaleBound
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PathLaplacianResultant
open ArchonPhysics.PathLaplacianSpecialization
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.RandomMassResultantBridge
open ArchonPhysics.RandomMassSimpleSpectrum
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison
open MeasureTheory Set

noncomputable section

/-- Embed the three free inverse masses into the six-site unit-background
slice. -/
def sixSiteSliceInverseWeights (x : Fin 3 → Real) : Fin 6 → Real :=
  ![x 0, x 1, x 2, 1, 1, 1]

/-- Polynomial substitution leaving the first three inverse-mass variables
free and freezing the remaining three at one. -/
def sixSiteRepeatedRootSliceSubstitution :
    Fin 6 → MvPolynomial (Fin 3) Real :=
  ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2,
    MvPolynomial.C 1, MvPolynomial.C 1, MvPolynomial.C 1]

/-- The six-site repeated-root resultant restricted to the actual three-mass
unit-background slice. -/
def sixSiteRepeatedRootSlicePolynomial : MvPolynomial (Fin 3) Real :=
  MvPolynomial.eval₂
    (MvPolynomial.C : Real →+* MvPolynomial (Fin 3) Real)
    sixSiteRepeatedRootSliceSubstitution
    (symbolicRepeatedRootCertificate (N := 6))

/-- Evaluating the restricted polynomial is the same as evaluating the full
six-variable certificate at the embedded slice weights. -/
theorem evaluate_sixSiteRepeatedRootSlicePolynomial
    (x : Fin 3 → Real) :
    MvPolynomial.eval x sixSiteRepeatedRootSlicePolynomial =
      MvPolynomial.eval (sixSiteSliceInverseWeights x)
        (symbolicRepeatedRootCertificate (N := 6)) := by
  unfold sixSiteRepeatedRootSlicePolynomial
  rw [MvPolynomial.eval_eval₂]
  have hcoeff :
      (MvPolynomial.eval x).comp
          (MvPolynomial.C : Real →+* MvPolynomial (Fin 3) Real) =
        RingHom.id Real := by
    ext a
    simp
  rw [hcoeff, MvPolynomial.eval₂_id]
  apply congrArg
    (fun g ↦ MvPolynomial.eval g
      (symbolicRepeatedRootCertificate (N := 6)))
  funext k
  fin_cases k <;>
    simp [sixSiteRepeatedRootSliceSubstitution,
      sixSiteSliceInverseWeights]

/-- The slice point `(0, 1, 1)` embeds as the standard broken-cycle path
specialization `(0, 1, 1, 1, 1, 1)`. -/
theorem sixSiteSliceInverseWeights_path :
    sixSiteSliceInverseWeights ![(0 : Real), 1, 1] =
      pathWeightCoordinates 6 := by
  funext k
  simp only [sixSiteSliceInverseWeights, pathWeightCoordinates, pathWeight]
  have hzero : ((siteEquivFin 6).symm k = 0 ↔ k = 0) := by
    constructor
    · intro h
      apply Fin.ext
      rw [← val_siteEquivFin_symm k, h]
      rfl
    · intro h
      subst k
      apply ZMod.val_injective
      rw [val_siteEquivFin_symm]
      rfl
  simp only [hzero]
  fin_cases k <;> norm_num
  rfl

/-- The restricted three-variable repeated-root certificate is nonzero. -/
theorem sixSiteRepeatedRootSlicePolynomial_ne_zero :
    sixSiteRepeatedRootSlicePolynomial ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval (![(0 : Real), 1, 1] : Fin 3 → Real)) hzero
  rw [evaluate_sixSiteRepeatedRootSlicePolynomial,
    sixSiteSliceInverseWeights_path,
    evaluate_symbolicRepeatedRootCertificate] at heval
  simp only [map_zero] at heval
  exact path_specialization_fixedResultant_ne_zero
    (N := 6) (by omega) heval

/-- The actual positive-mass configuration of the six-site three-mass
slice. -/
def actualSixSiteThreeMassConfig (triple : MassTriple) :
    Lattice.PositiveMassConfig 6 :=
  threeMassSiteConfig frozenUnitMassSix
    (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6) triple

/-- The Hermitian harmonic matrix of the six-site three-mass slice. -/
def actualSixSiteThreeMassHarmonic (triple : MassTriple) :
    HermitianMatrix (Lattice.Site 6) :=
  threeMassHarmonicHermitian frozenUnitMassSix
    (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6) triple

/-- On the iid support, the actual inverse-mass coordinates are precisely the
three inverse raw masses followed by three unit coordinates. -/
theorem inverseMassCoordinates_actualSixSiteThreeMassConfig
    {triple : MassTriple} (htriple : triple ∈ iidMassTripleSupport) :
    inverseMassCoordinates (actualSixSiteThreeMassConfig triple) =
      sixSiteSliceInverseWeights
        (iidInverseMassTripleCoordinates triple) := by
  funext k
  fin_cases k <;>
    norm_num +decide [inverseMassCoordinates,
      actualSixSiteThreeMassConfig, sixSiteSliceInverseWeights,
      iidInverseMassTripleCoordinates, siteEquivFin, threeMassSiteConfig,
      frozenUnitMassSix, clippedMass_eq_self,
      htriple.1.1, htriple.1.2, htriple.2]
  all_goals rfl

/-- A positive ordered duplicate on the supported six-site slice forces the
restricted repeated-root certificate to vanish. -/
theorem sixSiteRepeatedRootSlicePolynomial_vanishes_of_orderedPositiveDuplicate
    {triple : MassTriple} (htriple : triple ∈ iidMassTripleSupport)
    (hduplicate :
      HasOrderedPositiveDuplicate (actualSixSiteThreeMassConfig triple)) :
    MvPolynomial.eval (iidInverseMassTripleCoordinates triple)
      sixSiteRepeatedRootSlicePolynomial = 0 := by
  have hrepeated := repeatedPositiveHarmonic_of_orderedPositiveDuplicate
    (actualSixSiteThreeMassConfig triple) hduplicate
  have hcertificate := certificate_vanishes_of_repeatedPositiveHarmonic
    (actualSixSiteThreeMassConfig triple) hrepeated
  rw [inverseMassCoordinates_actualSixSiteThreeMassConfig htriple] at hcertificate
  rw [evaluate_sixSiteRepeatedRootSlicePolynomial]
  exact hcertificate

/-- Positive ordered duplicates have zero probability in the genuine
three-mass six-site slice. -/
theorem iidMassTripleLaw_actualSixSite_orderedPositiveDuplicate_eq_zero :
    iidMassTripleLaw
      {triple |
        HasOrderedPositiveDuplicate
          (actualSixSiteThreeMassConfig triple)} = 0 := by
  apply measure_mono_null (t :=
    {triple |
      MvPolynomial.eval (iidInverseMassTripleCoordinates triple)
        sixSiteRepeatedRootSlicePolynomial = 0} ∪
      iidMassTripleSupportᶜ)
  · intro triple hduplicate
    by_cases htriple : triple ∈ iidMassTripleSupport
    · exact Or.inl
        (sixSiteRepeatedRootSlicePolynomial_vanishes_of_orderedPositiveDuplicate
          htriple hduplicate)
    · exact Or.inr htriple
  · apply measure_union_null
    · exact iidMassTripleLaw_zeroSet_eval_inverseCoordinates
        sixSiteRepeatedRootSlicePolynomial
        sixSiteRepeatedRootSlicePolynomial_ne_zero
    · exact mem_ae_iff.mp iidMassTriple_mem_support_ae

/-- Failure of full ordered simplicity is null on the actual six-site
three-mass slice. -/
theorem iidMassTripleLaw_actualSixSite_not_simpleOrderedSpectrum_eq_zero :
    iidMassTripleLaw
      {triple |
        ¬ SimpleOrderedSpectrum
          (actualSixSiteThreeMassHarmonic triple)} = 0 := by
  apply measure_mono_null (t :=
    {triple |
      HasOrderedPositiveDuplicate
        (actualSixSiteThreeMassConfig triple)})
  · intro triple hnonsimple
    by_contra hnotDuplicate
    apply hnonsimple
    simpa [actualSixSiteThreeMassHarmonic,
      actualSixSiteThreeMassConfig, threeMassHarmonicHermitian,
      harmonicHermitian] using
      simpleOrderedSpectrum_of_not_orderedPositiveDuplicate
        (actualSixSiteThreeMassConfig triple) hnotDuplicate
  · exact iidMassTripleLaw_actualSixSite_orderedPositiveDuplicate_eq_zero

/-- Equivalent almost-sure formulation of full ordered simplicity on the
three-mass slice. -/
theorem actualSixSite_simpleOrderedSpectrum_ae :
    ∀ᵐ triple ∂iidMassTripleLaw,
      SimpleOrderedSpectrum (actualSixSiteThreeMassHarmonic triple) := by
  have hnot := measure_eq_zero_iff_ae_notMem.mp
    iidMassTripleLaw_actualSixSite_not_simpleOrderedSpectrum_eq_zero
  filter_upwards [hnot] with triple htriple
  simpa using htriple

/-- Under simple spectrum, all three decay-chart modes `0`, `3`, and `4`
are strictly positive because none is the deterministic last zero mode. -/
theorem actualSixSiteDecayModes_energy_pos_of_simple
    (triple : MassTriple)
    (hsimple :
      SimpleOrderedSpectrum (actualSixSiteThreeMassHarmonic triple)) :
    ∀ r, 0 < orderedEigenvalue
      (actualSixSiteThreeMassHarmonic triple) (cleanSixSiteDecayModes r) := by
  have hsimple' : SimpleOrderedSpectrum
      (harmonicHermitian (actualSixSiteThreeMassConfig triple)) := by
    simpa [actualSixSiteThreeMassHarmonic,
      actualSixSiteThreeMassConfig, threeMassHarmonicHermitian] using hsimple
  intro r
  have hfrequency : 0 < orderedModeFrequency
      (harmonicHermitian (actualSixSiteThreeMassConfig triple))
      (cleanSixSiteDecayModes r) := by
    apply (orderedModeFrequency_pos_iff_ne_last
      (actualSixSiteThreeMassConfig triple) hsimple'
      (cleanSixSiteDecayModes r)).2
    apply Fin.ne_of_val_ne
    fin_cases r <;>
      norm_num [cleanSixSiteDecayModes, lastOrderedIndex, Lattice.Site]
  simpa [actualSixSiteThreeMassHarmonic,
    actualSixSiteThreeMassConfig, threeMassHarmonicHermitian,
    orderedModeFrequency] using hfrequency

/-- The physical near-resonance patch with the null nonsimple locus
removed. -/
def actualSixSiteSimpleNearResonancePatch (epsilon : Real) : Set MassTriple :=
  actualSixSiteNearResonancePatch epsilon ∩
    {triple | SimpleOrderedSpectrum
      (actualSixSiteThreeMassHarmonic triple)}

/-- Every point in the simple near-resonance patch has three strictly
positive selected decay modes. -/
theorem actualSixSiteSimpleNearResonancePatch_decayModes_energy_pos
    {epsilon : Real} {triple : MassTriple}
    (htriple : triple ∈ actualSixSiteSimpleNearResonancePatch epsilon) :
    ∀ r, 0 < orderedEigenvalue
      (actualSixSiteThreeMassHarmonic triple) (cleanSixSiteDecayModes r) :=
  actualSixSiteDecayModes_energy_pos_of_simple triple htriple.2

/-- Every positive mismatch width contains a strictly positive-probability
set of genuine six-site mass triples with full simple ordered spectrum. -/
theorem iidMassTripleLaw_actualSixSiteSimpleNearResonancePatch_pos
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    0 < iidMassTripleLaw
      (actualSixSiteSimpleNearResonancePatch epsilon) := by
  have hset :
      actualSixSiteSimpleNearResonancePatch epsilon =
        actualSixSiteNearResonancePatch epsilon \
          {triple |
            ¬ SimpleOrderedSpectrum
              (actualSixSiteThreeMassHarmonic triple)} := by
    ext triple
    simp [actualSixSiteSimpleNearResonancePatch]
  rw [hset,
    measure_sdiff_null
      iidMassTripleLaw_actualSixSite_not_simpleOrderedSpectrum_eq_zero]
  exact iidMassTripleLaw_actualSixSiteNearResonancePatch_pos hepsilon

end

end ArchonPhysics.ActualSixSiteThreeMassSimpleSpectrum
