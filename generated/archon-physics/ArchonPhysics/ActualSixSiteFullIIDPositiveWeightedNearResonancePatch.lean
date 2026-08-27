import ArchonPhysics.ActualSixSiteNearResonantFiniteCollisionEliminationCertificate
import ArchonPhysics.LocalCollisionMarkContinuity
import ArchonPhysics.FiniteMassPolynomialAvoidance
import ArchonPhysics.FiniteMassLawOpenPatch

/-!
# A full-six-IID positive weighted near-resonance patch

The six-site elimination certificate is first embedded in the full
six-coordinate mass space.  Continuity of the harmonic and dual matrices,
ordered eigenvalues, simple-spectrum projectors, and the normalized collision
weight then makes all certified strict inequalities stable under perturbing
*all six* masses.  Thus the three frozen unit masses in the algebraic witness
may be replaced by genuinely iid masses on a nonempty open patch.

This is a fixed-volume local statement.  It does not embed the patch into
larger periodic chains, count good blocks, prove an `N`-uniform mismatch
small-ball lower bound, or establish collision-network connectivity.
-/

open scoped Matrix

namespace ArchonPhysics.ActualSixSiteFullIIDPositiveWeightedNearResonancePatch

open ArchonPhysics
open ArchonPhysics.ActualSixSiteCleanDecayResonancePatch
open ArchonPhysics.ActualSixSiteNearResonantFiniteCollisionEliminationCertificate
open ArchonPhysics.ActualSixSiteNearResonantJacobianWitness
open ArchonPhysics.ActualSixSiteNearResonantPathResidualWitness
open ArchonPhysics.ActualSixSiteThreeMassSimpleSpectrum
open ArchonPhysics.ActualThreeMassHellmannFeynmanJacobian
open ArchonPhysics.ActualThreeMassLiftedJacobianPolynomial
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.LocalCollisionMarkContinuity
open ArchonPhysics.MarkedEmpiricalResonanceTransfer
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.SimpleSpectrumProjectorContinuity
open ArchonPhysics.ThreeParameterProjectorWeightJacobian
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison
open Filter Set

noncomputable section

/-- The six raw iid mass coordinates, in periodic-site order. -/
abbrev SixMassVector := Fin 6 → Real

/-- Clip six raw coordinates into a pointwise positive physical mass
configuration. -/
def fullSixMassConfig (x : SixMassVector) : Lattice.PositiveMassConfig 6 where
  mass i := clippedMass (x ⟨i.val, i.val_lt⟩)
  mass_pos i := clippedMass_pos _

/-- Embed the old three-variable slice in the full six-coordinate space. -/
def sixMassVectorFromTriple (triple : MassTriple) : SixMassVector :=
  ![triple.1.1, triple.1.2, triple.2, 1, 1, 1]

/-- Read the first three raw coordinates in the nested convention used by
the actual three-mass chart. -/
def firstMassTriple (x : SixMassVector) : MassTriple :=
  ((x 0, x 1), x 2)

/-- Physical site-space harmonic matrix for all six variable masses. -/
def fullSixHarmonic (x : SixMassVector) :
    HermitianMatrix (Lattice.Site 6) :=
  harmonicHermitian (fullSixMassConfig x)

/-- Physical mass-weighted difference matrix for all six variable masses. -/
def fullSixBondMatrix (x : SixMassVector) :
    Matrix (Lattice.Site 6) (Lattice.Site 6) Real :=
  massWeightedDifferenceMatrix (fullSixMassConfig x)

/-- Edge-space dual harmonic matrix used by the genuine projector Jacobian. -/
def fullSixDualHarmonic (x : SixMassVector) :
    HermitianMatrix (Lattice.Site 6) :=
  dualMassWeightedHarmonicHermitian (fullSixMassConfig x)

/-- The selected decay-channel mismatch in the full six-mass family. -/
def fullSixSelectedMismatch (x : SixMassVector) : Real :=
  orderedPhaseMismatch (fullSixHarmonic x) actualFourSiteDecaySign
    cleanSixSiteDecayModes

/-- The selected normalized squared interaction weight, written through the
joint bond/spectrum API used by the local continuity theorem. -/
def fullSixSelectedInteractionWeight (x : SixMassVector) : Real :=
  orderedNormalizedInteractionWeight (fullSixBondMatrix x)
    (fullSixHarmonic x) cleanSixSiteDecayModes

/-- The generic joint-data definition is exactly the physical harmonic
normalized interaction weight. -/
theorem fullSixSelectedInteractionWeight_eq_harmonic (x : SixMassVector) :
    fullSixSelectedInteractionWeight x =
      harmonicOrderedNormalizedInteractionWeight (fullSixMassConfig x)
        cleanSixSiteDecayModes := by
  exact orderedNormalizedInteractionWeight_harmonic_eq
    (fullSixMassConfig x) cleanSixSiteDecayModes

/-- Projector minor controlling the lifted Jacobian with respect to the first
three masses while the last three masses are frozen at their sampled values. -/
def fullSixSelectedProjectorWeightMatrix (x : SixMassVector) :
    Matrix (Fin 3) (Fin 3) Real :=
  orderedProjectorWeightMatrix (fullSixDualHarmonic x)
    cleanSixSiteDecayModes
    (actualThreeMassCycleDirection
      (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6))

/-- Coordinatewise interior of the six-fold iid support. -/
def fullSixMassSupportInterior : Set SixMassVector :=
  {x | ∀ i, x i ∈ Ioo massLower massUpper}

theorem continuous_fullSixMassConfig_mass (i : Lattice.Site 6) :
    Continuous fun x : SixMassVector => (fullSixMassConfig x).mass i := by
  change Continuous fun x : SixMassVector =>
    clippedMass (x ⟨i.val, i.val_lt⟩)
  unfold clippedMass
  fun_prop

theorem continuous_fullSixBondMatrix_apply (i j : Lattice.Site 6) :
    Continuous fun x : SixMassVector => fullSixBondMatrix x i j := by
  unfold fullSixBondMatrix massWeightedDifferenceMatrix
  simp only [Matrix.mul_apply, Matrix.diagonal_apply]
  apply continuous_finsetSum Finset.univ
  intro k _hk
  by_cases hkj : k = j
  · subst k
    simp only [ite_true]
    exact continuous_const.mul
      ((Real.continuous_sqrt.comp
        (continuous_fullSixMassConfig_mass j)).inv₀
          (fun x => Real.sqrt_ne_zero'.2
            ((fullSixMassConfig x).mass_pos j)))
  · simpa [hkj] using
      (continuous_const : Continuous fun _ : SixMassVector => (0 : Real))

theorem continuous_fullSixBondMatrix :
    Continuous fullSixBondMatrix := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_fullSixBondMatrix_apply i j

theorem continuous_fullSixHarmonic :
    Continuous fullSixHarmonic := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold massWeightedHarmonicMatrix
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply continuous_finsetSum Finset.univ
  intro k _hk
  exact (continuous_fullSixBondMatrix_apply k i).mul
    (continuous_fullSixBondMatrix_apply k j)

theorem continuous_fullSixDualHarmonic :
    Continuous fullSixDualHarmonic := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold dualMassWeightedHarmonicMatrix
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply continuous_finsetSum Finset.univ
  intro k _hk
  exact (continuous_fullSixBondMatrix_apply i k).mul
    (continuous_fullSixBondMatrix_apply j k)

theorem continuous_fullSixSelectedMismatch :
    Continuous fullSixSelectedMismatch := by
  unfold fullSixSelectedMismatch
  exact (continuous_orderedPhaseMismatch actualFourSiteDecaySign
    cleanSixSiteDecayModes).comp continuous_fullSixHarmonic

theorem eventually_simple_fullSixHarmonic
    {x : SixMassVector}
    (hsimple : SimpleOrderedSpectrum (fullSixHarmonic x)) :
    ∀ᶠ y in nhds x, SimpleOrderedSpectrum (fullSixHarmonic y) := by
  unfold SimpleOrderedSpectrum
  change ∀ᶠ y in nhds x, ∀ i j,
    orderedEigenvalue (fullSixHarmonic y) i =
      orderedEigenvalue (fullSixHarmonic y) j → i = j
  rw [eventually_all]
  intro i
  rw [eventually_all]
  intro j
  by_cases hij : i = j
  · subst j
    exact Filter.Eventually.of_forall fun _ _ => rfl
  · have hne : orderedEigenvalue (fullSixHarmonic x) i ≠
        orderedEigenvalue (fullSixHarmonic x) j := hsimple.ne hij
    have hi : ContinuousAt
        (fun y => orderedEigenvalue (fullSixHarmonic y) i) x :=
      ((continuous_orderedEigenvalue i).comp continuous_fullSixHarmonic).continuousAt
    have hj : ContinuousAt
        (fun y => orderedEigenvalue (fullSixHarmonic y) j) x :=
      ((continuous_orderedEigenvalue j).comp continuous_fullSixHarmonic).continuousAt
    filter_upwards [(hi.ne_iff_eventually_ne hj).1 hne] with y hnear
    exact fun heq => (hnear heq).elim

theorem continuousAt_fullSixSelectedProjectorWeightMatrix_apply
    {x : SixMassVector}
    (hsimpleDual : SimpleOrderedSpectrum (fullSixDualHarmonic x))
    (r s : Fin 3) :
    ContinuousAt
      (fun y => fullSixSelectedProjectorWeightMatrix y r s) x := by
  unfold fullSixSelectedProjectorWeightMatrix orderedProjectorWeightMatrix
  simp only [dotProduct, Matrix.mulVec]
  apply tendsto_finsetSum Finset.univ
  intro i _hi
  apply ContinuousAt.mul continuousAt_const
  apply tendsto_finsetSum Finset.univ
  intro j _hj
  apply ContinuousAt.mul
  · exact (continuousAt_orderedModeProjector_apply
      (fullSixDualHarmonic x) hsimpleDual
      (cleanSixSiteDecayModes r) i j).comp_of_eq
        continuous_fullSixDualHarmonic.continuousAt rfl
  · exact continuousAt_const

theorem continuousAt_fullSixSelectedProjectorWeightMatrix_det
    {x : SixMassVector}
    (hsimpleDual : SimpleOrderedSpectrum (fullSixDualHarmonic x)) :
    ContinuousAt
      (fun y => (fullSixSelectedProjectorWeightMatrix y).det) x := by
  simp only [Matrix.det_apply']
  apply tendsto_finsetSum Finset.univ
  intro permutation _hpermutation
  apply ContinuousAt.mul continuousAt_const
  apply tendsto_finsetProd Finset.univ
  intro i _hi
  exact continuousAt_fullSixSelectedProjectorWeightMatrix_apply
    hsimpleDual (permutation i) i


@[simp] theorem firstMassTriple_sixMassVectorFromTriple
    (triple : MassTriple) :
    firstMassTriple (sixMassVectorFromTriple triple) = triple := by
  rfl

set_option maxRecDepth 100000 in
/-- The full six-coordinate embedding is exactly the former three-variable
unit-background configuration. -/
theorem fullSixMassConfig_sixMassVectorFromTriple
    (triple : MassTriple) :
    fullSixMassConfig (sixMassVectorFromTriple triple) =
      actualSixSiteThreeMassConfig triple := by
  change Lattice.PositiveMassConfig.mk _ _ =
    Lattice.PositiveMassConfig.mk _ _
  rw [Lattice.PositiveMassConfig.mk.injEq]
  funext i
  generalize hj : siteEquivFin 6 i = j
  have hi : i = (siteEquivFin 6).symm j := by
    rw [← hj]
    simp
  rw [hi]
  clear hi hj i
  fin_cases j <;>
    simp (config := { decide := true }) [fullSixMassConfig,
      sixMassVectorFromTriple, actualSixSiteThreeMassConfig,
      threeMassSiteConfig, frozenUnitMassSix,
      PeriodicWeightedCycleBlockGluing.val_siteEquivFin_symm,
      clippedMass, massLower, massUpper] <;> norm_num

@[simp] theorem fullSixHarmonic_sixMassVectorFromTriple
    (triple : MassTriple) :
    fullSixHarmonic (sixMassVectorFromTriple triple) =
      actualSixSiteThreeMassHarmonic triple := by
  change harmonicHermitian
      (fullSixMassConfig (sixMassVectorFromTriple triple)) =
    harmonicHermitian (actualSixSiteThreeMassConfig triple)
  rw [fullSixMassConfig_sixMassVectorFromTriple]

@[simp] theorem fullSixBondMatrix_sixMassVectorFromTriple
    (triple : MassTriple) :
    fullSixBondMatrix (sixMassVectorFromTriple triple) =
      massWeightedDifferenceMatrix (actualSixSiteThreeMassConfig triple) := by
  unfold fullSixBondMatrix
  rw [fullSixMassConfig_sixMassVectorFromTriple]

@[simp] theorem fullSixDualHarmonic_sixMassVectorFromTriple
    (triple : MassTriple) :
    fullSixDualHarmonic (sixMassVectorFromTriple triple) =
      actualThreeMassDualHermitian frozenUnitMassSix
        (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6)
        triple := by
  unfold fullSixDualHarmonic actualThreeMassDualHermitian
  rw [fullSixMassConfig_sixMassVectorFromTriple]
  rfl

@[simp] theorem fullSixSelectedMismatch_sixMassVectorFromTriple
    (triple : MassTriple) :
    fullSixSelectedMismatch (sixMassVectorFromTriple triple) =
      (actualSixSiteLiftedFrequencyChart triple).2 := by
  unfold fullSixSelectedMismatch actualSixSiteLiftedFrequencyChart
    actualThreeMassLiftedFrequencyChart
  rw [fullSixHarmonic_sixMassVectorFromTriple]
  rfl

@[simp] theorem fullSixSelectedInteractionWeight_sixMassVectorFromTriple
    (triple : MassTriple) :
    fullSixSelectedInteractionWeight (sixMassVectorFromTriple triple) =
      harmonicOrderedNormalizedInteractionWeight
        (actualSixSiteThreeMassConfig triple) cleanSixSiteDecayModes := by
  rw [fullSixSelectedInteractionWeight_eq_harmonic,
    fullSixMassConfig_sixMassVectorFromTriple]

@[simp] theorem fullSixSelectedProjectorWeightMatrix_sixMassVectorFromTriple
    (triple : MassTriple) :
    fullSixSelectedProjectorWeightMatrix (sixMassVectorFromTriple triple) =
      actualThreeMassProjectorWeightMatrix frozenUnitMassSix
        (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6)
        cleanSixSiteDecayModes triple := by
  unfold fullSixSelectedProjectorWeightMatrix
    actualThreeMassProjectorWeightMatrix
  rw [fullSixDualHarmonic_sixMassVectorFromTriple]

/-- An interior three-mass witness embeds coordinatewise into the interior of
the full six-fold iid support. -/
theorem sixMassVectorFromTriple_mem_fullSixMassSupportInterior
    {triple : MassTriple}
    (htriple : triple ∈ interior iidMassTripleSupport) :
    sixMassVectorFromTriple triple ∈ fullSixMassSupportInterior := by
  rw [iidMassTripleSupport, interior_prod_eq,
    TwoParameterSpectralAveragingAtlas.iidMassPairSupport,
    interior_prod_eq, massSupport, interior_Icc] at htriple
  intro i
  fin_cases i
  · exact htriple.1.1
  · exact htriple.1.2
  · exact htriple.2
  all_goals norm_num [sixMassVectorFromTriple, massLower, massUpper]

/-- A full six-coordinate sample is good when it lies in the interior of the
iid cube, has simple spectrum and positive selected energies, lies in the
requested physical mismatch strip, has positive physical interaction weight,
and has nonzero first-three-coordinate projector minor.  The final condition
is deliberately stated as a projector-minor proxy; this definition does not
identify it with a six-coordinate physical Jacobian. -/
def fullSixPhysicalWeightedNearResonanceWithProjectorMinor
    (epsilon : Real) : Set SixMassVector :=
  {x |
    x ∈ fullSixMassSupportInterior ∧
    SimpleOrderedSpectrum (fullSixHarmonic x) ∧
    (∀ r, 0 < orderedEigenvalue
      (fullSixHarmonic x) (cleanSixSiteDecayModes r)) ∧
    |fullSixSelectedMismatch x| < epsilon ∧
    0 < fullSixSelectedInteractionWeight x ∧
    (fullSixSelectedProjectorWeightMatrix x).det ≠ 0}

theorem isOpen_fullSixMassSupportInterior :
    IsOpen fullSixMassSupportInterior := by
  rw [show fullSixMassSupportInterior =
      ⋂ i, {x : SixMassVector | x i ∈ Ioo massLower massUpper} by
    ext x
    simp [fullSixMassSupportInterior]]
  exact isOpen_iInter_of_finite fun i ↦
    isOpen_Ioo.preimage (continuous_apply i)

/-- Every positive mismatch width contains an open, positive-`finiteMassLaw`
patch of genuinely six-variable iid masses on which the selected physical
collision weight is positive.  The additionally transported nonzero
determinant is explicitly only the first-three-coordinate projector minor. -/
theorem exists_positive_finiteMassLaw_fullSix_physicalWeightedNearResonancePatch
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ patch : Set SixMassVector,
      IsOpen patch ∧
      0 < finiteMassLaw 6 patch ∧
      patch ⊆ fullSixPhysicalWeightedNearResonanceWithProjectorMinor epsilon := by
  obtain ⟨t, _ht, hinterior, hmismatch, hsimple, hJacobian, hweight⟩ :=
    exists_actualSixSiteNearResonant_weightedJacobianWitness_of_finiteCertificate
      hepsilon
  let triple : MassTriple := nearResonantMassTriple t
  let x : SixMassVector := sixMassVectorFromTriple triple
  have hxInterior : x ∈ fullSixMassSupportInterior := by
    exact sixMassVectorFromTriple_mem_fullSixMassSupportInterior hinterior
  have hsimpleFull : SimpleOrderedSpectrum (fullSixHarmonic x) := by
    simpa [x, triple] using hsimple
  have henergyFull : ∀ r, 0 < orderedEigenvalue
      (fullSixHarmonic x) (cleanSixSiteDecayModes r) := by
    intro r
    simpa [x, triple] using
      actualSixSiteDecayModes_energy_pos_of_simple
        (nearResonantMassTriple t) hsimple r
  have hmismatchFull : |fullSixSelectedMismatch x| < epsilon := by
    simpa [x, triple, actualSixSiteNearResonantMismatchPath] using hmismatch
  have hweightFull : 0 < fullSixSelectedInteractionWeight x := by
    simpa [x, triple] using hweight
  have hsimplePhysical : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian frozenUnitMassSix
        (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6)
        (nearResonantMassTriple t)) := by
    simpa [actualSixSiteThreeMassHarmonic] using hsimple
  have hpositivePhysical : ∀ r, 0 < orderedEigenvalue
      (threeMassHarmonicHermitian frozenUnitMassSix
        (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6)
        (nearResonantMassTriple t)) (cleanSixSiteDecayModes r) := by
    intro r
    simpa [actualSixSiteThreeMassHarmonic] using
      actualSixSiteDecayModes_energy_pos_of_simple
        (nearResonantMassTriple t) hsimple r
  have hprojectorSlice :
      (actualThreeMassProjectorWeightMatrix frozenUnitMassSix
        (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6)
        cleanSixSiteDecayModes (nearResonantMassTriple t)).det ≠ 0 :=
    (actualThreeMassLiftedFrequencyJacobian_det_ne_zero_iff_projectorWeight
      frozenUnitMassSix (by decide) (by decide) (by decide)
      actualFourSiteDecaySign cleanSixSiteDecayModes hinterior
      hsimplePhysical hpositivePhysical).1 hJacobian
  have hprojectorFull :
      (fullSixSelectedProjectorWeightMatrix x).det ≠ 0 := by
    simpa [x, triple] using hprojectorSlice
  have hsimpleDual : SimpleOrderedSpectrum (fullSixDualHarmonic x) := by
    have hdual := simple_actualThreeMassDualHermitian_of_simple
      frozenUnitMassSix
      (0 : Lattice.Site 6) (1 : Lattice.Site 6) (2 : Lattice.Site 6)
      (nearResonantMassTriple t) hsimplePhysical
    simpa [x, triple] using hdual
  have hfrequencyFull : PositiveOrderedModeTuple
      (fullSixHarmonic x) cleanSixSiteDecayModes := by
    intro r
    exact Real.sqrt_pos.2 (henergyFull r)
  have hpair : Continuous fun y : SixMassVector ↦
      (fullSixBondMatrix y, fullSixHarmonic y) :=
    continuous_fullSixBondMatrix.prodMk continuous_fullSixHarmonic
  have hweightEventually :
      ∀ᶠ y in nhds x, 0 < fullSixSelectedInteractionWeight y := by
    have hgeneric :=
      (continuousAt_orderedNormalizedInteractionWeight
        (fullSixBondMatrix x) (fullSixHarmonic x) hsimpleFull
        cleanSixSiteDecayModes hfrequencyFull).eventually
          (eventually_gt_nhds hweightFull)
    exact hpair.continuousAt hgeneric
  have hprojectorEventually :
      ∀ᶠ y in nhds x,
        (fullSixSelectedProjectorWeightMatrix y).det ≠ 0 :=
    ((continuousAt_fullSixSelectedProjectorWeightMatrix_det hsimpleDual).ne_iff_eventually_ne
      continuousAt_const).1 hprojectorFull
  have henergyEventually :
      ∀ᶠ y in nhds x, ∀ r, 0 < orderedEigenvalue
        (fullSixHarmonic y) (cleanSixSiteDecayModes r) := by
    rw [eventually_all]
    intro r
    exact (((continuous_orderedEigenvalue (cleanSixSiteDecayModes r)).comp
      continuous_fullSixHarmonic).continuousAt).eventually
        (eventually_gt_nhds (henergyFull r))
  have hgood :
      fullSixPhysicalWeightedNearResonanceWithProjectorMinor epsilon ∈ nhds x := by
    filter_upwards [
      isOpen_fullSixMassSupportInterior.mem_nhds hxInterior,
      eventually_simple_fullSixHarmonic hsimpleFull,
      henergyEventually,
      continuous_fullSixSelectedMismatch.abs.continuousAt.eventually
        (eventually_lt_nhds hmismatchFull),
      hweightEventually,
      hprojectorEventually] with y hyInterior hySimple hyEnergy hyMismatch
        hyWeight hyProjector
    exact ⟨hyInterior, hySimple, hyEnergy, hyMismatch, hyWeight, hyProjector⟩
  obtain ⟨patch, hpatchSubset, hpatchOpen, hxPatch⟩ := mem_nhds_iff.mp hgood
  refine ⟨patch, hpatchOpen, ?_, hpatchSubset⟩
  exact ArchonPhysics.FiniteMassLawOpenPatch.finiteMassLaw_pos_of_isOpen_of_mem_interior
    hpatchOpen x hxPatch hxInterior
end

end ArchonPhysics.ActualSixSiteFullIIDPositiveWeightedNearResonancePatch
