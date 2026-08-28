import ArchonPhysics.ActualFourSitePositiveProjectorWitness
import ArchonPhysics.ActualThreeMassCollisionWeightedProjectorMinorZeroAtom
import ArchonPhysics.ActualThreeMassCollisionWeightedProjectorMinorTail
import ArchonPhysics.CanonicalCollisionSoftLegBound
import ArchonPhysics.OrderedTranslationLastMode
import ArchonPhysics.PathLaplacianResultant
import ArchonPhysics.RandomMassOrderedProjectorBridge

/-!
# Four-site actual collision-weighted projector-minor zero atom

This module closes the zero-atom problem for the first nontrivial periodic
volume of the frozen random-mass model.  Three iid masses vary and the fourth
mass is one.  A three-variable specialization of the genuine repeated-root
resultant proves simple spectrum almost surely.  The explicit coefficient
Jacobian polynomial then proves that the actual projector minor of the three
positive modes is nonzero almost surely.

Finally, every all-distinct positive mode triple at volume four is a row
permutation of those three modes; triples containing the deterministic last
translation mode have zero physical collision density.  Consequently the
complete collision-weighted minor law has no atom at zero.  No genericity,
nondegeneracy, or tail-rate hypothesis is introduced.

This finite-volume theorem is a strict zero-level improvement, but it is not
an `N`-uniform quantitative small-minor estimate.
-/

open scoped BigOperators Matrix ENNReal

namespace ArchonPhysics.ActualFourSiteCollisionWeightedMinorZeroAtom

open ArchonPhysics
open ArchonPhysics.ActualFourSitePositiveProjectorWitness
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningTrace
open ArchonPhysics.ActualThreeMassCollisionWeightedProjectorMinorBadPeak
open ArchonPhysics.ActualThreeMassCollisionWeightedProjectorMinorTail
open ArchonPhysics.ActualThreeMassCollisionWeightedProjectorMinorZeroAtom
open ArchonPhysics.ActualThreeMassLiftedPerSiteBudget
open ArchonPhysics.CanonicalCollisionSoftLegBound
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.ActualThreeMassHellmannFeynmanJacobian
open ArchonPhysics.ActualThreeMassLiftedJacobianPolynomial
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.ActualThreeMassWeightedProjectorMinorDistribution
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
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassResultantBridge
open ArchonPhysics.RandomMassSimpleSpectrum
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open Filter
open MeasureTheory Set

noncomputable section

/-- Embed the three free inverse masses in the frozen-unit four-site slice. -/
def fourSiteRepeatedRootSliceInverseWeights (x : Fin 3 → Real) : Fin 4 → Real :=
  ![x 0, x 1, x 2, 1]

/-- Leave the first three inverse masses free and freeze the fourth at one. -/
def fourSiteRepeatedRootSliceSubstitution :
    Fin 4 → MvPolynomial (Fin 3) Real :=
  ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2,
    MvPolynomial.C 1]

/-- Repeated-root resultant restricted to the actual three-mass four-site
slice. -/
def fourSiteRepeatedRootSlicePolynomial : MvPolynomial (Fin 3) Real :=
  MvPolynomial.eval₂
    (MvPolynomial.C : Real →+* MvPolynomial (Fin 3) Real)
    fourSiteRepeatedRootSliceSubstitution
    (symbolicRepeatedRootCertificate (N := 4))

theorem evaluate_fourSiteRepeatedRootSlicePolynomial
    (x : Fin 3 → Real) :
    MvPolynomial.eval x fourSiteRepeatedRootSlicePolynomial =
      MvPolynomial.eval (fourSiteRepeatedRootSliceInverseWeights x)
        (symbolicRepeatedRootCertificate (N := 4)) := by
  unfold fourSiteRepeatedRootSlicePolynomial
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
      (symbolicRepeatedRootCertificate (N := 4)))
  funext k
  fin_cases k <;>
    simp [fourSiteRepeatedRootSliceSubstitution,
      fourSiteRepeatedRootSliceInverseWeights]

theorem fourSiteRepeatedRootSliceInverseWeights_path :
    fourSiteRepeatedRootSliceInverseWeights ![(0 : Real), 1, 1] =
      pathWeightCoordinates 4 := by
  funext k
  simp only [fourSiteRepeatedRootSliceInverseWeights,
    pathWeightCoordinates, pathWeight]
  have hzero : ((siteEquivFin 4).symm k = 0 ↔ k = 0) := by
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

/-- The restricted repeated-root certificate is genuinely nonzero. -/
theorem fourSiteRepeatedRootSlicePolynomial_ne_zero :
    fourSiteRepeatedRootSlicePolynomial ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval (![(0 : Real), 1, 1] : Fin 3 → Real)) hzero
  rw [evaluate_fourSiteRepeatedRootSlicePolynomial,
    fourSiteRepeatedRootSliceInverseWeights_path,
    evaluate_symbolicRepeatedRootCertificate] at heval
  simp only [map_zero] at heval
  exact path_specialization_fixedResultant_ne_zero
    (N := 4) (by omega) heval

theorem fourSiteRepeatedRootSlicePolynomial_vanishes_of_orderedPositiveDuplicate
    {triple : MassTriple} (htriple : triple ∈ iidMassTripleSupport)
    (hduplicate :
      HasOrderedPositiveDuplicate (actualFourSiteMassConfig triple)) :
    MvPolynomial.eval (iidInverseMassTripleCoordinates triple)
      fourSiteRepeatedRootSlicePolynomial = 0 := by
  have hrepeated := repeatedPositiveHarmonic_of_orderedPositiveDuplicate
    (actualFourSiteMassConfig triple) hduplicate
  have hcertificate := certificate_vanishes_of_repeatedPositiveHarmonic
    (actualFourSiteMassConfig triple) hrepeated
  rw [inverseMassCoordinates_actualFourSiteMassConfig htriple] at hcertificate
  have hweights :
      fourSiteInverseWeights triple =
        fourSiteRepeatedRootSliceInverseWeights
          (iidInverseMassTripleCoordinates triple) := by
    funext k
    fin_cases k <;>
      simp [fourSiteInverseWeights,
        fourSiteRepeatedRootSliceInverseWeights,
        iidInverseMassTripleCoordinates]
  rw [hweights] at hcertificate
  rw [evaluate_fourSiteRepeatedRootSlicePolynomial]
  exact hcertificate

theorem iidMassTripleLaw_actualFourSite_orderedPositiveDuplicate_eq_zero :
    iidMassTripleLaw
      {triple |
        HasOrderedPositiveDuplicate (actualFourSiteMassConfig triple)} = 0 := by
  apply measure_mono_null (t :=
    {triple |
      MvPolynomial.eval (iidInverseMassTripleCoordinates triple)
        fourSiteRepeatedRootSlicePolynomial = 0} ∪
      iidMassTripleSupportᶜ)
  · intro triple hduplicate
    by_cases htriple : triple ∈ iidMassTripleSupport
    · exact Or.inl
        (fourSiteRepeatedRootSlicePolynomial_vanishes_of_orderedPositiveDuplicate
          htriple hduplicate)
    · exact Or.inr htriple
  · apply measure_union_null
    · exact iidMassTripleLaw_zeroSet_eval_inverseCoordinates
        fourSiteRepeatedRootSlicePolynomial
        fourSiteRepeatedRootSlicePolynomial_ne_zero
    · exact mem_ae_iff.mp iidMassTriple_mem_support_ae

/-- The frozen-unit four-site slice has simple ordered spectrum almost surely
under the exact iid mass-triple law. -/
theorem actualFourSite_simpleOrderedSpectrum_ae :
    ∀ᵐ triple ∂iidMassTripleLaw,
      SimpleOrderedSpectrum (actualFourSiteHarmonic triple) := by
  have hnot : iidMassTripleLaw
      {triple | ¬ SimpleOrderedSpectrum (actualFourSiteHarmonic triple)} = 0 := by
    apply measure_mono_null (t :=
      {triple |
        HasOrderedPositiveDuplicate (actualFourSiteMassConfig triple)})
    · intro triple hnonsimple
      by_contra hnotDuplicate
      apply hnonsimple
      simpa [actualFourSiteHarmonic, actualFourSiteMassConfig,
        threeMassHarmonicHermitian, harmonicHermitian] using
        simpleOrderedSpectrum_of_not_orderedPositiveDuplicate
          (actualFourSiteMassConfig triple) hnotDuplicate
    · exact iidMassTripleLaw_actualFourSite_orderedPositiveDuplicate_eq_zero
  have hae := measure_eq_zero_iff_ae_notMem.mp hnot
  filter_upwards [hae] with triple htriple
  simpa using htriple

/-- The endpoints of the frozen uniform mass interval are null, so one mass
coordinate lies in the open support interval almost surely. -/
theorem massCoordinate_mem_interior_massSupport_ae :
    ∀ᵐ mass ∂massCoordinateLaw, mass ∈ interior massSupport := by
  have hlower : massCoordinateLaw ({massLower} : Set Real) = 0 := by
    apply le_antisymm
    · exact (massCoordinateLaw_le_three_smul_volume
        ({massLower} : Set Real)).trans_eq (by simp)
    · exact bot_le
  have hupper : massCoordinateLaw ({massUpper} : Set Real) = 0 := by
    apply le_antisymm
    · exact (massCoordinateLaw_le_three_smul_volume
        ({massUpper} : Set Real)).trans_eq (by simp)
    · exact bot_le
  have hnotLower := measure_eq_zero_iff_ae_notMem.mp hlower
  have hnotUpper := measure_eq_zero_iff_ae_notMem.mp hupper
  filter_upwards [massCoordinate_mem_support_ae, hnotLower, hnotUpper]
    with mass hsupport hneLower hneUpper
  rw [massSupport, interior_Icc]
  simp only [mem_singleton_iff] at hneLower hneUpper
  exact ⟨lt_of_le_of_ne hsupport.1 (Ne.symm hneLower),
    lt_of_le_of_ne hsupport.2 hneUpper⟩

/-- The genuine three-mass law lies in the open mass cube almost surely. -/
theorem iidMassTriple_mem_interior_support_ae :
    ∀ᵐ triple ∂iidMassTripleLaw,
      triple ∈ interior iidMassTripleSupport := by
  have hpair : ∀ᵐ pair ∂iidMassPairLaw,
      pair ∈ interior iidMassPairSupport := by
    rw [iidMassPairLaw, Measure.ae_prod_mem_iff_ae_ae_mem]
    · filter_upwards [massCoordinate_mem_interior_massSupport_ae]
        with first hfirst
      filter_upwards [massCoordinate_mem_interior_massSupport_ae]
        with second hsecond
      simpa [iidMassPairSupport, interior_prod_eq] using
        (show first ∈ interior massSupport ∧
          second ∈ interior massSupport from ⟨hfirst, hsecond⟩)
    · exact isOpen_interior.measurableSet
  rw [iidMassTripleLaw, Measure.ae_prod_mem_iff_ae_ae_mem]
  · filter_upwards [hpair] with pair hpairInterior
    filter_upwards [massCoordinate_mem_interior_massSupport_ae]
      with third hthird
    simpa [iidMassTripleSupport, interior_prod_eq] using
      (show pair ∈ interior iidMassPairSupport ∧
        third ∈ interior massSupport from ⟨hpairInterior, hthird⟩)
  · exact isOpen_interior.measurableSet

/-- The actual projector minor of the three positive four-site modes is
nonzero almost surely under the exact iid mass-triple law. -/
theorem actualFourSitePositiveModes_projectorMinor_ne_zero_ae :
    ∀ᵐ triple ∂iidMassTripleLaw,
      (actualThreeMassProjectorWeightMatrix frozenUnitMassFour
        (0 : Lattice.Site 4) (1 : Lattice.Site 4) (2 : Lattice.Site 4)
        actualFourSitePositiveModes triple).det ≠ 0 := by
  have hpolynomial : ∀ᵐ triple ∂iidMassTripleLaw,
      MvPolynomial.eval (iidInverseMassTripleCoordinates triple)
        fourSiteCoefficientJacobianPolynomial ≠ 0 := by
    have hnot := measure_eq_zero_iff_ae_notMem.mp
      iidMassTripleLaw_fourSiteCoefficientJacobianPolynomial_zero
    filter_upwards [hnot] with triple htriple
    simpa using htriple
  filter_upwards [iidMassTriple_mem_interior_support_ae,
    actualFourSite_simpleOrderedSpectrum_ae, hpolynomial]
      with triple hinterior hsimple hpolynomial
  have hlifted := actualFourSiteLiftedFrequencyJacobian_det_ne_zero
    hinterior hsimple hpolynomial
  have henergies := actualFourSite_first_second_third_energy_pos triple hsimple
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
  exact
    (actualThreeMassLiftedFrequencyJacobian_det_ne_zero_iff_projectorWeight
      frozenUnitMassFour (by decide) (by decide) (by decide)
      actualFourSiteDecaySign actualFourSitePositiveModes hinterior
      (by simpa [actualFourSiteHarmonic] using hsimple) hpositive).mp
        (by simpa [actualFourSiteLiftedFrequencyJacobian] using hlifted)

/-- At volume four, every injective ordered triple avoiding the last mode is
a row permutation of the three positive-mode matrix. -/
theorem actualFourSite_projectorMinor_ne_zero_of_allDistinct_of_avoidsLast
    (modes : OrderedModeTriple 4) (hdistinct : AllDistinctModes modes)
    (havoids : ∀ r, modes r ≠
      lastOrderedIndex (ι := Lattice.Site 4))
    (triple : MassTriple)
    (hbase :
      (actualThreeMassProjectorWeightMatrix frozenUnitMassFour
        (0 : Lattice.Site 4) (1 : Lattice.Site 4) (2 : Lattice.Site 4)
        actualFourSitePositiveModes triple).det ≠ 0) :
    (actualThreeMassProjectorWeightMatrix frozenUnitMassFour
      (0 : Lattice.Site 4) (1 : Lattice.Site 4) (2 : Lattice.Site 4)
      modes triple).det ≠ 0 := by
  have hmodesInjective : Function.Injective modes := by
    intro r s hrs
    fin_cases r <;> fin_cases s <;>
      simp_all [AllDistinctModes]
  let e : Fin 3 → Fin 3 := fun r =>
    ⟨(modes r).val, by
      have hlt : (modes r).val < 4 := by
        simpa [Lattice.Site] using (modes r).isLt
      have hne := havoids r
      have hneVal : (modes r).val ≠ 3 := by
        intro heq
        apply hne
        apply Fin.ext
        simpa [lastOrderedIndex, Lattice.Site] using heq
      omega⟩
  have heInjective : Function.Injective e := by
    intro r s hrs
    apply hmodesInjective
    apply Fin.ext
    have hvals := congrArg Fin.val hrs
    change (modes r).val = (modes s).val at hvals
    exact hvals
  have heBijective : Function.Bijective e :=
    (Fintype.bijective_iff_injective_and_card e).2
      ⟨heInjective, by simp⟩
  let sigma : Equiv.Perm (Fin 3) := Equiv.ofBijective e heBijective
  have hmodes : modes = actualFourSitePositiveModes ∘ sigma := by
    funext r
    apply Fin.ext
    rfl
  let base : Matrix (Fin 3) (Fin 3) Real :=
    actualThreeMassProjectorWeightMatrix frozenUnitMassFour
      (0 : Lattice.Site 4) (1 : Lattice.Site 4) (2 : Lattice.Site 4)
      actualFourSitePositiveModes triple
  have hmatrix :
      actualThreeMassProjectorWeightMatrix frozenUnitMassFour
          (0 : Lattice.Site 4) (1 : Lattice.Site 4) (2 : Lattice.Site 4)
          modes triple =
        base.submatrix sigma id := by
    rw [hmodes]
    ext r s
    rfl
  rw [hmatrix, Matrix.det_permute]
  exact mul_ne_zero (by simp) hbase

/-- The base three-positive-mode actual zero locus is iid-null. -/
theorem iidMassTripleLaw_actualFourSitePositiveModes_projectorMinorZeroSet_eq_zero :
    iidMassTripleLaw
      (actualThreeMassProjectorMinorZeroSet frozenUnitMassFour
        (0 : Lattice.Site 4) (1 : Lattice.Site 4) (2 : Lattice.Site 4)
        actualFourSitePositiveModes) = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [actualFourSitePositiveModes_projectorMinor_ne_zero_ae]
    with triple hminor
  intro hzero
  apply hminor
  simpa [actualThreeMassProjectorMinorZeroSet,
    actualThreeMassProjectorMinorMagnitude] using hzero

/-- Every all-distinct four-site tuple has zero collision-weighted mass on
its actual projector-minor zero locus.  Tuples involving the translation
mode are killed by the exact positive-frequency filter; all other tuples are
row permutations of the three-mode base case. -/
theorem actualFourSite_modewise_collisionWeighted_projectorMinorZeroMass_eq_zero
    (modes : OrderedModeTriple 4) (hdistinct : AllDistinctModes modes) :
    (iidMassTripleLaw.withDensity
      (actualThreeMassAllDistinctTupleWeight frozenUnitMassFour
        (0 : Lattice.Site 4) (1 : Lattice.Site 4) (2 : Lattice.Site 4)
        modes))
      (actualThreeMassProjectorMinorZeroSet frozenUnitMassFour
        (0 : Lattice.Site 4) (1 : Lattice.Site 4) (2 : Lattice.Site 4)
        modes) = 0 := by
  by_cases havoids : ∀ r, modes r ≠
      lastOrderedIndex (ι := Lattice.Site 4)
  · apply (withDensity_absolutelyContinuous iidMassTripleLaw
      (actualThreeMassAllDistinctTupleWeight frozenUnitMassFour
        (0 : Lattice.Site 4) (1 : Lattice.Site 4) (2 : Lattice.Site 4)
        modes))
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [actualFourSitePositiveModes_projectorMinor_ne_zero_ae]
      with triple hbase
    intro hzero
    have hminor :=
      actualFourSite_projectorMinor_ne_zero_of_allDistinct_of_avoidsLast
        modes hdistinct havoids triple hbase
    apply hminor
    simpa [actualThreeMassProjectorMinorZeroSet,
      actualThreeMassProjectorMinorMagnitude] using hzero
  · push Not at havoids
    obtain ⟨r, hr⟩ := havoids
    have hweight :
        actualThreeMassAllDistinctTupleWeight frozenUnitMassFour
          (0 : Lattice.Site 4) (1 : Lattice.Site 4) (2 : Lattice.Site 4)
          modes = fun _triple => 0 := by
      funext triple
      have hnotPositive : ¬ IsPositiveOrderedTriple
          (threeMassSiteConfig frozenUnitMassFour
            (0 : Lattice.Site 4) (1 : Lattice.Site 4)
            (2 : Lattice.Site 4) triple) modes := by
        intro hpositive
        have hmodePositive := hpositive r
        rw [mem_orderedPositiveModeIndices_iff] at hmodePositive
        rw [hr] at hmodePositive
        exact ((orderedModeFrequency_pos_iff_ne_last_unconditional
          _ _).mp hmodePositive) rfl
      simp [actualThreeMassAllDistinctTupleWeight,
        actualThreeMassPositiveTupleWeight, hdistinct, hnotPositive]
    rw [hweight]
    simp

/-- Complete finite-volume result: the genuine collision-weighted
projector-minor distribution for the frozen-unit four-site iid model has no
atom at zero. -/
theorem actualFourSite_collisionWeightedProjectorMinorDistribution_singleton_zero :
    actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution
        frozenUnitMassFour (0 : Lattice.Site 4) (1 : Lattice.Site 4)
          (2 : Lattice.Site 4) ({0} : Set Real) = 0 := by
  apply
    (actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution_singleton_zero_iff_allDistinct
      frozenUnitMassFour (0 : Lattice.Site 4) (1 : Lattice.Site 4)
        (2 : Lattice.Site 4)).2
  exact actualFourSite_modewise_collisionWeighted_projectorMinorZeroMass_eq_zero

/-- Hence the complete genuine four-site collision-weighted small-minor tail
vanishes at reciprocal-natural thresholds, with no zero-atom premise. -/
theorem tendsto_actualFourSite_collisionWeightedProjectorMinorBadLevel_zero :
    Tendsto
      (fun n : Nat =>
        actualThreeMassAllDistinctCollisionWeightedProjectorMinorBadLevel
          frozenUnitMassFour (0 : Lattice.Site 4) (1 : Lattice.Site 4)
            (2 : Lattice.Site 4) (1 / ((n : Real) + 1)))
      atTop (nhds 0) := by
  apply
    tendsto_actualThreeMassAllDistinctCollisionWeightedProjectorMinorBadLevel_zero_of_singleton
      frozenUnitMassFour
  · intro site
    norm_num [frozenUnitMassFour, massSupport, massLower, massUpper]
  · exact actualFourSite_collisionWeightedProjectorMinorDistribution_singleton_zero

end

end ArchonPhysics.ActualFourSiteCollisionWeightedMinorZeroAtom
