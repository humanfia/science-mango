import ArchonPhysics.R32CanonicalFreeBondConcentrationV3Final
import ArchonPhysics.MeasurableOrderedEigenframe
import ArchonPhysics.RandomMassOrderedPhyslibBasisIntertwining

/-!
# Measurable signed-frame R32 free-bond events, V2

The original normalized edge frame is built from Mathlib's noncomputable
Hermitian `eigenvectorBasis`.  Its signs are harmless at fixed mass but are
not known to depend measurably on mass.  This module uses the project's
globally measurable first-positive-pivot signed ordered eigenvector instead.
On simple spectrum the new coefficient differs from the original coefficient
only by a sign, so the coefficient-square and quenched variance bounds are
unchanged.

The canonical good event is finite-grid defined and hence genuinely Borel.
A separate deterministic time-net lemma upgrades it to a complete interval.
This avoids claiming measurability of an uncountable existential projection.
-/

open scoped BigOperators Matrix

namespace ArchonPhysics.R32SignedFreeBondMeasurabilityV3Final

open ArchonPhysics
open ArchonPhysics.HarmonicModes
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.MeasurableHarmonicData
open ArchonPhysics.MeasurableOrderedEigenframe
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.R32CanonicalFreeBondConcentrationV3Final
open ArchonPhysics.R32FrozenBondCoefficientBoundV2
open ArchonPhysics.R32FrozenEnergyDilution
open ArchonPhysics.R32HaarScalarTailCleanV4
open ArchonPhysics.RandomMassOrderedPhyslibBasisIntertwining
open MeasureTheory Set

noncomputable section

/-! ## Signed normalized edge frame -/

/-- Incidence coordinate of the globally measurable signed ordered vector. -/
def signedOrderedRawEdgeMode {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mode : HarmonicOrderedModeIndex N) (bond : Lattice.Site N) : Real :=
  Matrix.mulVec (massWeightedDifferenceMatrix m)
    (signedOrderedEigenvector (harmonicHermitian m) mode) bond

/-- Complete normalized signed edge frame, with the deterministic constant
edge vector in the translation slot. -/
def signedNormalizedEdgeFrame {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mode : HarmonicOrderedModeIndex N) (bond : Lattice.Site N) : Real :=
  if mode = lastOrderedIndex (ι := Lattice.Site N) then
    constantEdgeMode bond
  else
    signedOrderedRawEdgeMode m mode bond /
      orderedModeFrequency (harmonicHermitian m) mode

/-- Frozen R32 modal radius in the measurable signed edge frame. -/
def signedFrozenBondCoefficient {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (bond : Lattice.Site N)
    (mode : HarmonicOrderedModeIndex N) : Real :=
  Real.sqrt (2 * frozenTwoBandEnergy N mode) *
    signedNormalizedEdgeFrame m mode bond

theorem measurable_signedOrderedRawEdgeMode
    {Omega : Type*} [MeasurableSpace Omega]
    {N : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (hmass : ∀ site, Measurable fun omega ↦ (massSample omega).mass site)
    (mode : HarmonicOrderedModeIndex N) (bond : Lattice.Site N) :
    Measurable fun omega ↦
      signedOrderedRawEdgeMode (massSample omega) mode bond := by
  have hB := measurable_massWeightedDifferenceMatrix_of_coordinate
    massSample hmass
  have hA : Measurable fun omega ↦ harmonicHermitian (massSample omega) := by
    apply Measurable.subtype_mk
    exact measurable_massWeightedHarmonicMatrix_of_coordinate massSample hmass
  have hv := measurable_signedOrderedEigenvector
    (fun omega ↦ harmonicHermitian (massSample omega)) hA mode
  unfold signedOrderedRawEdgeMode Matrix.mulVec dotProduct
  apply Finset.measurable_sum
  intro site _hsite
  exact ((measurable_pi_apply site).comp
      ((measurable_pi_apply bond).comp hB)).mul
    ((measurable_pi_apply site).comp hv)

theorem measurable_signedNormalizedEdgeFrame
    {Omega : Type*} [MeasurableSpace Omega]
    {N : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (hmass : ∀ site, Measurable fun omega ↦ (massSample omega).mass site)
    (mode : HarmonicOrderedModeIndex N) (bond : Lattice.Site N) :
    Measurable fun omega ↦
      signedNormalizedEdgeFrame (massSample omega) mode bond := by
  by_cases hmode : mode = lastOrderedIndex (ι := Lattice.Site N)
  · simp [signedNormalizedEdgeFrame, hmode]
  · have hA : Measurable fun omega ↦
        harmonicHermitian (massSample omega) := by
      apply Measurable.subtype_mk
      exact measurable_massWeightedHarmonicMatrix_of_coordinate massSample hmass
    have hfrequency : Measurable fun omega ↦
        orderedModeFrequency (harmonicHermitian (massSample omega)) mode :=
      (measurable_orderedModeFrequencies_unconditional
        (fun omega ↦ harmonicHermitian (massSample omega)) hA).eval
    simp only [signedNormalizedEdgeFrame, if_neg hmode]
    change Measurable
      ((fun omega ↦ signedOrderedRawEdgeMode
          (massSample omega) mode bond) /
        (fun omega ↦ orderedModeFrequency
          (harmonicHermitian (massSample omega)) mode))
    exact (measurable_signedOrderedRawEdgeMode
      massSample hmass mode bond).div hfrequency

theorem measurable_signedFrozenBondCoefficient
    {Omega : Type*} [MeasurableSpace Omega]
    {N : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (hmass : ∀ site, Measurable fun omega ↦ (massSample omega).mass site)
    (bond : Lattice.Site N) (mode : HarmonicOrderedModeIndex N) :
    Measurable fun omega ↦
      signedFrozenBondCoefficient (massSample omega) bond mode := by
  exact measurable_const.mul
    (measurable_signedNormalizedEdgeFrame massSample hmass mode bond)

/-! ## Equality of coefficient squares on simple spectrum -/

theorem signedOrderedRawEdgeMode_eq_orientation_mul
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (mode : HarmonicOrderedModeIndex N) (bond : Lattice.Site N) :
    signedOrderedRawEdgeMode m mode bond =
      orderedPhyslibOrientation m mode * orderedRawEdgeMode m mode bond := by
  unfold signedOrderedRawEdgeMode orderedRawEdgeMode orderedSiteMode
  rw [signedOrderedEigenvector_eq_orientation_smul_normalModeBasis
    m hsimple mode, Matrix.mulVec_smul]
  rfl

theorem signedFrozenBondCoefficient_sq_eq_original
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (bond : Lattice.Site N) (mode : HarmonicOrderedModeIndex N) :
    signedFrozenBondCoefficient m bond mode ^ 2 =
      r32FrozenBondCoefficient m bond mode ^ 2 := by
  by_cases hmode : mode = lastOrderedIndex (ι := Lattice.Site N)
  · subst mode
    simp [signedFrozenBondCoefficient, r32FrozenBondCoefficient,
      frozenTwoBandEnergy]
  · have horientation := orderedPhyslibOrientation_sq m hsimple mode
    unfold signedFrozenBondCoefficient r32FrozenBondCoefficient
      signedNormalizedEdgeFrame harmonicNormalizedEdgeFrame
    simp only [if_neg hmode]
    rw [signedOrderedRawEdgeMode_eq_orientation_mul
      m hsimple mode bond]
    calc
      (Real.sqrt (2 * frozenTwoBandEnergy N mode) *
          (orderedPhyslibOrientation m mode *
            orderedRawEdgeMode m mode bond /
            orderedModeFrequency (harmonicHermitian m) mode)) ^ 2 =
          orderedPhyslibOrientation m mode ^ 2 *
            (Real.sqrt (2 * frozenTwoBandEnergy N mode) *
              (orderedRawEdgeMode m mode bond /
                orderedModeFrequency (harmonicHermitian m) mode)) ^ 2 := by
        ring
      _ = _ := by rw [horientation, one_mul]

theorem sum_sq_signedFrozenBondCoefficient_le_six_div_pred
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (bond : Lattice.Site N) :
    (∑ mode : HarmonicOrderedModeIndex N,
      signedFrozenBondCoefficient m bond mode ^ 2) ≤
      6 / (((N - 1 : Nat) : Real)) := by
  calc
    (∑ mode : HarmonicOrderedModeIndex N,
        signedFrozenBondCoefficient m bond mode ^ 2) =
        ∑ mode : HarmonicOrderedModeIndex N,
          r32FrozenBondCoefficient m bond mode ^ 2 := by
      apply Finset.sum_congr rfl
      intro mode _hmode
      exact signedFrozenBondCoefficient_sq_eq_original
        m hsimple bond mode
    _ ≤ 6 / (((N - 1 : Nat) : Real)) :=
      sum_sq_r32FrozenBondCoefficient_le_six_div_pred
        hN m hsimple bond

/-! ## Jointly measurable fixed-time signed field -/

def signedHaarBondField {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (bond : Lattice.Site N)
    (phase : HarmonicOrderedModeIndex N → UnitAddCircle)
    (time : Real) : Real :=
  fixedTimeHaarScalarSum
    (signedFrozenBondCoefficient m bond)
    (orderedModeFrequency (harmonicHermitian m)) time phase

theorem measurable_signedHaarBondField
    {Omega : Type*} [MeasurableSpace Omega]
    {N : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (hmass : ∀ site, Measurable fun omega ↦ (massSample omega).mass site)
    (phaseSample : Omega → HarmonicOrderedModeIndex N → UnitAddCircle)
    (hphase : Measurable phaseSample)
    (bond : Lattice.Site N) (time : Real) :
    Measurable fun omega ↦
      signedHaarBondField (massSample omega) bond
        (phaseSample omega) time := by
  have hA : Measurable fun omega ↦ harmonicHermitian (massSample omega) := by
    apply Measurable.subtype_mk
    exact measurable_massWeightedHarmonicMatrix_of_coordinate massSample hmass
  have hfrequency : ∀ mode : HarmonicOrderedModeIndex N,
      Measurable fun omega ↦
        orderedModeFrequency (harmonicHermitian (massSample omega)) mode :=
    fun mode ↦ (measurable_pi_apply mode).comp
      (measurable_orderedModeFrequencies_unconditional
        (fun omega ↦ harmonicHermitian (massSample omega)) hA)
  unfold signedHaarBondField fixedTimeHaarScalarSum
  apply Finset.measurable_sum
  intro mode _hmode
  apply (measurable_signedFrozenBondCoefficient
    massSample hmass bond mode).mul
  have hphaseCoordinate : Measurable fun omega ↦
      phaseSample omega mode := (measurable_pi_apply mode).comp hphase
  unfold fixedTimeHaarCarrier fixedTimePhaseAdvance
  fun_prop

/-! ## Canonical mass restriction and simple-spectrum guard -/

def rawCanonicalFrozenMass {N : Nat} [NeZero N]
    (mass : RandomEnsemble.RawMassSequence) :
    Lattice.PositiveMassConfig N :=
  canonicalIIDMassPhaseEnsemble.restrictPositiveMass
    (mass, fun _ ↦ 0)

theorem measurable_rawCanonicalFrozenMass_coordinate
    {N : Nat} [NeZero N] (site : Lattice.Site N) :
    Measurable fun mass : RandomEnsemble.RawMassSequence ↦
      (rawCanonicalFrozenMass (N := N) mass).mass site := by
  change Measurable fun mass : RandomEnsemble.RawMassSequence ↦
    RandomEnsemble.clippedMass (mass site.val)
  exact RandomEnsemble.measurable_clippedMass.comp
    (measurable_pi_apply site.val)

theorem measurableSet_simpleOrderedSpectrum
    {Omega ι : Type*} [MeasurableSpace Omega]
    [Fintype ι] [DecidableEq ι]
    (sample : Omega → HermitianMatrix ι) (hsample : Measurable sample) :
    MeasurableSet {omega | SimpleOrderedSpectrum (sample omega)} := by
  let eigenvalue : Fin (Fintype.card ι) → Omega → Real :=
    fun mode omega ↦ orderedEigenvalue (sample omega) mode
  have heigenvalue : ∀ mode, Measurable (eigenvalue mode) :=
    fun mode ↦ (measurable_pi_apply mode).comp
      (measurable_orderedEigenvalues_unconditional sample hsample)
  have heq : {omega | SimpleOrderedSpectrum (sample omega)} =
      ⋂ mode, ⋂ other, ⋂ (_h : mode ≠ other),
        {omega | eigenvalue mode omega ≠ eigenvalue other omega} := by
    ext omega
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hinjective mode other hne
      exact fun hequal ↦ hne (hinjective hequal)
    · intro hpair mode other hequal
      by_contra hne
      exact hpair mode other hne hequal
  rw [heq]
  exact MeasurableSet.iInter fun mode ↦
    MeasurableSet.iInter fun other ↦
      MeasurableSet.iInter fun _hne ↦
        (measurableSet_eq_fun
          (heigenvalue mode) (heigenvalue other)).compl

theorem measurableSet_canonicalSimpleOrderedSpectrum
    {N : Nat} [NeZero N] :
    MeasurableSet {sample : RandomEnsemble.SampleSpace |
      SimpleOrderedSpectrum
        (harmonicHermitian
          (rawCanonicalFrozenMass (N := N) sample.1))} := by
  let massSample : RandomEnsemble.SampleSpace →
      Lattice.PositiveMassConfig N := fun sample ↦
    rawCanonicalFrozenMass sample.1
  have hmass : ∀ site, Measurable fun sample ↦
      (massSample sample).mass site := fun site ↦
    (measurable_rawCanonicalFrozenMass_coordinate site).comp measurable_fst
  have hA : Measurable fun sample ↦
      harmonicHermitian (massSample sample) := by
    apply Measurable.subtype_mk
    exact measurable_massWeightedHarmonicMatrix_of_coordinate massSample hmass
  exact measurableSet_simpleOrderedSpectrum _ hA

theorem measurable_canonicalSignedHaarBondField
    {N : Nat} [NeZero N]
    (bond : Lattice.Site N) (time : Real) :
    Measurable fun sample : RandomEnsemble.SampleSpace ↦
      signedHaarBondField
        (rawCanonicalFrozenMass (N := N) sample.1) bond
        (orderedPhaseBlockFromSequence (N := N) sample.2) time := by
  let massSample : RandomEnsemble.SampleSpace →
      Lattice.PositiveMassConfig N := fun sample ↦
    rawCanonicalFrozenMass sample.1
  let phaseSample : RandomEnsemble.SampleSpace →
      HarmonicOrderedModeIndex N → UnitAddCircle := fun sample ↦
    orderedPhaseBlockFromSequence sample.2
  have hmass : ∀ site, Measurable fun sample ↦
      (massSample sample).mass site := fun site ↦
    (measurable_rawCanonicalFrozenMass_coordinate site).comp measurable_fst
  have hphase : Measurable phaseSample :=
    measurable_orderedPhaseBlockFromSequence.comp measurable_snd
  exact measurable_signedHaarBondField massSample hmass
    phaseSample hphase bond time

/-! ## Generic and concrete finite-grid Borel events -/

def canonicalSignedSimpleGridBad
    {N : Nat} [NeZero N] {K : Type*} [Fintype K]
    (grid : K → Real) (g : Real) : Set RandomEnsemble.SampleSpace :=
  {sample |
    SimpleOrderedSpectrum
      (harmonicHermitian
        (rawCanonicalFrozenMass (N := N) sample.1))} ∩
  ⋃ index : Lattice.Site N × K,
    {sample |
      |signedHaarBondField
        (rawCanonicalFrozenMass (N := N) sample.1) index.1
        (orderedPhaseBlockFromSequence (N := N) sample.2)
        (grid index.2)| > g ^ 4 / 2}

def canonicalSignedGridGood
    {N : Nat} [NeZero N] {K : Type*} [Fintype K]
    (grid : K → Real) (g : Real) : Set RandomEnsemble.SampleSpace :=
  {sample |
    SimpleOrderedSpectrum
      (harmonicHermitian
        (rawCanonicalFrozenMass (N := N) sample.1))} ∩
    (canonicalSignedSimpleGridBad (N := N) grid g)ᶜ

theorem measurableSet_canonicalSignedSimpleGridBad
    {N : Nat} [NeZero N] {K : Type*} [Fintype K]
    (grid : K → Real) (g : Real) :
    MeasurableSet (canonicalSignedSimpleGridBad (N := N) grid g) := by
  apply measurableSet_canonicalSimpleOrderedSpectrum.inter
  apply MeasurableSet.iUnion
  intro index
  exact measurableSet_lt measurable_const
    (measurable_canonicalSignedHaarBondField
      (N := N) index.1 (grid index.2)).abs

theorem measurableSet_canonicalSignedGridGood
    {N : Nat} [NeZero N] {K : Type*} [Fintype K]
    (grid : K → Real) (g : Real) :
    MeasurableSet (canonicalSignedGridGood (N := N) grid g) := by
  exact measurableSet_canonicalSimpleOrderedSpectrum.inter
    (measurableSet_canonicalSignedSimpleGridBad
      (N := N) grid g).compl

/-- Concrete V2 bad event on the rescaled kinetic time grid. -/
def canonicalSignedSimpleFreeGridBad {N : Nat} [NeZero N]
    (T g : Real) : Set RandomEnsemble.SampleSpace :=
  canonicalSignedSimpleGridBad (N := N) (freeTimeGrid T g) g

/-- Concrete V2 finite-grid good event. -/
def canonicalSignedFreeGridGood {N : Nat} [NeZero N]
    (T g : Real) : Set RandomEnsemble.SampleSpace :=
  canonicalSignedGridGood (N := N) (freeTimeGrid T g) g

theorem measurableSet_canonicalSignedSimpleFreeGridBad
    {N : Nat} [NeZero N] (T g : Real) :
    MeasurableSet (canonicalSignedSimpleFreeGridBad (N := N) T g) :=
  measurableSet_canonicalSignedSimpleGridBad (freeTimeGrid T g) g

theorem measurableSet_canonicalSignedFreeGridGood
    {N : Nat} [NeZero N] (T g : Real) :
    MeasurableSet (canonicalSignedFreeGridGood (N := N) T g) :=
  measurableSet_canonicalSignedGridGood (freeTimeGrid T g) g

/-! ## Deterministic finite-grid to whole-window upgrade -/

theorem canonicalSignedGridGood_grid_bound
    {N : Nat} [NeZero N] {K : Type*} [Fintype K]
    (grid : K → Real) (g : Real)
    {sample : RandomEnsemble.SampleSpace}
    (hgood : sample ∈ canonicalSignedGridGood (N := N) grid g)
    (bond : Lattice.Site N) (index : K) :
    |signedHaarBondField
      (rawCanonicalFrozenMass (N := N) sample.1) bond
      (orderedPhaseBlockFromSequence (N := N) sample.2)
      (grid index)| ≤ g ^ 4 / 2 := by
  by_contra hnot
  have hbad : sample ∈ canonicalSignedSimpleGridBad (N := N) grid g := by
    refine ⟨hgood.1, ?_⟩
    exact Set.mem_iUnion_of_mem (bond, index) (lt_of_not_ge hnot)
  exact hgood.2 hbad

theorem canonicalSignedGridGood_implies_window_bound
    {N : Nat} [NeZero N] {K : Type*} [Fintype K]
    (grid : K → Real) (g horizon mesh lipschitz : Real)
    (hnet : ∀ time ∈ Icc (0 : Real) horizon,
      ∃ index, |time - grid index| ≤ mesh)
    (hlipschitz_nonneg : 0 ≤ lipschitz)
    (hslack : lipschitz * mesh ≤ g ^ 4 / 2)
    {sample : RandomEnsemble.SampleSpace}
    (hgood : sample ∈ canonicalSignedGridGood (N := N) grid g)
    (hlipschitz : ∀ (bond : Lattice.Site N) (s t : Real),
      |signedHaarBondField
          (rawCanonicalFrozenMass (N := N) sample.1) bond
          (orderedPhaseBlockFromSequence (N := N) sample.2) t -
        signedHaarBondField
          (rawCanonicalFrozenMass (N := N) sample.1) bond
          (orderedPhaseBlockFromSequence (N := N) sample.2) s| ≤
        lipschitz * |t - s|)
    (bond : Lattice.Site N) (time : Real)
    (htime : time ∈ Icc (0 : Real) horizon) :
    |signedHaarBondField
      (rawCanonicalFrozenMass (N := N) sample.1) bond
      (orderedPhaseBlockFromSequence (N := N) sample.2) time| ≤
      g ^ 4 := by
  obtain ⟨index, hindex⟩ := hnet time htime
  have hgrid := canonicalSignedGridGood_grid_bound
    grid g hgood bond index
  have hvariation := hlipschitz bond (grid index) time
  have hvariation' :
      |signedHaarBondField
          (rawCanonicalFrozenMass (N := N) sample.1) bond
          (orderedPhaseBlockFromSequence (N := N) sample.2) time -
        signedHaarBondField
          (rawCanonicalFrozenMass (N := N) sample.1) bond
          (orderedPhaseBlockFromSequence (N := N) sample.2)
          (grid index)| ≤ g ^ 4 / 2 := by
    exact hvariation.trans
      ((mul_le_mul_of_nonneg_left hindex hlipschitz_nonneg).trans hslack)
  calc
    |signedHaarBondField
        (rawCanonicalFrozenMass (N := N) sample.1) bond
        (orderedPhaseBlockFromSequence (N := N) sample.2) time| ≤
        |signedHaarBondField
            (rawCanonicalFrozenMass (N := N) sample.1) bond
            (orderedPhaseBlockFromSequence (N := N) sample.2) time -
          signedHaarBondField
            (rawCanonicalFrozenMass (N := N) sample.1) bond
            (orderedPhaseBlockFromSequence (N := N) sample.2)
            (grid index)| +
        |signedHaarBondField
          (rawCanonicalFrozenMass (N := N) sample.1) bond
          (orderedPhaseBlockFromSequence (N := N) sample.2)
          (grid index)| := by
      calc
        |_| = |(signedHaarBondField
                  (rawCanonicalFrozenMass (N := N) sample.1) bond
                  (orderedPhaseBlockFromSequence (N := N) sample.2) time -
                signedHaarBondField
                  (rawCanonicalFrozenMass (N := N) sample.1) bond
                  (orderedPhaseBlockFromSequence (N := N) sample.2)
                  (grid index)) +
                signedHaarBondField
                  (rawCanonicalFrozenMass (N := N) sample.1) bond
                  (orderedPhaseBlockFromSequence (N := N) sample.2)
                  (grid index)| := by congr 1 <;> ring
        _ ≤ _ := abs_add_le _ _
    _ ≤ g ^ 4 / 2 + g ^ 4 / 2 := add_le_add hvariation' hgrid
    _ = g ^ 4 := by ring

#print axioms measurableSet_canonicalSignedSimpleFreeGridBad
#print axioms measurableSet_canonicalSignedFreeGridGood
#print axioms canonicalSignedGridGood_implies_window_bound

end

end ArchonPhysics.R32SignedFreeBondMeasurabilityV3Final
