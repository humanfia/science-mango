import ArchonPhysics.ActualEightSiteNarrowPhysicalExactDecay
import ArchonPhysics.LocalCollisionMarkContinuity
import ArchonPhysics.FiniteMassLawOpenPatch

/-!
# A full-eight-IID positive weighted near-resonance patch

The unconditional narrow-path witness is a point of the full eight-coordinate
mass cube.  Continuity of the harmonic and dual matrices, ordered spectrum,
simple-spectrum projectors, and normalized collision weight makes all of its
strict properties stable under perturbing all eight masses.  Consequently,
every positive mismatch width contains an open event of strictly positive
eight-coordinate iid mass probability.

This remains a fixed-volume local statement.  It does not identify the local
projectors with modes of a larger coupled periodic chain.
-/

open scoped Matrix

namespace ArchonPhysics.ActualEightSiteFullIIDPositiveWeightedNearResonancePatch

open ArchonPhysics
open ArchonPhysics.ActualEightSiteExactDecayIVTBridge
open ArchonPhysics.ActualEightSiteNarrowPhysicalExactDecay
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
open ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison
open Filter Set

noncomputable section

/-- Coordinatewise interior of the eight-fold iid mass support. -/
def fullEightMassSupportInterior : Set EightMassVector :=
  {x | ∀ i, x i ∈ Ioo massLower massUpper}

theorem continuous_fullEightBondMatrix :
    Continuous fullEightBondMatrix := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_fullEightBondMatrix_apply i j

theorem continuous_fullEightDualHarmonic :
    Continuous fullEightDualHarmonic := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold dualMassWeightedHarmonicMatrix
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply continuous_finsetSum Finset.univ
  intro k _hk
  exact (continuous_fullEightBondMatrix_apply i k).mul
    (continuous_fullEightBondMatrix_apply j k)

theorem continuous_actualEightSiteSelectedMismatch :
    Continuous actualEightSiteSelectedMismatch := by
  unfold actualEightSiteSelectedMismatch
  exact (continuous_orderedPhaseMismatch actualEightSiteDecaySign
    actualEightSiteDecayModes).comp continuous_fullEightHarmonic

theorem eventually_simple_fullEightHarmonic
    {x : EightMassVector}
    (hsimple : SimpleOrderedSpectrum (fullEightHarmonic x)) :
    ∀ᶠ y in nhds x, SimpleOrderedSpectrum (fullEightHarmonic y) := by
  unfold SimpleOrderedSpectrum
  change ∀ᶠ y in nhds x, ∀ i j,
    orderedEigenvalue (fullEightHarmonic y) i =
      orderedEigenvalue (fullEightHarmonic y) j → i = j
  rw [eventually_all]
  intro i
  rw [eventually_all]
  intro j
  by_cases hij : i = j
  · subst j
    exact Filter.Eventually.of_forall fun _ _ => rfl
  · have hne : orderedEigenvalue (fullEightHarmonic x) i ≠
        orderedEigenvalue (fullEightHarmonic x) j := hsimple.ne hij
    have hi : ContinuousAt
        (fun y => orderedEigenvalue (fullEightHarmonic y) i) x :=
      ((continuous_orderedEigenvalue i).comp continuous_fullEightHarmonic).continuousAt
    have hj : ContinuousAt
        (fun y => orderedEigenvalue (fullEightHarmonic y) j) x :=
      ((continuous_orderedEigenvalue j).comp continuous_fullEightHarmonic).continuousAt
    filter_upwards [(hi.ne_iff_eventually_ne hj).1 hne] with y hnear
    exact fun heq => (hnear heq).elim

theorem continuousAt_actualEightSiteSelectedProjectorMinor
    {x : EightMassVector}
    (hsimpleDual : SimpleOrderedSpectrum (fullEightDualHarmonic x)) :
    ContinuousAt actualEightSiteSelectedProjectorMinor x := by
  unfold actualEightSiteSelectedProjectorMinor
  simp only [Matrix.det_apply']
  apply tendsto_finsetSum Finset.univ
  intro permutation _hpermutation
  apply ContinuousAt.mul continuousAt_const
  apply tendsto_finsetProd Finset.univ
  intro r _hr
  unfold orderedProjectorWeightMatrix
  simp only [dotProduct, Matrix.mulVec]
  apply tendsto_finsetSum Finset.univ
  intro i _hi
  apply ContinuousAt.mul continuousAt_const
  apply tendsto_finsetSum Finset.univ
  intro j _hj
  apply ContinuousAt.mul
  · exact (continuousAt_orderedModeProjector_apply
      (fullEightDualHarmonic x) hsimpleDual
      (actualEightSiteDecayModes (permutation r)) i j).comp_of_eq
        continuous_fullEightDualHarmonic.continuousAt rfl
  · exact continuousAt_const

/-- A full eight-coordinate sample is good when it lies in the iid-support
interior and retains every strict physical property of the exact witness. -/
def fullEightPhysicalWeightedNearResonanceWithProjectorMinor
    (epsilon : Real) : Set EightMassVector :=
  {x |
    x ∈ fullEightMassSupportInterior ∧
    SimpleOrderedSpectrum (fullEightHarmonic x) ∧
    (∀ r, 0 < orderedEigenvalue
      (fullEightHarmonic x) (actualEightSiteDecayModes r)) ∧
    |actualEightSiteSelectedMismatch x| < epsilon ∧
    0 < actualEightSiteSelectedInteractionWeight x ∧
    actualEightSiteSelectedProjectorMinor x ≠ 0}

theorem isOpen_fullEightMassSupportInterior :
    IsOpen fullEightMassSupportInterior := by
  rw [show fullEightMassSupportInterior =
      ⋂ i, {x : EightMassVector | x i ∈ Ioo massLower massUpper} by
    ext x
    simp [fullEightMassSupportInterior]]
  exact isOpen_iInter_of_finite fun i ↦
    isOpen_Ioo.preimage (continuous_apply i)

/-- Every positive mismatch width contains an open, positive-probability
eight-coordinate iid patch with positive physical collision weight and the
certified nonzero projector minor. -/
theorem exists_positive_finiteMassLaw_fullEight_physicalWeightedNearResonancePatch
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ patch : Set EightMassVector,
      IsOpen patch ∧
      0 < finiteMassLaw 8 patch ∧
      patch ⊆ fullEightPhysicalWeightedNearResonanceWithProjectorMinor epsilon := by
  obtain ⟨t, _ht, hinterior, hmismatch, hsimple, hweight, hprojector, _hgram⟩ :=
    exists_actualEightSite_narrow_physicalExactDecay
  let x : EightMassVector := actualEightSiteRationalMassPath t
  have hxInterior : x ∈ fullEightMassSupportInterior := by
    exact hinterior
  have hsimpleFull : SimpleOrderedSpectrum (fullEightHarmonic x) := by
    simpa [x] using hsimple
  have henergyFull : ∀ r, 0 < orderedEigenvalue
      (fullEightHarmonic x) (actualEightSiteDecayModes r) := by
    intro r
    exact Real.sqrt_pos.1 (actualEightSiteSelectedFrequency_pos x r)
  have hmismatchFull : |actualEightSiteSelectedMismatch x| < epsilon := by
    have hzero : actualEightSiteSelectedMismatch x = 0 := by
      simpa [x, actualEightSiteRationalPathMismatch] using hmismatch
    rw [hzero, abs_zero]
    exact hepsilon
  have hweightFull : 0 < actualEightSiteSelectedInteractionWeight x := by
    simpa [x] using hweight
  have hprojectorFull : actualEightSiteSelectedProjectorMinor x ≠ 0 := by
    simpa [x] using hprojector
  have hsimpleDual : SimpleOrderedSpectrum (fullEightDualHarmonic x) := by
    intro i j hij
    apply hsimpleFull
    simpa only [fullEightHarmonic, fullEightDualHarmonic,
      orderedEigenvalue_harmonic_eq_dual] using hij
  have hfrequencyFull : PositiveOrderedModeTuple
      (fullEightHarmonic x) actualEightSiteDecayModes := by
    intro r
    exact actualEightSiteSelectedFrequency_pos x r
  have hpair : Continuous fun y : EightMassVector ↦
      (fullEightBondMatrix y, fullEightHarmonic y) :=
    continuous_fullEightBondMatrix.prodMk continuous_fullEightHarmonic
  have hweightEventually :
      ∀ᶠ y in nhds x, 0 < actualEightSiteSelectedInteractionWeight y := by
    have hgeneric :=
      (continuousAt_orderedNormalizedInteractionWeight
        (fullEightBondMatrix x) (fullEightHarmonic x) hsimpleFull
        actualEightSiteDecayModes hfrequencyFull).eventually
          (eventually_gt_nhds hweightFull)
    exact hpair.continuousAt hgeneric
  have hprojectorEventually :
      ∀ᶠ y in nhds x, actualEightSiteSelectedProjectorMinor y ≠ 0 :=
    ((continuousAt_actualEightSiteSelectedProjectorMinor hsimpleDual).ne_iff_eventually_ne
      continuousAt_const).1 hprojectorFull
  have henergyEventually :
      ∀ᶠ y in nhds x, ∀ r, 0 < orderedEigenvalue
        (fullEightHarmonic y) (actualEightSiteDecayModes r) := by
    rw [eventually_all]
    intro r
    exact (((continuous_orderedEigenvalue (actualEightSiteDecayModes r)).comp
      continuous_fullEightHarmonic).continuousAt).eventually
        (eventually_gt_nhds (henergyFull r))
  have hgood :
      fullEightPhysicalWeightedNearResonanceWithProjectorMinor epsilon ∈ nhds x := by
    filter_upwards [
      isOpen_fullEightMassSupportInterior.mem_nhds hxInterior,
      eventually_simple_fullEightHarmonic hsimpleFull,
      henergyEventually,
      continuous_actualEightSiteSelectedMismatch.abs.continuousAt.eventually
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

end ArchonPhysics.ActualEightSiteFullIIDPositiveWeightedNearResonancePatch
