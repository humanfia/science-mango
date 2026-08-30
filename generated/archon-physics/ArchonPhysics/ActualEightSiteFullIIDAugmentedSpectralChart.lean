import ArchonPhysics.ActualEightSiteFullJointSpectralDifferentiability
import ArchonPhysics.ActualEightSiteExactAllDistinctLinearSmallBall
import ArchonPhysics.ParametricPartialJacobianAugmentedLocalChart

/-!
# A genuine full-eight-IID augmented spectral chart

The five unselected masses are retained as environment coordinates and the
three selected masses `(2,5,7)` are sent to the physical
`(child₁, child₂, mismatch)` chart.  At the certified exact resonance, the
partialDerivative derivative in those three selected directions is the already
certified nondegenerate Hellmann--Feynman Jacobian.  The general parametric
inverse-function bridge therefore gives an eight-dimensional local chart.

This is the non-circular geometric bridge needed before a full-eight iid
quantitative small-ball estimate: it derives environment stability from a
joint strict derivative and retains the environment coordinates exactly.
-/

open scoped Matrix Topology

namespace ArchonPhysics.ActualEightSiteFullIIDAugmentedSpectralChart

open ArchonPhysics
open ArchonPhysics.ActualEightSiteExactAllDistinctLinearSmallBall
open ArchonPhysics.ActualEightSiteExactDecayIVTBridge
open ArchonPhysics.ActualEightSiteFullIIDPositiveWeightedNearResonancePatch
open ArchonPhysics.ActualEightSiteFullJointSpectralDifferentiability
open ArchonPhysics.ActualEightSiteNarrowPhysicalExactDecay
open ArchonPhysics.ActualThreeMassHellmannFeynmanJacobian
open ArchonPhysics.ActualThreeMassLiftedSimpleEigenvalueDifferentiability
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.MarkedEmpiricalResonanceTransfer
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.ParametricPartialJacobianAugmentedLocalChart
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Filter Set

noncomputable section

/-- The five masses outside the selected physical sites `(2,5,7)`. -/
abbrev EightMassEnvironment := Fin 5 → Real

/-- A coordinate permutation separating the five environment masses from
the selected three masses. -/
def splitEightMassLinearEquiv :
    EightMassVector ≃ₗ[Real] EightMassEnvironment × MassTriple where
  toFun x := (![x 0, x 1, x 3, x 4, x 6], ((x 2, x 5), x 7))
  invFun p := ![p.1 0, p.1 1, p.2.1.1, p.1 2,
    p.1 3, p.2.1.2, p.1 4, p.2.2]
  map_add' x y := by
    apply Prod.ext
    · ext i
      fin_cases i <;> rfl
    · apply Prod.ext
      · apply Prod.ext <;> rfl
      · rfl
  map_smul' c x := by
    apply Prod.ext
    · ext i
      fin_cases i <;> rfl
    · apply Prod.ext
      · apply Prod.ext <;> rfl
      · rfl
  left_inv x := by ext i <;> fin_cases i <;> rfl
  right_inv p := by
    apply Prod.ext
    · ext i
      fin_cases i <;> rfl
    · apply Prod.ext
      · apply Prod.ext <;> rfl
      · rfl

/-- The continuous linear version of the coordinate split. -/
def splitEightMass :
    EightMassVector ≃L[Real] EightMassEnvironment × MassTriple :=
  splitEightMassLinearEquiv.toContinuousLinearEquiv

@[simp] theorem splitEightMass_apply (x : EightMassVector) :
    splitEightMass x =
      (![x 0, x 1, x 3, x 4, x 6], ((x 2, x 5), x 7)) := rfl

@[simp] theorem splitEightMass_symm_apply
    (p : EightMassEnvironment × MassTriple) :
    splitEightMass.symm p = ![p.1 0, p.1 1, p.2.1.1, p.1 2,
      p.1 3, p.2.1.2, p.1 4, p.2.2] := rfl

/-- The actual full-eight lifted chart, expressed as a family over the five
unchanged environment coordinates. -/
def fullEightLiftedFamily
    (p : EightMassEnvironment × MassTriple) : MassTriple :=
  actualEightSiteFullLiftedFrequencyChart (splitEightMass.symm p)

/-- Holding the five environment coordinates fixed and varying the selected
triple is exactly the genuine `threeMassSiteConfig` construction. -/
theorem fullEightMassConfig_split_fixed_environment
    {x : EightMassVector} (hx : x ∈ fullEightMassSupportInterior)
    (triple : MassTriple) :
    fullEightMassConfig
        (splitEightMass.symm ((splitEightMass x).1, triple)) =
      threeMassSiteConfig (fullEightMassConfig x)
        (actualEightSiteSelectedSites 0)
        (actualEightSiteSelectedSites 1)
        (actualEightSiteSelectedSites 2) triple := by
  rw [Lattice.PositiveMassConfig.mk.injEq]
  funext site
  generalize hindex : siteEquivFin 8 site = index
  have hsite : site = (siteEquivFin 8).symm index := by
    rw [← hindex]
    simp
  rw [hsite]
  clear hsite hindex site
  fin_cases index <;>
    simp (config := { decide := true })
      [splitEightMass, splitEightMassLinearEquiv, fullEightMassConfig,
        threeMassSiteConfig, actualEightSiteSelectedSites,
        val_siteEquivFin_symm, clippedMass_eq_self,
        show x 0 ∈ massSupport from ⟨(hx 0).1.le, (hx 0).2.le⟩,
        show x 1 ∈ massSupport from ⟨(hx 1).1.le, (hx 1).2.le⟩,
        show x 3 ∈ massSupport from ⟨(hx 3).1.le, (hx 3).2.le⟩,
        show x 4 ∈ massSupport from ⟨(hx 4).1.le, (hx 4).2.le⟩,
        show x 6 ∈ massSupport from ⟨(hx 6).1.le, (hx 6).2.le⟩]

/-- Consequently, the selected-mass slice of the full-eight chart is
definitionally the actual three-mass lifted spectral chart. -/
theorem fullEightLiftedFamily_fixed_environment
    {x : EightMassVector} (hx : x ∈ fullEightMassSupportInterior)
    (triple : MassTriple) :
    fullEightLiftedFamily ((splitEightMass x).1, triple) =
      actualThreeMassLiftedFrequencyChart (fullEightMassConfig x)
        (actualEightSiteSelectedSites 0)
        (actualEightSiteSelectedSites 1)
        (actualEightSiteSelectedSites 2)
        actualEightSiteDecaySign actualEightSiteDecayModes triple := by
  unfold fullEightLiftedFamily actualEightSiteFullLiftedFrequencyChart
    actualThreeMassLiftedFrequencyChart actualEightSiteSelectedMismatch
    orderedPhaseMismatch
  rw [show fullEightHarmonic
      (splitEightMass.symm ((splitEightMass x).1, triple)) =
      threeMassHarmonicHermitian (fullEightMassConfig x)
        (actualEightSiteSelectedSites 0)
        (actualEightSiteSelectedSites 1)
        (actualEightSiteSelectedSites 2) triple by
    unfold fullEightHarmonic threeMassHarmonicHermitian
    rw [fullEightMassConfig_split_fixed_environment hx triple]]

/-- At the certified exact resonance, the joint full-eight family has a
strict derivative whose selected three-mass partialDerivative derivative is
invertible.  The invertibility is derived from the actual projector minor;
it is not an added transversality assumption. -/
theorem exists_fullEightLiftedFamily_strictDerivative_partial_isInvertible :
    ∃ t ∈ Ioo ArchonPhysics.ActualEightSiteNarrowProjectorMinorBridge.actualEightSiteNarrowLower ArchonPhysics.ActualEightSiteNarrowProjectorMinorBridge.actualEightSiteNarrowUpper,
      let x := actualEightSiteRationalMassPath t
      ∃ derivative :
          (EightMassEnvironment × MassTriple) →L[Real] MassTriple,
        x ∈ fullEightMassSupportInterior ∧
          actualEightSiteSelectedMismatch x = 0 ∧
          HasStrictFDerivAt fullEightLiftedFamily derivative
            (splitEightMass x) ∧
          (derivative ∘L ContinuousLinearMap.inr Real
            EightMassEnvironment MassTriple).IsInvertible := by
  obtain ⟨t, ht, hinterior, hresonance, hsimple,
      _hweight, hminor, _hgram⟩ :=
    exists_actualEightSite_narrow_physicalExactDecay
  let x := actualEightSiteRationalMassPath t
  have hx : x ∈ fullEightMassSupportInterior := hinterior
  have hxresonance : actualEightSiteSelectedMismatch x = 0 := by
    simpa [x, actualEightSiteRationalPathMismatch] using hresonance
  have hsimpleFull : SimpleOrderedSpectrum (fullEightHarmonic x) := hsimple
  obtain ⟨Dfull, hDfull⟩ :=
    exists_hasStrictFDerivAt_actualEightSiteFullLiftedFrequencyChart
      hx hsimpleFull
  let derivative :
      (EightMassEnvironment × MassTriple) →L[Real] MassTriple :=
    Dfull ∘L splitEightMass.symm.toContinuousLinearMap
  have hfamily : HasStrictFDerivAt fullEightLiftedFamily derivative
      (splitEightMass x) := by
    change HasStrictFDerivAt
      (fun p => actualEightSiteFullLiftedFrequencyChart (splitEightMass.symm p))
      derivative (splitEightMass x)
    simpa [derivative, Function.comp_def] using
      hDfull.comp (splitEightMass x) splitEightMass.symm.hasStrictFDerivAt
  let partialDerivative : MassTriple →L[Real] MassTriple :=
    derivative ∘L ContinuousLinearMap.inr Real
      EightMassEnvironment MassTriple
  have hsliceRaw := hfamily.hasFDerivAt.comp (splitEightMass x).2
      (hasFDerivAt_prodMk_right (splitEightMass x).1
        (splitEightMass x).2)
  have hslice : HasFDerivAt
      (fun triple : MassTriple =>
        fullEightLiftedFamily ((splitEightMass x).1, triple))
      partialDerivative (splitEightMass x).2 := by
    change HasFDerivAt
      (fun triple : MassTriple =>
        fullEightLiftedFamily ((splitEightMass x).1, triple))
      partialDerivative (splitEightMass x).2 at hsliceRaw
    simpa [partialDerivative] using hsliceRaw
  have htriple : (splitEightMass x).2 ∈ interior iidMassTripleSupport := by
    simpa [x, splitEightMass, splitEightMassLinearEquiv,
      actualEightSiteSelectedMassTriple] using
      actualEightSiteSelectedMassTriple_mem_interior hinterior
  have hharmonic :
      threeMassHarmonicHermitian (fullEightMassConfig x)
        (actualEightSiteSelectedSites 0)
        (actualEightSiteSelectedSites 1)
        (actualEightSiteSelectedSites 2) (splitEightMass x).2 =
        fullEightHarmonic x := by
    simpa [x, splitEightMass, splitEightMassLinearEquiv, actualEightSiteSelectedMassTriple] using
      threeMassHarmonic_actualEightSiteSelectedMassTriple hinterior
  have hsimpleThree : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian (fullEightMassConfig x)
        (actualEightSiteSelectedSites 0)
        (actualEightSiteSelectedSites 1)
        (actualEightSiteSelectedSites 2) (splitEightMass x).2) := by
    rw [hharmonic]
    exact hsimpleFull
  have hpositive : ∀ r, 0 < orderedEigenvalue
      (threeMassHarmonicHermitian (fullEightMassConfig x)
        (actualEightSiteSelectedSites 0)
        (actualEightSiteSelectedSites 1)
        (actualEightSiteSelectedSites 2) (splitEightMass x).2)
      (actualEightSiteDecayModes r) := by
    intro r
    rw [hharmonic]
    exact Real.sqrt_pos.1 (actualEightSiteSelectedFrequency_pos x r)
  let J := actualThreeMassLiftedFrequencyJacobian (fullEightMassConfig x)
    (actualEightSiteSelectedSites 0)
    (actualEightSiteSelectedSites 1)
    (actualEightSiteSelectedSites 2)
    actualEightSiteDecaySign actualEightSiteDecayModes (splitEightMass x).2
  have hsliceThree : HasFDerivAt
      (actualThreeMassLiftedFrequencyChart (fullEightMassConfig x)
        (actualEightSiteSelectedSites 0)
        (actualEightSiteSelectedSites 1)
        (actualEightSiteSelectedSites 2)
        actualEightSiteDecaySign actualEightSiteDecayModes)
      partialDerivative (splitEightMass x).2 := by
    simpa only [fullEightLiftedFamily_fixed_environment hx] using hslice
  have hJpartial : J = partialDerivative := by
    simpa [J, actualThreeMassLiftedFrequencyJacobian] using
      hsliceThree.fderiv
  have hprojector :
      (actualThreeMassProjectorWeightMatrix (fullEightMassConfig x)
        (actualEightSiteSelectedSites 0)
        (actualEightSiteSelectedSites 1)
        (actualEightSiteSelectedSites 2)
        actualEightSiteDecayModes (splitEightMass x).2).det ≠ 0 := by
    simpa [x, splitEightMass, splitEightMassLinearEquiv, actualEightSiteSelectedMassTriple] using
      (show (actualThreeMassProjectorWeightMatrix
        (fullEightMassConfig (actualEightSiteRationalMassPath t))
        (actualEightSiteSelectedSites 0)
        (actualEightSiteSelectedSites 1)
        (actualEightSiteSelectedSites 2)
        actualEightSiteDecayModes
        (actualEightSiteSelectedMassTriple
          (actualEightSiteRationalMassPath t))).det ≠ 0 by
          rw [actualThreeMassProjectorWeightMatrix_selected_eq hinterior]
          exact hminor)
  have hJdet : J.det ≠ 0 := by
    apply (actualThreeMassLiftedFrequencyJacobian_det_ne_zero_iff_projectorWeight
      (fullEightMassConfig x)
      (by decide : actualEightSiteSelectedSites 1 ≠
        actualEightSiteSelectedSites 0)
      (by decide : actualEightSiteSelectedSites 2 ≠
        actualEightSiteSelectedSites 0)
      (by decide : actualEightSiteSelectedSites 2 ≠
        actualEightSiteSelectedSites 1)
      actualEightSiteDecaySign actualEightSiteDecayModes htriple
      hsimpleThree hpositive).2
    exact hprojector
  have hpartialDet : partialDerivative.det ≠ 0 := by
    rw [← hJpartial]
    exact hJdet
  have hpartialInvertible : partialDerivative.IsInvertible := by
    let partialEquiv := partialDerivative.toContinuousLinearEquivOfDetNeZero hpartialDet
    exact ⟨partialEquiv,
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero
        partialDerivative hpartialDet⟩
  exact ⟨t, ht, derivative, hx, hxresonance, hfamily, hpartialInvertible⟩

/-- The certified full-eight point admits an open, injective augmented chart
inside the eight-fold mass-support interior.  The output is
`(child₁, child₂,mismatch, environment)` in nested product form. -/
theorem exists_fullEightIID_open_injective_augmentedSpectralPatch :
    ∃ t ∈ Ioo ArchonPhysics.ActualEightSiteNarrowProjectorMinorBridge.actualEightSiteNarrowLower ArchonPhysics.ActualEightSiteNarrowProjectorMinorBridge.actualEightSiteNarrowUpper,
      let x := actualEightSiteRationalMassPath t
      ∃ patch : Set (EightMassEnvironment × MassTriple),
        IsOpen patch ∧
        splitEightMass x ∈ patch ∧
        patch ⊆ splitEightMass '' fullEightMassSupportInterior ∧
        InjOn (augmentedMap fullEightLiftedFamily) patch ∧
        IsOpen (augmentedMap fullEightLiftedFamily '' patch) := by
  obtain ⟨t, ht, derivative, hx, _hxresonance, hderivative, hpartial⟩ :=
    exists_fullEightLiftedFamily_strictDerivative_partial_isInvertible
  let x := actualEightSiteRationalMassPath t
  -- The existential witness used above is fixed by the theorem statement;
  -- recover its interior property directly from membership of the support
  -- neighbourhood below rather than identifying two arbitrary witnesses.
  have hnhds : splitEightMass '' fullEightMassSupportInterior ∈
      𝓝 (splitEightMass x) := by
    have himageOpen : IsOpen
        (splitEightMass '' fullEightMassSupportInterior) :=
      splitEightMass.toHomeomorph.isOpen_image.2
        isOpen_fullEightMassSupportInterior
    exact himageOpen.mem_nhds ⟨x, hx, rfl⟩
  obtain ⟨patch, hopen, hpoint, hsupport, hinjective, himageOpen⟩ :=
    exists_open_injective_augmentedPatch hderivative hpartial hnhds
  exact ⟨t, ht, patch, hopen, hpoint, hsupport, hinjective, himageOpen⟩

end

end ArchonPhysics.ActualEightSiteFullIIDAugmentedSpectralChart
