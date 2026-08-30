import ArchonPhysics.ActualEightSiteNarrowPhysicalExactDecay
import ArchonPhysics.ActualThreeMassHellmannFeynmanJacobian
import ArchonPhysics.ActualThreeMassLiftedExactResonanceLinearSmallBall
import ArchonPhysics.PeriodicWeightedCycleBlockGluing

/-!
# An unconditional eight-site all-distinct linear small-ball slope

The certified eight-site decay resonance has a nonzero projector minor in
the three physical mass directions `(2, 5, 7)`.  Replacing exactly those
three coordinates by iid masses realizes the generic actual three-mass
lifted chart.  The Hellmann--Feynman determinant identity therefore turns
the certified minor into a nonzero true Jacobian, and the exact-resonance
reverse-coarea theorem supplies a positive linear small-ball slope.

The conclusion is a genuine fixed-eight, frozen-five-environment theorem.
Transport to a volume-uniform globally coupled-chain collision measure is a
separate localization/additivity problem.
-/

namespace ArchonPhysics.ActualEightSiteExactAllDistinctLinearSmallBall

open ArchonPhysics
open ArchonPhysics.ActualEightSiteExactDecayIVTBridge
open ArchonPhysics.ActualEightSiteNarrowPhysicalExactDecay
open ArchonPhysics.ActualEightSiteNarrowProjectorMinorBridge
open ArchonPhysics.ActualThreeMassHellmannFeynmanJacobian
open ArchonPhysics.ActualThreeMassLiftedExactResonanceLinearSmallBall
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualTwoMassChildRepeatedMismatchLowerBound
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MarkedEmpiricalResonanceTransfer
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.SingleMassRankOnePerturbation
open ArchonPhysics.ThreeParameterProjectorWeightJacobian
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open MeasureTheory Set

noncomputable section

/-- The raw masses at the three physical sites certified by the projector
minor, in the nested convention of `MassTriple`. -/
def actualEightSiteSelectedMassTriple (x : EightMassVector) : MassTriple :=
  ((x 2, x 5), x 7)

theorem actualEightSiteSelectedMassTriple_mem_interior
    {x : EightMassVector}
    (hx : ∀ i, x i ∈ Ioo massLower massUpper) :
    actualEightSiteSelectedMassTriple x ∈ interior iidMassTripleSupport := by
  rw [iidMassTripleSupport, interior_prod_eq, iidMassPairSupport,
    interior_prod_eq, massSupport, interior_Icc]
  exact ⟨⟨hx 2, hx 5⟩, hx 7⟩

/-- Replacing the selected three coordinates by their current raw values
reconstructs the original physical eight-site mass configuration exactly. -/
theorem threeMassSiteConfig_actualEightSiteSelectedMassTriple
    {x : EightMassVector}
    (hx : ∀ i, x i ∈ Ioo massLower massUpper) :
    threeMassSiteConfig (fullEightMassConfig x)
      (actualEightSiteSelectedSites 0)
      (actualEightSiteSelectedSites 1)
      (actualEightSiteSelectedSites 2)
      (actualEightSiteSelectedMassTriple x) =
        fullEightMassConfig x := by
  have hsupport : ∀ i, x i ∈ massSupport := fun i =>
    ⟨(hx i).1.le, (hx i).2.le⟩
  have hclip : ∀ i, clippedMass (x i) = x i := fun i =>
    clippedMass_eq_self (hsupport i)
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
      [threeMassSiteConfig, fullEightMassConfig,
        actualEightSiteSelectedMassTriple, actualEightSiteSelectedSites,
        val_siteEquivFin_symm, hclip]

theorem threeMassHarmonic_actualEightSiteSelectedMassTriple
    {x : EightMassVector}
    (hx : ∀ i, x i ∈ Ioo massLower massUpper) :
    threeMassHarmonicHermitian (fullEightMassConfig x)
      (actualEightSiteSelectedSites 0)
      (actualEightSiteSelectedSites 1)
      (actualEightSiteSelectedSites 2)
      (actualEightSiteSelectedMassTriple x) =
        fullEightHarmonic x := by
  unfold threeMassHarmonicHermitian fullEightHarmonic
  rw [threeMassSiteConfig_actualEightSiteSelectedMassTriple hx]

theorem actualThreeMassProjectorWeightMatrix_selected_eq
    {x : EightMassVector}
    (hx : ∀ i, x i ∈ Ioo massLower massUpper) :
    actualThreeMassProjectorWeightMatrix (fullEightMassConfig x)
      (actualEightSiteSelectedSites 0)
      (actualEightSiteSelectedSites 1)
      (actualEightSiteSelectedSites 2)
      actualEightSiteDecayModes (actualEightSiteSelectedMassTriple x) =
        orderedProjectorWeightMatrix (fullEightDualHarmonic x)
          actualEightSiteDecayModes
          (fun s => cycleMassPerturbationVector
            (actualEightSiteSelectedSites s)) := by
  unfold actualThreeMassProjectorWeightMatrix actualThreeMassDualHermitian
    actualThreeMassCycleDirection actualThreeMassSelectedSite
    fullEightDualHarmonic
  rw [threeMassSiteConfig_actualEightSiteSelectedMassTriple hx]
  rfl

/-- The unconditional exact eight-site witness supplies a positive linear
small-ball slope for the genuine conditional iid three-mass mismatch law. -/
theorem exists_actualEightSite_exactAllDistinct_linearSmallBallLower :
    ∃ t ∈ Ioo actualEightSiteNarrowLower actualEightSiteNarrowUpper,
      ∃ constant radius : Real, 0 < constant ∧ 0 < radius ∧
        ∀ delta : Real, 0 < delta → delta ≤ radius →
          constant * delta ≤
            (Measure.map Prod.snd
              (Measure.map
                (actualThreeMassLiftedFrequencyChart
                  (fullEightMassConfig (actualEightSiteRationalMassPath t))
                  (actualEightSiteSelectedSites 0)
                  (actualEightSiteSelectedSites 1)
                  (actualEightSiteSelectedSites 2)
                  actualEightSiteDecaySign actualEightSiteDecayModes)
                iidMassTripleLaw)
              (absoluteMismatchSublevel delta)).toReal := by
  obtain ⟨t, ht, hinterior, hresonance, hsimple,
      _hweight, hminor, _hgram⟩ :=
    exists_actualEightSite_narrow_physicalExactDecay
  let x : EightMassVector := actualEightSiteRationalMassPath t
  let triple : MassTriple := actualEightSiteSelectedMassTriple x
  let fixed : Lattice.PositiveMassConfig 8 := fullEightMassConfig x
  have htriple : triple ∈ interior iidMassTripleSupport := by
    exact actualEightSiteSelectedMassTriple_mem_interior hinterior
  have hharmonic :
      threeMassHarmonicHermitian fixed
        (actualEightSiteSelectedSites 0)
        (actualEightSiteSelectedSites 1)
        (actualEightSiteSelectedSites 2) triple =
      fullEightHarmonic x := by
    exact threeMassHarmonic_actualEightSiteSelectedMassTriple hinterior
  have hsimpleThree : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed
        (actualEightSiteSelectedSites 0)
        (actualEightSiteSelectedSites 1)
        (actualEightSiteSelectedSites 2) triple) := by
    rw [hharmonic]
    exact hsimple
  have hpositive : ∀ r, 0 < orderedEigenvalue
      (threeMassHarmonicHermitian fixed
        (actualEightSiteSelectedSites 0)
        (actualEightSiteSelectedSites 1)
        (actualEightSiteSelectedSites 2) triple)
      (actualEightSiteDecayModes r) := by
    intro r
    rw [hharmonic]
    exact Real.sqrt_pos.1 (actualEightSiteSelectedFrequency_pos x r)
  have hprojector :
      (actualThreeMassProjectorWeightMatrix fixed
        (actualEightSiteSelectedSites 0)
        (actualEightSiteSelectedSites 1)
        (actualEightSiteSelectedSites 2)
        actualEightSiteDecayModes triple).det ≠ 0 := by
    rw [actualThreeMassProjectorWeightMatrix_selected_eq hinterior]
    exact hminor
  have hJacobian :
      (actualThreeMassLiftedFrequencyJacobian fixed
        (actualEightSiteSelectedSites 0)
        (actualEightSiteSelectedSites 1)
        (actualEightSiteSelectedSites 2)
        actualEightSiteDecaySign actualEightSiteDecayModes triple).det ≠ 0 := by
    apply (actualThreeMassLiftedFrequencyJacobian_det_ne_zero_iff_projectorWeight
      fixed
      (by decide : actualEightSiteSelectedSites 1 ≠
        actualEightSiteSelectedSites 0)
      (by decide : actualEightSiteSelectedSites 2 ≠
        actualEightSiteSelectedSites 0)
      (by decide : actualEightSiteSelectedSites 2 ≠
        actualEightSiteSelectedSites 1)
      actualEightSiteDecaySign actualEightSiteDecayModes htriple
      hsimpleThree hpositive).2
    exact hprojector
  have hresonanceThree :
      (actualThreeMassLiftedFrequencyChart fixed
        (actualEightSiteSelectedSites 0)
        (actualEightSiteSelectedSites 1)
        (actualEightSiteSelectedSites 2)
        actualEightSiteDecaySign actualEightSiteDecayModes triple).2 = 0 := by
    unfold actualThreeMassLiftedFrequencyChart
    rw [hharmonic]
    simpa [x, actualEightSiteRationalPathMismatch,
      actualEightSiteSelectedMismatch, orderedPhaseMismatch] using hresonance
  obtain ⟨constant, radius, hconstant, hradius, hbound⟩ :=
    exists_actualThreeMass_exactResonance_linearSmallBallLower
      fixed
      (by decide : actualEightSiteSelectedSites 1 ≠
        actualEightSiteSelectedSites 0)
      (by decide : actualEightSiteSelectedSites 2 ≠
        actualEightSiteSelectedSites 0)
      (by decide : actualEightSiteSelectedSites 2 ≠
        actualEightSiteSelectedSites 1)
      actualEightSiteDecaySign actualEightSiteDecayModes triple htriple
      hsimpleThree hpositive hJacobian hresonanceThree
  exact ⟨t, ht, constant, radius, hconstant, hradius, hbound⟩

end

end ArchonPhysics.ActualEightSiteExactAllDistinctLinearSmallBall
