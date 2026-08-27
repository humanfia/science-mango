import ArchonPhysics.ActualSixSiteFullIIDPositiveWeightedNearResonancePatch
import ArchonPhysics.CanonicalRankFrequencyMarkedAnnealedMismatchBridge
import ArchonPhysics.CanonicalRankFrequencyMarkedFourSectorPartition
import ArchonPhysics.SelectedTriadMismatchLower
import ArchonPhysics.CanonicalOnShellInverseTimeSmallBallLower

/-!
# The full-six physical patch enters the canonical annealed mismatch measure

This module identifies the complete marked mismatch pushforward with the
existing scalar per-site collision measure, and reindexes the six raw iid
coordinates into the canonical six-site positive mass configuration.

The final positivity statement is deliberately fixed at volume six.  It is
not a uniform-in-volume linear small-ball estimate.
-/

namespace ArchonPhysics.ActualSixSiteCanonicalAnnealedNearResonanceLower

open ArchonPhysics
open ArchonPhysics.ActualSixSiteCleanDecayResonancePatch
open ArchonPhysics.BroadenedResonanceMeasure
open ArchonPhysics.CanonicalOnShellInverseTimeSmallBallLower
open ArchonPhysics.ActualSixSiteFullIIDPositiveWeightedNearResonancePatch
open ArchonPhysics.CanonicalCollisionPerSiteMeasureFourier
open ArchonPhysics.CanonicalJointFrequencyPerSiteMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedAnnealedMismatchBridge
open ArchonPhysics.CanonicalRankFrequencyMarkedFourSectorPartition
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedProbabilityJointLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
open ArchonPhysics.CollisionFourierWeakLimitBridge
open ArchonPhysics.FrozenCollisionPerSiteNormalization
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.MarkedEmpiricalResonanceTransfer
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open ArchonPhysics.SelectedTriadMismatchLower
open Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Forgetting ranks and then taking signed mismatch sends the complete raw
marked measure to the existing scalar weighted mismatch measure. -/
theorem map_positiveWeightedRankFrequencyTripleFiniteMeasure_markedMismatch
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 -> InteractionSign) :
    (positiveWeightedRankFrequencyTripleFiniteMeasure m).map
        (markedFrequencyMismatch sign) =
      positiveWeightedMismatchFiniteMeasure m sign := by
  apply FiniteMeasure.toMeasure_injective
  rw [FiniteMeasure.toMeasure_map]
  rw [markedFrequencyMismatch_eq_frequencyTripleMismatch_forgetRank]
  rw [← Measure.map_map (measurable_frequencyTripleMismatch sign)
    measurable_forgetRankFrequencyTriple]
  change Measure.map (frequencyTripleMismatch sign)
      (Measure.map forgetRankFrequencyTriple
        (positiveWeightedRankFrequencyTripleMeasure m)) =
    positiveWeightedMismatchMeasure m sign
  rw [map_positiveWeightedRankFrequencyTripleMeasure_forgetRank]
  exact map_positiveWeightedFrequencyTripleMeasure_eq_mismatchMeasure m sign

/-- At every sequence index, the complete canonical marked mismatch
pushforward is exactly the existing scalar per-site finite measure at the
same physical volume. -/
theorem map_canonicalMarkedPerSiteSequence_eq_collisionPerSite
    (sign : Fin 3 -> InteractionSign) (n : Nat)
    (omega : RandomEnsemble.SampleSpace) :
    (canonicalMarkedPerSiteSequence n omega).map
        (markedFrequencyMismatch sign) =
      canonicalCollisionPerSiteFiniteMeasure
        canonicalIIDMassPhaseEnsemble sign (n + 1) omega := by
  unfold canonicalMarkedPerSiteSequence
    canonicalRankFrequencyTriplePerSiteFiniteMeasure
    canonicalCollisionPerSiteFiniteMeasure
    perSitePositiveWeightedMismatchFiniteMeasure
  rw [FiniteMeasure.map_smul,
    map_positiveWeightedRankFrequencyTripleFiniteMeasure_markedMismatch]

/-- The first six canonical mass coordinates, reindexed by periodic sites,
give exactly the full-six physical mass configuration. -/
theorem fullSixMassConfig_restrictMassFin_eq_canonical
    (omega : RandomEnsemble.SampleSpace) :
    fullSixMassConfig
        (canonicalIIDMassPhaseEnsemble.restrictMassFin (N := 6) omega) =
      canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := 6) omega := by
  rw [Lattice.PositiveMassConfig.mk.injEq]
  funext site
  change clippedMass
      (canonicalIIDMassPhaseEnsemble.mass
        (siteEquivFin 6 site).val omega) =
    canonicalIIDMassPhaseEnsemble.mass site.val omega
  rw [clippedMass_eq_self
    (canonicalIIDMassPhaseEnsemble.mass_mem_support
      (siteEquivFin 6 site).val omega)]
  rfl


/-- For every positive mismatch width, the physical decay mismatch window of
the canonical six-site annealed per-site measure has strictly positive mass.
This is qualitative at the fixed physical volume `6`; no width-uniform slope
or volume-uniform constant is asserted. -/
theorem canonicalDecaySixSiteAnnealed_absoluteMismatchSublevel_pos
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    0 <
      (canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure
          decayInteractionSign 3 : Measure Real)
        (absoluteMismatchSublevel epsilon) := by
  have hwindow : MeasurableSet (absoluteMismatchSublevel epsilon) :=
    measurableSet_absoluteMismatchSublevel epsilon
  obtain ⟨patch, hopen, hpatchMass, hpatchSubset⟩ :=
    exists_positive_finiteMassLaw_fullSix_physicalWeightedNearResonancePatch
      hepsilon
  let event : Set RandomEnsemble.SampleSpace :=
    {omega |
      canonicalIIDMassPhaseEnsemble.restrictMassFin (N := 6) omega ∈ patch}
  have hmeasure :=
    (canonicalIIDMassPhaseEnsemble.restrictMassFin_hasLaw (N := 6)).measure_eq
      hopen.measurableSet
  have heventPos : 0 < RandomEnsemble.canonicalLaw event := by
    change 0 < canonicalIIDMassPhaseEnsemble.probability
      {omega | patch
        (canonicalIIDMassPhaseEnsemble.restrictMassFin (N := 6) omega)}
    rw [hmeasure]
    exact hpatchMass
  let integrand : RandomEnsemble.SampleSpace → ENNReal := fun omega ↦
    ((((canonicalMarkedPerSiteSequence 3 omega).map
      (markedFrequencyMismatch decayInteractionSign) : FiniteMeasure Real) :
        Measure Real) (absoluteMismatchSublevel epsilon))
  have hintegrandMeas : Measurable integrand :=
    (Measure.measurable_coe hwindow).comp
      (measurable_toMeasure_canonicalMarkedMismatchPerSiteSequence
        decayInteractionSign 3)
  have heventSubset : event ⊆ Function.support integrand := by
    intro omega homega
    have hgood := hpatchSubset homega
    rcases hgood with
      ⟨_hinterior, _hsimple, henergy, hmismatch, hweight, _hprojector⟩
    let mass :=
      canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := 6) omega
    have hmass :
        fullSixMassConfig
            (canonicalIIDMassPhaseEnsemble.restrictMassFin (N := 6) omega) =
          mass := by
      exact fullSixMassConfig_restrictMassFin_eq_canonical omega
    have hpositive : IsPositiveOrderedTriple mass cleanSixSiteDecayModes := by
      intro r
      rw [mem_orderedPositiveModeIndices_iff]
      rw [← hmass]
      simpa [fullSixHarmonic, orderedModeFrequency] using
        Real.sqrt_pos.2 (henergy r)
    have hmismatchWindow :
        orderedThreeWaveMismatch mass decayInteractionSign
            cleanSixSiteDecayModes ∈
          absoluteMismatchSublevel epsilon := by
      change
        |orderedThreeWaveMismatch mass decayInteractionSign
          cleanSixSiteDecayModes| ≤ epsilon
      rw [← hmass]
      simpa [orderedThreeWaveMismatch, fullSixSelectedMismatch,
        fullSixHarmonic, orderedPhaseMismatch, decayInteractionSign,
        ActualThreeMassLiftedJacobianPolynomial.actualFourSiteDecaySign] using
        (le_of_lt hmismatch)
    have hweightMass :
        0 < harmonicOrderedNormalizedInteractionWeight mass
          cleanSixSiteDecayModes := by
      rw [← hmass]
      rw [← fullSixSelectedInteractionWeight_eq_harmonic]
      exact hweight
    have hlower :=
      invSite_mul_selectedTriad_weight_le_perSiteMismatch_apply
        mass decayInteractionSign cleanSixSiteDecayModes
        (absoluteMismatchSublevel epsilon) hwindow hpositive hmismatchWindow
    have hintegrandEq :
        integrand omega =
          (perSitePositiveWeightedMismatchFiniteMeasure mass
              decayInteractionSign : Measure Real)
            (absoluteMismatchSublevel epsilon) := by
      calc
        integrand omega =
            (canonicalCollisionPerSiteFiniteMeasure
                canonicalIIDMassPhaseEnsemble decayInteractionSign 4 omega :
              Measure Real) (absoluteMismatchSublevel epsilon) := by
          exact congrArg
            (fun mu : FiniteMeasure Real =>
              (mu : Measure Real) (absoluteMismatchSublevel epsilon))
            (map_canonicalMarkedPerSiteSequence_eq_collisionPerSite
              decayInteractionSign 3 omega)
        _ = (perSitePositiveWeightedMismatchFiniteMeasure mass
              decayInteractionSign : Measure Real)
            (absoluteMismatchSublevel epsilon) := by rfl
    have hcoefficient :
        0 < (↑((6 : NNReal)⁻¹) : ENNReal) := by positivity
    have hweightENN :
        0 < ENNReal.ofReal
          (harmonicOrderedNormalizedInteractionWeight mass
            cleanSixSiteDecayModes) :=
      ENNReal.ofReal_pos.mpr hweightMass
    have hintegrandPos : 0 < integrand omega := by
      rw [hintegrandEq]
      exact lt_of_lt_of_le (ENNReal.mul_pos hcoefficient.ne' hweightENN.ne') hlower
    exact ne_of_gt hintegrandPos
  have hintegralPos :
      0 < ∫⁻ omega, integrand omega ∂ RandomEnsemble.canonicalLaw := by
    rw [lintegral_pos_iff_support hintegrandMeas]
    exact lt_of_lt_of_le heventPos (measure_mono heventSubset)
  rw [canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure_apply
    decayInteractionSign 3 hwindow]
  exact hintegralPos


/-- The fixed-six qualitative small-ball positivity feeds the exact
inverse-time resonance kernel at every positive time.  The resulting
broadened mass is positive, but this theorem gives no time-uniform positive
lower bound because the patch probability can shrink with the window. -/
theorem canonicalDecaySixSiteAnnealed_broadenedResonanceMeasure_mass_pos
    {T : Real} (hT : 0 < T) :
    0 <
      ((broadenedResonanceMeasure
        (canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure
          decayInteractionSign 3)
        id measurable_id T hT).mass : Real) := by
  let mu : FiniteMeasure Real :=
    canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure
      decayInteractionSign 3
  have hepsilon : 0 < 1 / (4 * T) := by positivity
  have hsmallENN :
      0 < (mu : Measure Real)
        (absoluteMismatchSublevel (1 / (4 * T))) := by
    dsimp [mu]
    exact canonicalDecaySixSiteAnnealed_absoluteMismatchSublevel_pos hepsilon
  have hsmallReal :
      0 < (mu : Measure Real).real
        (absoluteMismatchSublevel (1 / (4 * T))) :=
    ENNReal.toReal_pos hsmallENN.ne' (measure_ne_top _ _)
  have hheight : 0 < T / (4 * Real.pi) := by positivity
  have hlower :=
    halfHeight_mul_smallBall_le_broadenedResonanceMeasure_mass mu hT
  exact lt_of_lt_of_le (mul_pos hheight hsmallReal) hlower

end

end ArchonPhysics.ActualSixSiteCanonicalAnnealedNearResonanceLower
