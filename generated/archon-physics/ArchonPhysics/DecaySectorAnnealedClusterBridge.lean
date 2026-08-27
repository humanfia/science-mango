import ArchonPhysics.AnnealedFiniteMeasureWeakLimit
import ArchonPhysics.CanonicalRankFrequencyMarkedVolumeDominationBridge
import ArchonPhysics.DecayChannelSectorClusterDecomposition
import ArchonPhysics.FiniteMeasureEventualOpenLInfinityWeakLimit
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Sectorwise annealed decay-cluster bridge

This module constructs Giry barycenters of predicate-restricted canonical
decay-sector mismatch measures.  Along a supplied cluster subsequence, an
almost-everywhere identification with one fixed sector cluster implies weak
convergence of the annealed measures to that cluster.

The almost-everywhere identification is explicit.  A
`DecaySectorClusterDecomposition` only records convergence at its one anchor
realization, which by itself cannot determine a law-level barycenter.

Eventual annealed bounds for each fixed open set then give Lebesgue
domination, nonnegative test-function estimates, and bounded
Radon--Nikodym densities sector by sector.  No result recombines these bounds
into a full-law estimate or upgrades them to realization-wise domination.
-/

open scoped Topology ENNReal

namespace ArchonPhysics.DecaySectorAnnealedClusterBridge

open ArchonPhysics
open ArchonPhysics.AnnealedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalCollisionPerSiteMeasureFourier
open ArchonPhysics.CanonicalComplexSpectralPolynomialMomentAllVolume
open ArchonPhysics.DecayChannelMismatchSectorWeakLimit
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.DecayChannelSectorClusterDecomposition
open ArchonPhysics.DecayChannelSectorSimultaneousCompactness
open ArchonPhysics.FiniteMeasureEventualOpenLInfinityWeakLimit
open ArchonPhysics.FiniteMeasureWeakLimitDominationDensity
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassMeasurableModeCoupling
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.RepeatedParentChildMismatchWeakLimitNull
open Filter MeasureTheory Set

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ## Giry-measurable sector measures -/

/-- A predicate-restricted positive weighted mismatch measure is measurable
as a Giry-valued random variable.  The tuple predicate is deterministic; all
sample dependence remains in the ordered spectrum and interaction weight. -/
theorem measurable_positiveWeightedMismatchMeasureWhere_sample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (sign : Fin 3 → InteractionSign)
    (keep : OrderedModeTriple N → Prop) :
    Measurable fun omega ↦ positiveWeightedMismatchMeasureWhere
      (ensemble.restrictPositiveMass (N := N) omega) sign keep := by
  classical
  unfold positiveWeightedMismatchMeasureWhere
  apply Finset.measurable_sum
  intro modes _hmodes
  have hcondition : MeasurableSet
      {omega | IsPositiveOrderedTriple
        (ensemble.restrictPositiveMass (N := N) omega) modes ∧ keep modes} := by
    by_cases hkeep : keep modes
    · have heq :
          {omega | IsPositiveOrderedTriple
              (ensemble.restrictPositiveMass (N := N) omega) modes ∧
                keep modes} =
            {omega | IsPositiveOrderedTriple
              (ensemble.restrictPositiveMass (N := N) omega) modes} := by
        ext omega
        simp only [mem_ofPred_eq, hkeep, and_true]
      rw [heq]
      exact measurableSet_isPositiveOrderedTripleSample ensemble modes
    · have heq :
          {omega | IsPositiveOrderedTriple
              (ensemble.restrictPositiveMass (N := N) omega) modes ∧
                keep modes} = (∅ : Set Omega) := by
        ext omega
        simp only [mem_ofPred_eq, hkeep, and_false, mem_empty_iff_false]
      rw [heq]
      exact MeasurableSet.empty
  apply Measurable.ite hcondition
  · have hcoefficient : Measurable fun omega ↦
        ENNReal.ofReal (harmonicOrderedNormalizedInteractionWeight
          (ensemble.restrictPositiveMass (N := N) omega) modes) :=
      (measurable_orderedNormalizedInteractionWeightSample
        ensemble modes).ennreal_ofReal
    have hdirac : Measurable fun omega ↦
        Measure.dirac (orderedThreeWaveMismatch
          (ensemble.restrictPositiveMass (N := N) omega) sign modes) :=
      Measure.measurable_dirac.comp
        (measurable_orderedThreeWaveMismatchSample ensemble sign modes)
    refine Measure.measurable_of_measurable_coe _ fun A hA ↦ ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    exact hcoefficient.mul ((Measure.measurable_coe hA).comp hdirac)
  · exact measurable_const

/-- Direct Giry measurability of every canonical per-site restricted decay
sector. -/
theorem measurable_toMeasure_canonicalDecaySectorPerSiteMismatchFiniteMeasure
    (ensemble : IIDMassPhaseEnsemble Omega)
    (keep : {N : Nat} → [NeZero N] → OrderedModeTriple N → Prop)
    (n : Nat) :
    Measurable fun omega ↦
      (canonicalDecaySectorPerSiteMismatchFiniteMeasure
        ensemble keep n omega : Measure Real) := by
  have hraw := measurable_positiveWeightedMismatchMeasureWhere_sample
    ensemble decayInteractionSign (keep (N := n + 2))
  refine Measure.measurable_of_measurable_coe _ fun A hA ↦ ?_
  simp only [canonicalDecaySectorPerSiteMismatchFiniteMeasure,
    perSitePositiveWeightedMismatchFiniteMeasureWhere,
    positiveWeightedMismatchFiniteMeasureWhere]
  exact measurable_const.mul ((Measure.measurable_coe hA).comp hraw)

/-- Common finite mass ceiling for each annealed canonical decay sector. -/
def canonicalDecaySectorAnnealedMassCeiling : NNReal :=
  ⟨canonicalCollisionPerSiteMassCeiling,
    canonicalCollisionPerSiteMassCeiling_nonneg⟩

theorem canonicalDecaySectorPerSiteMismatchFiniteMeasure_mass_le_ae
    (keep : {N : Nat} → [NeZero N] → OrderedModeTriple N → Prop)
    (n : Nat) :
    ∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
      (canonicalDecaySectorPerSiteMismatchFiniteMeasure
        canonicalIIDMassPhaseEnsemble keep n omega).mass ≤
          canonicalDecaySectorAnnealedMassCeiling := by
  filter_upwards
    [canonicalPositiveVolumes_simpleOrderedSpectrum_ae
      canonicalIIDMassPhaseEnsemble] with omega hsimple
  have hspectrum : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
          (N := n + 2) omega)) := by
    simpa only [Nat.add_assoc] using hsimple (n + 1) (by omega)
  rw [← NNReal.coe_le_coe]
  calc
    ((canonicalDecaySectorPerSiteMismatchFiniteMeasure
        canonicalIIDMassPhaseEnsemble keep n omega).mass : Real) ≤
        ((canonicalCollisionPerSiteFiniteMeasure
          canonicalIIDMassPhaseEnsemble decayInteractionSign n omega).mass :
            Real) := by
      exact_mod_cast
        canonicalDecaySectorPerSiteMismatchFiniteMeasure_mass_le_full
          canonicalIIDMassPhaseEnsemble keep n omega
    _ ≤ canonicalCollisionPerSiteMassCeiling :=
      canonicalCollisionPerSiteFiniteMeasure_mass_le
        canonicalIIDMassPhaseEnsemble decayInteractionSign n omega hspectrum

/-! ## Sector barycenters and honest cluster identification -/

/-- The law-level barycenter of one canonical predicate-restricted decay
sector at finite volume. -/
def canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
    (keep : {N : Nat} → [NeZero N] → OrderedModeTriple N → Prop)
    (n : Nat) : FiniteMeasure Real :=
  annealedFiniteMeasure RandomEnsemble.canonicalLaw
    (fun omega ↦ canonicalDecaySectorPerSiteMismatchFiniteMeasure
      canonicalIIDMassPhaseEnsemble keep n omega)
    (measurable_toMeasure_canonicalDecaySectorPerSiteMismatchFiniteMeasure
      canonicalIIDMassPhaseEnsemble keep n)
    canonicalDecaySectorAnnealedMassCeiling
    (canonicalDecaySectorPerSiteMismatchFiniteMeasure_mass_le_ae keep n)

/-- Evaluation of a sector barycenter is exactly expected sector mass. -/
theorem canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure_apply
    (keep : {N : Nat} → [NeZero N] → OrderedModeTriple N → Prop)
    (n : Nat) {A : Set Real} (hA : MeasurableSet A) :
    (canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure keep n :
      Measure Real) A =
      ∫⁻ omega,
        (canonicalDecaySectorPerSiteMismatchFiniteMeasure
          canonicalIIDMassPhaseEnsemble keep n omega : Measure Real) A
        ∂ RandomEnsemble.canonicalLaw := by
  exact annealedFiniteMeasure_apply RandomEnsemble.canonicalLaw
    (fun omega ↦ canonicalDecaySectorPerSiteMismatchFiniteMeasure
      canonicalIIDMassPhaseEnsemble keep n omega)
    (measurable_toMeasure_canonicalDecaySectorPerSiteMismatchFiniteMeasure
      canonicalIIDMassPhaseEnsemble keep n)
    canonicalDecaySectorAnnealedMassCeiling
    (canonicalDecaySectorPerSiteMismatchFiniteMeasure_mass_le_ae keep n) hA

/-- Almost-everywhere weak convergence of one sector along a subsequence to
one fixed target passes through its Giry barycenter. -/
theorem canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure_tendsto_along_of_tendsto_ae
    (keep : {N : Nat} → [NeZero N] → OrderedModeTriple N → Prop)
    (subsequence : Nat → Nat) (sectorTarget : FiniteMeasure Real)
    (hlimit : ∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
      Tendsto
        (fun j ↦ canonicalDecaySectorPerSiteMismatchFiniteMeasure
          canonicalIIDMassPhaseEnsemble keep (subsequence j) omega)
        atTop (nhds sectorTarget)) :
    Tendsto
      (fun j ↦ canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
        keep (subsequence j))
      atTop (nhds sectorTarget) := by
  exact annealedFiniteMeasure_tendsto_of_tendsto_ae_of_mass_le
    RandomEnsemble.canonicalLaw
    (fun j omega ↦ canonicalDecaySectorPerSiteMismatchFiniteMeasure
      canonicalIIDMassPhaseEnsemble keep (subsequence j) omega)
    sectorTarget
    (fun j ↦
      measurable_toMeasure_canonicalDecaySectorPerSiteMismatchFiniteMeasure
        canonicalIIDMassPhaseEnsemble keep (subsequence j))
    canonicalDecaySectorAnnealedMassCeiling
    (fun j ↦ canonicalDecaySectorPerSiteMismatchFiniteMeasure_mass_le_ae
      keep (subsequence j)) hlimit

/-- The additional law-level identification required to connect the
subsequence of one `DecaySectorClusterDecomposition` to annealed measures.
The cluster's own fields only cover its anchor realization. -/
structure CanonicalMainDecaySectorsAnnealedClusterIdentification
    {omega : RandomEnsemble.SampleSpace} {target : FiniteMeasure Real}
    (cluster : DecaySectorClusterDecomposition
      canonicalIIDMassPhaseEnsemble omega target) where
  allDistinct_tendsto_ae :
    ∀ᵐ sample ∂ RandomEnsemble.canonicalLaw,
      Tendsto
        (fun j ↦ canonicalDecaySectorPerSiteMismatchFiniteMeasure
          canonicalIIDMassPhaseEnsemble
          (fun {_N} _inst ↦ AllDistinctModes)
          (cluster.subsequence j) sample)
        atTop (nhds cluster.allDistinct)
  childRepeated_tendsto_ae :
    ∀ᵐ sample ∂ RandomEnsemble.canonicalLaw,
      Tendsto
        (fun j ↦ canonicalDecaySectorPerSiteMismatchFiniteMeasure
          canonicalIIDMassPhaseEnsemble
          (fun {_N} _inst ↦ ChildRepeated)
          (cluster.subsequence j) sample)
        atTop (nhds cluster.childRepeated)

theorem CanonicalMainDecaySectorsAnnealedClusterIdentification.allDistinct_tendsto
    {omega : RandomEnsemble.SampleSpace} {target : FiniteMeasure Real}
    {cluster : DecaySectorClusterDecomposition
      canonicalIIDMassPhaseEnsemble omega target}
    (identification :
      CanonicalMainDecaySectorsAnnealedClusterIdentification cluster) :
    Tendsto
      (fun j ↦ canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
        (fun {_N} _inst ↦ AllDistinctModes) (cluster.subsequence j))
      atTop (nhds cluster.allDistinct) :=
  canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure_tendsto_along_of_tendsto_ae
    (fun {_N} _inst ↦ AllDistinctModes) cluster.subsequence
    cluster.allDistinct identification.allDistinct_tendsto_ae

theorem CanonicalMainDecaySectorsAnnealedClusterIdentification.childRepeated_tendsto
    {omega : RandomEnsemble.SampleSpace} {target : FiniteMeasure Real}
    {cluster : DecaySectorClusterDecomposition
      canonicalIIDMassPhaseEnsemble omega target}
    (identification :
      CanonicalMainDecaySectorsAnnealedClusterIdentification cluster) :
    Tendsto
      (fun j ↦ canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
        (fun {_N} _inst ↦ ChildRepeated) (cluster.subsequence j))
      atTop (nhds cluster.childRepeated) :=
  canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure_tendsto_along_of_tendsto_ae
    (fun {_N} _inst ↦ ChildRepeated) cluster.subsequence
    cluster.childRepeated identification.childRepeated_tendsto_ae

/-! ## Eventual annealed open domination -/

/-- A sectorwise annealed estimate along one volume subsequence.  For each
fixed open set, the estimate is required only eventually in the subsequence
index. -/
structure CanonicalDecaySectorAnnealedEventualOpenVolumeDomination
    (keep : {N : Nat} → [NeZero N] → OrderedModeTriple N → Prop)
    (subsequence : Nat → Nat) where
  constant : ENNReal
  constant_ne_top : constant ≠ ∞
  error : Nat → ENNReal
  error_tendsto_zero : Tendsto error atTop (nhds 0)
  bound : ∀ G : Set Real, IsOpen G → ∀ᶠ j in atTop,
    (canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
      keep (subsequence j) : Measure Real) G ≤
      constant * (volume : Measure Real) G + error j

/-- An annealed upper sequence supplies the sectorwise fixed-open interface
once its comparison with the sector barycenter has been established. -/
def CanonicalDecaySectorAnnealedEventualOpenVolumeDomination.of_dominatingSequence
    {keep : {N : Nat} → [NeZero N] → OrderedModeTriple N → Prop}
    {subsequence : Nat → Nat}
    (constant : ENNReal) (constant_ne_top : constant ≠ ∞)
    (error : Nat → ENNReal)
    (error_tendsto_zero : Tendsto error atTop (nhds 0))
    (upper : Nat → FiniteMeasure Real)
    (hsector : ∀ j,
      (canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
        keep (subsequence j) : Measure Real) ≤ (upper j : Measure Real))
    (hupper : ∀ G : Set Real, IsOpen G → ∀ᶠ j in atTop,
      (upper j : Measure Real) G ≤
        constant * (volume : Measure Real) G + error j) :
    CanonicalDecaySectorAnnealedEventualOpenVolumeDomination
      keep subsequence where
  constant := constant
  constant_ne_top := constant_ne_top
  error := error
  error_tendsto_zero := error_tendsto_zero
  bound G hG := by
    filter_upwards [hupper G hG] with j hj
    exact (hsector j G).trans hj

/-- Eventual annealed fixed-open estimates pass to exact sector-target
Lebesgue domination. -/
theorem canonicalDecaySectorTarget_le_smul_volume_of_eventualOpen
    (keep : {N : Nat} → [NeZero N] → OrderedModeTriple N → Prop)
    (subsequence : Nat → Nat) (sectorTarget : FiniteMeasure Real)
    (hlimit : Tendsto
      (fun j ↦ canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
        keep (subsequence j))
      atTop (nhds sectorTarget))
    (domination : CanonicalDecaySectorAnnealedEventualOpenVolumeDomination
      keep subsequence) :
    (sectorTarget : Measure Real) ≤
      domination.constant • (volume : Measure Real) := by
  exact finiteMeasure_le_smul_of_tendsto_of_eventually_isOpen_apply_le
    (fun j ↦ canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
      keep (subsequence j))
    sectorTarget hlimit volume domination.constant domination.constant_ne_top
    domination.error domination.error_tendsto_zero domination.bound

/-- Nonnegative test-function consequence of a sectorwise annealed bound. -/
theorem canonicalDecaySectorTarget_lintegral_le_of_eventualOpen
    (keep : {N : Nat} → [NeZero N] → OrderedModeTriple N → Prop)
    (subsequence : Nat → Nat) (sectorTarget : FiniteMeasure Real)
    (hlimit : Tendsto
      (fun j ↦ canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
        keep (subsequence j))
      atTop (nhds sectorTarget))
    (domination : CanonicalDecaySectorAnnealedEventualOpenVolumeDomination
      keep subsequence)
    (f : Real → ENNReal) :
    ∫⁻ x, f x ∂(sectorTarget : Measure Real) ≤
      domination.constant * ∫⁻ x, f x ∂(volume : Measure Real) := by
  calc
    _ ≤ ∫⁻ x, f x ∂(domination.constant • (volume : Measure Real)) :=
      lintegral_mono'
        (canonicalDecaySectorTarget_le_smul_volume_of_eventualOpen
          keep subsequence sectorTarget hlimit domination) le_rfl
    _ = domination.constant * ∫⁻ x, f x ∂(volume : Measure Real) := by
      rw [lintegral_smul_measure]
      rfl

/-- Sectorwise annealed open domination gives an essentially bounded
Radon--Nikodym density for that sector target alone. -/
theorem canonicalDecaySectorTarget_exists_density_le_of_eventualOpen
    (keep : {N : Nat} → [NeZero N] → OrderedModeTriple N → Prop)
    (subsequence : Nat → Nat) (sectorTarget : FiniteMeasure Real)
    (hlimit : Tendsto
      (fun j ↦ canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
        keep (subsequence j))
      atTop (nhds sectorTarget))
    (domination : CanonicalDecaySectorAnnealedEventualOpenVolumeDomination
      keep subsequence) :
    ∃ density : Real → ENNReal,
      Measurable density ∧
      density ≤ᵐ[(volume : Measure Real)]
        (fun _ ↦ domination.constant) ∧
      (volume : Measure Real).withDensity density =
        (sectorTarget : Measure Real) :=
  exists_density_le_const_of_le_smul _ volume _
    (canonicalDecaySectorTarget_le_smul_volume_of_eventualOpen
      keep subsequence sectorTarget hlimit domination)

/-! ## Cluster-specialized endpoints for the two unresolved sectors -/

theorem CanonicalMainDecaySectorsAnnealedClusterIdentification.allDistinct_le_smul_volume
    {omega : RandomEnsemble.SampleSpace} {target : FiniteMeasure Real}
    {cluster : DecaySectorClusterDecomposition
      canonicalIIDMassPhaseEnsemble omega target}
    (identification :
      CanonicalMainDecaySectorsAnnealedClusterIdentification cluster)
    (domination : CanonicalDecaySectorAnnealedEventualOpenVolumeDomination
      (fun {_N} _inst ↦ AllDistinctModes) cluster.subsequence) :
    (cluster.allDistinct : Measure Real) ≤
      domination.constant • (volume : Measure Real) :=
  canonicalDecaySectorTarget_le_smul_volume_of_eventualOpen
    (fun {_N} _inst ↦ AllDistinctModes) cluster.subsequence
    cluster.allDistinct identification.allDistinct_tendsto domination

theorem CanonicalMainDecaySectorsAnnealedClusterIdentification.childRepeated_le_smul_volume
    {omega : RandomEnsemble.SampleSpace} {target : FiniteMeasure Real}
    {cluster : DecaySectorClusterDecomposition
      canonicalIIDMassPhaseEnsemble omega target}
    (identification :
      CanonicalMainDecaySectorsAnnealedClusterIdentification cluster)
    (domination : CanonicalDecaySectorAnnealedEventualOpenVolumeDomination
      (fun {_N} _inst ↦ ChildRepeated) cluster.subsequence) :
    (cluster.childRepeated : Measure Real) ≤
      domination.constant • (volume : Measure Real) :=
  canonicalDecaySectorTarget_le_smul_volume_of_eventualOpen
    (fun {_N} _inst ↦ ChildRepeated) cluster.subsequence
    cluster.childRepeated identification.childRepeated_tendsto domination

theorem CanonicalMainDecaySectorsAnnealedClusterIdentification.allDistinct_exists_density_le
    {omega : RandomEnsemble.SampleSpace} {target : FiniteMeasure Real}
    {cluster : DecaySectorClusterDecomposition
      canonicalIIDMassPhaseEnsemble omega target}
    (identification :
      CanonicalMainDecaySectorsAnnealedClusterIdentification cluster)
    (domination : CanonicalDecaySectorAnnealedEventualOpenVolumeDomination
      (fun {_N} _inst ↦ AllDistinctModes) cluster.subsequence) :
    ∃ density : Real → ENNReal,
      Measurable density ∧
      density ≤ᵐ[(volume : Measure Real)]
        (fun _ ↦ domination.constant) ∧
      (volume : Measure Real).withDensity density =
        (cluster.allDistinct : Measure Real) :=
  canonicalDecaySectorTarget_exists_density_le_of_eventualOpen
    (fun {_N} _inst ↦ AllDistinctModes) cluster.subsequence
    cluster.allDistinct identification.allDistinct_tendsto domination

theorem CanonicalMainDecaySectorsAnnealedClusterIdentification.childRepeated_exists_density_le
    {omega : RandomEnsemble.SampleSpace} {target : FiniteMeasure Real}
    {cluster : DecaySectorClusterDecomposition
      canonicalIIDMassPhaseEnsemble omega target}
    (identification :
      CanonicalMainDecaySectorsAnnealedClusterIdentification cluster)
    (domination : CanonicalDecaySectorAnnealedEventualOpenVolumeDomination
      (fun {_N} _inst ↦ ChildRepeated) cluster.subsequence) :
    ∃ density : Real → ENNReal,
      Measurable density ∧
      density ≤ᵐ[(volume : Measure Real)]
        (fun _ ↦ domination.constant) ∧
      (volume : Measure Real).withDensity density =
        (cluster.childRepeated : Measure Real) :=
  canonicalDecaySectorTarget_exists_density_le_of_eventualOpen
    (fun {_N} _inst ↦ ChildRepeated) cluster.subsequence
    cluster.childRepeated identification.childRepeated_tendsto domination

end

end ArchonPhysics.DecaySectorAnnealedClusterBridge
