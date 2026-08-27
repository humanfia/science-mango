import ArchonPhysics.ActualLiftedMismatchSmallBall
import ArchonPhysics.CanonicalAllDistinctCompactAtlasLegFrequencyMarginal
import ArchonPhysics.CanonicalDecayAnnealedSectorVolumeDomination
import ArchonPhysics.CanonicalDecayMainSectorBroadenedMassUpper

/-!
# Actual main decay sectors instantiated on a canonical cluster

This module removes the remaining indexing and measure-identification gap
between the actual finite-volume spectral atlases and a scalar canonical
decay-sector cluster.

For `AllDistinctModes`, the genuinely model-specific thermodynamic input is
recorded without disguise: one uniform bound on the actual joint good coarea
laws and one vanishing annealed mass for their unweighted bad complements.
All finite-volume laws in that interface are the actual three-mass harmonic
charts.  Exact iid Fubini reconstruction and bounded child-frequency support
then produce the scalar arbitrary-set estimate.

For `ChildRepeated`, the existing actual two-mass annealed atlas sequence
already supplies the corresponding two inputs.  A general reindexing lemma
converts marked-index estimates at `n + 1` to any cofinal cluster
subsequence.  The final theorem feeds the resulting two cluster
dominations into the complete broadened-mass upper bound; the two singular
parent--child sectors continue to use their unconditional `O(T^(-1/2))`
decay and require no raw Lebesgue domination.
-/

open scoped ENNReal Topology

namespace ArchonPhysics.CanonicalDecayActualMainSectorClusterInstantiation

open ArchonPhysics
open ArchonPhysics.ActualLiftedMismatchSmallBall
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedFiniteVolumeTrace
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassAllDistinctJointCoareaOverlap
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningTrace
open ArchonPhysics.CanonicalAllDistinctCompactAtlasLegFrequencyMarginal
open ArchonPhysics.CanonicalAllDistinctRawLiftedLawIdentification
open ArchonPhysics.CanonicalChildRepeatedAnnealedAtlasSmallBall
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalDecayAnnealedSectorVolumeDomination
open ArchonPhysics.CanonicalDecayMainSectorBroadenedMassUpper
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMarginal
open ArchonPhysics.DecayChannelMismatchSectorWeakLimit
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.DecayChannelSectorClusterDecomposition
open ArchonPhysics.DecaySectorAnnealedClusterBridge
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.IIDMassTripleFiniteVolumeReconstruction
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.RepeatedParentChildMismatchWeakLimitNull
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Filter MeasureTheory Set

noncomputable section

/-! ## Exact raw scalar identification -/

/-- Forgetting the two child frequencies in the actual raw lifted
all-distinct law recovers exactly the existing per-site scalar mismatch
finite measure. -/
theorem map_snd_allDistinctPerSiteRawLiftedMeasure_eq
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (sign : Fin 3 -> InteractionSign) :
    Measure.map Prod.snd (allDistinctPerSiteRawLiftedMeasure mass sign) =
      ((perSitePositiveWeightedMismatchFiniteMeasureWhere
        mass sign AllDistinctModes : FiniteMeasure Real) : Measure Real) := by
  unfold allDistinctPerSiteRawLiftedMeasure
  rw [Measure.map_map measurable_snd
    (measurable_plainChildMismatchCoordinates sign)]
  rw [show Prod.snd ∘ plainChildMismatchCoordinates sign =
      frequencyTripleMismatch sign by
    funext frequency
    rfl]
  unfold perSitePositiveWeightedFrequencyTripleMeasureWhere
  rw [Measure.map_smul,
    map_positiveWeightedFrequencyTripleMeasureWhere_eq_mismatchWhere]
  unfold perSitePositiveWeightedMismatchFiniteMeasureWhere
  rw [FiniteMeasure.toMeasure_smul]
  change (N : ENNReal)⁻¹ •
      positiveWeightedMismatchMeasureWhere mass sign AllDistinctModes =
    (((((N : Nat) : NNReal)⁻¹ : NNReal) : ENNReal) •
      positiveWeightedMismatchMeasureWhere mass sign AllDistinctModes)
  rw [ENNReal.coe_inv (by exact_mod_cast NeZero.ne N : (N : NNReal) ≠ 0)]
  rfl

/-- Exact annealed actual-chart representation of the canonical scalar
all-distinct sector at one finite volume. -/
theorem canonicalDecaySectorAnnealed_allDistinct_eq_map_snd_bind_actual
    {N : Nat} [NeZero N]
    (site₀ site₁ site₂ : Lattice.Site N)
    (h₀₁ : site₀ ≠ site₁) (h₀₂ : site₀ ≠ site₂)
    (h₁₂ : site₁ ≠ site₂)
    (n : Nat) (hN : N = n + 2) :
    (canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
        (fun {_N} _inst ↦ AllDistinctModes) n : Measure Real) =
      Measure.map Prod.snd
        ((iidFiniteMassVectorLaw
            (finiteVolumeMassComplement site₀ site₁ site₂)).bind
          (fun rest ↦ actualThreeMassAllDistinctJointLiftedMeasure
            (finiteEnvironmentPositiveMassConfig site₀ site₁ site₂ rest)
            site₀ site₁ site₂ decayInteractionSign)) := by
  subst N
  apply Measure.ext
  intro A hA
  rw [canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure_apply
    (fun {_N} _inst ↦ AllDistinctModes) n hA]
  rw [Measure.map_apply measurable_snd hA]
  have hactual : Measurable fun rest : FiniteMassVector
      (finiteVolumeMassComplement site₀ site₁ site₂) ↦
      actualThreeMassAllDistinctJointLiftedMeasure
        (finiteEnvironmentPositiveMassConfig site₀ site₁ site₂ rest)
        site₀ site₁ site₂ decayInteractionSign :=
    measurable_actualThreeMassAllDistinctJointLiftedMeasure_finiteEnvironment
      site₀ site₁ site₂ decayInteractionSign
  rw [Measure.bind_apply (hA.preimage measurable_snd) hactual.aemeasurable]
  have hbind := bind_allDistinctPerSiteRawLiftedMeasure_eq_complement
    canonicalIIDMassPhaseEnsemble site₀ site₁ site₂
      h₀₁ h₀₂ h₁₂ decayInteractionSign
  have hraw : Measurable fun omega ↦
      allDistinctPerSiteRawLiftedMeasure
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
          (N := n + 2) omega) decayInteractionSign :=
    measurable_allDistinctPerSiteRawLiftedMeasure
      (fun omega ↦ canonicalIIDMassPhaseEnsemble.restrictPositiveMass
        (N := n + 2) omega)
      (fun site ↦ by
        simpa only [IIDMassPhaseEnsemble.restrictPositiveMass_mass] using
          canonicalIIDMassPhaseEnsemble.mass_measurable site.val)
      decayInteractionSign
  have hbindApply := congrArg
    (fun measure : Measure MassTriple ↦ measure (Prod.snd ⁻¹' A)) hbind
  rw [Measure.bind_apply (hA.preimage measurable_snd) hraw.aemeasurable,
    Measure.bind_apply (hA.preimage measurable_snd) hactual.aemeasurable]
      at hbindApply
  rw [← hbindApply]
  apply lintegral_congr
  intro omega
  rw [← Measure.map_apply measurable_snd hA,
    map_snd_allDistinctPerSiteRawLiftedMeasure_eq]
  rfl

/-! ## Actual all-distinct thermodynamic coarea data -/

/-- The precise cross-volume data still required from the actual
three-mass all-distinct charts.  Compact-atlas construction is already
available volume by volume; the two fields below that remain genuinely
uniform are `goodCoarea` and `badMass_le`, together with finiteness and
vanishing of their displayed bounds. -/
structure ActualThreeMassAllDistinctAnnealedRawCoareaSequence where
  site₀ : (n : Nat) → Lattice.Site ((n + 1) + 2)
  site₁ : (n : Nat) → Lattice.Site ((n + 1) + 2)
  site₂ : (n : Nat) → Lattice.Site ((n + 1) + 2)
  site₀_ne_site₁ : ∀ n, site₀ n ≠ site₁ n
  site₀_ne_site₂ : ∀ n, site₀ n ≠ site₂ n
  site₁_ne_site₂ : ∀ n, site₁ n ≠ site₂ n
  good : (n : Nat) →
    FiniteMassVector
      (finiteVolumeMassComplement (site₀ n) (site₁ n) (site₂ n)) →
    OrderedModeTriple ((n + 1) + 2) → Set MassTriple
  good_measurable : ∀ n rest modes, MeasurableSet (good n rest modes)
  regularCeiling : ENNReal
  regularCeiling_ne_top : regularCeiling ≠ ∞
  goodCoarea : ∀ n rest,
    actualThreeMassAllDistinctJointGoodCoareaBound
      (finiteEnvironmentPositiveMassConfig
        (site₀ n) (site₁ n) (site₂ n) rest)
      (site₀ n) (site₁ n) (site₂ n) decayInteractionSign
      (good n rest) regularCeiling
  badError : Nat → ENNReal
  badError_ne_top : ∀ n, badError n ≠ ∞
  badError_tendsto_zero : Tendsto badError atTop (nhds 0)
  badMass_le : ∀ n,
    (∫⁻ rest,
      actualThreeMassAllDistinctJointBadLiftedMeasure
        (finiteEnvironmentPositiveMassConfig
          (site₀ n) (site₁ n) (site₂ n) rest)
        (site₀ n) (site₁ n) (site₂ n) decayInteractionSign
        (good n rest) Set.univ
      ∂iidFiniteMassVectorLaw
        (finiteVolumeMassComplement
          (site₀ n) (site₁ n) (site₂ n))) ≤ badError n

/-- The summed actual good lifted all-distinct law remains supported in the
physical child-frequency cylinder. -/
theorem actualThreeMassAllDistinctJointGood_ae_mem_childCylinder
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N)
    (good : OrderedModeTriple N → Set MassTriple) :
    ∀ᵐ point ∂actualThreeMassAllDistinctJointGoodLiftedMeasure
        fixed site₀ site₁ site₂ decayInteractionSign good,
      point ∈ liftedChildFrequencyCylinder (Real.sqrt 5) := by
  apply ae_iff.mpr
  unfold actualThreeMassAllDistinctJointGoodLiftedMeasure
  rw [Measure.smul_apply, Measure.coe_finsetSum]
  simp only [Finset.sum_apply, smul_eq_mul]
  have hsummand (modes : OrderedModeTriple N) :
      Measure.map
          (actualThreeMassLiftedFrequencyChart
            fixed site₀ site₁ site₂ decayInteractionSign modes)
          ((iidMassTripleLaw.withDensity
            (actualThreeMassAllDistinctTupleWeight
              fixed site₀ site₁ site₂ modes)).restrict (good modes))
          (liftedChildFrequencyCylinder (Real.sqrt 5))ᶜ = 0 :=
    ae_iff.mp
      (ae_map_actualThreeMassLiftedFrequencyChart_mem_childCylinder
        fixed hfixed site₀ site₁ site₂ decayInteractionSign modes
        ((iidMassTripleLaw.withDensity
          (actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂ modes)).restrict (good modes)))
  calc
    _ = (N : ENNReal)⁻¹ * 0 := by
      congr 1
      apply Finset.sum_eq_zero
      intro modes _hmodes
      exact hsummand modes
    _ = 0 := mul_zero _

/-- Actual joint coarea, exact iid reconstruction, and bounded physical
child frequencies give the full scalar all-distinct arbitrary-set estimate.
The only error is the annealed unweighted bad-source mass. -/
theorem canonicalDecaySectorAnnealed_allDistinct_apply_le_of_actualCoarea
    (data : ActualThreeMassAllDistinctAnnealedRawCoareaSequence)
    (n : Nat) {A : Set Real} (hA : MeasurableSet A) :
    (canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
        (fun {_N} _inst ↦ AllDistinctModes) (n + 1) : Measure Real) A ≤
      (data.regularCeiling *
          (ENNReal.ofReal (Real.sqrt 5) * ENNReal.ofReal (Real.sqrt 5))) *
          (volume : Measure Real) A + data.badError n := by
  rw [canonicalDecaySectorAnnealed_allDistinct_eq_map_snd_bind_actual
    (data.site₀ n) (data.site₁ n) (data.site₂ n)
    (data.site₀_ne_site₁ n) (data.site₀_ne_site₂ n)
    (data.site₁_ne_site₂ n) (n + 1) rfl]
  rw [Measure.map_apply measurable_snd hA]
  have hactual : Measurable fun rest : FiniteMassVector
      (finiteVolumeMassComplement
        (data.site₀ n) (data.site₁ n) (data.site₂ n)) ↦
      actualThreeMassAllDistinctJointLiftedMeasure
        (finiteEnvironmentPositiveMassConfig
          (data.site₀ n) (data.site₁ n) (data.site₂ n) rest)
        (data.site₀ n) (data.site₁ n) (data.site₂ n)
        decayInteractionSign :=
    measurable_actualThreeMassAllDistinctJointLiftedMeasure_finiteEnvironment
      (data.site₀ n) (data.site₁ n) (data.site₂ n)
      decayInteractionSign
  rw [Measure.bind_apply (hA.preimage measurable_snd) hactual.aemeasurable]
  let regular : ENNReal := data.regularCeiling *
    (ENNReal.ofReal (Real.sqrt 5) * ENNReal.ofReal (Real.sqrt 5))
  let _ : IsProbabilityMeasure (iidFiniteMassVectorLaw
      (finiteVolumeMassComplement
        (data.site₀ n) (data.site₁ n) (data.site₂ n))) := by
    unfold iidFiniteMassVectorLaw
    infer_instance
  calc
    _ ≤ ∫⁻ rest,
        regular * (volume : Measure Real) A +
          actualThreeMassAllDistinctJointBadLiftedMeasure
            (finiteEnvironmentPositiveMassConfig
              (data.site₀ n) (data.site₁ n) (data.site₂ n) rest)
            (data.site₀ n) (data.site₁ n) (data.site₂ n)
            decayInteractionSign (data.good n rest) Set.univ
        ∂iidFiniteMassVectorLaw
          (finiteVolumeMassComplement
            (data.site₀ n) (data.site₁ n) (data.site₂ n)) := by
      apply lintegral_mono
      intro rest
      let fixed := finiteEnvironmentPositiveMassConfig
        (data.site₀ n) (data.site₁ n) (data.site₂ n) rest
      let goodLifted := actualThreeMassAllDistinctJointGoodLiftedMeasure
        fixed (data.site₀ n) (data.site₁ n) (data.site₂ n)
        decayInteractionSign (data.good n rest)
      let badLifted := actualThreeMassAllDistinctJointBadLiftedMeasure
        fixed (data.site₀ n) (data.site₁ n) (data.site₂ n)
        decayInteractionSign (data.good n rest)
      have hpoint := map_snd_good_add_bad_apply_le
        goodLifted badLifted data.regularCeiling (Real.sqrt 5)
        (data.goodCoarea n rest)
        (actualThreeMassAllDistinctJointGood_ae_mem_childCylinder
          fixed
          (finiteEnvironmentPositiveMassConfig_mass_mem_support
            (data.site₀ n) (data.site₁ n) (data.site₂ n) rest)
          (data.site₀ n) (data.site₁ n) (data.site₂ n)
          (data.good n rest)) hA
      rw [← actualThreeMassAllDistinctJointLiftedMeasure_eq_good_add_bad
        fixed (data.site₀ n) (data.site₁ n) (data.site₂ n)
        decayInteractionSign (data.good n rest)
        (data.good_measurable n rest),
        Measure.map_apply measurable_snd hA] at hpoint
      exact hpoint
    _ = regular * (volume : Measure Real) A +
        ∫⁻ rest,
          actualThreeMassAllDistinctJointBadLiftedMeasure
            (finiteEnvironmentPositiveMassConfig
              (data.site₀ n) (data.site₁ n) (data.site₂ n) rest)
            (data.site₀ n) (data.site₁ n) (data.site₂ n)
            decayInteractionSign (data.good n rest) Set.univ
          ∂iidFiniteMassVectorLaw
            (finiteVolumeMassComplement
              (data.site₀ n) (data.site₁ n) (data.site₂ n)) := by
      rw [lintegral_add_left measurable_const]
      simp only [lintegral_const, measure_univ, mul_one]
    _ ≤ regular * (volume : Measure Real) A + data.badError n := by
      gcongr
      exact data.badMass_le n

/-- The actual all-distinct coarea sequence discharges the complete marked
scalar volume-domination interface. -/
def canonicalDecaySectorAnnealed_allDistinct_volumeDomination_of_actualCoarea
    (data : ActualThreeMassAllDistinctAnnealedRawCoareaSequence) :
    CanonicalDecaySectorAnnealedMarkedIndexVolumeDomination
      (fun {_N} _inst ↦ AllDistinctModes) where
  constant := data.regularCeiling *
    (ENNReal.ofReal (Real.sqrt 5) * ENNReal.ofReal (Real.sqrt 5))
  constant_ne_top := ENNReal.mul_ne_top data.regularCeiling_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  error := data.badError
  error_tendsto_zero := data.badError_tendsto_zero
  bound := canonicalDecaySectorAnnealed_allDistinct_apply_le_of_actualCoarea
    data

/-! ## Marked index to an actual cluster subsequence -/

/-- Every cofinal subsequence eventually lies in the positive marked-index
range, so an estimate stated at `n + 1` reindexes without loss. -/
def markedIndexVolumeDomination_alongCofinal
    {keep : {N : Nat} → [NeZero N] → OrderedModeTriple N → Prop}
    (domination : CanonicalDecaySectorAnnealedMarkedIndexVolumeDomination keep)
    (subsequence : Nat → Nat)
    (hsubsequence : Tendsto subsequence atTop atTop) :
    CanonicalDecaySectorAnnealedEventualOpenVolumeDomination
      keep subsequence where
  constant := domination.constant
  constant_ne_top := domination.constant_ne_top
  error := fun j ↦ domination.error (subsequence j - 1)
  error_tendsto_zero := domination.error_tendsto_zero.comp
    ((tendsto_sub_atTop_nat 1).comp hsubsequence)
  bound := by
    intro G hG
    filter_upwards [hsubsequence.eventually (eventually_ge_atTop 1)]
      with j hj
    simpa only [Nat.sub_add_cancel hj] using
      domination.bound (subsequence j - 1) G hG.measurableSet

theorem allDistinct_cluster_le_smul_volume_of_markedIndex
    {omega : RandomEnsemble.SampleSpace} {target : FiniteMeasure Real}
    {cluster : DecaySectorClusterDecomposition
      canonicalIIDMassPhaseEnsemble omega target}
    (identification :
      CanonicalMainDecaySectorsAnnealedClusterIdentification cluster)
    (domination : CanonicalDecaySectorAnnealedMarkedIndexVolumeDomination
      (fun {_N} _inst ↦ AllDistinctModes)) :
    (cluster.allDistinct : Measure Real) ≤
      domination.constant • (volume : Measure Real) :=
  identification.allDistinct_le_smul_volume
    (markedIndexVolumeDomination_alongCofinal domination cluster.subsequence
      cluster.subsequence_strictMono.tendsto_atTop)

theorem childRepeated_cluster_le_smul_volume_of_markedIndex
    {omega : RandomEnsemble.SampleSpace} {target : FiniteMeasure Real}
    {cluster : DecaySectorClusterDecomposition
      canonicalIIDMassPhaseEnsemble omega target}
    (identification :
      CanonicalMainDecaySectorsAnnealedClusterIdentification cluster)
    (domination : CanonicalDecaySectorAnnealedMarkedIndexVolumeDomination
      (fun {_N} _inst ↦ ChildRepeated)) :
    (cluster.childRepeated : Measure Real) ≤
      domination.constant • (volume : Measure Real) :=
  identification.childRepeated_le_smul_volume
    (markedIndexVolumeDomination_alongCofinal domination cluster.subsequence
      cluster.subsequence_strictMono.tendsto_atTop)

/-- Both actual main-sector atlas sequences instantiate the exact cluster
dominations required by the broadened recombination theorem. -/
theorem canonicalDecayCluster_mainSectorDomination_of_actualAtlases
    {omega : RandomEnsemble.SampleSpace}
    {target : FiniteMeasure Real}
    {cluster : DecaySectorClusterDecomposition
      canonicalIIDMassPhaseEnsemble omega target}
    (identification :
      CanonicalMainDecaySectorsAnnealedClusterIdentification cluster)
    (allDistinct : ActualThreeMassAllDistinctAnnealedRawCoareaSequence)
    (childRepeated : ActualTwoMassChildRepeatedAnnealedAtlasSequence) :
    (cluster.allDistinct : Measure Real) ≤
        (canonicalDecaySectorAnnealed_allDistinct_volumeDomination_of_actualCoarea
          allDistinct).constant • (volume : Measure Real) ∧
      (cluster.childRepeated : Measure Real) ≤
        (canonicalDecaySectorAnnealed_childRepeated_volumeDomination_of_actualAtlas
          childRepeated).constant • (volume : Measure Real) := by
  exact ⟨
    allDistinct_cluster_le_smul_volume_of_markedIndex identification
      (canonicalDecaySectorAnnealed_allDistinct_volumeDomination_of_actualCoarea
        allDistinct),
    childRepeated_cluster_le_smul_volume_of_markedIndex identification
      (canonicalDecaySectorAnnealed_childRepeated_volumeDomination_of_actualAtlas
        childRepeated)⟩

/-- Consumer-ready complete broadened-mass upper bound from the two actual
main-sector atlas sequences.  No density premise is imposed on either
parent--child raw law. -/
theorem canonicalBroadenedCollisionPerSiteMeasureLimit_eventually_mass_le_of_actualMainSectorAtlases
    (omega : RandomEnsemble.SampleSpace)
    (cluster : DecaySectorClusterDecomposition
      canonicalIIDMassPhaseEnsemble omega
      (canonicalCollisionPerSiteMeasureLimit canonicalIIDMassPhaseEnsemble
        decayInteractionSign))
    (identification :
      CanonicalMainDecaySectorsAnnealedClusterIdentification cluster)
    (allDistinct : ActualThreeMassAllDistinctAnnealedRawCoareaSequence)
    (childRepeated : ActualTwoMassChildRepeatedAnnealedAtlasSequence)
    (time : Nat → Real) (htime_pos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop) :
    ∀ᶠ n in atTop,
      (canonicalBroadenedCollisionPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble decayInteractionSign
        (time n) (htime_pos n)).mass ≤
      (canonicalDecaySectorAnnealed_allDistinct_volumeDomination_of_actualCoarea
        allDistinct).constant.toNNReal +
      (canonicalDecaySectorAnnealed_childRepeated_volumeDomination_of_actualAtlas
        childRepeated).constant.toNNReal + 1 := by
  let allDomination :=
    canonicalDecaySectorAnnealed_allDistinct_volumeDomination_of_actualCoarea
      allDistinct
  let childDomination :=
    canonicalDecaySectorAnnealed_childRepeated_volumeDomination_of_actualAtlas
      childRepeated
  have hsectors := canonicalDecayCluster_mainSectorDomination_of_actualAtlases
    identification allDistinct childRepeated
  have hall : (cluster.allDistinct : Measure Real) ≤
      allDomination.constant.toNNReal • (volume : Measure Real) := by
    rw [ENNReal.smul_def,
      ENNReal.coe_toNNReal allDomination.constant_ne_top]
    simpa only [allDomination] using hsectors.1
  have hchild : (cluster.childRepeated : Measure Real) ≤
      childDomination.constant.toNNReal • (volume : Measure Real) := by
    rw [ENNReal.smul_def,
      ENNReal.coe_toNNReal childDomination.constant_ne_top]
    simpa only [childDomination] using hsectors.2
  exact
    canonicalBroadenedCollisionPerSiteMeasureLimit_eventually_mass_le_of_mainSectorDomination
      canonicalIIDMassPhaseEnsemble omega cluster
      allDomination.constant.toNNReal childDomination.constant.toNNReal
      hall hchild time htime_pos htime

end

end ArchonPhysics.CanonicalDecayActualMainSectorClusterInstantiation
