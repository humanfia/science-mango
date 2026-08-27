import ArchonPhysics.ChildRepeatedBoundedDifferenceAudit

/-!
# Exact annealed center of finite-product child weak tests

The real weak test used by the bounded-difference audit is a function of the
first `n+2` iid masses.  Its product-space expectation is exactly the
`testAgainstNN` pairing of the genuine canonical annealed reduced child law.
Thus any future concentration estimate is centered at the same annealed law
controlled by the actual two-mass coarea reconstruction.
-/

open scoped ENNReal NNReal BoundedContinuousFunction

namespace ArchonPhysics.ChildRepeatedAnnealedWeakTestCenter

open ArchonPhysics
open ArchonPhysics.ActualTwoMassChildRepeatedDeterministicBridge
open ArchonPhysics.ChildRepeatedAnnealedReducedMeasure
open ArchonPhysics.ChildRepeatedBoundedDifferenceAudit
open ArchonPhysics.ChildRepeatedCanonicalWeakLimitBridge
open ArchonPhysics.ChildRepeatedDiagonalHybridKernel
open ArchonPhysics.ChildRepeatedFrequencyDiagonalWeakLimit
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory ProbabilityTheory Set

noncomputable section

/-- The pair-indexed finite-volume child law, packaged as a finite measure. -/
def finChildRepeatedReducedFiniteMeasure
    (n : Nat) (x : Fin (n + 2) → Real) :
    FiniteMeasure (Real × Real) :=
  (perSitePositiveWeightedFrequencyTripleFiniteMeasureWhere
    (finChildRepeatedPositiveMassConfig n x) ChildRepeated).map
      childRepeatedFrequencyProjection

theorem finChildRepeatedReducedFiniteMeasure_toMeasure_eq_pairMeasure
    (n : Nat) (x : Fin (n + 2) → Real) :
    (finChildRepeatedReducedFiniteMeasure n x : Measure (Real × Real)) =
      childRepeatedReducedPerSitePairMeasure
        (finChildRepeatedPositiveMassConfig n x) := by
  unfold finChildRepeatedReducedFiniteMeasure
  change Measure.map childRepeatedFrequencyProjection
      (perSitePositiveWeightedFrequencyTripleMeasureWhere
        (finChildRepeatedPositiveMassConfig n x) ChildRepeated) = _
  exact map_perSiteChildRepeatedFrequencyMeasure_eq_pairMeasure
    (finChildRepeatedPositiveMassConfig n x)

/-- The real raw integral is exactly the real coercion of the finite-measure
weak test functional. -/
theorem finChildRepeatedReducedRawTest_eq_testAgainstNN
    (n : Nat) (test : (Real × Real) →ᵇ NNReal)
    (x : Fin (n + 2) → Real) :
    finChildRepeatedReducedRawTest n test x =
      ((finChildRepeatedReducedFiniteMeasure n x).testAgainstNN test : Real) := by
  unfold finChildRepeatedReducedRawTest FiniteMeasure.testAgainstNN
  rw [finChildRepeatedReducedFiniteMeasure_toMeasure_eq_pairMeasure]
  rfl

/-- The first `n+2` canonical positive mass representatives. -/
def canonicalChildRepeatedFinMassVector
    (n : Nat) (omega : RandomEnsemble.SampleSpace) :
    Fin (n + 2) → Real :=
  fun i ↦ massAt i.val omega

theorem measurable_canonicalChildRepeatedFinMassVector (n : Nat) :
    Measurable (canonicalChildRepeatedFinMassVector n) := by
  exact measurable_pi_lambda _ fun i ↦ measurable_massAt i.val

/-- The finite vector has the genuine iid product law. -/
theorem canonicalChildRepeatedFinMassVector_hasLaw (n : Nat) :
    HasLaw (canonicalChildRepeatedFinMassVector n)
      (Measure.pi fun _ : Fin (n + 2) ↦ massCoordinateLaw)
      canonicalLaw := by
  exact (massCoordinates_iIndep.precomp Fin.val_injective).hasLaw_pi
    (fun i ↦ massAt_hasLaw i.val)

theorem finChildRepeatedPositiveMassConfig_canonicalFinMassVector
    (n : Nat) (omega : RandomEnsemble.SampleSpace) :
    finChildRepeatedPositiveMassConfig n
        (canonicalChildRepeatedFinMassVector n omega) =
      canonicalIIDMassPhaseEnsemble.restrictPositiveMass
        (N := n + 2) omega := by
  rw [Lattice.PositiveMassConfig.mk.injEq]
  funext site
  change clippedMass (massAt site.val omega) = massAt site.val omega
  exact clippedMass_eq_self (clippedMass_mem_support _)

/-- On canonical samples, the finite-vector law is the exact projected
child-repeated reduced law used to define the annealed barycenter. -/
theorem finChildRepeatedReducedFiniteMeasure_canonicalFinMassVector
    (n : Nat) (omega : RandomEnsemble.SampleSpace) :
    finChildRepeatedReducedFiniteMeasure n
        (canonicalChildRepeatedFinMassVector n omega) =
      ((canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
          canonicalIIDMassPhaseEnsemble n omega).map
        CanonicalRankFrequencyMarkedMeasure.forgetRankFrequencyTriple).map
          childRepeatedFrequencyProjection := by
  rw [map_canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure_forgetRank]
  unfold finChildRepeatedReducedFiniteMeasure
    canonicalChildRepeatedFrequencyPerSiteFiniteMeasure
  rw [finChildRepeatedPositiveMassConfig_canonicalFinMassVector]

/-- A bounded-continuous test of an annealed finite measure is the ordinary
expectation of the corresponding tests of the random finite measures. -/
theorem annealedFiniteMeasure_testAgainstNN_eq_integral
    {Omega X : Type*} [MeasurableSpace Omega]
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (probability : Measure Omega) [IsFiniteMeasure probability]
    (randomMeasure : Omega → FiniteMeasure X)
    (hmeasure : Measurable fun omega ↦
      (randomMeasure omega : Measure X))
    (massCeiling : NNReal)
    (hmass : ∀ᵐ omega ∂probability,
      (randomMeasure omega).mass ≤ massCeiling)
    (test : X →ᵇ NNReal) :
    ((AnnealedFiniteMeasureWeakLimit.annealedFiniteMeasure
        probability randomMeasure hmeasure massCeiling hmass).testAgainstNN
      test : Real) =
      ∫ omega, ((randomMeasure omega).testAgainstNN test : Real)
        ∂probability := by
  let integrand : Omega → ENNReal := fun omega ↦
    ∫⁻ x, (test x : ENNReal) ∂(randomMeasure omega : Measure X)
  have hintegrand : Measurable integrand := by
    exact (Measure.measurable_lintegral
      test.measurable_coe_ennreal_comp).comp hmeasure
  have hfinite : ∀ omega, integrand omega < ∞ := by
    intro omega
    exact test.lintegral_lt_top_of_nnreal (randomMeasure omega)
  have hbind :
      ∫⁻ x, (test x : ENNReal)
          ∂(AnnealedFiniteMeasureWeakLimit.annealedFiniteMeasure
            probability randomMeasure hmeasure massCeiling hmass :
              Measure X) =
        ∫⁻ omega, integrand omega ∂probability := by
    change
      ∫⁻ x, (test x : ENNReal)
          ∂(probability.bind fun omega ↦
            (randomMeasure omega : Measure X)) = _
    exact Measure.lintegral_bind hmeasure.aemeasurable
      test.measurable_coe_ennreal_comp.aemeasurable
  have hright :
      ∫ omega, ((randomMeasure omega).testAgainstNN test : Real)
          ∂probability =
        (∫⁻ omega, integrand omega ∂probability).toReal := by
    rw [← integral_toReal hintegrand.aemeasurable
      (ae_of_all probability hfinite)]
    apply integral_congr_ae
    filter_upwards with omega
    rfl
  rw [hright, ← hbind]
  rfl

/-- Exact identification of the finite-product concentration center with the
canonical annealed reduced child weak test. -/
theorem integral_finChildRepeatedReducedRawTest_eq_annealed_testAgainstNN
    (n : Nat) (test : (Real × Real) →ᵇ NNReal) :
    ∫ x, finChildRepeatedReducedRawTest n test x
        ∂(Measure.pi fun _ : Fin (n + 2) ↦ massCoordinateLaw) =
      (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n).testAgainstNN
        test := by
  let randomMeasure : RandomEnsemble.SampleSpace →
      FiniteMeasure (Real × Real) := fun omega ↦
    ((canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
        canonicalIIDMassPhaseEnsemble n omega).map
      CanonicalRankFrequencyMarkedMeasure.forgetRankFrequencyTriple).map
        childRepeatedFrequencyProjection
  have htransport :=
    (canonicalChildRepeatedFinMassVector_hasLaw n).integral_comp
      (measurable_finChildRepeatedReducedRawTest n test).aestronglyMeasurable
  have hpoint (omega : RandomEnsemble.SampleSpace) :
      finChildRepeatedReducedRawTest n test
          (canonicalChildRepeatedFinMassVector n omega) =
        ((randomMeasure omega).testAgainstNN test : Real) := by
    rw [finChildRepeatedReducedRawTest_eq_testAgainstNN]
    rw [finChildRepeatedReducedFiniteMeasure_canonicalFinMassVector]
  have hannealed := annealedFiniteMeasure_testAgainstNN_eq_integral
    canonicalLaw randomMeasure
    (measurable_toMeasure_canonicalChildRepeatedReducedPerSite
      canonicalIIDMassPhaseEnsemble n)
    ChildRepeatedCanonicalClusterLimit.childRepeatedCanonicalMassCeiling
    (canonicalChildRepeatedReducedPerSite_mass_le_ae n) test
  calc
    ∫ x, finChildRepeatedReducedRawTest n test x
        ∂(Measure.pi fun _ : Fin (n + 2) ↦ massCoordinateLaw) =
      ∫ omega, finChildRepeatedReducedRawTest n test
          (canonicalChildRepeatedFinMassVector n omega) ∂canonicalLaw :=
        htransport.symm
    _ = ∫ omega, ((randomMeasure omega).testAgainstNN test : Real)
          ∂canonicalLaw := by
        apply integral_congr_ae
        exact ae_of_all _ hpoint
    _ = _ := hannealed.symm

end

end ArchonPhysics.ChildRepeatedAnnealedWeakTestCenter
