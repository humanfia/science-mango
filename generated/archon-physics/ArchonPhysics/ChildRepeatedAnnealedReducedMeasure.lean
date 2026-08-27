import ArchonPhysics.AnnealedFiniteMeasureWeakLimit
import ArchonPhysics.CanonicalRankFrequencyMarkedAnnealedMismatchBridge
import ArchonPhysics.ChildRepeatedCanonicalClusterLimit

/-!
# Annealed reduced measure for the child-repeated sector

This module constructs the genuine Giry barycenter of the finite-volume
child-repeated parent/child frequency measure.  Its evaluation is exactly the
expectation of the corresponding random atomic measure.  This is the legal
target of conditional two-mass spectral averaging; no realization-wise
statement is inferred from it.
-/

open scoped Topology ENNReal

namespace ArchonPhysics.ChildRepeatedAnnealedReducedMeasure

open ArchonPhysics
open ArchonPhysics.AnnealedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedAnnealedMismatchBridge
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedConvergenceInProbability
open ArchonPhysics.CanonicalComplexSpectralPolynomialMomentAllVolume
open ArchonPhysics.CanonicalJointFrequencyPerSiteMeasure
open ArchonPhysics.ChildRepeatedCanonicalClusterLimit
open ArchonPhysics.ChildRepeatedCanonicalWeakLimitBridge
open ArchonPhysics.ChildRepeatedDiagonalHybridKernel
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassMeasurableModeCoupling
open Filter MeasureTheory Set

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The unnormalized child-repeated marked measure is Giry-measurable in the
random mass sample. -/
theorem measurable_positiveWeightedRankFrequencyTripleMeasureWhere_childRepeated
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] :
    Measurable fun omega ↦
      positiveWeightedRankFrequencyTripleMeasureWhere
        (ensemble.restrictPositiveMass (N := N) omega) ChildRepeated := by
  classical
  unfold positiveWeightedRankFrequencyTripleMeasureWhere
  apply Finset.measurable_sum
  intro modes _hmodes
  by_cases hchild : ChildRepeated modes
  · have hevent : MeasurableSet {omega |
        IsPositiveOrderedTriple
          (ensemble.restrictPositiveMass (N := N) omega) modes ∧
            ChildRepeated modes} := by
      simpa only [hchild, and_true] using
        measurableSet_isPositiveOrderedTripleSample ensemble modes
    apply Measurable.ite hevent
    · have hcoefficient : Measurable fun omega ↦
          ENNReal.ofReal (harmonicOrderedNormalizedInteractionWeight
            (ensemble.restrictPositiveMass (N := N) omega) modes) :=
        (measurable_orderedNormalizedInteractionWeightSample
          ensemble modes).ennreal_ofReal
      have hdirac : Measurable fun omega ↦
          Measure.dirac (orderedRankFrequencyTriple
            (ensemble.restrictPositiveMass (N := N) omega) modes) :=
        Measure.measurable_dirac.comp
          (measurable_orderedRankFrequencyTriple_sample ensemble modes)
      refine Measure.measurable_of_measurable_coe _ fun A hA ↦ ?_
      simp only [Measure.smul_apply, smul_eq_mul]
      exact hcoefficient.mul ((Measure.measurable_coe hA).comp hdirac)
    · exact measurable_const
  · simp only [hchild, and_false, if_false]
    exact measurable_const

/-- The canonical per-site child-repeated marked finite measure is directly
Giry-measurable. -/
theorem measurable_toMeasure_canonicalChildRepeatedRankFrequencyPerSite
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) :
    Measurable fun omega ↦
      (canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
        ensemble n omega : Measure (Fin 3 → RankFrequencyMark)) := by
  have hraw :=
    measurable_positiveWeightedRankFrequencyTripleMeasureWhere_childRepeated
      (ensemble := ensemble) (N := n + 2)
  refine Measure.measurable_of_measurable_coe _ fun A hA ↦ ?_
  simp only [canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure,
    positiveWeightedRankFrequencyTripleFiniteMeasureWhere]
  exact measurable_const.mul ((Measure.measurable_coe hA).comp hraw)

/-- Giry measurability survives the two exact frequency projections. -/
theorem measurable_toMeasure_canonicalChildRepeatedReducedPerSite
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) :
    Measurable fun omega ↦
      ((((canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
          ensemble n omega).map forgetRankFrequencyTriple).map
        childRepeatedFrequencyProjection :
          FiniteMeasure (Real × Real)) : Measure (Real × Real)) := by
  have hforget := Measure.measurable_map forgetRankFrequencyTriple
    measurable_forgetRankFrequencyTriple
  have hpair := Measure.measurable_map childRepeatedFrequencyProjection
    measurable_childRepeatedFrequencyProjection
  exact hpair.comp (hforget.comp
    (measurable_toMeasure_canonicalChildRepeatedRankFrequencyPerSite
      ensemble n))

/-- Projection preserves the inherited child-sector mass ceiling almost
surely for the canonical iid ensemble. -/
theorem canonicalChildRepeatedReducedPerSite_mass_le_ae (n : Nat) :
    ∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
      (((canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
          canonicalIIDMassPhaseEnsemble n omega).map
        forgetRankFrequencyTriple).map
          childRepeatedFrequencyProjection).mass ≤
        childRepeatedCanonicalMassCeiling := by
  filter_upwards
    [canonicalPositiveVolumes_simpleOrderedSpectrum_ae
      canonicalIIDMassPhaseEnsemble] with omega hsimple
  rw [finiteMeasure_mass_map_of_measurable _ _
      measurable_childRepeatedFrequencyProjection,
    finiteMeasure_mass_map_of_measurable _ _
      measurable_forgetRankFrequencyTriple]
  exact canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure_mass_le
    canonicalIIDMassPhaseEnsemble n omega (hsimple (n + 1) (by omega))

/-- Genuine annealed reduced parent/child measure at one finite volume. -/
def canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure
    (n : Nat) : FiniteMeasure (Real × Real) :=
  annealedFiniteMeasure RandomEnsemble.canonicalLaw
    (fun omega ↦
      ((canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
        canonicalIIDMassPhaseEnsemble n omega).map
          forgetRankFrequencyTriple).map childRepeatedFrequencyProjection)
    (measurable_toMeasure_canonicalChildRepeatedReducedPerSite
      canonicalIIDMassPhaseEnsemble n)
    childRepeatedCanonicalMassCeiling
    (canonicalChildRepeatedReducedPerSite_mass_le_ae n)

/-- Evaluation of the annealed reduced law is exactly the expectation of
the random atomic child-repeated reduced law. -/
theorem canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure_apply
    (n : Nat) {A : Set (Real × Real)} (hA : MeasurableSet A) :
    (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n :
      Measure (Real × Real)) A =
      ∫⁻ omega,
        (((((canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
            canonicalIIDMassPhaseEnsemble n omega).map
          forgetRankFrequencyTriple).map childRepeatedFrequencyProjection :
            FiniteMeasure (Real × Real)) : Measure (Real × Real)) A)
        ∂ RandomEnsemble.canonicalLaw := by
  exact annealedFiniteMeasure_apply RandomEnsemble.canonicalLaw
    (fun omega ↦
      ((canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
        canonicalIIDMassPhaseEnsemble n omega).map
          forgetRankFrequencyTriple).map childRepeatedFrequencyProjection)
    (measurable_toMeasure_canonicalChildRepeatedReducedPerSite
      canonicalIIDMassPhaseEnsemble n)
    childRepeatedCanonicalMassCeiling
    (canonicalChildRepeatedReducedPerSite_mass_le_ae n) hA

end

end ArchonPhysics.ChildRepeatedAnnealedReducedMeasure
