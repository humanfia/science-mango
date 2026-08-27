import ArchonPhysics.BoundedMassCompactSupportedFiniteMeasureSubsequence
import ArchonPhysics.ChildRepeatedCanonicalSubsequenceLimit

/-!
# Hybrid marked lift of an arbitrary scalar child-repeated cluster

The simultaneous four-sector compactness theorem selects scalar mismatch
cluster points.  A scalar cluster alone forgets the singular parent/child
geometry.  Here any such supplied child-repeated scalar cluster is lifted,
after a further cofinal subsequence, to a marked finite-measure cluster.  Weak
limit uniqueness identifies the supplied scalar cluster exactly with the
marked cluster's mismatch pushforward, while the latter retains the diagonal
and `omega_parent - 2 * omega_child` hybrid carriers.

This is a carrier theorem, not a zero-atom theorem.
-/

open scoped Topology

namespace ArchonPhysics.ChildRepeatedScalarClusterHybridLift

open ArchonPhysics
open ArchonPhysics.BoundedMassCompactSupportedFiniteMeasureSubsequence
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.ChildRepeatedCanonicalClusterLimit
open ArchonPhysics.ChildRepeatedCanonicalSubsequenceLimit
open ArchonPhysics.ChildRepeatedCanonicalWeakLimitBridge
open ArchonPhysics.ChildRepeatedDiagonalHybridKernel
open ArchonPhysics.ChildRepeatedFrequencyDiagonalWeakLimit
open ArchonPhysics.DecayChannelMismatchSectorWeakLimit
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Exact geometric lift data for one supplied scalar child-sector cluster. -/
structure ChildRepeatedScalarClusterHybridLiftData
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (size : Nat -> Nat) (scalarTarget : FiniteMeasure Real) where
  markedTarget : FiniteMeasure (Fin 3 -> RankFrequencyMark)
  subsequence : Nat -> Nat
  strictMono : StrictMono subsequence
  markedTendsto : Tendsto
    (fun j => canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
      ensemble (size (subsequence j)) omega)
    atTop (nhds markedTarget)
  scalar_eq_mismatch : scalarTarget =
    (markedTarget.map forgetRankFrequencyTriple).map
      (frequencyTripleMismatch decayInteractionSign)
  markedDiagonal :
    (markedTarget : Measure (Fin 3 -> RankFrequencyMark))
      (childRepeatedRankFrequencyDiagonalᶜ) = 0
  frequencyDiagonal :
    (markedTarget.map forgetRankFrequencyTriple : Measure (Fin 3 -> Real))
      (childRepeatedFrequencyDiagonalᶜ) = 0
  frequencyReconstruction :
    (((markedTarget.map forgetRankFrequencyTriple).map
      childRepeatedFrequencyProjection).map
        childRepeatedFrequencyDiagonalLift) =
      markedTarget.map forgetRankFrequencyTriple
  mismatchReduced :
    (markedTarget.map forgetRankFrequencyTriple).map
        (frequencyTripleMismatch decayInteractionSign) =
      ((markedTarget.map forgetRankFrequencyTriple).map
        childRepeatedFrequencyProjection).map childRepeatedDecayMismatch
  hybridGraph :
    Measure.map childRepeatedHybridCoordinates
        (markedTarget.map forgetRankFrequencyTriple : Measure (Fin 3 -> Real))
      (childRepeatedHybridGraphᶜ) = 0

/-- Every scalar child-repeated weak cluster along simple frozen volumes has
a cofinal marked hybrid lift.  In particular this applies to the child member
of any common four-sector subsequence. -/
theorem exists_childRepeatedScalarClusterHybridLift_of_simple
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (size : Nat -> Nat) (scalarTarget : FiniteMeasure Real)
    (hsimple : forall j,
      SimpleOrderedSpectrum
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := size j + 2) omega)))
    (hscalar : Tendsto
      (fun j => canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
        (fun {_N} _inst => ChildRepeated) (size j) omega)
      atTop (nhds scalarTarget)) :
    Nonempty (ChildRepeatedScalarClusterHybridLiftData
      ensemble omega size scalarTarget) := by
  let source : Nat -> FiniteMeasure (Fin 3 -> RankFrequencyMark) :=
    fun j => canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
      ensemble (size j) omega
  have hmass : forall j, (source j).mass <=
      childRepeatedCanonicalMassCeiling := by
    intro j
    dsimp only [source]
    exact canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure_mass_le
      ensemble (size j) omega (hsimple j)
  have hsupport : forall j,
      (source j : Measure (Fin 3 -> RankFrequencyMark))
        (collisionRankFrequencyTripleSupportᶜ) = 0 := by
    intro j
    dsimp only [source]
    exact
      canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure_compl_uniformSupport_eq_zero
        ensemble (size j) omega
  obtain ⟨markedTarget, subsequence, hmono, hmarkedRaw⟩ :=
    exists_weaklyConvergent_subsequence_of_compactSupport_of_mass_le
      source childRepeatedCanonicalMassCeiling
      collisionRankFrequencyTripleSupport
      collisionRankFrequencyTripleSupport_isCompact hmass hsupport
  have hmarked : Tendsto
      (fun j => canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
        ensemble (size (subsequence j)) omega)
      atTop (nhds markedTarget) := by
    simpa [source, Function.comp_def] using hmarkedRaw
  let selectedSize : Nat -> Nat := fun j => size (subsequence j)
  have hscalarFromMarked := canonicalChildRepeated_decaySector_tendsto
    ensemble omega selectedSize markedTarget (by
      simpa [selectedSize] using hmarked)
  have hscalarSelected : Tendsto
      (fun j => canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
        (fun {_N} _inst => ChildRepeated) (size (subsequence j)) omega)
      atTop (nhds scalarTarget) := by
    simpa [Function.comp_def] using hscalar.comp hmono.tendsto_atTop
  have hscalarIdentification : scalarTarget =
      (markedTarget.map forgetRankFrequencyTriple).map
        (frequencyTripleMismatch decayInteractionSign) :=
    tendsto_nhds_unique hscalarSelected (by
      simpa [selectedSize] using hscalarFromMarked)
  have hmarkedDiagonal :=
    canonicalChildRepeatedMarkedWeakLimit_compl_diagonal_eq_zero
      ensemble omega selectedSize markedTarget (by
        simpa [selectedSize] using hmarked)
  have hfrequencyDiagonal :=
    canonicalChildRepeatedMarkedWeakLimit_frequencyMarginal_compl_diagonal_eq_zero
      ensemble omega selectedSize markedTarget (by
        simpa [selectedSize] using hmarked)
  have hreconstruction :=
    canonicalChildRepeatedMarkedWeakLimit_frequency_reconstruction
      ensemble omega selectedSize markedTarget (by
        simpa [selectedSize] using hmarked)
  have hreduced :=
    canonicalChildRepeatedMarkedWeakLimit_decayMismatch_eq_reduced
      ensemble omega selectedSize markedTarget (by
        simpa [selectedSize] using hmarked)
  have hhybrid :=
    canonicalChildRepeatedMarkedWeakLimit_hybrid_compl_graph_eq_zero
      ensemble omega selectedSize markedTarget (by
        simpa [selectedSize] using hmarked)
  exact ⟨{
    markedTarget := markedTarget
    subsequence := subsequence
    strictMono := hmono
    markedTendsto := hmarked
    scalar_eq_mismatch := hscalarIdentification
    markedDiagonal := hmarkedDiagonal
    frequencyDiagonal := hfrequencyDiagonal
    frequencyReconstruction := hreconstruction
    mismatchReduced := hreduced
    hybridGraph := hhybrid }⟩

/-- The supplied scalar cluster's zero atom is exactly the reduced hybrid
law's mass on `omega_parent = 2 * omega_child`; no nullity is assumed. -/
theorem ChildRepeatedScalarClusterHybridLiftData.scalar_singleton_zero_iff
    {ensemble : IIDMassPhaseEnsemble Omega} {omega : Omega}
    {size : Nat -> Nat} {scalarTarget : FiniteMeasure Real}
    (lift : ChildRepeatedScalarClusterHybridLiftData
      ensemble omega size scalarTarget) :
    (scalarTarget : Measure Real) ({0} : Set Real) = 0 ↔
      (((lift.markedTarget.map forgetRankFrequencyTriple).map
        childRepeatedFrequencyProjection :
        FiniteMeasure (Real × Real)) : Measure (Real × Real))
          childRepeatedReducedResonanceLine = 0 := by
  have happly := congrArg
    (fun measure : FiniteMeasure Real =>
      (measure : Measure Real) ({0} : Set Real))
    lift.scalar_eq_mismatch
  have hmismatchIff :
      ((((lift.markedTarget.map forgetRankFrequencyTriple).map
          (frequencyTripleMismatch decayInteractionSign) :
        FiniteMeasure Real) : Measure Real) ({0} : Set Real) = 0) ↔
      (((lift.markedTarget.map forgetRankFrequencyTriple).map
        childRepeatedFrequencyProjection :
        FiniteMeasure (Real × Real)) : Measure (Real × Real))
          childRepeatedReducedResonanceLine = 0 := by
    rw [lift.mismatchReduced]
    rw [map_childRepeatedDecayMismatch_singleton_zero]
  constructor
  · intro hscalar
    apply hmismatchIff.mp
    rw [← happly]
    exact hscalar
  · intro hline
    rw [happly]
    exact hmismatchIff.mpr hline

end

end ArchonPhysics.ChildRepeatedScalarClusterHybridLift
