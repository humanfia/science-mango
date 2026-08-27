import ArchonPhysics.ChildRepeatedAnnealedReducedMeasure
import ArchonPhysics.FiniteMeasureAnnealedWeakTestDomination
import ArchonPhysics.ChildRepeatedMismatchPushforwardLInfinity
import ArchonPhysics.ChildRepeatedReducedResonanceLineNullity

/-!
# Annealed weak-test closure for child-repeated clusters

Finite-volume child-repeated spectral measures are atomic, so a uniform
setwise Lebesgue bound cannot hold realization by realization.  This module
uses the valid replacement: the genuine annealed reduced measure satisfies a
setwise estimate, while quenched and annealed measures become asymptotically
equal against bounded continuous tests.  The latter is precisely the
self-averaging statement still required from the random lattice model.
-/

open scoped Topology ENNReal BoundedContinuousFunction

namespace ArchonPhysics.ChildRepeatedAnnealedWeakTestLInfinity

open ArchonPhysics
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.ChildRepeatedAnnealedReducedMeasure
open ArchonPhysics.ChildRepeatedCanonicalClusterLimit
open ArchonPhysics.ChildRepeatedCanonicalWeakLimitBridge
open ArchonPhysics.ChildRepeatedDiagonalHybridKernel
open ArchonPhysics.ChildRepeatedMismatchPushforwardLInfinity
open ArchonPhysics.ChildRepeatedReducedResonanceLineNullity
open ArchonPhysics.ChildRepeatedScalarClusterHybridLift
open ArchonPhysics.FiniteMeasureAnnealedWeakTestDomination
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open Filter MeasureTheory

noncomputable section

/-- Annealed planar domination transfers to a canonical quenched child
cluster under bounded-continuous-test self-averaging. -/
theorem childRepeatedScalarClusterHybridLift_reduced_le_volume_of_annealed_of_testAgainstNN_dist
    {omega : RandomEnsemble.SampleSpace}
    {size : Nat → Nat} {scalarTarget : FiniteMeasure Real}
    (lift : ChildRepeatedScalarClusterHybridLiftData
      canonicalIIDMassPhaseEnsemble omega size scalarTarget)
    (C : ENNReal) (hC : C ≠ ∞)
    (error : Nat → ENNReal) (herror : Tendsto error atTop (nhds 0))
    (hbound : ∀ j A, MeasurableSet A →
      (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure
        (size (lift.subsequence j)) : Measure (Real × Real)) A ≤
          C * (volume : Measure (Real × Real)) A + error j)
    (hclose : ∀ f : (Real × Real) →ᵇ NNReal,
      Tendsto
        (fun j ↦ dist
          (((canonicalChildRepeatedFrequencyPerSiteFiniteMeasure
              canonicalIIDMassPhaseEnsemble
              (size (lift.subsequence j)) omega).map
            childRepeatedFrequencyProjection).testAgainstNN f)
          ((canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure
              (size (lift.subsequence j))).testAgainstNN f))
        atTop (nhds 0)) :
    ((((lift.markedTarget.map forgetRankFrequencyTriple).map
        childRepeatedFrequencyProjection :
      FiniteMeasure (Real × Real)) : Measure (Real × Real))) ≤
      C • (volume : Measure (Real × Real)) := by
  let quenched : Nat → FiniteMeasure (Real × Real) := fun j ↦
    (canonicalChildRepeatedFrequencyPerSiteFiniteMeasure
      canonicalIIDMassPhaseEnsemble
      (size (lift.subsequence j)) omega).map
        childRepeatedFrequencyProjection
  let annealed : Nat → FiniteMeasure (Real × Real) := fun j ↦
    canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure
      (size (lift.subsequence j))
  let target : FiniteMeasure (Real × Real) :=
    (lift.markedTarget.map forgetRankFrequencyTriple).map
      childRepeatedFrequencyProjection
  have hfrequency := canonicalChildRepeated_frequencyMarginal_tendsto
    canonicalIIDMassPhaseEnsemble omega
      (fun j ↦ size (lift.subsequence j))
      lift.markedTarget lift.markedTendsto
  have hquenched : Tendsto quenched atTop (nhds target) := by
    exact FiniteMeasure.tendsto_map_of_tendsto_of_continuous
      (fun j ↦ canonicalChildRepeatedFrequencyPerSiteFiniteMeasure
        canonicalIIDMassPhaseEnsemble
        (size (lift.subsequence j)) omega)
      (lift.markedTarget.map forgetRankFrequencyTriple)
      hfrequency continuous_childRepeatedFrequencyProjection
  exact
    finiteMeasure_le_smul_of_annealed_apply_le_of_quenched_tendsto_of_testAgainstNN_dist
      quenched annealed target hquenched (by
        intro f
        exact hclose f)
      (volume : Measure (Real × Real)) C hC error herror (by
        intro j A hA
        exact hbound j A hA)

/-- The corresponding reduced-law upper absolute continuity. -/
theorem childRepeatedScalarClusterHybridLift_reduced_absolutelyContinuous_of_annealed_of_testAgainstNN_dist
    {omega : RandomEnsemble.SampleSpace}
    {size : Nat → Nat} {scalarTarget : FiniteMeasure Real}
    (lift : ChildRepeatedScalarClusterHybridLiftData
      canonicalIIDMassPhaseEnsemble omega size scalarTarget)
    (C : ENNReal) (hC : C ≠ ∞)
    (error : Nat → ENNReal) (herror : Tendsto error atTop (nhds 0))
    (hbound : ∀ j A, MeasurableSet A →
      (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure
        (size (lift.subsequence j)) : Measure (Real × Real)) A ≤
          C * (volume : Measure (Real × Real)) A + error j)
    (hclose : ∀ f : (Real × Real) →ᵇ NNReal,
      Tendsto
        (fun j ↦ dist
          (((canonicalChildRepeatedFrequencyPerSiteFiniteMeasure
              canonicalIIDMassPhaseEnsemble
              (size (lift.subsequence j)) omega).map
            childRepeatedFrequencyProjection).testAgainstNN f)
          ((canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure
              (size (lift.subsequence j))).testAgainstNN f))
        atTop (nhds 0)) :
    ((((lift.markedTarget.map forgetRankFrequencyTriple).map
        childRepeatedFrequencyProjection :
      FiniteMeasure (Real × Real)) : Measure (Real × Real))) ≪
      (volume : Measure (Real × Real)) := by
  exact
    (childRepeatedScalarClusterHybridLift_reduced_le_volume_of_annealed_of_testAgainstNN_dist
      lift C hC error herror hbound hclose).absolutelyContinuous.trans
        Measure.smul_absolutelyContinuous

/-- The annealed route gives the scalar mismatch `L∞` estimate with the
same transverse-frequency factor as the deterministic planar endpoint. -/
theorem childRepeatedScalarClusterHybridLift_scalar_le_volume_of_annealed_of_testAgainstNN_dist
    {omega : RandomEnsemble.SampleSpace}
    {size : Nat → Nat} {scalarTarget : FiniteMeasure Real}
    (lift : ChildRepeatedScalarClusterHybridLiftData
      canonicalIIDMassPhaseEnsemble omega size scalarTarget)
    (C : ENNReal) (hC : C ≠ ∞)
    (error : Nat → ENNReal) (herror : Tendsto error atTop (nhds 0))
    (hbound : ∀ j A, MeasurableSet A →
      (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure
        (size (lift.subsequence j)) : Measure (Real × Real)) A ≤
          C * (volume : Measure (Real × Real)) A + error j)
    (hclose : ∀ f : (Real × Real) →ᵇ NNReal,
      Tendsto
        (fun j ↦ dist
          (((canonicalChildRepeatedFrequencyPerSiteFiniteMeasure
              canonicalIIDMassPhaseEnsemble
              (size (lift.subsequence j)) omega).map
            childRepeatedFrequencyProjection).testAgainstNN f)
          ((canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure
              (size (lift.subsequence j))).testAgainstNN f))
        atTop (nhds 0)) :
    (scalarTarget : Measure Real) ≤
      (C * ENNReal.ofReal collisionFrequencyCeiling) •
        (volume : Measure Real) := by
  apply childRepeatedScalarClusterHybridLift_scalar_le_volume_of_reduced_le_volume
    lift C
  exact
    childRepeatedScalarClusterHybridLift_reduced_le_volume_of_annealed_of_testAgainstNN_dist
      lift C hC error herror hbound hclose

/-- In particular the exact child-repeated resonance atom vanishes. -/
theorem ChildRepeatedScalarClusterHybridLiftData.scalar_singleton_zero_of_annealed_of_testAgainstNN_dist
    {omega : RandomEnsemble.SampleSpace}
    {size : Nat → Nat} {scalarTarget : FiniteMeasure Real}
    (lift : ChildRepeatedScalarClusterHybridLiftData
      canonicalIIDMassPhaseEnsemble omega size scalarTarget)
    (C : ENNReal) (hC : C ≠ ∞)
    (error : Nat → ENNReal) (herror : Tendsto error atTop (nhds 0))
    (hbound : ∀ j A, MeasurableSet A →
      (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure
        (size (lift.subsequence j)) : Measure (Real × Real)) A ≤
          C * (volume : Measure (Real × Real)) A + error j)
    (hclose : ∀ f : (Real × Real) →ᵇ NNReal,
      Tendsto
        (fun j ↦ dist
          (((canonicalChildRepeatedFrequencyPerSiteFiniteMeasure
              canonicalIIDMassPhaseEnsemble
              (size (lift.subsequence j)) omega).map
            childRepeatedFrequencyProjection).testAgainstNN f)
          ((canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure
              (size (lift.subsequence j))).testAgainstNN f))
        atTop (nhds 0)) :
    (scalarTarget : Measure Real) ({0} : Set Real) = 0 := by
  exact ChildRepeatedScalarClusterHybridLiftData.scalar_singleton_zero_of_reducedAC lift
    (childRepeatedScalarClusterHybridLift_reduced_absolutelyContinuous_of_annealed_of_testAgainstNN_dist
      lift C hC error herror hbound hclose)

end


end ArchonPhysics.ChildRepeatedAnnealedWeakTestLInfinity
