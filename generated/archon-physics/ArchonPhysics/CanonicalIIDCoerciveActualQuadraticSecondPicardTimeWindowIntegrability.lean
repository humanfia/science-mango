import ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardHistoryIntegrability

/-!
# Joint finite-time-window integrability of the actual quadratic second Picard source

The fixed-time result is strengthened here to the product of the canonical
sample space with a compact time interval.  This is the measure-theoretic
interface needed for legitimate Fubini and iterated Duhamel manipulations; it
does not assert any estimate on a kinetic time scale.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardTimeWindowIntegrability

open scoped BigOperators Matrix
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualFreeQuadraticHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveExpectationHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FiniteHarmonicHaarPhasePropagation
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.PhaseEnergyModeCoordinates
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]

theorem continuous_canonicalOrderedFreeCoordinate_time
    (a : Real) (omega : CanonicalSample) (k : OrderedModeIndex N) :
    Continuous fun time : Real =>
      canonicalOrderedFreeCoordinate (N := N) a time omega k := by
  unfold canonicalOrderedFreeCoordinate freeRealModeCoordinate
    realPhaseModeCoordinate physicalFreePhaseEvolution
    freeHarmonicPhaseEvolution harmonicPhaseAdvance
  have htranslated : Continuous fun time : Real =>
      (((-canonicalOrderedFrequency (N := N) k omega) * time /
          (2 * Real.pi) : Real) : UnitAddCircle) +
        orderedPhaseSample canonicalIIDMassPhaseEnsemble omega k := by
    fun_prop
  exact continuous_const.mul
    (Complex.continuous_re.comp (continuous_unitPhase.comp htranslated))

theorem continuous_canonicalOrderedFreeQuadraticTensorSource_time
    (a : Real) (omega : CanonicalSample) (observed : OrderedModeIndex N) :
    Continuous fun time : Real =>
      canonicalOrderedFreeQuadraticTensorSource (N := N)
        a observed time omega := by
  unfold canonicalOrderedFreeQuadraticTensorSource
  apply continuous_finsetSum Finset.univ
  intro modes _hmodes
  apply continuous_const.mul
  apply continuous_finsetProd Finset.univ
  intro r _hr
  exact Complex.continuous_ofReal.comp
    (continuous_canonicalOrderedFreeCoordinate_time (N := N) a omega
      ((orderedIndexEquiv).symm (modes r)))

theorem continuous_canonicalOrderedFreeQuadraticRotatedSource_time
    (a : Real) (omega : CanonicalSample) (observed : OrderedModeIndex N) :
    Continuous fun time : Real =>
      canonicalOrderedFreeQuadraticRotatedSource (N := N)
        a observed time omega := by
  unfold canonicalOrderedFreeQuadraticRotatedSource
  exact
    (continuous_const.mul
      (continuous_phaseFactor_real.comp (by fun_prop))).mul
      (continuous_canonicalOrderedFreeQuadraticTensorSource_time
        (N := N) a omega observed)

theorem continuous_canonicalOrderedQuadraticFirstPicardCoefficient_time
    (kappa a : Real) (omega : CanonicalSample)
    (observed : OrderedModeIndex N) :
    Continuous fun time : Real =>
      canonicalOrderedQuadraticFirstPicardCoefficient (N := N)
        kappa a time omega observed := by
  unfold canonicalOrderedQuadraticFirstPicardCoefficient
  apply intervalIntegral.continuous_primitive
  intro left right
  exact
    (continuous_const.mul
      (continuous_canonicalOrderedFreeQuadraticRotatedSource_time
        (N := N) a omega observed)).intervalIntegrable left right

theorem continuous_canonicalOrderedQuadraticFirstPicardCoordinate_time
    (kappa a : Real) (omega : CanonicalSample)
    (observed : OrderedModeIndex N) :
    Continuous fun time : Real =>
      canonicalOrderedQuadraticFirstPicardCoordinate (N := N)
        kappa a time omega observed := by
  unfold canonicalOrderedQuadraticFirstPicardCoordinate
    interactionPictureCorrectionCoordinate phaseRenormalize
  have hcoefficient :=
    continuous_canonicalOrderedQuadraticFirstPicardCoefficient_time
      (N := N) kappa a omega observed
  have hphase : Continuous fun time : Real =>
      phaseFactor (-(canonicalOrderedFrequency (N := N) observed omega * time)) :=
    continuous_phaseFactor_real.comp (by fun_prop)
  exact (continuous_const.mul
    (Complex.continuous_re.comp (hphase.mul hcoefficient))).div_const _

theorem continuous_canonicalOrderedQuadraticSecondPicardCrossSource_time
    (kappa a : Real) (omega : CanonicalSample)
    (observed : OrderedModeIndex N) :
    Continuous fun time : Real =>
      canonicalOrderedQuadraticSecondPicardCrossSource (N := N)
        kappa a observed time omega := by
  unfold canonicalOrderedQuadraticSecondPicardCrossSource
  apply continuous_finsetSum Finset.univ
  intro modes _hmodes
  have hfree0 := continuous_canonicalOrderedFreeCoordinate_time
    (N := N) a omega
      ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes 0))
  have hfree1 := continuous_canonicalOrderedFreeCoordinate_time
    (N := N) a omega
      ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes 1))
  have hfirst0 :=
    continuous_canonicalOrderedQuadraticFirstPicardCoordinate_time
      (N := N) kappa a omega
        ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes 0))
  have hfirst1 :=
    continuous_canonicalOrderedQuadraticFirstPicardCoordinate_time
      (N := N) kappa a omega
        ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes 1))
  exact continuous_const.mul
    ((hfree0.mul hfirst1).add (hfirst0.mul hfree1))

theorem continuous_canonicalOrderedQuadraticSecondPicardRotatedSource_time
    (kappa a : Real) (omega : CanonicalSample)
    (observed : OrderedModeIndex N) :
    Continuous fun time : Real =>
      canonicalOrderedQuadraticSecondPicardRotatedSource (N := N)
        kappa a observed time omega := by
  unfold canonicalOrderedQuadraticSecondPicardRotatedSource
  have hcross :=
    continuous_canonicalOrderedQuadraticSecondPicardCrossSource_time
      (N := N) kappa a omega observed
  have hforce : Continuous fun time : Real =>
      -(kappa * canonicalOrderedQuadraticSecondPicardCrossSource (N := N)
        kappa a observed time omega) :=
    (continuous_const.mul hcross).neg
  exact
    (continuous_phaseFactor_real.comp (by fun_prop)).mul
      (continuous_forcedModeSource_comp
        (canonicalOrderedFrequency (N := N) observed omega) hforce)

theorem continuous_canonicalSignedQuadraticSecondPicardRotatedSource_time
    (kappa a : Real) (omega : CanonicalSample)
    (entry : Prod PhaseSign (OrderedModeIndex N)) :
    Continuous fun time : Real =>
      canonicalSignedQuadraticSecondPicardRotatedSource (N := N)
        kappa a entry time omega := by
  cases entry with
  | mk sign observed =>
  cases sign with
  | phase =>
      exact continuous_canonicalOrderedQuadraticSecondPicardRotatedSource_time
        (N := N) kappa a omega observed
  | conjugate =>
      exact Complex.continuous_conj.comp
        (continuous_canonicalOrderedQuadraticSecondPicardRotatedSource_time
          (N := N) kappa a omega observed)

theorem measurable_canonicalSignedQuadraticSecondPicardRotatedSource_time_sample
    (kappa a : Real) (entry : Prod PhaseSign (OrderedModeIndex N)) :
    Measurable fun st : Prod Real CanonicalSample =>
      canonicalSignedQuadraticSecondPicardRotatedSource (N := N)
        kappa a entry st.1 st.2 := by
  exact measurable_uncurry_of_continuous_of_measurable
    (fun omega =>
      continuous_canonicalSignedQuadraticSecondPicardRotatedSource_time
        (N := N) kappa a omega entry)
    (fun time =>
      measurable_canonicalSignedQuadraticSecondPicardRotatedSource
        (N := N) kappa a entry time)

end
end ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardTimeWindowIntegrability
