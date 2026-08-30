import ArchonPhysics.CanonicalIIDCoerciveActualFreeQuadraticHistoryIntegrability
import ArchonPhysics.RandomMassPositiveLateWindowObservable

/-!
# Actual canonical quadratic second-Picard history at arbitrary time

The first Picard coefficient is constructed as a measurable parameterized
time integral of the ordered free-quadratic source. Its reconstructed real
modal history is then inserted into the ordered signed quadratic tensor.
On the almost-sure simple-spectrum event this finite sum agrees exactly with
the orientation-corrected Physlib quadratic second-Picard source.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardHistoryIntegrability

open scoped BigOperators Matrix
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CanonicalCollisionSoftLegBound
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationTheorem
open ArchonPhysics.CanonicalIIDCoerciveActualFreeQuadraticHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualPointwiseDuhamelHistoryExpansion
open ArchonPhysics.CanonicalIIDCoerciveExpectationHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ComplexModeAmplitude
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FiniteHarmonicHaarPhasePropagation
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedEigenframe
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ModeCoupling
open ArchonPhysics.OrderedPositiveInitialEnergyProfile
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhaseEnergyModeCoordinates
open ArchonPhysics.PhyslibFPUTActualDuhamelSourceHistoryExpansion
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.QuadraticTensorHistoryExpansion
open ArchonPhysics.RandomMassOrderedPhyslibBasisIntertwining
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]

theorem measurable_canonicalOrderedFreeCoordinate_prod
    (a : Real) (k : OrderedModeIndex N) :
    Measurable fun st : CanonicalSample × Real =>
      canonicalOrderedFreeCoordinate (N := N) a st.2 st.1 k := by
  unfold canonicalOrderedFreeCoordinate freeRealModeCoordinate
    realPhaseModeCoordinate physicalFreePhaseEvolution
    freeHarmonicPhaseEvolution harmonicPhaseAdvance
  have hradius : Measurable fun st : CanonicalSample × Real =>
      canonicalOrderedFreeRadius (N := N) a st.1 k :=
    (measurable_canonicalOrderedFreeRadius (N := N) a k).comp measurable_fst
  have hfrequency : Measurable fun st : CanonicalSample × Real =>
      canonicalOrderedFrequency (N := N) k st.1 :=
    (measurable_canonicalOrderedFrequency (N := N) k).comp measurable_fst
  have hphase : Measurable fun st : CanonicalSample × Real =>
      orderedPhaseSample canonicalIIDMassPhaseEnsemble st.1 k :=
    (canonicalIIDMassPhaseEnsemble.phase_measurable
      (orderedModeIndexEquivFin N k).val).comp measurable_fst
  have htranslated : Measurable fun st : CanonicalSample × Real =>
      (((-canonicalOrderedFrequency (N := N) k st.1) * st.2 /
        (2 * Real.pi) : Real) : UnitAddCircle) +
        orderedPhaseSample canonicalIIDMassPhaseEnsemble st.1 k := by
    fun_prop
  exact hradius.mul
    (Complex.continuous_re.measurable.comp
      (continuous_unitPhase.measurable.comp htranslated))

theorem measurable_canonicalOrderedFreeQuadraticTensorSource_prod
    (a : Real) (observed : OrderedModeIndex N) :
    Measurable fun st : CanonicalSample × Real =>
      canonicalOrderedFreeQuadraticTensorSource (N := N)
        a observed st.2 st.1 := by
  unfold canonicalOrderedFreeQuadraticTensorSource
  apply Finset.measurable_sum
  intro modes _hmodes
  apply (Complex.measurable_ofReal.comp
    ((measurable_canonicalOrderedSignedInteractionTensor (N := N) 3
      (Fin.cons observed (fun r =>
        (orderedIndexEquiv (ι := Lattice.Site N)).symm (modes r)))).comp
          measurable_fst)).mul
  apply Finset.measurable_prod
  intro r _hr
  exact Complex.measurable_ofReal.comp
    (measurable_canonicalOrderedFreeCoordinate_prod (N := N) a
      ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes r)))

theorem measurable_canonicalOrderedFreeQuadraticRotatedSource_prod
    (a : Real) (observed : OrderedModeIndex N) :
    Measurable fun st : CanonicalSample × Real =>
      canonicalOrderedFreeQuadraticRotatedSource (N := N)
        a observed st.2 st.1 := by
  unfold canonicalOrderedFreeQuadraticRotatedSource
    forcedModeSource phaseFactor
  have hfrequency : Measurable fun st : CanonicalSample × Real =>
      canonicalOrderedFrequency (N := N) observed st.1 :=
    (measurable_canonicalOrderedFrequency (N := N) observed).comp
      measurable_fst
  have htensor :=
    measurable_canonicalOrderedFreeQuadraticTensorSource_prod
      (N := N) a observed
  fun_prop

/-- Complex-valued version of the repository's parameter interval-integral
measurability adapter. -/
theorem measurable_intervalIntegral_prod_right_complex
    {S : Type*} [MeasurableSpace S]
    (f : S × Real -> Complex) (hf : Measurable f) (a b : Real) :
    Measurable fun s => ∫ t in a..b, f (s, t) := by
  unfold intervalIntegral
  have hab : StronglyMeasurable fun st : S × Real => f st :=
    hf.stronglyMeasurable
  have hba : StronglyMeasurable fun st : S × Real => f st := hab
  exact
    (hab.integral_prod_right'
      (ν := volume.restrict (Set.Ioc a b))).measurable.sub
    (hba.integral_prod_right'
      (ν := volume.restrict (Set.Ioc b a))).measurable

/-- Ordered interaction-picture first-Picard coefficient. -/
def canonicalOrderedQuadraticFirstPicardCoefficient
    (kappa a time : Real) (omega : CanonicalSample)
    (k : OrderedModeIndex N) : Complex :=
  ∫ s in (0 : Real)..time,
    (kappa : Complex) *
      canonicalOrderedFreeQuadraticRotatedSource (N := N)
        a k s omega

theorem measurable_canonicalOrderedQuadraticFirstPicardCoefficient
    (kappa a time : Real) (k : OrderedModeIndex N) :
    Measurable fun omega : CanonicalSample =>
      canonicalOrderedQuadraticFirstPicardCoefficient (N := N)
        kappa a time omega k := by
  unfold canonicalOrderedQuadraticFirstPicardCoefficient
  exact measurable_intervalIntegral_prod_right_complex
    (fun st : CanonicalSample × Real =>
      (kappa : Complex) *
        canonicalOrderedFreeQuadraticRotatedSource (N := N)
          a k st.2 st.1)
    (measurable_const.mul
      (measurable_canonicalOrderedFreeQuadraticRotatedSource_prod
        (N := N) a k)) 0 time

theorem canonicalOrderedFreeQuadraticRotatedSource_kappa_eq_orientedPhyslib
    (kappa a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (observed : OrderedModeIndex N) (time : Real) :
    (kappa : Complex) *
        canonicalOrderedFreeQuadraticRotatedSource (N := N)
          a observed time omega =
      (orderedPhyslibOrientation
          (canonicalMass (N := N) omega) observed : Complex) *
        physlibFreeQuadraticRotatedSource
          (canonicalMass (N := N) omega) kappa 1
          (orderedPhyslibModeIndex observed)
          (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
          (canonicalReindexedPhyslibHaarPhase (N := N) omega) time := by
  rw [canonicalOrderedFreeQuadraticRotatedSource_eq_orientedPhyslib
    (N := N) a omega hsimple observed time]
  unfold physlibFreeQuadraticRotatedSource
    physlibQuadraticCoupling forcedModeSource
    freeQuadraticPicardIntegrand
  push_cast
  ring

theorem canonicalOrderedQuadraticFirstPicardCoefficient_eq_orientedPhyslib
    (kappa a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (observed : OrderedModeIndex N) (time : Real) :
    canonicalOrderedQuadraticFirstPicardCoefficient (N := N)
        kappa a time omega observed =
      (orderedPhyslibOrientation
          (canonicalMass (N := N) omega) observed : Complex) *
        physlibQuadraticFirstPicardCoefficient
          (canonicalMass (N := N) omega) kappa
          (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
          (canonicalReindexedPhyslibHaarPhase (N := N) omega)
          time (orderedPhyslibModeIndex observed) := by
  unfold canonicalOrderedQuadraticFirstPicardCoefficient
    physlibQuadraticFirstPicardCoefficient
    freeQuadraticInteractionPictureCorrection
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _hs
  exact canonicalOrderedFreeQuadraticRotatedSource_kappa_eq_orientedPhyslib
    (N := N) kappa a omega hsimple observed s

theorem interactionPictureCorrectionCoordinate_real_mul
    (frequency time scale : Real) (correction : Complex) :
    interactionPictureCorrectionCoordinate frequency time
        ((scale : Complex) * correction) =
      scale * interactionPictureCorrectionCoordinate
        frequency time correction := by
  unfold interactionPictureCorrectionCoordinate phaseRenormalize
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  ring

/-- Real first-Picard coordinate in the measurable ordered frame. -/
def canonicalOrderedQuadraticFirstPicardCoordinate
    (kappa a time : Real) (omega : CanonicalSample)
    (k : OrderedModeIndex N) : Real :=
  interactionPictureCorrectionCoordinate
    (canonicalOrderedFrequency (N := N) k omega) time
    (canonicalOrderedQuadraticFirstPicardCoefficient (N := N)
      kappa a time omega k)

theorem measurable_canonicalOrderedQuadraticFirstPicardCoordinate
    (kappa a time : Real) (k : OrderedModeIndex N) :
    Measurable fun omega : CanonicalSample =>
      canonicalOrderedQuadraticFirstPicardCoordinate (N := N)
        kappa a time omega k := by
  unfold canonicalOrderedQuadraticFirstPicardCoordinate
    interactionPictureCorrectionCoordinate phaseRenormalize phaseFactor
  have hfrequency := measurable_canonicalOrderedFrequency (N := N) k
  have hcoefficient :=
    measurable_canonicalOrderedQuadraticFirstPicardCoefficient
      (N := N) kappa a time k
  fun_prop

theorem canonicalOrderedQuadraticFirstPicardCoordinate_eq_orientedPhyslib
    (kappa a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (observed : OrderedModeIndex N) (time : Real) :
    canonicalOrderedQuadraticFirstPicardCoordinate (N := N)
        kappa a time omega observed =
      orderedPhyslibOrientation
          (canonicalMass (N := N) omega) observed *
        physlibQuadraticFirstPicardModalHistory
          (canonicalMass (N := N) omega) kappa
          (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
          (canonicalReindexedPhyslibHaarPhase (N := N) omega)
          time (orderedPhyslibModeIndex observed) := by
  unfold canonicalOrderedQuadraticFirstPicardCoordinate
  rw [canonicalOrderedQuadraticFirstPicardCoefficient_eq_orientedPhyslib
    (N := N) kappa a omega hsimple observed time]
  rw [show canonicalOrderedFrequency (N := N) observed omega =
      modeFrequency (canonicalMass (N := N) omega)
        (orderedPhyslibModeIndex observed) by
    exact orderedModeFrequency_harmonicHermitian_eq
      (canonicalMass (N := N) omega) observed]
  rw [interactionPictureCorrectionCoordinate_real_mul]
  rfl

theorem physlibQuadraticFirstPicardModalHistory_eq_orientation_mul_canonical
    (kappa a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (observed : OrderedModeIndex N) (time : Real) :
    physlibQuadraticFirstPicardModalHistory
          (canonicalMass (N := N) omega) kappa
          (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
          (canonicalReindexedPhyslibHaarPhase (N := N) omega)
          time (orderedPhyslibModeIndex observed) =
      orderedPhyslibOrientation
          (canonicalMass (N := N) omega) observed *
        canonicalOrderedQuadraticFirstPicardCoordinate (N := N)
          kappa a time omega observed := by
  have hcoordinate :=
    canonicalOrderedQuadraticFirstPicardCoordinate_eq_orientedPhyslib
      (N := N) kappa a omega hsimple observed time
  have horientation := orderedPhyslibOrientation_sq
    (canonicalMass (N := N) omega) hsimple observed
  calc
    _ = 1 * physlibQuadraticFirstPicardModalHistory
          (canonicalMass (N := N) omega) kappa
          (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
          (canonicalReindexedPhyslibHaarPhase (N := N) omega)
          time (orderedPhyslibModeIndex observed) := by ring
    _ = orderedPhyslibOrientation
          (canonicalMass (N := N) omega) observed ^ 2 *
        physlibQuadraticFirstPicardModalHistory
          (canonicalMass (N := N) omega) kappa
          (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
          (canonicalReindexedPhyslibHaarPhase (N := N) omega)
          time (orderedPhyslibModeIndex observed) := by rw [horientation]
    _ = _ := by rw [hcoordinate]; ring

/-- Measurable ordered polarized contraction of one free leg with one
first-Picard leg. -/
def canonicalOrderedQuadraticSecondPicardCrossSource
    (kappa a : Real) (observed : OrderedModeIndex N) (time : Real)
    (omega : CanonicalSample) : Real :=
  ∑ modes : Fin 2 -> Lattice.Site N,
    orderedSignedInteractionTensor (canonicalMass (N := N) omega) 3
        (Fin.cons observed (fun r =>
          (orderedIndexEquiv (ι := Lattice.Site N)).symm (modes r))) *
      (canonicalOrderedFreeCoordinate (N := N) a time omega
          ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes 0)) *
        canonicalOrderedQuadraticFirstPicardCoordinate (N := N)
          kappa a time omega
          ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes 1)) +
       canonicalOrderedQuadraticFirstPicardCoordinate (N := N)
          kappa a time omega
          ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes 0)) *
        canonicalOrderedFreeCoordinate (N := N) a time omega
          ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes 1)))

theorem measurable_canonicalOrderedQuadraticSecondPicardCrossSource
    (kappa a : Real) (observed : OrderedModeIndex N) (time : Real) :
    Measurable fun omega : CanonicalSample =>
      canonicalOrderedQuadraticSecondPicardCrossSource (N := N)
        kappa a observed time omega := by
  unfold canonicalOrderedQuadraticSecondPicardCrossSource
  apply Finset.measurable_sum
  intro modes _hmodes
  apply (measurable_canonicalOrderedSignedInteractionTensor (N := N) 3
    (Fin.cons observed (fun r =>
      (orderedIndexEquiv (ι := Lattice.Site N)).symm (modes r)))).mul
  exact ((measurable_canonicalOrderedFreeCoordinate (N := N) a time
      ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes 0))).mul
    (measurable_canonicalOrderedQuadraticFirstPicardCoordinate
      (N := N) kappa a time
      ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes 1)))).add
    ((measurable_canonicalOrderedQuadraticFirstPicardCoordinate
      (N := N) kappa a time
      ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes 0))).mul
    (measurable_canonicalOrderedFreeCoordinate (N := N) a time
      ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes 1))))

theorem canonicalOrderedQuadraticSecondPicardCrossSource_eq_orientedPhyslib
    (kappa a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (observed : OrderedModeIndex N) (time : Real) :
    canonicalOrderedQuadraticSecondPicardCrossSource (N := N)
        kappa a observed time omega =
      orderedPhyslibOrientation
          (canonicalMass (N := N) omega) observed *
        quadraticTensorCrossContraction
          (canonicalMass (N := N) omega)
          (orderedPhyslibModeIndex observed)
          (freeWeightedConfiguration
            (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
            (modeFrequency (canonicalMass (N := N) omega)) time
            (canonicalReindexedPhyslibHaarPhase (N := N) omega))
          (physlibQuadraticFirstPicardModalHistory
            (canonicalMass (N := N) omega) kappa
            (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
            (canonicalReindexedPhyslibHaarPhase (N := N) omega) time) := by
  classical
  unfold canonicalOrderedQuadraticSecondPicardCrossSource
    quadraticTensorCrossContraction
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro modes _hmodes
  rw [orderedSignedInteractionTensor_eq_orientationProduct_mul
    (canonicalMass (N := N) omega) hsimple]
  have horientation :
      (fun r : Fin 3 => orderedPhyslibOrientation
        (canonicalMass (N := N) omega)
        ((Fin.cons observed (fun s : Fin 2 =>
          (orderedIndexEquiv (ι := Lattice.Site N)).symm (modes s)) :
            Fin 3 -> OrderedModeIndex N) r)) =
        Fin.cons
          (orderedPhyslibOrientation (canonicalMass (N := N) omega) observed)
          (fun s : Fin 2 => orderedPhyslibOrientation
            (canonicalMass (N := N) omega)
            ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes s))) := by
    change (orderedPhyslibOrientation (canonicalMass (N := N) omega)) ∘
        Fin.cons observed (fun s : Fin 2 =>
          (orderedIndexEquiv (ι := Lattice.Site N)).symm (modes s)) = _
    rw [Fin.comp_cons]
    rfl
  rw [horientation, Fin.prod_cons]
  have htuple :
      (fun r : Fin 3 => orderedPhyslibModeIndex
        ((Fin.cons observed (fun s : Fin 2 =>
          (orderedIndexEquiv (ι := Lattice.Site N)).symm (modes s)) :
            Fin 3 -> OrderedModeIndex N) r)) =
        Fin.cons (orderedPhyslibModeIndex observed) modes := by
    change orderedPhyslibModeIndex ∘
        Fin.cons observed (fun s : Fin 2 =>
          (orderedIndexEquiv (ι := Lattice.Site N)).symm (modes s)) = _
    rw [Fin.comp_cons]
    congr 1
    funext s
    simp [orderedPhyslibModeIndex]
  rw [htuple]
  have hfree0 := freeRealModeCoordinate_canonicalOriented
    (N := N) a omega time
      ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes 0))
  have hfree1 := freeRealModeCoordinate_canonicalOriented
    (N := N) a omega time
      ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes 1))
  have hfirst0 :=
    physlibQuadraticFirstPicardModalHistory_eq_orientation_mul_canonical
      (N := N) kappa a omega hsimple
        ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes 0)) time
  have hfirst1 :=
    physlibQuadraticFirstPicardModalHistory_eq_orientation_mul_canonical
      (N := N) kappa a omega hsimple
        ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes 1)) time
  simp only [orderedPhyslibModeIndex, Equiv.apply_symm_apply] at hfree0 hfree1 hfirst0 hfirst1
  simp only [freeWeightedConfiguration_apply]
  rw [hfree0, hfree1, hfirst0, hfirst1]
  simp only [Fin.prod_univ_two]
  ring

def canonicalOrderedQuadraticSecondPicardRotatedSource
    (kappa a : Real) (observed : OrderedModeIndex N) (time : Real)
    (omega : CanonicalSample) : Complex :=
  phaseFactor (canonicalOrderedFrequency (N := N) observed omega * time) *
    forcedModeSource (canonicalOrderedFrequency (N := N) observed omega)
      (-(kappa * canonicalOrderedQuadraticSecondPicardCrossSource
        (N := N) kappa a observed time omega))

def canonicalSignedQuadraticSecondPicardRotatedSource
    (kappa a : Real) (entry : PhaseSign × OrderedModeIndex N)
    (time : Real) (omega : CanonicalSample) : Complex :=
  phaseSignActComplex entry.1
    (canonicalOrderedQuadraticSecondPicardRotatedSource (N := N)
      kappa a entry.2 time omega)

theorem measurable_canonicalOrderedQuadraticSecondPicardRotatedSource
    (kappa a : Real) (observed : OrderedModeIndex N) (time : Real) :
    Measurable fun omega : CanonicalSample =>
      canonicalOrderedQuadraticSecondPicardRotatedSource (N := N)
        kappa a observed time omega := by
  unfold canonicalOrderedQuadraticSecondPicardRotatedSource
    forcedModeSource phaseFactor
  have hfrequency := measurable_canonicalOrderedFrequency (N := N) observed
  have hcross :=
    measurable_canonicalOrderedQuadraticSecondPicardCrossSource
      (N := N) kappa a observed time
  fun_prop

theorem measurable_canonicalSignedQuadraticSecondPicardRotatedSource
    (kappa a : Real) (entry : PhaseSign × OrderedModeIndex N)
    (time : Real) :
    Measurable fun omega : CanonicalSample =>
      canonicalSignedQuadraticSecondPicardRotatedSource (N := N)
        kappa a entry time omega := by
  rcases entry with ⟨sign, observed⟩
  cases sign with
  | phase =>
      exact measurable_canonicalOrderedQuadraticSecondPicardRotatedSource
        (N := N) kappa a observed time
  | conjugate =>
      exact Complex.continuous_conj.measurable.comp
        (measurable_canonicalOrderedQuadraticSecondPicardRotatedSource
          (N := N) kappa a observed time)

theorem canonicalOrderedQuadraticSecondPicardRotatedSource_eq_orientedPhyslib
    (kappa a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (observed : OrderedModeIndex N) (time : Real) :
    canonicalOrderedQuadraticSecondPicardRotatedSource (N := N)
        kappa a observed time omega =
      (orderedPhyslibOrientation
          (canonicalMass (N := N) omega) observed : Complex) *
        physlibQuadraticSecondPicardRotatedSource
          (canonicalMass (N := N) omega) kappa
          (orderedPhyslibModeIndex observed)
          (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
          (canonicalReindexedPhyslibHaarPhase (N := N) omega) time := by
  unfold canonicalOrderedQuadraticSecondPicardRotatedSource
    physlibQuadraticSecondPicardRotatedSource
  rw [canonicalOrderedQuadraticSecondPicardCrossSource_eq_orientedPhyslib
    (N := N) kappa a omega hsimple observed time]
  rw [show modeFrequency (canonicalMass (N := N) omega)
        (orderedPhyslibModeIndex observed) =
      canonicalOrderedFrequency (N := N) observed omega by
    exact (orderedModeFrequency_harmonicHermitian_eq
      (canonicalMass (N := N) omega) observed).symm]
  unfold forcedModeSource
  push_cast
  ring

theorem canonicalQuadraticSecondPicardSource_eq_measurableOrdered
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (entry : PhaseSign × OrderedModeIndex N) (time : Real) :
    canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry .quadraticSecondPicard (omega, time) =
      canonicalSignedQuadraticSecondPicardRotatedSource (N := N)
        1 a entry time omega := by
  rcases entry with ⟨sign, observed⟩
  unfold canonicalQuadraticDuhamelHistorySource
    actualFiniteQuadraticHistorySource
    canonicalSignedQuadraticSecondPicardRotatedSource
  rw [canonicalOrderedQuadraticSecondPicardRotatedSource_eq_orientedPhyslib
    (N := N) 1 a omega hsimple observed time]
  cases sign <;> simp [phaseSignActComplex]


/-! ## Deterministic first-Picard modal-rate envelope -/

/-- Finite-volume deterministic envelope for the modal `l1` growth rate of
the reconstructed quadratic first-Picard history. -/
def canonicalFirstPicardModalL1RateEnvelope
    (N : Nat) (kappa : Real) : Real :=
  (N : Real) *
    (|kappa| * canonicalFreeQuadraticTensorRowEnvelope N *
      canonicalFreeRadiusL1Envelope N ^ 2 * (N : Real))

theorem firstPicardModalL1Rate_canonical_le
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (kappa : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega))) :
    firstPicardModalL1Rate
        (canonicalMass (N := N) omega) kappa
        (canonicalOrientedPhyslibFreeRadius (N := N) a omega) <=
      canonicalFirstPicardModalL1RateEnvelope N kappa := by
  unfold firstPicardModalL1Rate
    canonicalFirstPicardModalL1RateEnvelope
  calc
    (∑ observed : Lattice.Site N,
        if 0 < modeFrequency (canonicalMass (N := N) omega) observed then
          |kappa| *
              observedInteractionTensorAbsMass (n := 2)
                (canonicalMass (N := N) omega) observed *
              radiusL1
                (canonicalOrientedPhyslibFreeRadius (N := N) a omega) ^ 2 /
            modeFrequency (canonicalMass (N := N) omega) observed
        else 0) <=
        ∑ _observed : Lattice.Site N,
          |kappa| * canonicalFreeQuadraticTensorRowEnvelope N *
            canonicalFreeRadiusL1Envelope N ^ 2 * (N : Real) := by
      apply Finset.sum_le_sum
      intro observed _hobserved
      by_cases homega :
          0 < modeFrequency (canonicalMass (N := N) omega) observed
      · rw [if_pos homega, div_eq_mul_inv]
        let k : OrderedModeIndex N :=
          (orderedIndexEquiv (ι := Lattice.Site N)).symm observed
        have hfrequency :
            canonicalOrderedFrequency (N := N) k omega =
              modeFrequency (canonicalMass (N := N) omega) observed := by
          simpa [canonicalOrderedFrequency, k, orderedPhyslibModeIndex] using
            (orderedModeFrequency_harmonicHermitian_eq
              (canonicalMass (N := N) omega) k)
        have hk :
            k ≠ lastOrderedIndex (ι := Lattice.Site N) := by
          apply
            (orderedModeFrequency_pos_iff_ne_last_unconditional
              (canonicalMass (N := N) omega) k).mp
          change 0 < canonicalOrderedFrequency (N := N) k omega
          rw [hfrequency]
          exact homega
        have hinv :
            (modeFrequency
              (canonicalMass (N := N) omega) observed)⁻¹ <=
                (N : Real) := by
          rw [← hfrequency]
          exact inv_canonicalOrderedFrequency_le_volume k hk omega
        have htensor := observedInteractionTensorAbsMass_canonical_le
          (N := N) omega observed
        have hradius := canonicalOrientedPhyslibFreeRadiusL1_le
          (N := N) hN ha0 ha1 omega hsimple
        have htensor0 :
            0 <= observedInteractionTensorAbsMass (n := 2)
              (canonicalMass (N := N) omega) observed := by
          unfold observedInteractionTensorAbsMass
          positivity
        have hT0 :
            0 <= canonicalFreeQuadraticTensorRowEnvelope N := by
          unfold canonicalFreeQuadraticTensorRowEnvelope
          positivity
        have hradius0 :
            0 <= radiusL1
              (canonicalOrientedPhyslibFreeRadius (N := N) a omega) := by
          unfold radiusL1
          positivity
        have hR0 : 0 <= canonicalFreeRadiusL1Envelope N := by
          unfold canonicalFreeRadiusL1Envelope
          positivity
        have hradiusSq :
            radiusL1
                (canonicalOrientedPhyslibFreeRadius (N := N) a omega) ^ 2 <=
              canonicalFreeRadiusL1Envelope N ^ 2 := by
          simpa only [pow_two] using
            mul_self_le_mul_self hradius0 hradius
        have hrow :
            |kappa| *
                observedInteractionTensorAbsMass (n := 2)
                  (canonicalMass (N := N) omega) observed *
                radiusL1
                  (canonicalOrientedPhyslibFreeRadius (N := N) a omega) ^ 2 <=
              |kappa| * canonicalFreeQuadraticTensorRowEnvelope N *
                canonicalFreeRadiusL1Envelope N ^ 2 := by
          simpa only [mul_assoc] using
            (mul_le_mul_of_nonneg_left
              (mul_le_mul htensor hradiusSq (sq_nonneg _) hT0)
              (abs_nonneg kappa))
        exact mul_le_mul hrow hinv (inv_nonneg.mpr homega.le)
          (by positivity)
      · rw [if_neg homega]
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (abs_nonneg kappa) (by
              unfold canonicalFreeQuadraticTensorRowEnvelope
              positivity))
            (sq_nonneg _))
          (Nat.cast_nonneg N)
    _ = (N : Real) *
        (|kappa| * canonicalFreeQuadraticTensorRowEnvelope N *
          canonicalFreeRadiusL1Envelope N ^ 2 * (N : Real)) := by
      simp

/-! ## Fixed-time second-Picard source envelope -/

/-- Explicit finite-volume envelope for the polarized quadratic second-Picard
source at one prescribed time. -/
def canonicalQuadraticSecondPicardSourceEnvelope
    (N : Nat) [NeZero N] (kappa time : Real) : Real :=
  canonicalPositiveFrequencyNormalizationEnvelope N *
    (|kappa| *
      (2 * canonicalFreeQuadraticTensorRowEnvelope N *
        canonicalFreeRadiusL1Envelope N *
        (canonicalFirstPicardModalL1RateEnvelope N kappa * |time|)))

theorem norm_canonicalSignedQuadraticSecondPicardRotatedSource_le
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (kappa : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (time : Real) :
    ‖canonicalSignedQuadraticSecondPicardRotatedSource (N := N)
        kappa a entry time omega‖ <=
      canonicalQuadraticSecondPicardSourceEnvelope N kappa time := by
  rcases entry with ⟨sign, observed⟩
  rw [canonicalSignedQuadraticSecondPicardRotatedSource,
    norm_phaseSignActComplex,
    canonicalOrderedQuadraticSecondPicardRotatedSource_eq_orientedPhyslib
      (N := N) kappa a omega hsimple observed time,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_orderedPhyslibOrientation
      (canonicalMass (N := N) omega) hsimple observed, one_mul]
  have homega : 0 < modeFrequency (canonicalMass (N := N) omega)
      (orderedPhyslibModeIndex observed) := by
    rw [show modeFrequency (canonicalMass (N := N) omega)
          (orderedPhyslibModeIndex observed) =
        canonicalOrderedFrequency (N := N) observed omega by
      exact (orderedModeFrequency_harmonicHermitian_eq
        (canonicalMass (N := N) omega) observed).symm]
    exact canonicalOrderedFrequency_pos observed hentry omega
  unfold physlibQuadraticSecondPicardRotatedSource
  rw [norm_mul, norm_phaseFactor, one_mul,
    norm_forcedModeSource homega, abs_neg, abs_mul]
  have hnormalization :
      (Real.sqrt (2 * modeFrequency (canonicalMass (N := N) omega)
        (orderedPhyslibModeIndex observed)))⁻¹ <=
        canonicalPositiveFrequencyNormalizationEnvelope N := by
    rw [show modeFrequency (canonicalMass (N := N) omega)
          (orderedPhyslibModeIndex observed) =
        canonicalOrderedFrequency (N := N) observed omega by
      exact (orderedModeFrequency_harmonicHermitian_eq
        (canonicalMass (N := N) omega) observed).symm]
    exact inv_sqrt_two_mul_canonicalOrderedFrequency_le_envelope
      observed hentry omega
  have htensor := observedInteractionTensorAbsMass_canonical_le
    (N := N) omega (orderedPhyslibModeIndex observed)
  have hfreeRaw := modalAbsSum_freeWeightedConfiguration_le
    (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
    (modeFrequency (canonicalMass (N := N) omega)) time
    (canonicalReindexedPhyslibHaarPhase (N := N) omega)
  have hradius := canonicalOrientedPhyslibFreeRadiusL1_le
    (N := N) hN ha0 ha1 omega hsimple
  have hfree :
      modalAbsSum
          (freeWeightedConfiguration
            (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
            (modeFrequency (canonicalMass (N := N) omega)) time
            (canonicalReindexedPhyslibHaarPhase (N := N) omega)) <=
        canonicalFreeRadiusL1Envelope N :=
    hfreeRaw.trans hradius
  have hfirstRaw := firstPicardHistoryL1_le_rate_mul_abs_time
    (canonicalMass (N := N) omega) kappa
    (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
    (canonicalReindexedPhyslibHaarPhase (N := N) omega) time
  have hrate := firstPicardModalL1Rate_canonical_le
    (N := N) hN ha0 ha1 kappa omega hsimple
  have hfirst :
      modalAbsSum
          (physlibQuadraticFirstPicardModalHistory
            (canonicalMass (N := N) omega) kappa
            (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
            (canonicalReindexedPhyslibHaarPhase (N := N) omega) time) <=
        canonicalFirstPicardModalL1RateEnvelope N kappa * |time| := by
    change firstPicardHistoryL1
        (canonicalMass (N := N) omega) kappa
        (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
        (canonicalReindexedPhyslibHaarPhase (N := N) omega) time <= _
    exact hfirstRaw.trans
      (mul_le_mul_of_nonneg_right hrate (abs_nonneg time))
  have hcross := abs_quadraticTensorCrossContraction_le
    (canonicalMass (N := N) omega)
    (orderedPhyslibModeIndex observed)
    (freeWeightedConfiguration
      (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
      (modeFrequency (canonicalMass (N := N) omega)) time
      (canonicalReindexedPhyslibHaarPhase (N := N) omega))
    (physlibQuadraticFirstPicardModalHistory
      (canonicalMass (N := N) omega) kappa
      (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
      (canonicalReindexedPhyslibHaarPhase (N := N) omega) time)
  have htensor0 :
      0 <= observedInteractionTensorAbsMass (n := 2)
        (canonicalMass (N := N) omega)
        (orderedPhyslibModeIndex observed) := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hT0 : 0 <= canonicalFreeQuadraticTensorRowEnvelope N := by
    unfold canonicalFreeQuadraticTensorRowEnvelope
    positivity
  have hfree0 :
      0 <= modalAbsSum
        (freeWeightedConfiguration
          (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
          (modeFrequency (canonicalMass (N := N) omega)) time
          (canonicalReindexedPhyslibHaarPhase (N := N) omega)) :=
    modalAbsSum_nonneg _
  have hR0 : 0 <= canonicalFreeRadiusL1Envelope N := by
    unfold canonicalFreeRadiusL1Envelope
    positivity
  have hfirst0 :
      0 <= modalAbsSum
        (physlibQuadraticFirstPicardModalHistory
          (canonicalMass (N := N) omega) kappa
          (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
          (canonicalReindexedPhyslibHaarPhase (N := N) omega) time) :=
    modalAbsSum_nonneg _
  have hrateEnvelope0 :
      0 <= canonicalFirstPicardModalL1RateEnvelope N kappa := by
    unfold canonicalFirstPicardModalL1RateEnvelope
    positivity
  have htwoTensor :
      2 * observedInteractionTensorAbsMass (n := 2)
          (canonicalMass (N := N) omega)
          (orderedPhyslibModeIndex observed) <=
        2 * canonicalFreeQuadraticTensorRowEnvelope N :=
    mul_le_mul_of_nonneg_left htensor (by norm_num)
  have htwoTensorFree :
      2 * observedInteractionTensorAbsMass (n := 2)
            (canonicalMass (N := N) omega)
            (orderedPhyslibModeIndex observed) *
          modalAbsSum
            (freeWeightedConfiguration
              (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
              (modeFrequency (canonicalMass (N := N) omega)) time
              (canonicalReindexedPhyslibHaarPhase (N := N) omega)) <=
        2 * canonicalFreeQuadraticTensorRowEnvelope N *
          canonicalFreeRadiusL1Envelope N := by
    exact mul_le_mul htwoTensor hfree hfree0
      (mul_nonneg (by norm_num) hT0)
  have hcrossBound :
      |quadraticTensorCrossContraction
          (canonicalMass (N := N) omega)
          (orderedPhyslibModeIndex observed)
          (freeWeightedConfiguration
            (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
            (modeFrequency (canonicalMass (N := N) omega)) time
            (canonicalReindexedPhyslibHaarPhase (N := N) omega))
          (physlibQuadraticFirstPicardModalHistory
            (canonicalMass (N := N) omega) kappa
            (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
            (canonicalReindexedPhyslibHaarPhase (N := N) omega) time)| <=
        2 * canonicalFreeQuadraticTensorRowEnvelope N *
          canonicalFreeRadiusL1Envelope N *
          (canonicalFirstPicardModalL1RateEnvelope N kappa * |time|) := by
    exact hcross.trans
      (mul_le_mul htwoTensorFree hfirst hfirst0
        (mul_nonneg
          (mul_nonneg (by norm_num) hT0) hR0))
  have hnumerator :
      |kappa| *
          |quadraticTensorCrossContraction
            (canonicalMass (N := N) omega)
            (orderedPhyslibModeIndex observed)
            (freeWeightedConfiguration
              (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
              (modeFrequency (canonicalMass (N := N) omega)) time
              (canonicalReindexedPhyslibHaarPhase (N := N) omega))
            (physlibQuadraticFirstPicardModalHistory
              (canonicalMass (N := N) omega) kappa
              (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
              (canonicalReindexedPhyslibHaarPhase (N := N) omega) time)| <=
        |kappa| *
          (2 * canonicalFreeQuadraticTensorRowEnvelope N *
            canonicalFreeRadiusL1Envelope N *
            (canonicalFirstPicardModalL1RateEnvelope N kappa * |time|)) :=
    mul_le_mul_of_nonneg_left hcrossBound (abs_nonneg kappa)
  unfold canonicalQuadraticSecondPicardSourceEnvelope
  rw [div_eq_mul_inv]
  have hproduct := mul_le_mul hnumerator hnormalization
    (inv_nonneg.mpr (Real.sqrt_nonneg _))
    (mul_nonneg (abs_nonneg kappa)
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) hT0) hR0)
        (mul_nonneg hrateEnvelope0 (abs_nonneg time))))
  simpa [mul_comm, mul_left_comm, mul_assoc] using hproduct

theorem integrable_canonicalSignedQuadraticSecondPicardRotatedSource_fixedTime
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (kappa : Real) (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalSignedQuadraticSecondPicardRotatedSource (N := N)
        kappa a entry time omega)
      canonicalIIDMassPhaseEnsemble.probability := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  apply Integrable.of_bound
    (measurable_canonicalSignedQuadraticSecondPicardRotatedSource
      (N := N) kappa a entry time).aestronglyMeasurable
    (canonicalQuadraticSecondPicardSourceEnvelope N kappa time)
  filter_upwards [RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae (N := N)
    canonicalIIDMassPhaseEnsemble (by omega)] with omega hsimple
  apply norm_canonicalSignedQuadraticSecondPicardRotatedSource_le
    (N := N) hN ha0 ha1 kappa omega
  · simpa [canonicalMass, harmonicHermitianSample, harmonicHermitian] using hsimple
  · exact hentry

theorem integrable_canonicalQuadraticSecondPicardSource_fixedTime
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry .quadraticSecondPicard (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  have hcanonical :=
    integrable_canonicalSignedQuadraticSecondPicardRotatedSource_fixedTime
      (N := N) hN ha0 ha1 1 entry hentry time
  refine hcanonical.congr ?_
  filter_upwards [RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae (N := N)
    canonicalIIDMassPhaseEnsemble (by omega)] with omega hsimple
  symm
  apply canonicalQuadraticSecondPicardSource_eq_measurableOrdered
    (N := N) flowKappa flowBeta flowG hflowBeta a omega
  simpa [canonicalMass, harmonicHermitianSample, harmonicHermitian] using hsimple

end
end ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardHistoryIntegrability
