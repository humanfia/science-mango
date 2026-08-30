import ArchonPhysics.CanonicalIIDCoerciveActualFreeQuadraticHistoryIntegrability
import ArchonPhysics.CanonicalIIDCoerciveExplicitEnergyBlockMomentBound

/-!
# Actual canonical defect-square history integrability at arbitrary time

The quadratic defect-square history contains the true Hamiltonian modal
position minus its freely rotating reference, squared inside one cubic
interaction row.  Physlib's eigenbasis is not a measurable choice as the
random masses vary.  We therefore rewrite the source in the explicit signed
ordered eigenframe.  On the almost-sure simple-spectrum event all orientation
signs cancel exactly.

The ordered expression is globally measurable.  At every fixed finite volume
and time it is bounded by the conserved-energy radius plus the deterministic
free-radius envelope, so the genuine canonical `defectSquare` source is
Bochner integrable.  No RPA, kinetic, Markov, small-denominator, or
recollision assumption is used.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualDefectSquareHistoryIntegrability

open scoped BigOperators Matrix
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualDuhamelPhysicalReferenceTimeZeroCore
open ArchonPhysics.CanonicalIIDCoerciveActualFreeQuadraticHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualPointwiseDuhamelHistoryExpansion
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationTheorem
open ArchonPhysics.CanonicalIIDCoerciveExplicitEnergyBlockMomentBound
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedEigenframe
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualDuhamelSourceHistoryExpansion
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.QuadraticTensorHistoryExpansion
open ArchonPhysics.RandomMassMeasurableHarmonicEnergy
open ArchonPhysics.RandomMassMeasurableOrderedEigenframe
open ArchonPhysics.RandomMassOrderedPhyslibBasisIntertwining
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ReducedModeTransform
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]

/-- The actual-minus-free modal history in the measurable ordered signed
frame. -/
def canonicalOrderedHistoryDefect
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a time : Real) (omega : CanonicalSample)
    (k : OrderedModeIndex N) : Real :=
  canonicalOrderedModalPosition (N := N)
      flowKappa flowBeta flowG hflowBeta a k (omega, time) -
    canonicalOrderedFreeCoordinate (N := N) a time omega k

theorem measurable_canonicalOrderedHistoryDefect
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a time : Real) (k : OrderedModeIndex N) :
    Measurable fun omega : CanonicalSample =>
      canonicalOrderedHistoryDefect (N := N)
        flowKappa flowBeta flowG hflowBeta a time omega k := by
  unfold canonicalOrderedHistoryDefect
  exact ((measurable_canonicalOrderedModalPosition (N := N)
    flowKappa flowBeta flowG hflowBeta a k).comp
      (measurable_id.prodMk measurable_const)).sub
    (measurable_canonicalOrderedFreeCoordinate (N := N) a time k)

/-- The measurable ordered actual coordinate is the oriented reindexing of
the Physlib actual modal history. -/
theorem canonicalOrderedModalPosition_eq_orientedPhyslibActual
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (time : Real) (k : OrderedModeIndex N) :
    canonicalOrderedModalPosition (N := N)
        flowKappa flowBeta flowG hflowBeta a k (omega, time) =
      orderedPhyslibOrientation (canonicalMass (N := N) omega) k *
        physlibActualModalHistory (canonicalMass (N := N) omega)
          (canonicalPhyslibPositionPath (N := N)
            flowKappa flowBeta flowG hflowBeta a omega) time
          (orderedPhyslibModeIndex k) := by
  have hcoordinate := orderedSignedCoordinate_eq_orientation_mul_modalCoordinates
    (canonicalMass (N := N) omega) hsimple k
    (sqrtMassTransform (canonicalMass (N := N) omega)
      (canonicalFlowPosition (N := N)
        flowKappa flowBeta flowG hflowBeta a (omega, time)))
  simpa [canonicalOrderedModalPosition, orderedSignedCoordinate,
    orderedEigenvectorSample, harmonicHermitianSample, harmonicHermitian,
    canonicalMass, massWeightedPositionSample, physlibActualModalHistory,
    massWeightedPosition,
    realReparametrize_canonicalPhyslibPositionPath] using hcoordinate

theorem canonicalOrderedHistoryDefect_eq_orientedPhyslib
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (time : Real) (k : OrderedModeIndex N) :
    canonicalOrderedHistoryDefect (N := N)
        flowKappa flowBeta flowG hflowBeta a time omega k =
      orderedPhyslibOrientation (canonicalMass (N := N) omega) k *
        physlibModalHistoryDefect (canonicalMass (N := N) omega)
          (canonicalPhyslibPositionPath (N := N)
            flowKappa flowBeta flowG hflowBeta a omega)
          (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
          (canonicalReindexedPhyslibHaarPhase (N := N) omega) time
          (orderedPhyslibModeIndex k) := by
  have hfree := freeRealModeCoordinate_canonicalOriented
    (N := N) a omega time k
  have horientation := orderedPhyslibOrientation_sq
    (canonicalMass (N := N) omega) hsimple k
  have hfree_prime : canonicalOrderedFreeCoordinate (N := N) a time omega k =
      orderedPhyslibOrientation (canonicalMass (N := N) omega) k *
        freeRealModeCoordinate
          (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
          (modeFrequency (canonicalMass (N := N) omega)) time
          (canonicalReindexedPhyslibHaarPhase (N := N) omega)
          (orderedPhyslibModeIndex k) := by
    calc
      canonicalOrderedFreeCoordinate (N := N) a time omega k =
          1 * canonicalOrderedFreeCoordinate (N := N) a time omega k := by ring
      _ = orderedPhyslibOrientation (canonicalMass (N := N) omega) k ^ 2 *
          canonicalOrderedFreeCoordinate (N := N) a time omega k := by
        rw [horientation]
      _ = orderedPhyslibOrientation (canonicalMass (N := N) omega) k *
          (orderedPhyslibOrientation (canonicalMass (N := N) omega) k *
            canonicalOrderedFreeCoordinate (N := N) a time omega k) := by ring
      _ = _ := by rw [hfree]
  unfold canonicalOrderedHistoryDefect physlibModalHistoryDefect
  rw [canonicalOrderedModalPosition_eq_orientedPhyslibActual
    (N := N) flowKappa flowBeta flowG hflowBeta a omega hsimple time k]
  simp only [PiLp.sub_apply]
  rw [hfree_prime, freeWeightedConfiguration_apply]
  ring

/-- Explicit ordered contraction of two actual-minus-free history legs. -/
def canonicalOrderedDefectSquareTensorSource
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (observed : OrderedModeIndex N) (time : Real)
    (omega : CanonicalSample) : Complex :=
  ∑ modes : Fin 2 -> Lattice.Site N,
    (orderedSignedInteractionTensor (canonicalMass (N := N) omega) 3
      (Fin.cons observed (fun r =>
        (orderedIndexEquiv (ι := Lattice.Site N)).symm (modes r))) : Complex) *
      ∏ r, (canonicalOrderedHistoryDefect (N := N)
        flowKappa flowBeta flowG hflowBeta a time omega
          ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes r)) : Complex)

def canonicalOrderedDefectSquareRotatedSource
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (observed : OrderedModeIndex N) (time : Real)
    (omega : CanonicalSample) : Complex :=
  (forcedModeSource (canonicalOrderedFrequency (N := N) observed omega) (-1) *
      phaseFactor (canonicalOrderedFrequency (N := N) observed omega * time)) *
    canonicalOrderedDefectSquareTensorSource (N := N)
      flowKappa flowBeta flowG hflowBeta a observed time omega

def canonicalSignedDefectSquareRotatedSource
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (entry : PhaseSign × OrderedModeIndex N) (time : Real)
    (omega : CanonicalSample) : Complex :=
  phaseSignActComplex entry.1
    (canonicalOrderedDefectSquareRotatedSource (N := N)
      flowKappa flowBeta flowG hflowBeta a entry.2 time omega)

theorem measurable_canonicalOrderedDefectSquareTensorSource
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (observed : OrderedModeIndex N) (time : Real) :
    Measurable fun omega : CanonicalSample =>
      canonicalOrderedDefectSquareTensorSource (N := N)
        flowKappa flowBeta flowG hflowBeta a observed time omega := by
  unfold canonicalOrderedDefectSquareTensorSource
  apply Finset.measurable_sum
  intro modes _hmodes
  apply (Complex.measurable_ofReal.comp
    (measurable_canonicalOrderedSignedInteractionTensor (N := N) 3
      (Fin.cons observed (fun r =>
        (orderedIndexEquiv (ι := Lattice.Site N)).symm (modes r))))).mul
  apply Finset.measurable_prod
  intro r _hr
  exact Complex.measurable_ofReal.comp
    (measurable_canonicalOrderedHistoryDefect (N := N)
      flowKappa flowBeta flowG hflowBeta a time
        ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes r)))

theorem measurable_canonicalOrderedDefectSquareRotatedSource
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (observed : OrderedModeIndex N) (time : Real) :
    Measurable fun omega : CanonicalSample =>
      canonicalOrderedDefectSquareRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a observed time omega := by
  unfold canonicalOrderedDefectSquareRotatedSource forcedModeSource phaseFactor
  have hfrequency := measurable_canonicalOrderedFrequency (N := N) observed
  have htensor := measurable_canonicalOrderedDefectSquareTensorSource
    (N := N) flowKappa flowBeta flowG hflowBeta a observed time
  fun_prop

theorem measurable_canonicalSignedDefectSquareRotatedSource
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (entry : PhaseSign × OrderedModeIndex N) (time : Real) :
    Measurable fun omega : CanonicalSample =>
      canonicalSignedDefectSquareRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a entry time omega := by
  rcases entry with ⟨sign, observed⟩
  cases sign with
  | phase =>
      exact measurable_canonicalOrderedDefectSquareRotatedSource
        (N := N) flowKappa flowBeta flowG hflowBeta a observed time
  | conjugate =>
      exact Complex.continuous_conj.measurable.comp
        (measurable_canonicalOrderedDefectSquareRotatedSource
          (N := N) flowKappa flowBeta flowG hflowBeta a observed time)

theorem canonicalOrderedDefectSquareTensorSource_eq_orientedPhyslib
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (observed : OrderedModeIndex N) (time : Real) :
    canonicalOrderedDefectSquareTensorSource (N := N)
        flowKappa flowBeta flowG hflowBeta a observed time omega =
      (orderedPhyslibOrientation
          (canonicalMass (N := N) omega) observed : Complex) *
        distinguishedTensorContraction (canonicalMass (N := N) omega)
          (physlibModalHistoryDefect (canonicalMass (N := N) omega)
            (canonicalPhyslibPositionPath (N := N)
              flowKappa flowBeta flowG hflowBeta a omega)
            (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
            (canonicalReindexedPhyslibHaarPhase (N := N) omega) time)
          (orderedPhyslibModeIndex observed) 2 := by
  classical
  unfold canonicalOrderedDefectSquareTensorSource
    distinguishedTensorContraction
  push_cast
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
  have hdefect0 := canonicalOrderedHistoryDefect_eq_orientedPhyslib
    (N := N) flowKappa flowBeta flowG hflowBeta a omega hsimple time
      ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes 0))
  have hdefect1 := canonicalOrderedHistoryDefect_eq_orientedPhyslib
    (N := N) flowKappa flowBeta flowG hflowBeta a omega hsimple time
      ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes 1))
  simp only [orderedPhyslibModeIndex, Equiv.apply_symm_apply] at hdefect0 hdefect1
  simp only [Fin.prod_univ_two]
  rw [hdefect0, hdefect1]
  push_cast
  have horientation0 :
      ((orderedPhyslibOrientation (canonicalMass (N := N) omega)
        ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes 0)) : Real) : Complex) ^ 2 = 1 := by
    exact_mod_cast orderedPhyslibOrientation_sq
      (canonicalMass (N := N) omega) hsimple
        ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes 0))
  have horientation1 :
      ((orderedPhyslibOrientation (canonicalMass (N := N) omega)
        ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes 1)) : Real) : Complex) ^ 2 = 1 := by
    exact_mod_cast orderedPhyslibOrientation_sq
      (canonicalMass (N := N) omega) hsimple
        ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes 1))
  ring_nf
  rw [horientation0, horientation1]
  ring

theorem canonicalOrderedDefectSquareRotatedSource_eq_orientedPhyslib
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (observed : OrderedModeIndex N) (time : Real) :
    canonicalOrderedDefectSquareRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a observed time omega =
      (orderedPhyslibOrientation
          (canonicalMass (N := N) omega) observed : Complex) *
        physlibQuadraticDefectSquareRotatedSource
          (canonicalMass (N := N) omega) 1 1
          (orderedPhyslibModeIndex observed)
          (canonicalPhyslibPositionPath (N := N)
            flowKappa flowBeta flowG hflowBeta a omega)
          (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
          (canonicalReindexedPhyslibHaarPhase (N := N) omega) time := by
  unfold canonicalOrderedDefectSquareRotatedSource
    physlibQuadraticDefectSquareRotatedSource
  rw [canonicalOrderedDefectSquareTensorSource_eq_orientedPhyslib
    (N := N) flowKappa flowBeta flowG hflowBeta a omega hsimple observed time]
  rw [show modeFrequency (canonicalMass (N := N) omega)
        (orderedPhyslibModeIndex observed) =
      canonicalOrderedFrequency (N := N) observed omega by
    exact (orderedModeFrequency_harmonicHermitian_eq
      (canonicalMass (N := N) omega) observed).symm]
  norm_num
  unfold forcedModeSource
  push_cast
  ring

theorem canonicalQuadraticDefectSquareSource_eq_measurableOrdered
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
        entry .defectSquare (omega, time) =
      canonicalSignedDefectSquareRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a entry time omega := by
  rcases entry with ⟨sign, observed⟩
  unfold canonicalQuadraticDuhamelHistorySource
    actualFiniteQuadraticHistorySource
    canonicalSignedDefectSquareRotatedSource
  rw [canonicalOrderedDefectSquareRotatedSource_eq_orientedPhyslib
    (N := N) flowKappa flowBeta flowG hflowBeta a omega hsimple observed time]
  cases sign <;> simp [phaseSignActComplex]

/-- A coarse deterministic `l1` envelope for the actual modal position. -/
def canonicalActualHistoryL1Envelope
    (N : Nat) (C flowKappa flowBeta G : Real) : Real :=
  (N : Real) *
    (2 * canonicalExplicitHilbertRadius N C flowKappa flowBeta G)

def canonicalHistoryDefectL1Envelope
    (N : Nat) (C flowKappa flowBeta G : Real) : Real :=
  canonicalActualHistoryL1Envelope N C flowKappa flowBeta G +
    canonicalFreeRadiusL1Envelope N

def canonicalDefectSquareSourceEnvelope
    (N : Nat) [NeZero N] (C flowKappa flowBeta G : Real) : Real :=
  canonicalPositiveFrequencyNormalizationEnvelope N *
    (canonicalFreeQuadraticTensorRowEnvelope N *
      canonicalHistoryDefectL1Envelope N C flowKappa flowBeta G ^ 2)

theorem actualHistoryL1_canonical_le
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (C : Real) (hC : 0 <= C)
    (hPoincare : forall (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) ->
        ‖q‖ <= C * ‖Lattice.forwardDifference q‖)
    (flowKappa flowBeta flowG G : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (hG : 0 <= G) (hg : |flowG| <= G)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (time : Real) :
    actualHistoryL1 (canonicalMass (N := N) omega)
        (canonicalPhyslibPositionPath (N := N)
          flowKappa flowBeta flowG hflowBeta a omega) time <=
      canonicalActualHistoryL1Envelope N C flowKappa flowBeta G := by
  let R := canonicalExplicitHilbertRadius N C flowKappa flowBeta G
  let B := 2 * R
  have hflow :=
    norm_canonicalFlowPosition_and_momentum_le_explicitEnergy_of_simple
      hN ha0 ha1 C hC hPoincare flowKappa flowBeta flowG G
        hflowBeta hG hg omega hsimple time
  have hordered : forall k : OrderedModeIndex N,
      |canonicalOrderedModalPosition (N := N)
        flowKappa flowBeta flowG hflowBeta a k (omega, time)| <= B := by
    intro k
    have hproject := abs_orderedSignedCoordinate_le_norm
      (canonicalMass (N := N) omega) hsimple k
      (sqrtMassTransform (canonicalMass (N := N) omega)
        (canonicalFlowPosition (N := N)
          flowKappa flowBeta flowG hflowBeta a (omega, time)))
    have hweight := norm_sqrtMassTransform_le_two_mul
      (canonicalMass (N := N) omega) (canonicalMass_upper omega)
      (canonicalFlowPosition (N := N)
        flowKappa flowBeta flowG hflowBeta a (omega, time))
    have hbound : ‖sqrtMassTransform (canonicalMass (N := N) omega)
        (canonicalFlowPosition (N := N)
          flowKappa flowBeta flowG hflowBeta a (omega, time))‖ <= B := by
      exact hweight.trans (by dsimp [B, R]; gcongr; exact hflow.1)
    simpa [canonicalOrderedModalPosition, orderedSignedCoordinate,
      orderedEigenvectorSample, harmonicHermitianSample, harmonicHermitian,
      canonicalMass, massWeightedPositionSample] using hproject.trans hbound
  unfold actualHistoryL1 modalAbsSum canonicalActualHistoryL1Envelope
  calc
    (∑ site : Lattice.Site N,
        |physlibActualModalHistory (canonicalMass (N := N) omega)
          (canonicalPhyslibPositionPath (N := N)
            flowKappa flowBeta flowG hflowBeta a omega) time site|) <=
        ∑ _site : Lattice.Site N, B := by
      apply Finset.sum_le_sum
      intro site _hsite
      let k : OrderedModeIndex N :=
        (orderedIndexEquiv (ι := Lattice.Site N)).symm site
      have hcoord := canonicalOrderedModalPosition_eq_orientedPhyslibActual
        (N := N) flowKappa flowBeta flowG hflowBeta a omega hsimple time k
      have habs := congrArg abs hcoord
      rw [abs_mul, abs_orderedPhyslibOrientation
        (canonicalMass (N := N) omega) hsimple k, one_mul] at habs
      have hsite :
          |physlibActualModalHistory (canonicalMass (N := N) omega)
            (canonicalPhyslibPositionPath (N := N)
              flowKappa flowBeta flowG hflowBeta a omega) time
              (orderedPhyslibModeIndex k)| <= B := by
        calc
          |physlibActualModalHistory (canonicalMass (N := N) omega)
            (canonicalPhyslibPositionPath (N := N)
              flowKappa flowBeta flowG hflowBeta a omega) time
              (orderedPhyslibModeIndex k)| =
              |canonicalOrderedModalPosition (N := N)
                flowKappa flowBeta flowG hflowBeta a k (omega, time)| :=
            habs.symm
          _ <= B := hordered k
      simpa [k, orderedPhyslibModeIndex] using hsite
    _ = (N : Real) * B := by simp
    _ = (N : Real) *
        (2 * canonicalExplicitHilbertRadius N C flowKappa flowBeta G) := rfl

theorem historyDefectL1Envelope_canonical_le
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (C : Real) (hC : 0 <= C)
    (hPoincare : forall (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) ->
        ‖q‖ <= C * ‖Lattice.forwardDifference q‖)
    (flowKappa flowBeta flowG G : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (hG : 0 <= G) (hg : |flowG| <= G)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (time : Real) :
    historyDefectL1Envelope (canonicalMass (N := N) omega)
        (canonicalPhyslibPositionPath (N := N)
          flowKappa flowBeta flowG hflowBeta a omega)
        (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
        (canonicalReindexedPhyslibHaarPhase (N := N) omega) time <=
      canonicalHistoryDefectL1Envelope N C flowKappa flowBeta G := by
  unfold historyDefectL1Envelope canonicalHistoryDefectL1Envelope
  apply add_le_add
  · exact actualHistoryL1_canonical_le (N := N)
      hN ha0 ha1 C hC hPoincare flowKappa flowBeta flowG G
        hflowBeta hG hg omega hsimple time
  · exact (modalAbsSum_freeWeightedConfiguration_le
      (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
      (modeFrequency (canonicalMass (N := N) omega)) time
      (canonicalReindexedPhyslibHaarPhase (N := N) omega)).trans
        (canonicalOrientedPhyslibFreeRadiusL1_le
          (N := N) hN ha0 ha1 omega hsimple)

theorem norm_canonicalSignedDefectSquareRotatedSource_le
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (C : Real) (hC : 0 <= C)
    (hPoincare : forall (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) ->
        ‖q‖ <= C * ‖Lattice.forwardDifference q‖)
    (flowKappa flowBeta flowG G : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (hG : 0 <= G) (hg : |flowG| <= G)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (time : Real) :
    ‖canonicalSignedDefectSquareRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a entry time omega‖ <=
      canonicalDefectSquareSourceEnvelope N C flowKappa flowBeta G := by
  rcases entry with ⟨sign, observed⟩
  rw [canonicalSignedDefectSquareRotatedSource,
    norm_phaseSignActComplex,
    canonicalOrderedDefectSquareRotatedSource_eq_orientedPhyslib
      (N := N) flowKappa flowBeta flowG hflowBeta a omega hsimple observed time,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_orderedPhyslibOrientation
      (canonicalMass (N := N) omega) hsimple observed, one_mul]
  have hwpos : 0 < modeFrequency (canonicalMass (N := N) omega)
      (orderedPhyslibModeIndex observed) := by
    rw [show modeFrequency (canonicalMass (N := N) omega)
          (orderedPhyslibModeIndex observed) =
        canonicalOrderedFrequency (N := N) observed omega by
      exact (orderedModeFrequency_harmonicHermitian_eq
        (canonicalMass (N := N) omega) observed).symm]
    exact canonicalOrderedFrequency_pos observed hentry omega
  have hbase := norm_quadraticDefectSquareRotatedSource_le
    (canonicalMass (N := N) omega) 1 1
      (orderedPhyslibModeIndex observed)
      (canonicalPhyslibPositionPath (N := N)
        flowKappa flowBeta flowG hflowBeta a omega)
      (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
      (canonicalReindexedPhyslibHaarPhase (N := N) omega) time hwpos
  change ‖physlibQuadraticDefectSquareRotatedSource
      (canonicalMass (N := N) omega) 1 1
      (orderedPhyslibModeIndex observed)
      (canonicalPhyslibPositionPath (N := N)
        flowKappa flowBeta flowG hflowBeta a omega)
      (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
      (canonicalReindexedPhyslibHaarPhase (N := N) omega) time‖ <= _
  refine hbase.trans ?_
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
  have hdefect := historyDefectL1Envelope_canonical_le
    (N := N) hN ha0 ha1 C hC hPoincare
      flowKappa flowBeta flowG G hflowBeta hG hg omega hsimple time
  have htensor0 : 0 <= observedInteractionTensorAbsMass (n := 2)
      (canonicalMass (N := N) omega)
      (orderedPhyslibModeIndex observed) := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hT0 : 0 <= canonicalFreeQuadraticTensorRowEnvelope N := by
    unfold canonicalFreeQuadraticTensorRowEnvelope
    positivity
  have hdefect0 : 0 <= historyDefectL1Envelope
      (canonicalMass (N := N) omega)
      (canonicalPhyslibPositionPath (N := N)
        flowKappa flowBeta flowG hflowBeta a omega)
      (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
      (canonicalReindexedPhyslibHaarPhase (N := N) omega) time := by
    unfold historyDefectL1Envelope actualHistoryL1 freeHistoryL1
    exact add_nonneg (modalAbsSum_nonneg _) (modalAbsSum_nonneg _)
  have hD0 : 0 <= canonicalHistoryDefectL1Envelope
      N C flowKappa flowBeta G := hdefect0.trans hdefect
  have hdefectSq : historyDefectL1Envelope
      (canonicalMass (N := N) omega)
      (canonicalPhyslibPositionPath (N := N)
        flowKappa flowBeta flowG hflowBeta a omega)
      (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
      (canonicalReindexedPhyslibHaarPhase (N := N) omega) time ^ 2 <=
        canonicalHistoryDefectL1Envelope N C flowKappa flowBeta G ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hdefect0 hdefect
  have hproduct :
      observedInteractionTensorAbsMass (n := 2)
          (canonicalMass (N := N) omega)
          (orderedPhyslibModeIndex observed) *
        historyDefectL1Envelope (canonicalMass (N := N) omega)
          (canonicalPhyslibPositionPath (N := N)
            flowKappa flowBeta flowG hflowBeta a omega)
          (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
          (canonicalReindexedPhyslibHaarPhase (N := N) omega) time ^ 2 <=
        canonicalFreeQuadraticTensorRowEnvelope N *
          canonicalHistoryDefectL1Envelope N C flowKappa flowBeta G ^ 2 :=
    mul_le_mul htensor hdefectSq (sq_nonneg _) hT0
  norm_num
  unfold canonicalDefectSquareSourceEnvelope
  rw [div_eq_mul_inv]
  have hmul := mul_le_mul hnormalization hproduct
    (mul_nonneg htensor0 (sq_nonneg _))
    canonicalPositiveFrequencyNormalizationEnvelope_nonneg
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

theorem integrable_canonicalSignedDefectSquareRotatedSource_fixedTime
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (C : Real) (hC : 0 <= C)
    (hPoincare : forall (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) ->
        ‖q‖ <= C * ‖Lattice.forwardDifference q‖)
    (flowKappa flowBeta flowG G : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (hG : 0 <= G) (hg : |flowG| <= G)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalSignedDefectSquareRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a entry time omega)
      canonicalIIDMassPhaseEnsemble.probability := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  apply Integrable.of_bound
    (measurable_canonicalSignedDefectSquareRotatedSource
      (N := N) flowKappa flowBeta flowG hflowBeta a entry time).aestronglyMeasurable
    (canonicalDefectSquareSourceEnvelope N C flowKappa flowBeta G)
  filter_upwards [RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae (N := N)
    canonicalIIDMassPhaseEnsemble (by omega)] with omega hsimple
  apply norm_canonicalSignedDefectSquareRotatedSource_le
    (N := N) hN ha0 ha1 C hC hPoincare
      flowKappa flowBeta flowG G hflowBeta hG hg omega
  · simpa [canonicalMass, harmonicHermitianSample, harmonicHermitian] using hsimple
  · exact hentry

theorem integrable_canonicalQuadraticDefectSquareSource_fixedTime
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (C : Real) (hC : 0 <= C)
    (hPoincare : forall (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) ->
        ‖q‖ <= C * ‖Lattice.forwardDifference q‖)
    (flowKappa flowBeta flowG G : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (hG : 0 <= G) (hg : |flowG| <= G)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry .defectSquare (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  have hcanonical :=
    integrable_canonicalSignedDefectSquareRotatedSource_fixedTime
      (N := N) hN ha0 ha1 C hC hPoincare
        flowKappa flowBeta flowG G hflowBeta hG hg entry hentry time
  refine hcanonical.congr ?_
  filter_upwards [RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae (N := N)
    canonicalIIDMassPhaseEnsemble (by omega)] with omega hsimple
  symm
  apply canonicalQuadraticDefectSquareSource_eq_measurableOrdered
    (N := N) flowKappa flowBeta flowG hflowBeta a omega
  simpa [canonicalMass, harmonicHermitianSample, harmonicHermitian] using hsimple

end
end ArchonPhysics.CanonicalIIDCoerciveActualDefectSquareHistoryIntegrability
