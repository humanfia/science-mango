import ArchonPhysics.CanonicalIIDCoerciveActualDuhamelPhysicalReferenceTimeZeroCore
import ArchonPhysics.CanonicalIIDCoerciveOrderedPhyslibSourceIntertwining
import ArchonPhysics.CubicVertexInfraredBound
import ArchonPhysics.MeasurableHarmonicData
import ArchonPhysics.CanonicalIIDCoerciveInitialHaarBlockFactorization
import ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope

/-!
# Actual canonical free-quadratic history integrability at arbitrary time

The Physlib normal-mode basis is not a measurable choice as the random masses
vary.  This module removes that obstruction for the first nontrivial Duhamel
primitive.  It uses an orientation-signed radial presentation of the same
free initial orbit, rewrites every input coordinate and the cubic interaction
tensor into the explicit measurable ordered signed eigenframe, and proves
exact equality on the almost-sure simple-spectrum event.

The resulting canonical finite sum is globally measurable.  A finite-volume
bound follows from total initial energy one, the uniform infrared frequency
bound, and the cubic-vertex estimate.  Consequently the genuine canonical
`freeFirstPicard` source is Bochner integrable at every fixed real time.  No
RPA, kinetic, Markov, small-denominator, or recollision assumption is used.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualFreeQuadraticHistoryIntegrability

open scoped BigOperators Matrix
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualDuhamelPhysicalReferenceTimeZeroCore
open ArchonPhysics.CanonicalIIDCoerciveActualPointwiseDuhamelHistoryExpansion
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationTheorem
open ArchonPhysics.CanonicalIIDCoerciveExpectationHierarchy
open ArchonPhysics.CanonicalIIDCoerciveInitialHaarBlockFactorization
open ArchonPhysics.CanonicalIIDCoerciveInitialHaarBlockMoment
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.CubicVertexInfraredBound
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.FiniteHarmonicHaarPhasePropagation
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableHarmonicData
open ArchonPhysics.MeasurableOrderedEigenframe
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ModeCoupling
open ArchonPhysics.OrderedPositiveInitialEnergyProfile
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhaseEnergyModeCoordinates
open ArchonPhysics.PhyslibFPUTActualDuhamelSourceHistoryExpansion
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.RandomMassOrderedPhyslibBasisIntertwining
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]

/-- Ordered prescribed-energy radius in real modal-coordinate normalization. -/
def canonicalOrderedFreeRadius
    (a : Real) (omega : CanonicalSample) (k : OrderedModeIndex N) : Real :=
  phaseEnergyRadius (orderedTargetEnergy N a)
    (fun l => canonicalOrderedFrequency (N := N) l omega) k

/-- The free real modal coordinate in the measurable ordered signed frame. -/
def canonicalOrderedFreeCoordinate
    (a : Real) (time : Real) (omega : CanonicalSample)
    (k : OrderedModeIndex N) : Real :=
  freeRealModeCoordinate
    (canonicalOrderedFreeRadius (N := N) a omega)
    (fun l => canonicalOrderedFrequency (N := N) l omega) time
    (fun l => orderedPhaseSample canonicalIIDMassPhaseEnsemble omega l) k

/-- A Physlib-indexed radial presentation whose orientation sign absorbs the
normal-basis sign.  Negative radii are harmless: only the resulting free real
coordinate enters the Picard source. -/
def canonicalOrientedPhyslibFreeRadius
    (a : Real) (omega : CanonicalSample) (site : Lattice.Site N) : Real :=
  let k : OrderedModeIndex N := (orderedIndexEquiv (ι := Lattice.Site N)).symm site
  orderedPhyslibOrientation (canonicalMass (N := N) omega) k *
    canonicalOrderedFreeRadius (N := N) a omega k

/-- Reindex the canonical Haar phase into Physlib's mode labels. -/
def canonicalReindexedPhyslibHaarPhase
    (omega : CanonicalSample) : UnitAddTorus (Lattice.Site N) :=
  fun site => orderedPhaseSample canonicalIIDMassPhaseEnsemble omega
    ((orderedIndexEquiv (ι := Lattice.Site N)).symm site)

/-- Bond coefficient in the explicit measurable signed ordered frame. -/
def orderedSignedBondModeCoefficient
    (m : Lattice.PositiveMassConfig N) (j : Lattice.Site N)
    (k : OrderedModeIndex N) : Real :=
  Matrix.mulVec (massWeightedDifferenceMatrix m)
    (signedOrderedEigenvector (harmonicHermitian m) k) j

/-- Interaction tensor in the explicit measurable signed ordered frame. -/
def orderedSignedInteractionTensor
    (m : Lattice.PositiveMassConfig N) (n : Nat)
    (modes : Fin n -> OrderedModeIndex N) : Real :=
  ∑ j, ∏ r, orderedSignedBondModeCoefficient m j (modes r)

theorem orderedSignedBondModeCoefficient_eq_orientation_mul
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (j : Lattice.Site N) (k : OrderedModeIndex N) :
    orderedSignedBondModeCoefficient m j k =
      orderedPhyslibOrientation m k *
        bondModeCoefficient m j (orderedPhyslibModeIndex k) := by
  unfold orderedSignedBondModeCoefficient bondModeCoefficient
  rw [signedOrderedEigenvector_eq_orientation_smul_normalModeBasis
    m hsimple k]
  rw [Matrix.mulVec_smul]
  rfl

theorem orderedSignedInteractionTensor_eq_orientationProduct_mul
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (n : Nat) (modes : Fin n -> OrderedModeIndex N) :
    orderedSignedInteractionTensor m n modes =
      (∏ r, orderedPhyslibOrientation m (modes r)) *
        interactionTensor m n (fun r => orderedPhyslibModeIndex (modes r)) := by
  classical
  unfold orderedSignedInteractionTensor interactionTensor
  simp_rw [orderedSignedBondModeCoefficient_eq_orientation_mul m hsimple]
  calc
    (∑ j, ∏ r, orderedPhyslibOrientation m (modes r) *
        bondModeCoefficient m j (orderedPhyslibModeIndex (modes r))) =
        ∑ j, (∏ r, orderedPhyslibOrientation m (modes r)) *
          ∏ r, bondModeCoefficient m j (orderedPhyslibModeIndex (modes r)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.prod_mul_distrib]
    _ = _ := by rw [Finset.mul_sum]

/-- Orientation-free canonical finite sum corresponding to the free
quadratic tensor contraction. -/
def canonicalOrderedFreeQuadraticTensorSource
    (a : Real) (observed : OrderedModeIndex N) (time : Real)
    (omega : CanonicalSample) : Complex :=
  ∑ modes : Fin 2 -> Lattice.Site N,
    (orderedSignedInteractionTensor (canonicalMass (N := N) omega) 3
      (Fin.cons observed (fun r =>
        (orderedIndexEquiv (ι := Lattice.Site N)).symm (modes r))) : Complex) *
      ∏ r, (canonicalOrderedFreeCoordinate (N := N) a time omega
        ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes r)) : Complex)

/-- Measurable ordered version of the unit free-quadratic rotated source. -/
def canonicalOrderedFreeQuadraticRotatedSource
    (a : Real) (observed : OrderedModeIndex N) (time : Real)
    (omega : CanonicalSample) : Complex :=
  (forcedModeSource (canonicalOrderedFrequency (N := N) observed omega) (-1) *
      phaseFactor (canonicalOrderedFrequency (N := N) observed omega * time)) *
    canonicalOrderedFreeQuadraticTensorSource (N := N) a observed time omega

def canonicalSignedFreeQuadraticRotatedSource
    (a : Real) (entry : PhaseSign × OrderedModeIndex N) (time : Real)
    (omega : CanonicalSample) : Complex :=
  phaseSignActComplex entry.1
    (canonicalOrderedFreeQuadraticRotatedSource (N := N)
      a entry.2 time omega)


theorem measurable_canonicalOrderedFreeRadius
    (a : Real) (k : OrderedModeIndex N) :
    Measurable fun omega : CanonicalSample =>
      canonicalOrderedFreeRadius (N := N) a omega k := by
  unfold canonicalOrderedFreeRadius phaseEnergyRadius
  exact measurable_const.sqrt.div
    (measurable_canonicalOrderedFrequency (N := N) k)

theorem measurable_canonicalOrderedFreeCoordinate
    (a time : Real) (k : OrderedModeIndex N) :
    Measurable fun omega : CanonicalSample =>
      canonicalOrderedFreeCoordinate (N := N) a time omega k := by
  unfold canonicalOrderedFreeCoordinate freeRealModeCoordinate
    realPhaseModeCoordinate physicalFreePhaseEvolution
    freeHarmonicPhaseEvolution harmonicPhaseAdvance
  have hradius := measurable_canonicalOrderedFreeRadius (N := N) a k
  have hfrequency := measurable_canonicalOrderedFrequency (N := N) k
  have hphase : Measurable fun omega : CanonicalSample =>
      orderedPhaseSample canonicalIIDMassPhaseEnsemble omega k := by
    exact canonicalIIDMassPhaseEnsemble.phase_measurable
      (orderedModeIndexEquivFin N k).val
  have htranslated : Measurable fun omega : CanonicalSample =>
      (((-canonicalOrderedFrequency (N := N) k omega) * time /
        (2 * Real.pi) : Real) : UnitAddCircle) +
        orderedPhaseSample canonicalIIDMassPhaseEnsemble omega k := by
    fun_prop
  exact hradius.mul
    (Complex.continuous_re.measurable.comp
      (continuous_unitPhase.measurable.comp htranslated))

theorem measurable_canonicalOrderedSignedBondModeCoefficient
    (j : Lattice.Site N) (k : OrderedModeIndex N) :
    Measurable fun omega : CanonicalSample =>
      orderedSignedBondModeCoefficient
        (canonicalMass (N := N) omega) j k := by
  have hB :=
    measurable_massWeightedDifferenceMatrix_of_coordinate
      (canonicalMass (N := N))
      (fun i => measurable_canonicalMass_coordinate (N := N) i)
  have hv :=
    RandomMassMeasurableOrderedEigenframe.measurable_orderedEigenvectorSample
      canonicalIIDMassPhaseEnsemble k
  unfold orderedSignedBondModeCoefficient Matrix.mulVec dotProduct
  apply Finset.measurable_sum
  intro i _hi
  exact ((measurable_pi_apply i).comp ((measurable_pi_apply j).comp hB)).mul
    ((measurable_pi_apply i).comp hv)

theorem measurable_canonicalOrderedSignedInteractionTensor
    (n : Nat) (modes : Fin n -> OrderedModeIndex N) :
    Measurable fun omega : CanonicalSample =>
      orderedSignedInteractionTensor
        (canonicalMass (N := N) omega) n modes := by
  unfold orderedSignedInteractionTensor
  apply Finset.measurable_sum
  intro j _hj
  apply Finset.measurable_prod
  intro r _hr
  exact measurable_canonicalOrderedSignedBondModeCoefficient
    (N := N) j (modes r)

theorem measurable_canonicalOrderedFreeQuadraticTensorSource
    (a : Real) (observed : OrderedModeIndex N) (time : Real) :
    Measurable fun omega : CanonicalSample =>
      canonicalOrderedFreeQuadraticTensorSource (N := N)
        a observed time omega := by
  unfold canonicalOrderedFreeQuadraticTensorSource
  apply Finset.measurable_sum
  intro modes _hmodes
  apply (Complex.measurable_ofReal.comp
    (measurable_canonicalOrderedSignedInteractionTensor (N := N) 3
      (Fin.cons observed (fun r =>
        (orderedIndexEquiv (ι := Lattice.Site N)).symm (modes r))))).mul
  apply Finset.measurable_prod
  intro r _hr
  exact Complex.measurable_ofReal.comp
    (measurable_canonicalOrderedFreeCoordinate (N := N) a time
      ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes r)))

theorem measurable_canonicalOrderedFreeQuadraticRotatedSource
    (a : Real) (observed : OrderedModeIndex N) (time : Real) :
    Measurable fun omega : CanonicalSample =>
      canonicalOrderedFreeQuadraticRotatedSource (N := N)
        a observed time omega := by
  unfold canonicalOrderedFreeQuadraticRotatedSource forcedModeSource phaseFactor
  have hfrequency := measurable_canonicalOrderedFrequency (N := N) observed
  have htensor := measurable_canonicalOrderedFreeQuadraticTensorSource
    (N := N) a observed time
  fun_prop

theorem measurable_canonicalSignedFreeQuadraticRotatedSource
    (a : Real) (entry : PhaseSign × OrderedModeIndex N) (time : Real) :
    Measurable fun omega : CanonicalSample =>
      canonicalSignedFreeQuadraticRotatedSource (N := N)
        a entry time omega := by
  rcases entry with ⟨sign, observed⟩
  cases sign with
  | phase =>
      exact measurable_canonicalOrderedFreeQuadraticRotatedSource
        (N := N) a observed time
  | conjugate =>
      exact Complex.continuous_conj.measurable.comp
        (measurable_canonicalOrderedFreeQuadraticRotatedSource
          (N := N) a observed time)


theorem freeRealModeCoordinate_canonicalOriented
    (a : Real) (omega : CanonicalSample) (time : Real)
    (k : OrderedModeIndex N) :
    freeRealModeCoordinate
        (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
        (modeFrequency (canonicalMass (N := N) omega)) time
        (canonicalReindexedPhyslibHaarPhase (N := N) omega)
        (orderedPhyslibModeIndex k) =
      orderedPhyslibOrientation (canonicalMass (N := N) omega) k *
        canonicalOrderedFreeCoordinate (N := N) a time omega k := by
  unfold canonicalOrientedPhyslibFreeRadius
    canonicalReindexedPhyslibHaarPhase
    canonicalOrderedFreeCoordinate orderedPhyslibModeIndex
    freeRealModeCoordinate realPhaseModeCoordinate
    physicalFreePhaseEvolution freeHarmonicPhaseEvolution
    harmonicPhaseAdvance
  simp only [Equiv.symm_apply_apply, Pi.add_apply]
  rw [show modeFrequency (canonicalMass (N := N) omega)
        (orderedIndexEquiv k) =
      canonicalOrderedFrequency (N := N) k omega by
    symm
    exact orderedModeFrequency_harmonicHermitian_eq
      (canonicalMass (N := N) omega) k]
  ring

theorem canonicalOrderedFreeQuadraticTensorSource_eq_orientedPhyslib
    (a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (observed : OrderedModeIndex N) (time : Real) :
    canonicalOrderedFreeQuadraticTensorSource (N := N)
        a observed time omega =
      (orderedPhyslibOrientation
          (canonicalMass (N := N) omega) observed : Complex) *
        freeQuadraticTensorSource (canonicalMass (N := N) omega)
          (orderedPhyslibModeIndex observed)
          (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
          (modeFrequency (canonicalMass (N := N) omega)) time
          (canonicalReindexedPhyslibHaarPhase (N := N) omega) := by
  classical
  unfold canonicalOrderedFreeQuadraticTensorSource
    freeQuadraticTensorSource
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
  simp only [orderedPhyslibModeIndex, Equiv.apply_symm_apply] at hfree0 hfree1
  simp only [Fin.prod_univ_two]
  rw [hfree0, hfree1]
  push_cast
  ring

theorem canonicalOrderedFreeQuadraticRotatedSource_eq_orientedPhyslib
    (a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (observed : OrderedModeIndex N) (time : Real) :
    canonicalOrderedFreeQuadraticRotatedSource (N := N)
        a observed time omega =
      (orderedPhyslibOrientation
          (canonicalMass (N := N) omega) observed : Complex) *
        physlibFreeQuadraticRotatedSource
          (canonicalMass (N := N) omega) 1 1
          (orderedPhyslibModeIndex observed)
          (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
          (canonicalReindexedPhyslibHaarPhase (N := N) omega) time := by
  unfold canonicalOrderedFreeQuadraticRotatedSource
    physlibFreeQuadraticRotatedSource freeQuadraticPicardIntegrand
    physlibQuadraticCoupling
  rw [canonicalOrderedFreeQuadraticTensorSource_eq_orientedPhyslib
    (N := N) a omega hsimple observed time]
  rw [show modeFrequency (canonicalMass (N := N) omega)
        (orderedPhyslibModeIndex observed) =
      canonicalOrderedFrequency (N := N) observed omega by
    exact (orderedModeFrequency_harmonicHermitian_eq
      (canonicalMass (N := N) omega) observed).symm]
  norm_num
  ring

theorem canonicalQuadraticFreeFirstPicardSource_eq_measurableOrdered
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
        entry .freeFirstPicard (omega, time) =
      canonicalSignedFreeQuadraticRotatedSource (N := N)
        a entry time omega := by
  rcases entry with ⟨sign, observed⟩
  unfold canonicalQuadraticDuhamelHistorySource
    actualFiniteQuadraticHistorySource
    canonicalSignedFreeQuadraticRotatedSource
  rw [canonicalOrderedFreeQuadraticRotatedSource_eq_orientedPhyslib
    (N := N) a omega hsimple observed time]
  cases sign <;> simp [phaseSignActComplex]


/-- Coarse deterministic `l1` envelope for the prescribed-energy free
reference. -/
def canonicalFreeRadiusL1Envelope (N : Nat) : Real :=
  (N : Real) * (Real.sqrt 2 * (N : Real))

/-- Coarse deterministic absolute mass of one cubic interaction-tensor row. -/
def canonicalFreeQuadraticTensorRowEnvelope (N : Nat) : Real :=
  (N : Real) ^ 2 * Real.sqrt 125

/-- Coarse deterministic norm envelope for one unit free-quadratic rotated
source at arbitrary fixed time. -/
def canonicalFreeQuadraticSourceEnvelope (N : Nat) [NeZero N] : Real :=
  canonicalPositiveFrequencyNormalizationEnvelope N *
    (canonicalFreeQuadraticTensorRowEnvelope N *
      canonicalFreeRadiusL1Envelope N ^ 2)

theorem orderedTargetEnergy_nonneg
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (k : OrderedModeIndex N) :
    0 <= orderedTargetEnergy N a k := by
  unfold orderedTargetEnergy
  exact orderedPositiveInitialEnergyProfile_nonneg hN ha0 ha1 _

theorem orderedTargetEnergy_le_one
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (k : OrderedModeIndex N) :
    orderedTargetEnergy N a k <= 1 := by
  calc
    orderedTargetEnergy N a k <=
        ∑ l : OrderedModeIndex N, orderedTargetEnergy N a l := by
      exact Finset.single_le_sum
        (fun l _hl => orderedTargetEnergy_nonneg hN ha0 ha1 l)
        (Finset.mem_univ k)
    _ = 1 := sum_orderedTargetEnergy_eq_one hN a

theorem abs_canonicalOrderedFreeRadius_le
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (omega : CanonicalSample) (k : OrderedModeIndex N) :
    |canonicalOrderedFreeRadius (N := N) a omega k| <=
      Real.sqrt 2 * (N : Real) := by
  by_cases hk : k = lastOrderedIndex (ι := Lattice.Site N)
  · subst k
    simp [canonicalOrderedFreeRadius, phaseEnergyRadius]
  · have hE0 := orderedTargetEnergy_nonneg hN ha0 ha1 k
    have hE1 := orderedTargetEnergy_le_one hN ha0 ha1 k
    have hwpos := canonicalOrderedFrequency_pos k hk omega
    have hinv := inv_canonicalOrderedFrequency_le_volume k hk omega
    have hsqrt : Real.sqrt (2 * orderedTargetEnergy N a k) <=
        Real.sqrt 2 := by
      apply Real.sqrt_le_sqrt
      nlinarith
    unfold canonicalOrderedFreeRadius phaseEnergyRadius
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos hwpos,
      div_eq_mul_inv]
    exact mul_le_mul hsqrt hinv (inv_nonneg.mpr hwpos.le)
      (Real.sqrt_nonneg _)

theorem canonicalOrientedPhyslibFreeRadiusL1_le
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega))) :
    radiusL1 (canonicalOrientedPhyslibFreeRadius (N := N) a omega) <=
      canonicalFreeRadiusL1Envelope N := by
  unfold radiusL1 canonicalFreeRadiusL1Envelope
  calc
    (∑ site : Lattice.Site N,
        |canonicalOrientedPhyslibFreeRadius (N := N) a omega site|) <=
        ∑ _site : Lattice.Site N, Real.sqrt 2 * (N : Real) := by
      apply Finset.sum_le_sum
      intro site _hsite
      let k : OrderedModeIndex N :=
        (orderedIndexEquiv (ι := Lattice.Site N)).symm site
      rw [canonicalOrientedPhyslibFreeRadius, abs_mul,
        abs_orderedPhyslibOrientation
          (canonicalMass (N := N) omega) hsimple k, one_mul]
      exact abs_canonicalOrderedFreeRadius_le hN ha0 ha1 omega k
    _ = (N : Real) * (Real.sqrt 2 * (N : Real)) := by simp

theorem abs_interactionTensor_three_canonical_le_sqrt_125
    (omega : CanonicalSample)
    (modes : Fin 3 -> Lattice.Site N) :
    |interactionTensor (canonicalMass (N := N) omega) 3 modes| <=
      Real.sqrt 125 := by
  apply Real.abs_le_sqrt
  calc
    interactionTensor (canonicalMass (N := N) omega) 3 modes ^ 2 <=
        modeFrequencySq (canonicalMass (N := N) omega) (modes 0) *
          modeFrequencySq (canonicalMass (N := N) omega) (modes 1) *
            modeFrequencySq (canonicalMass (N := N) omega) (modes 2) :=
      interactionTensor_three_sq_le _ _
    _ <= 125 := by
      have h0 : modeFrequencySq (canonicalMass (N := N) omega) (modes 0) <= 5 := by
        simpa [canonicalMass] using (iid_modeFrequencySq_le_five
          canonicalIIDMassPhaseEnsemble omega (modes 0))
      have h1 : modeFrequencySq (canonicalMass (N := N) omega) (modes 1) <= 5 := by
        simpa [canonicalMass] using (iid_modeFrequencySq_le_five
          canonicalIIDMassPhaseEnsemble omega (modes 1))
      have h2 : modeFrequencySq (canonicalMass (N := N) omega) (modes 2) <= 5 := by
        simpa [canonicalMass] using (iid_modeFrequencySq_le_five
          canonicalIIDMassPhaseEnsemble omega (modes 2))
      have hn0 := modeFrequencySq_nonneg
        (canonicalMass (N := N) omega) (modes 0)
      have hn1 := modeFrequencySq_nonneg
        (canonicalMass (N := N) omega) (modes 1)
      calc
        modeFrequencySq (canonicalMass (N := N) omega) (modes 0) *
              modeFrequencySq (canonicalMass (N := N) omega) (modes 1) *
            modeFrequencySq (canonicalMass (N := N) omega) (modes 2) <=
            5 * 5 * 5 := by
          exact mul_le_mul
            (mul_le_mul h0 h1 hn1 (by norm_num)) h2
            (modeFrequencySq_nonneg _ _) (by norm_num)
        _ = 125 := by norm_num

theorem observedInteractionTensorAbsMass_canonical_le
    (omega : CanonicalSample) (observed : Lattice.Site N) :
    observedInteractionTensorAbsMass (n := 2)
        (canonicalMass (N := N) omega) observed <=
      canonicalFreeQuadraticTensorRowEnvelope N := by
  unfold observedInteractionTensorAbsMass
    canonicalFreeQuadraticTensorRowEnvelope
  calc
    (∑ modes : Fin 2 -> Lattice.Site N,
        |interactionTensor (canonicalMass (N := N) omega) 3
          (Fin.cons observed modes)|) <=
        ∑ _modes : Fin 2 -> Lattice.Site N, Real.sqrt 125 := by
      apply Finset.sum_le_sum
      intro modes _hmodes
      exact abs_interactionTensor_three_canonical_le_sqrt_125
        omega (Fin.cons observed modes)
    _ = (N : Real) ^ 2 * Real.sqrt 125 := by simp [pow_two]

theorem norm_canonicalSignedFreeQuadraticRotatedSource_le
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (time : Real) :
    ‖canonicalSignedFreeQuadraticRotatedSource (N := N)
        a entry time omega‖ <= canonicalFreeQuadraticSourceEnvelope N := by
  rcases entry with ⟨sign, observed⟩
  rw [canonicalSignedFreeQuadraticRotatedSource,
    norm_phaseSignActComplex,
    canonicalOrderedFreeQuadraticRotatedSource_eq_orientedPhyslib
      (N := N) a omega hsimple observed time,
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
  have hbase := norm_freeQuadraticPicardIntegrand_physlib_le
    (canonicalMass (N := N) omega) 1
      (orderedPhyslibModeIndex observed)
      (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
      (canonicalReindexedPhyslibHaarPhase (N := N) omega) time hwpos
  change ‖physlibFreeQuadraticRotatedSource
      (canonicalMass (N := N) omega) 1 1
      (orderedPhyslibModeIndex observed)
      (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
      (canonicalReindexedPhyslibHaarPhase (N := N) omega) time‖ <= _
  refine hbase.trans ?_
  have hnormalization :
      |(1 : Real)| / Real.sqrt
          (2 * modeFrequency (canonicalMass (N := N) omega)
            (orderedPhyslibModeIndex observed)) <=
        canonicalPositiveFrequencyNormalizationEnvelope N := by
    simp only [abs_one, one_div]
    rw [show modeFrequency (canonicalMass (N := N) omega)
          (orderedPhyslibModeIndex observed) =
        canonicalOrderedFrequency (N := N) observed omega by
      exact (orderedModeFrequency_harmonicHermitian_eq
        (canonicalMass (N := N) omega) observed).symm]
    exact inv_sqrt_two_mul_canonicalOrderedFrequency_le_envelope
      observed hentry omega
  have htensor := observedInteractionTensorAbsMass_canonical_le
    (N := N) omega (orderedPhyslibModeIndex observed)
  have hradius := canonicalOrientedPhyslibFreeRadiusL1_le
    (N := N) hN ha0 ha1 omega hsimple
  unfold canonicalFreeQuadraticSourceEnvelope
  have hR0 : 0 <= canonicalFreeRadiusL1Envelope N := by
    unfold canonicalFreeRadiusL1Envelope
    positivity
  have hradius0 : 0 <= radiusL1
      (canonicalOrientedPhyslibFreeRadius (N := N) a omega) := by
    unfold radiusL1
    positivity
  have htensor0 : 0 <= observedInteractionTensorAbsMass (n := 2)
      (canonicalMass (N := N) omega)
      (orderedPhyslibModeIndex observed) := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hT0 : 0 <= canonicalFreeQuadraticTensorRowEnvelope N := by
    unfold canonicalFreeQuadraticTensorRowEnvelope
    positivity
  have hradiusSq : radiusL1
      (canonicalOrientedPhyslibFreeRadius (N := N) a omega) ^ 2 <=
        canonicalFreeRadiusL1Envelope N ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hradius0 hradius
  exact mul_le_mul hnormalization
    (mul_le_mul htensor hradiusSq (sq_nonneg _) hT0)
    (mul_nonneg htensor0 (sq_nonneg _))
    canonicalPositiveFrequencyNormalizationEnvelope_nonneg

theorem integrable_canonicalSignedFreeQuadraticRotatedSource_fixedTime
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalSignedFreeQuadraticRotatedSource (N := N)
        a entry time omega)
      canonicalIIDMassPhaseEnsemble.probability := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  apply Integrable.of_bound
    (measurable_canonicalSignedFreeQuadraticRotatedSource
      (N := N) a entry time).aestronglyMeasurable
    (canonicalFreeQuadraticSourceEnvelope N)
  filter_upwards [RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae (N := N)
    canonicalIIDMassPhaseEnsemble (by omega)] with omega hsimple
  apply norm_canonicalSignedFreeQuadraticRotatedSource_le
    (N := N) hN ha0 ha1 omega
  · simpa [canonicalMass, harmonicHermitianSample, harmonicHermitian] using hsimple
  · exact hentry
theorem integrable_canonicalQuadraticFreeFirstPicardSource_fixedTime
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
        entry .freeFirstPicard (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  have hcanonical :=
    integrable_canonicalSignedFreeQuadraticRotatedSource_fixedTime
      (N := N) hN ha0 ha1 entry hentry time
  refine hcanonical.congr ?_
  filter_upwards [RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae (N := N)
    canonicalIIDMassPhaseEnsemble (by omega)] with omega hsimple
  symm
  apply canonicalQuadraticFreeFirstPicardSource_eq_measurableOrdered
    (N := N) flowKappa flowBeta flowG hflowBeta a omega
  simpa [canonicalMass, harmonicHermitianSample, harmonicHermitian] using hsimple

end
end ArchonPhysics.CanonicalIIDCoerciveActualFreeQuadraticHistoryIntegrability
