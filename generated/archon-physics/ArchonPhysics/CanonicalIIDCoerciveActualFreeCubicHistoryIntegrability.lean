import ArchonPhysics.CanonicalIIDCoerciveActualFreeQuadraticHistoryIntegrability

/-!
# Actual canonical free-cubic history integrability at arbitrary time

This module treats the quartic-force primitive evaluated on the free
reference orbit. All four modal legs are rewritten into the measurable
ordered signed eigenframe. On the almost-sure simple-spectrum event the
basis orientations cancel exactly, leaving a globally measurable finite sum.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualFreeCubicHistoryIntegrability

open scoped BigOperators Matrix
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.AcousticVertexScaling
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationTheorem
open ArchonPhysics.CanonicalIIDCoerciveActualFreeQuadraticHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualPointwiseDuhamelHistoryExpansion
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedEigenframe
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.ModeCoupling
open ArchonPhysics.OrderedPositiveInitialEnergyProfile
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTActualDuhamelSourceHistoryExpansion
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.RandomMassOrderedPhyslibBasisIntertwining
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]

/-- Ordered signed version of the free cubic tensor contraction. -/
def canonicalOrderedFreeCubicTensorSource
    (a : Real) (observed : OrderedModeIndex N) (time : Real)
    (omega : CanonicalSample) : Real :=
  ∑ modes : Fin 3 -> Lattice.Site N,
    orderedSignedInteractionTensor (canonicalMass (N := N) omega) 4
        (Fin.cons observed (fun r =>
          (orderedIndexEquiv (ι := Lattice.Site N)).symm (modes r))) *
      ∏ r, canonicalOrderedFreeCoordinate (N := N) a time omega
        ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes r))

/-- Globally measurable ordered version of the unit free-cubic source. -/
def canonicalOrderedFreeCubicRotatedSource
    (a : Real) (observed : OrderedModeIndex N) (time : Real)
    (omega : CanonicalSample) : Complex :=
  phaseFactor (canonicalOrderedFrequency (N := N) observed omega * time) *
    forcedModeSource (canonicalOrderedFrequency (N := N) observed omega)
      (-canonicalOrderedFreeCubicTensorSource (N := N)
        a observed time omega)

def canonicalSignedFreeCubicRotatedSource
    (a : Real) (entry : PhaseSign × OrderedModeIndex N) (time : Real)
    (omega : CanonicalSample) : Complex :=
  phaseSignActComplex entry.1
    (canonicalOrderedFreeCubicRotatedSource (N := N)
      a entry.2 time omega)

theorem measurable_canonicalOrderedFreeCubicTensorSource
    (a : Real) (observed : OrderedModeIndex N) (time : Real) :
    Measurable fun omega : CanonicalSample =>
      canonicalOrderedFreeCubicTensorSource (N := N)
        a observed time omega := by
  unfold canonicalOrderedFreeCubicTensorSource
  apply Finset.measurable_sum
  intro modes _hmodes
  apply (measurable_canonicalOrderedSignedInteractionTensor (N := N) 4
    (Fin.cons observed (fun r =>
      (orderedIndexEquiv (ι := Lattice.Site N)).symm (modes r)))).mul
  apply Finset.measurable_prod
  intro r _hr
  exact measurable_canonicalOrderedFreeCoordinate (N := N) a time
    ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes r))

theorem measurable_canonicalOrderedFreeCubicRotatedSource
    (a : Real) (observed : OrderedModeIndex N) (time : Real) :
    Measurable fun omega : CanonicalSample =>
      canonicalOrderedFreeCubicRotatedSource (N := N)
        a observed time omega := by
  unfold canonicalOrderedFreeCubicRotatedSource forcedModeSource phaseFactor
  have hfrequency := measurable_canonicalOrderedFrequency (N := N) observed
  have htensor := measurable_canonicalOrderedFreeCubicTensorSource
    (N := N) a observed time
  fun_prop

theorem measurable_canonicalSignedFreeCubicRotatedSource
    (a : Real) (entry : PhaseSign × OrderedModeIndex N) (time : Real) :
    Measurable fun omega : CanonicalSample =>
      canonicalSignedFreeCubicRotatedSource (N := N)
        a entry time omega := by
  rcases entry with ⟨sign, observed⟩
  cases sign with
  | phase =>
      exact measurable_canonicalOrderedFreeCubicRotatedSource
        (N := N) a observed time
  | conjugate =>
      exact Complex.continuous_conj.measurable.comp
        (measurable_canonicalOrderedFreeCubicRotatedSource
          (N := N) a observed time)

theorem canonicalOrderedFreeCubicTensorSource_eq_orientedPhyslib
    (a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (observed : OrderedModeIndex N) (time : Real) :
    canonicalOrderedFreeCubicTensorSource (N := N)
        a observed time omega =
      orderedPhyslibOrientation
          (canonicalMass (N := N) omega) observed *
        distinguishedTensorContraction
          (canonicalMass (N := N) omega)
          (freeWeightedConfiguration
            (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
            (modeFrequency (canonicalMass (N := N) omega)) time
            (canonicalReindexedPhyslibHaarPhase (N := N) omega))
          (orderedPhyslibModeIndex observed) 3 := by
  classical
  unfold canonicalOrderedFreeCubicTensorSource
    distinguishedTensorContraction
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro modes _hmodes
  rw [orderedSignedInteractionTensor_eq_orientationProduct_mul
    (canonicalMass (N := N) omega) hsimple]
  have horientation :
      (fun r : Fin 4 => orderedPhyslibOrientation
        (canonicalMass (N := N) omega)
        ((Fin.cons observed (fun s : Fin 3 =>
          (orderedIndexEquiv (ι := Lattice.Site N)).symm (modes s)) :
            Fin 4 -> OrderedModeIndex N) r)) =
        Fin.cons
          (orderedPhyslibOrientation (canonicalMass (N := N) omega) observed)
          (fun s : Fin 3 => orderedPhyslibOrientation
            (canonicalMass (N := N) omega)
            ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes s))) := by
    change (orderedPhyslibOrientation (canonicalMass (N := N) omega)) ∘
        Fin.cons observed (fun s : Fin 3 =>
          (orderedIndexEquiv (ι := Lattice.Site N)).symm (modes s)) = _
    rw [Fin.comp_cons]
    rfl
  rw [horientation, Fin.prod_cons]
  have htuple :
      (fun r : Fin 4 => orderedPhyslibModeIndex
        ((Fin.cons observed (fun s : Fin 3 =>
          (orderedIndexEquiv (ι := Lattice.Site N)).symm (modes s)) :
            Fin 4 -> OrderedModeIndex N) r)) =
        Fin.cons (orderedPhyslibModeIndex observed) modes := by
    change orderedPhyslibModeIndex ∘
        Fin.cons observed (fun s : Fin 3 =>
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
  have hfree2 := freeRealModeCoordinate_canonicalOriented
    (N := N) a omega time
      ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes 2))
  simp only [orderedPhyslibModeIndex, Equiv.apply_symm_apply] at hfree0 hfree1 hfree2
  simp only [freeWeightedConfiguration_apply, Fin.prod_univ_three]
  rw [hfree0, hfree1, hfree2]
  ring

theorem canonicalOrderedFreeCubicRotatedSource_eq_orientedPhyslib
    (a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (observed : OrderedModeIndex N) (time : Real) :
    canonicalOrderedFreeCubicRotatedSource (N := N)
        a observed time omega =
      (orderedPhyslibOrientation
          (canonicalMass (N := N) omega) observed : Complex) *
        physlibFreeCubicSecondPicardRotatedSource
          (canonicalMass (N := N) omega) 1
          (orderedPhyslibModeIndex observed)
          (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
          (canonicalReindexedPhyslibHaarPhase (N := N) omega) time := by
  unfold canonicalOrderedFreeCubicRotatedSource
    physlibFreeCubicSecondPicardRotatedSource
  rw [canonicalOrderedFreeCubicTensorSource_eq_orientedPhyslib
    (N := N) a omega hsimple observed time]
  rw [show modeFrequency (canonicalMass (N := N) omega)
        (orderedPhyslibModeIndex observed) =
      canonicalOrderedFrequency (N := N) observed omega by
    exact (orderedModeFrequency_harmonicHermitian_eq
      (canonicalMass (N := N) omega) observed).symm]
  unfold forcedModeSource
  push_cast
  ring

theorem canonicalQuarticFreeCubicSource_eq_measurableOrdered
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (entry : PhaseSign × OrderedModeIndex N) (time : Real) :
    canonicalQuarticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry .freeCubicSecondPicard (omega, time) =
      canonicalSignedFreeCubicRotatedSource (N := N)
        a entry time omega := by
  rcases entry with ⟨sign, observed⟩
  unfold canonicalQuarticDuhamelHistorySource
    actualFiniteQuarticHistorySource
    canonicalSignedFreeCubicRotatedSource
  rw [canonicalOrderedFreeCubicRotatedSource_eq_orientedPhyslib
    (N := N) a omega hsimple observed time]
  cases sign <;> simp [phaseSignActComplex]


/-- Four-factor finite Holder estimate used for the quartic interaction row. -/
theorem quadrupleProductSum_sq_le
    {ι : Type*} [Fintype ι] (a b c d : ι -> Real) :
    (∑ i, a i * b i * c i * d i) ^ 2 <=
      (∑ i, a i ^ 2) * (∑ i, b i ^ 2) *
        (∑ i, c i ^ 2) * (∑ i, d i ^ 2) := by
  classical
  have hbcd :
      (∑ i, (b i * c i * d i) ^ 2) <=
        (∑ i, b i ^ 2) * (∑ i, c i ^ 2) * (∑ i, d i ^ 2) := by
    calc
      (∑ i, (b i * c i * d i) ^ 2) =
          ∑ i, b i ^ 2 * (c i ^ 2 * d i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ <= ∑ i, b i ^ 2 *
          ((∑ j, c j ^ 2) * (∑ j, d j ^ 2)) := by
        apply Finset.sum_le_sum
        intro i _hi
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact mul_le_mul
          (Finset.single_le_sum (fun j _hj => sq_nonneg (c j))
            (Finset.mem_univ i))
          (Finset.single_le_sum (fun j _hj => sq_nonneg (d j))
            (Finset.mem_univ i))
          (sq_nonneg _)
          (Finset.sum_nonneg fun j _hj => sq_nonneg (c j))
      _ = (∑ i, b i ^ 2) *
          ((∑ i, c i ^ 2) * (∑ i, d i ^ 2)) := by
        exact (Finset.sum_mul Finset.univ
          (fun i : ι => b i ^ 2)
          ((∑ i, c i ^ 2) * (∑ i, d i ^ 2))).symm
      _ = (∑ i, b i ^ 2) * (∑ i, c i ^ 2) *
          (∑ i, d i ^ 2) := by
        ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a
    (fun i => b i * c i * d i)
  calc
    (∑ i, a i * b i * c i * d i) ^ 2 =
        (∑ i, a i * (b i * c i * d i)) ^ 2 := by
      congr 2
      funext i
      ring
    _ <= (∑ i, a i ^ 2) * (∑ i, (b i * c i * d i) ^ 2) := hcs
    _ <= (∑ i, a i ^ 2) *
        ((∑ i, b i ^ 2) * (∑ i, c i ^ 2) *
          (∑ i, d i ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hbcd
        (Finset.sum_nonneg fun i _hi => sq_nonneg (a i))
    _ = _ := by ring

theorem interactionTensor_four_eq_sum
    (m : Lattice.PositiveMassConfig N)
    (modes : Fin 4 -> Lattice.Site N) :
    interactionTensor m 4 modes =
      ∑ j, bondModeCoefficient m j (modes 0) *
        bondModeCoefficient m j (modes 1) *
        bondModeCoefficient m j (modes 2) *
        bondModeCoefficient m j (modes 3) := by
  unfold interactionTensor
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Fin.prod_univ_four]

theorem interactionTensor_four_sq_le
    (m : Lattice.PositiveMassConfig N)
    (modes : Fin 4 -> Lattice.Site N) :
    interactionTensor m 4 modes ^ 2 <=
      modeFrequencySq m (modes 0) * modeFrequencySq m (modes 1) *
        modeFrequencySq m (modes 2) * modeFrequencySq m (modes 3) := by
  rw [interactionTensor_four_eq_sum]
  calc
    (∑ j, bondModeCoefficient m j (modes 0) *
        bondModeCoefficient m j (modes 1) *
        bondModeCoefficient m j (modes 2) *
        bondModeCoefficient m j (modes 3)) ^ 2 <=
      (∑ j, bondModeCoefficient m j (modes 0) ^ 2) *
        (∑ j, bondModeCoefficient m j (modes 1) ^ 2) *
        (∑ j, bondModeCoefficient m j (modes 2) ^ 2) *
        (∑ j, bondModeCoefficient m j (modes 3) ^ 2) :=
      quadrupleProductSum_sq_le _ _ _ _
    _ = _ := by
      rw [sum_sq_bondModeCoefficient, sum_sq_bondModeCoefficient,
        sum_sq_bondModeCoefficient, sum_sq_bondModeCoefficient]

theorem abs_interactionTensor_four_canonical_le_twentyFive
    (omega : CanonicalSample) (modes : Fin 4 -> Lattice.Site N) :
    |interactionTensor (canonicalMass (N := N) omega) 4 modes| <= 25 := by
  have h0 : modeFrequencySq
      (canonicalMass (N := N) omega) (modes 0) <= 5 := by
    simpa [canonicalMass] using (iid_modeFrequencySq_le_five
      canonicalIIDMassPhaseEnsemble omega (modes 0))
  have h1 : modeFrequencySq
      (canonicalMass (N := N) omega) (modes 1) <= 5 := by
    simpa [canonicalMass] using (iid_modeFrequencySq_le_five
      canonicalIIDMassPhaseEnsemble omega (modes 1))
  have h2 : modeFrequencySq
      (canonicalMass (N := N) omega) (modes 2) <= 5 := by
    simpa [canonicalMass] using (iid_modeFrequencySq_le_five
      canonicalIIDMassPhaseEnsemble omega (modes 2))
  have h3 : modeFrequencySq
      (canonicalMass (N := N) omega) (modes 3) <= 5 := by
    simpa [canonicalMass] using (iid_modeFrequencySq_le_five
      canonicalIIDMassPhaseEnsemble omega (modes 3))
  have hn0 := modeFrequencySq_nonneg
    (canonicalMass (N := N) omega) (modes 0)
  have hn1 := modeFrequencySq_nonneg
    (canonicalMass (N := N) omega) (modes 1)
  have hn2 := modeFrequencySq_nonneg
    (canonicalMass (N := N) omega) (modes 2)
  have hn3 := modeFrequencySq_nonneg
    (canonicalMass (N := N) omega) (modes 3)
  have h01 :
      modeFrequencySq (canonicalMass (N := N) omega) (modes 0) *
          modeFrequencySq (canonicalMass (N := N) omega) (modes 1) <=
        5 * 5 :=
    mul_le_mul h0 h1 hn1 (by norm_num)
  have h012 :
      modeFrequencySq (canonicalMass (N := N) omega) (modes 0) *
            modeFrequencySq (canonicalMass (N := N) omega) (modes 1) *
          modeFrequencySq (canonicalMass (N := N) omega) (modes 2) <=
        (5 * 5) * 5 :=
    mul_le_mul h01 h2 hn2
      (mul_nonneg (by norm_num) (by norm_num))
  have h0123 :
      modeFrequencySq (canonicalMass (N := N) omega) (modes 0) *
              modeFrequencySq (canonicalMass (N := N) omega) (modes 1) *
            modeFrequencySq (canonicalMass (N := N) omega) (modes 2) *
          modeFrequencySq (canonicalMass (N := N) omega) (modes 3) <=
        ((5 * 5) * 5) * 5 :=
    mul_le_mul h012 h3 hn3
      (mul_nonneg (mul_nonneg (by norm_num) (by norm_num)) (by norm_num))
  have hsquare :
      interactionTensor (canonicalMass (N := N) omega) 4 modes ^ 2 <=
        625 := by
    exact (interactionTensor_four_sq_le
      (canonicalMass (N := N) omega) modes).trans (by norm_num at h0123 ⊢; exact h0123)
  have habs :
      |interactionTensor (canonicalMass (N := N) omega) 4 modes| <=
        Real.sqrt 625 := by
    exact Real.abs_le_sqrt hsquare
  norm_num at habs
  exact habs

def canonicalFreeCubicTensorRowEnvelope (N : Nat) : Real :=
  (N : Real) ^ 3 * 25

def canonicalFreeCubicSourceEnvelope (N : Nat) [NeZero N] : Real :=
  canonicalPositiveFrequencyNormalizationEnvelope N *
    (canonicalFreeCubicTensorRowEnvelope N *
      canonicalFreeRadiusL1Envelope N ^ 3)

theorem observedInteractionTensorAbsMass_three_canonical_le
    (omega : CanonicalSample) (observed : Lattice.Site N) :
    observedInteractionTensorAbsMass (n := 3)
        (canonicalMass (N := N) omega) observed <=
      canonicalFreeCubicTensorRowEnvelope N := by
  unfold observedInteractionTensorAbsMass
    canonicalFreeCubicTensorRowEnvelope
  calc
    (∑ modes : Fin 3 -> Lattice.Site N,
        |interactionTensor (canonicalMass (N := N) omega) 4
          (Fin.cons observed modes)|) <=
        ∑ _modes : Fin 3 -> Lattice.Site N, (25 : Real) := by
      apply Finset.sum_le_sum
      intro modes _hmodes
      exact abs_interactionTensor_four_canonical_le_twentyFive
        omega (Fin.cons observed modes)
    _ = (N : Real) ^ 3 * 25 := by
      simp [pow_succ]

theorem norm_canonicalSignedFreeCubicRotatedSource_le
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (time : Real) :
    ‖canonicalSignedFreeCubicRotatedSource (N := N)
        a entry time omega‖ <= canonicalFreeCubicSourceEnvelope N := by
  rcases entry with ⟨sign, observed⟩
  rw [canonicalSignedFreeCubicRotatedSource,
    norm_phaseSignActComplex,
    canonicalOrderedFreeCubicRotatedSource_eq_orientedPhyslib
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
  have hbase := norm_physlibFreeCubicSecondPicardRotatedSource_le
    (canonicalMass (N := N) omega) 1
      (orderedPhyslibModeIndex observed)
      (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
      (canonicalReindexedPhyslibHaarPhase (N := N) omega) time hwpos
  change ‖physlibFreeCubicSecondPicardRotatedSource
      (canonicalMass (N := N) omega) 1
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
  have htensor := observedInteractionTensorAbsMass_three_canonical_le
    (N := N) omega (orderedPhyslibModeIndex observed)
  have hradius := canonicalOrientedPhyslibFreeRadiusL1_le
    (N := N) hN ha0 ha1 omega hsimple
  have hfreeRaw := modalAbsSum_freeWeightedConfiguration_le
    (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
    (modeFrequency (canonicalMass (N := N) omega)) time
    (canonicalReindexedPhyslibHaarPhase (N := N) omega)
  have hfreeRadius : freeHistoryL1 (canonicalMass (N := N) omega)
      (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
      (canonicalReindexedPhyslibHaarPhase (N := N) omega) time <=
        radiusL1 (canonicalOrientedPhyslibFreeRadius (N := N) a omega) := by
    simpa [freeHistoryL1, radiusL1] using hfreeRaw
  have hfree : freeHistoryL1 (canonicalMass (N := N) omega)
      (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
      (canonicalReindexedPhyslibHaarPhase (N := N) omega) time <=
        canonicalFreeRadiusL1Envelope N :=
    hfreeRadius.trans hradius
  have hfree0 : 0 <= freeHistoryL1 (canonicalMass (N := N) omega)
      (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
      (canonicalReindexedPhyslibHaarPhase (N := N) omega) time := by
    unfold freeHistoryL1
    exact modalAbsSum_nonneg _
  have hfreePow := pow_le_pow_left₀ hfree0 hfree 3
  have htensor0 : 0 <= observedInteractionTensorAbsMass (n := 3)
      (canonicalMass (N := N) omega)
      (orderedPhyslibModeIndex observed) := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hrow0 : 0 <= canonicalFreeCubicTensorRowEnvelope N := by
    unfold canonicalFreeCubicTensorRowEnvelope
    positivity
  have hnormalization0 :
      0 <= |(1 : Real)| / Real.sqrt
        (2 * modeFrequency (canonicalMass (N := N) omega)
          (orderedPhyslibModeIndex observed)) := by positivity
  have hproduct :
      observedInteractionTensorAbsMass (n := 3)
            (canonicalMass (N := N) omega)
            (orderedPhyslibModeIndex observed) *
          freeHistoryL1 (canonicalMass (N := N) omega)
            (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
            (canonicalReindexedPhyslibHaarPhase (N := N) omega) time ^ 3 <=
        canonicalFreeCubicTensorRowEnvelope N *
          canonicalFreeRadiusL1Envelope N ^ 3 :=
    mul_le_mul htensor hfreePow (pow_nonneg hfree0 3) hrow0
  unfold canonicalFreeCubicSourceEnvelope
  simp only [abs_one, one_mul]
  rw [div_eq_mul_inv]
  calc
    (observedInteractionTensorAbsMass (n := 3)
          (canonicalMass (N := N) omega)
          (orderedPhyslibModeIndex observed) *
        freeHistoryL1 (canonicalMass (N := N) omega)
          (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
          (canonicalReindexedPhyslibHaarPhase (N := N) omega) time ^ 3) *
        (Real.sqrt
          (2 * modeFrequency (canonicalMass (N := N) omega)
            (orderedPhyslibModeIndex observed)))⁻¹ =
      (|(1 : Real)| / Real.sqrt
          (2 * modeFrequency (canonicalMass (N := N) omega)
            (orderedPhyslibModeIndex observed))) *
        (observedInteractionTensorAbsMass (n := 3)
            (canonicalMass (N := N) omega)
            (orderedPhyslibModeIndex observed) *
          freeHistoryL1 (canonicalMass (N := N) omega)
            (canonicalOrientedPhyslibFreeRadius (N := N) a omega)
            (canonicalReindexedPhyslibHaarPhase (N := N) omega) time ^ 3) := by
        simp only [abs_one, one_div]
        ring
    _ <= _ := mul_le_mul hnormalization hproduct
      (mul_nonneg htensor0 (pow_nonneg hfree0 3))
      canonicalPositiveFrequencyNormalizationEnvelope_nonneg

theorem integrable_canonicalSignedFreeCubicRotatedSource_fixedTime
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalSignedFreeCubicRotatedSource (N := N)
        a entry time omega)
      canonicalIIDMassPhaseEnsemble.probability := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  apply Integrable.of_bound
    (measurable_canonicalSignedFreeCubicRotatedSource
      (N := N) a entry time).aestronglyMeasurable
    (canonicalFreeCubicSourceEnvelope N)
  filter_upwards [RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae
    (N := N) canonicalIIDMassPhaseEnsemble (by omega)] with omega hsimple
  apply norm_canonicalSignedFreeCubicRotatedSource_le
    (N := N) hN ha0 ha1 omega
  · simpa [canonicalMass, harmonicHermitianSample, harmonicHermitian] using hsimple
  · exact hentry

theorem integrable_canonicalQuarticFreeCubicSource_fixedTime
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuarticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry .freeCubicSecondPicard (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  have hcanonical :=
    integrable_canonicalSignedFreeCubicRotatedSource_fixedTime
      (N := N) hN ha0 ha1 entry hentry time
  refine hcanonical.congr ?_
  filter_upwards [RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae
    (N := N) canonicalIIDMassPhaseEnsemble (by omega)] with omega hsimple
  symm
  apply canonicalQuarticFreeCubicSource_eq_measurableOrdered
    (N := N) flowKappa flowBeta flowG hflowBeta a omega
  simpa [canonicalMass, harmonicHermitianSample, harmonicHermitian] using hsimple
end
end ArchonPhysics.CanonicalIIDCoerciveActualFreeCubicHistoryIntegrability
