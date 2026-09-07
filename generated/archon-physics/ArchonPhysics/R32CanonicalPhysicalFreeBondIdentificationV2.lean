import ArchonPhysics.CanonicalIIDCoerciveInitialHaarBlockMoment
import ArchonPhysics.FreeFPUTMismatchPhaseExpansion
import ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
import ArchonPhysics.R32CanonicalFreeFlowIdentificationV2
import ArchonPhysics.R32DiluteNonlinearStability
import ArchonPhysics.R32PhysicalSignedFreeBondEventsV3Final

/-!
# Exact canonical zero-coupling physical bond identification

This isolated port reconstructs the physical position of the actual
canonical `g = 0` global flow in the globally measurable signed ordered
eigenframe.  Taking one forward difference gives exactly the V3 physical
signed Haar field at the same displayed physical time.
-/

open scoped BigOperators Matrix

namespace ArchonPhysics.R32CanonicalPhysicalFreeBondIdentificationV2

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveInitialHaarBlockMoment
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ComplexModeAmplitude
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.GlobalRandomMassModalObservable
open ArchonPhysics.GlobalReducedParametricFlowAdapter
open ArchonPhysics.HarmonicModes
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.InteractionPictureDuhamel
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedEigenframe
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhaseEnergyModeCoordinates
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.RandomMassMeasurableOrderedEigenframe
open ArchonPhysics.RandomMassMeasurableHarmonicEnergy
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPhaseLateWindowObservable
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassReducedPhaseInitialData
open ArchonPhysics.R32CanonicalFreeBondConcentrationV3Final
open ArchonPhysics.R32CanonicalFreeFlowIdentificationV2
open ArchonPhysics.R32DiluteNonlinearStability
open ArchonPhysics.R32FrozenEnergyDilution
open ArchonPhysics.R32FrozenFreeModalInvarianceV3
open ArchonPhysics.R32HaarScalarTailCleanV4
open ArchonPhysics.R32PhysicalSignedFreeBondEventsV3Final
open ArchonPhysics.R32SignedFreeBondMeasurabilityV3Final
open ArchonPhysics.SignedEigenframeModeAssembly
open UnitAddTorus

noncomputable section

variable {N : Nat} [NeZero N]

/-! ## Exact circle-phase convention -/

def orderedSingletonPhaseCharge {d : Type*} [DecidableEq d]
    (mode : d) : d → Int :=
  fun other ↦ if other = mode then 1 else 0

theorem chargeFrequency_orderedSingletonPhaseCharge
    {d : Type*} [Fintype d] [DecidableEq d]
    (mode : d) (frequency : d → Real) :
    chargeFrequency (orderedSingletonPhaseCharge mode) frequency =
      frequency mode := by
  classical
  unfold chargeFrequency orderedSingletonPhaseCharge
  rw [Fintype.sum_eq_single mode]
  · simp
  · intro other hne
    simp [hne]

theorem mFourier_orderedSingletonPhaseCharge
    {d : Type*} [Fintype d] [DecidableEq d]
    (mode : d) (phase : UnitAddTorus d) :
    mFourier (orderedSingletonPhaseCharge mode) phase =
      unitPhase (phase mode) := by
  classical
  unfold mFourier orderedSingletonPhaseCharge unitPhase
  change (∏ i : d, fourier (if i = mode then 1 else 0) (phase i)) =
    fourier 1 (phase mode)
  rw [Finset.prod_eq_single mode]
  · simp
  · intro other _hother hne
    simp [hne]
  · simp

theorem unitPhase_physicalFreePhaseEvolution_ordered
    {d : Type*} [Fintype d] [DecidableEq d]
    (frequency : d → Real) (time : Real)
    (phase : UnitAddTorus d) (mode : d) :
    unitPhase (physicalFreePhaseEvolution frequency time phase mode) =
      phaseFactor (-(frequency mode * time)) * unitPhase (phase mode) := by
  have h := mFourier_physicalFreePhaseEvolution
    (orderedSingletonPhaseCharge mode) frequency time phase
  rw [mFourier_orderedSingletonPhaseCharge,
    mFourier_orderedSingletonPhaseCharge,
    chargeFrequency_orderedSingletonPhaseCharge] at h
  rw [h]
  unfold phaseFactor
  congr 1
  push_cast
  ring

theorem fixedTimeHaarCarrier_eq_phaseFactor_mul_unitPhase
    (frequency time : Real) (phase : UnitAddCircle) :
    fixedTimeHaarCarrier frequency time phase =
      (phaseFactor (frequency * time) * unitPhase phase).re := by
  have hadd :
      fourier 1
          (((frequency * time / (2 * Real.pi) : Real) : UnitAddCircle) +
            phase) =
        fourier 1
            ((frequency * time / (2 * Real.pi) : Real) : UnitAddCircle) *
          fourier 1 phase := by
    simp [fourier_apply, AddCircle.toCircle_add]
  have hexp :
      fourier 1
          ((frequency * time / (2 * Real.pi) : Real) : UnitAddCircle) =
        phaseFactor (frequency * time) := by
    rw [fourier_coe_apply]
    norm_num
    unfold phaseFactor
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  unfold fixedTimeHaarCarrier fixedTimePhaseAdvance unitPhase
  rw [hadd, hexp]

theorem fixedTimeHaarCarrier_neg_time_eq_physicalFreePhase
    {d : Type*} [Fintype d] [DecidableEq d]
    (frequency : d → Real) (time : Real)
    (phase : UnitAddTorus d) (mode : d) :
    fixedTimeHaarCarrier (frequency mode) (-time) (phase mode) =
      (unitPhase
        (physicalFreePhaseEvolution frequency time phase mode)).re := by
  rw [fixedTimeHaarCarrier_eq_phaseFactor_mul_unitPhase,
    unitPhase_physicalFreePhaseEvolution_ordered]
  congr 2
  ring

/-! ## Recovering the actual free modal position -/

theorem interactionPictureCorrectionCoordinate_initialPhase
    {d : Type*} [Fintype d] [DecidableEq d]
    (energy : Real) (frequency : d → Real) (time : Real)
    (phase : UnitAddTorus d) (mode : d)
    (henergy : 0 ≤ energy) (hfrequency : 0 < frequency mode) :
    interactionPictureCorrectionCoordinate (frequency mode) time
        ((Real.sqrt (energy / frequency mode) : Complex) *
          unitPhase (phase mode)) =
      phaseCoordinate energy (frequency mode)
        (physicalFreePhaseEvolution frequency time phase mode) := by
  let evolved := physicalFreePhaseEvolution frequency time phase mode
  have hamp := complexModeAmplitude_phaseCoordinates
    evolved henergy hfrequency
  have hphase := unitPhase_physicalFreePhaseEvolution_ordered
    frequency time phase mode
  have hcancel :
      phaseFactor (frequency mode * time) *
          phaseFactor (-(frequency mode * time)) = 1 := by
    unfold phaseFactor
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 1
    congr 1
    push_cast
    ring
  have hrenormalized :
      phaseRenormalize (frequency mode * time)
          (complexModeAmplitude (frequency mode)
            (phaseCoordinate energy (frequency mode) evolved)
            (phaseMomentum energy evolved)) =
        (Real.sqrt (energy / frequency mode) : Complex) *
          unitPhase (phase mode) := by
    rw [hamp, hphase]
    unfold phaseRenormalize
    calc
      phaseFactor (frequency mode * time) *
          ((Real.sqrt (energy / frequency mode) : Complex) *
            (phaseFactor (-(frequency mode * time)) *
              unitPhase (phase mode))) =
          (Real.sqrt (energy / frequency mode) : Complex) *
            (phaseFactor (frequency mode * time) *
              phaseFactor (-(frequency mode * time))) *
                unitPhase (phase mode) := by ring
      _ = (Real.sqrt (energy / frequency mode) : Complex) *
          unitPhase (phase mode) := by rw [hcancel]; ring
  rw [← hrenormalized]
  exact interactionPictureCorrectionCoordinate_phaseRenormalize_complexModeAmplitude
    hfrequency

theorem signedFrameReconstruction_signedCoordinates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (x : ι → Real) :
    signedFrameReconstruction A
        (fun mode ↦ signedOrderedEigenvector A mode ⬝ᵥ x) = x := by
  let coefficient : Fin (Fintype.card ι) → Real :=
    fun mode ↦ signedOrderedEigenvector A mode ⬝ᵥ x
  have hprojected :
      signedFrameReconstruction A coefficient =
        ∑ mode : Fin (Fintype.card ι),
          orderedModeProjector A mode *ᵥ x := by
    unfold signedFrameReconstruction coefficient
    apply Finset.sum_congr rfl
    intro mode _hmode
    rw [← signedOrderedEigenvector_outerProduct A hsimple mode,
      Matrix.vecMulVec_mulVec]
    simp only [op_smul_eq_smul]
  rw [show (fun mode ↦ signedOrderedEigenvector A mode ⬝ᵥ x) =
      coefficient by rfl, hprojected]
  have hmul :
      (∑ mode : Fin (Fintype.card ι), orderedModeProjector A mode) *ᵥ x =
        ∑ mode : Fin (Fintype.card ι),
          orderedModeProjector A mode *ᵥ x := by
    simpa using Matrix.sum_mulVec Finset.univ
      (fun mode ↦ orderedModeProjector A mode) x
  rw [← hmul, orderedModeProjector_sum_eq_one A hsimple,
    Matrix.one_mulVec]

theorem signedLastEigenvector_dot_sqrtMassTransform_reduced_eq_zero
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (q : ReducedPositionSpace m) :
    signedOrderedEigenvector (harmonicHermitian m)
        (lastOrderedIndex (ι := Lattice.Site N)) ⬝ᵥ
      (sqrtMassTransform m (q : HilbertConfiguration N) :
        Lattice.Configuration N) = 0 := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (signedLastEigenvector_mem_translationSpan m hsimple)
  have htranslation :
      translationMode m ⬝ᵥ
          (sqrtMassTransform m (q : HilbertConfiguration N) :
            Lattice.Configuration N) = 0 := by
    calc
      translationMode m ⬝ᵥ
          (sqrtMassTransform m (q : HilbertConfiguration N) :
            Lattice.Configuration N) =
          ∑ site : Lattice.Site N,
            m.mass site * (q : HilbertConfiguration N) site := by
        unfold dotProduct
        apply Finset.sum_congr rfl
        intro site _hsite
        rw [sqrtMassTransform_apply]
        change Real.sqrt (m.mass site) *
            (Real.sqrt (m.mass site) *
              (q : HilbertConfiguration N) site) = _
        rw [← mul_assoc]
        rw [show Real.sqrt (m.mass site) * Real.sqrt (m.mass site) =
            m.mass site by
          simpa [pow_two] using Real.sq_sqrt (m.mass_pos site).le]
      _ = 0 := (mem_reducedPositionSpace_iff m _).1 q.property
  rw [← hc, smul_dotProduct, htranslation]
  simp

theorem canonicalFreeFlowOrderedModalPosition_eq_explicit
    (hN : 3 ≤ N) (kappa beta : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (sample : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) sample)))
    (time : Real) (mode : OrderedModeIndex N) :
    canonicalOrderedModalPosition (N := N)
        kappa beta 0 hbeta (1 / 4) mode (sample, time) =
      canonicalFrozenFreeModePosition sample time mode := by
  by_cases hlast : mode = lastOrderedIndex (ι := Lattice.Site N)
  · subst mode
    obtain ⟨z, _hz0, _hz, hmatch, _henergy⟩ :=
      canonicalRandomMassPhaseTrajectory_matches_reduced_of_simple
        canonicalIIDMassPhaseEnsemble hN
        (a := (1 / 4 : Real)) (by norm_num) (by norm_num)
        kappa beta 0 hbeta sample hsimple
    have hposition :
        canonicalFlowPosition (N := N)
            kappa beta 0 hbeta (1 / 4) (sample, time) =
          ((z time).1 : HilbertConfiguration N) := by
      simpa [canonicalFlowPosition, embedReducedPoint] using
        congrArg (fun x ↦ x.2.1) (hmatch time)
    have hactual :
        canonicalOrderedModalPosition (N := N)
            kappa beta 0 hbeta (1 / 4)
            (lastOrderedIndex (ι := Lattice.Site N)) (sample, time) = 0 := by
      unfold canonicalOrderedModalPosition massWeightedPositionSample
      rw [hposition]
      simpa [orderedEigenvectorSample, harmonicHermitianSample,
        harmonicHermitian, canonicalMass] using
        signedLastEigenvector_dot_sqrtMassTransform_reduced_eq_zero
          (canonicalMass (N := N) sample) hsimple (z time).1
    rw [hactual]
    simp [canonicalFrozenFreeModePosition, frozenTwoBandEnergy,
      phaseCoordinate]
  · have hfrequency :
        0 < orderedFrequencySample canonicalIIDMassPhaseEnsemble sample mode := by
      have hpos := (orderedModeFrequency_pos_iff_ne_last
        (canonicalMass (N := N) sample) hsimple mode).2 hlast
      simpa [orderedFrequencySample, harmonicHermitianSample,
        harmonicHermitian, canonicalMass] using hpos
    have hconstant := canonicalInteractionAmplitude_zeroCoupling_eq_initial
      hN (a := (1 / 4 : Real)) (by norm_num) (by norm_num)
      kappa beta hbeta sample hsimple mode
      (by simpa [orderedFrequencySample, harmonicHermitianSample,
          harmonicHermitian, canonicalMass] using hfrequency) time
    have hinitial := canonicalInteractionAmplitude_zero_of_simple
      hN (a := (1 / 4 : Real)) (by norm_num) (by norm_num)
      kappa beta 0 hbeta sample hsimple mode hlast
    have hrecover := interactionPictureCorrectionCoordinate_initialPhase
      (energy := frozenTwoBandEnergy N mode)
      (frequency := orderedFrequencySample
        canonicalIIDMassPhaseEnsemble sample)
      (time := time)
      (phase := fun k ↦
        orderedPhaseSample canonicalIIDMassPhaseEnsemble sample k)
      (mode := mode)
      (frozenTwoBandEnergy_nonneg hN mode) hfrequency
    calc
      canonicalOrderedModalPosition (N := N)
          kappa beta 0 hbeta (1 / 4) mode (sample, time) =
          interactionPictureCorrectionCoordinate
            (orderedFrequencySample canonicalIIDMassPhaseEnsemble sample mode)
            time
            (canonicalInteractionAmplitude (N := N)
              kappa beta 0 hbeta (1 / 4) mode (sample, time)) := by
        symm
        simpa [canonicalInteractionAmplitude, canonicalOrderedFrequency,
          orderedFrequencySample, harmonicHermitianSample,
          harmonicHermitian, canonicalMass] using
          (interactionPictureCorrectionCoordinate_phaseRenormalize_complexModeAmplitude
            (omega := orderedFrequencySample
              canonicalIIDMassPhaseEnsemble sample mode)
            (Q := canonicalOrderedModalPosition (N := N)
              kappa beta 0 hbeta (1 / 4) mode (sample, time))
            (P := canonicalOrderedModalMomentum (N := N)
              kappa beta 0 hbeta (1 / 4) mode (sample, time))
            (time := time) hfrequency)
      _ = interactionPictureCorrectionCoordinate
            (orderedFrequencySample canonicalIIDMassPhaseEnsemble sample mode)
            time
            (canonicalInteractionAmplitude (N := N)
              kappa beta 0 hbeta (1 / 4) mode (sample, 0)) := by
        rw [hconstant]
      _ = interactionPictureCorrectionCoordinate
            (orderedFrequencySample canonicalIIDMassPhaseEnsemble sample mode)
            time
            (((Real.sqrt
                (frozenTwoBandEnergy N mode /
                  orderedFrequencySample canonicalIIDMassPhaseEnsemble
                    sample mode) : Real) : Complex) *
              unitPhase
                (orderedPhaseSample canonicalIIDMassPhaseEnsemble
                  sample mode)) := by
        rw [hinitial]
        simp [canonicalInitialOrderedRadius, canonicalOrderedFrequency,
          frozenTwoBandEnergy, orderedFrequencySample,
          harmonicHermitianSample, harmonicHermitian, canonicalMass]
      _ = canonicalFrozenFreeModePosition sample time mode := by
        simpa [canonicalFrozenFreeModePosition, canonicalFrozenFreePhase]
          using hrecover

/-! ## Full physical-position reconstruction -/

def canonicalFrozenFreePhysicalPosition
    (sample : CanonicalSample) (time : Real) : HilbertConfiguration N :=
  inverseSqrtMassTransform (canonicalMass (N := N) sample)
    (WithLp.toLp 2
      (signedFrameReconstruction
        (harmonicHermitian (canonicalMass (N := N) sample))
        (canonicalFrozenFreeModePosition sample time)))

theorem canonicalFreeFlowMassWeightedPosition_eq_explicit
    (hN : 3 ≤ N) (kappa beta : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (sample : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) sample)))
    (time : Real) :
    (sqrtMassTransform (canonicalMass (N := N) sample)
        (canonicalFlowPosition (N := N)
          kappa beta 0 hbeta (1 / 4) (sample, time)) :
      Lattice.Configuration N) =
      signedFrameReconstruction
        (harmonicHermitian (canonicalMass (N := N) sample))
        (canonicalFrozenFreeModePosition sample time) := by
  let X : Lattice.Configuration N :=
    (sqrtMassTransform (canonicalMass (N := N) sample)
      (canonicalFlowPosition (N := N)
        kappa beta 0 hbeta (1 / 4) (sample, time)) :
      Lattice.Configuration N)
  calc
    X = signedFrameReconstruction
        (harmonicHermitian (canonicalMass (N := N) sample))
        (fun mode ↦
          signedOrderedEigenvector
              (harmonicHermitian (canonicalMass (N := N) sample)) mode ⬝ᵥ X) :=
      (signedFrameReconstruction_signedCoordinates
        (harmonicHermitian (canonicalMass (N := N) sample)) hsimple X).symm
    _ = signedFrameReconstruction
        (harmonicHermitian (canonicalMass (N := N) sample))
        (canonicalFrozenFreeModePosition sample time) := by
      apply congrArg
      funext mode
      simpa [X, canonicalOrderedModalPosition, orderedEigenvectorSample,
        massWeightedPositionSample, harmonicHermitianSample,
        harmonicHermitian, canonicalMass] using
        canonicalFreeFlowOrderedModalPosition_eq_explicit
          hN kappa beta hbeta sample hsimple time mode

theorem canonicalFreeFlowPosition_eq_explicit
    (hN : 3 ≤ N) (kappa beta : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (sample : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) sample)))
    (time : Real) :
    canonicalFlowPosition (N := N)
        kappa beta 0 hbeta (1 / 4) (sample, time) =
      canonicalFrozenFreePhysicalPosition sample time := by
  have hweighted := canonicalFreeFlowMassWeightedPosition_eq_explicit
    hN kappa beta hbeta sample hsimple time
  unfold canonicalFrozenFreePhysicalPosition
  ext site
  rw [inverseSqrtMassTransform_apply]
  have hsite := congrFun hweighted site
  rw [sqrtMassTransform_apply] at hsite
  change
    (canonicalFlowPosition (N := N)
        kappa beta 0 hbeta (1 / 4) (sample, time)) site =
      (Real.sqrt ((canonicalMass (N := N) sample).mass site))⁻¹ *
        signedFrameReconstruction
          (harmonicHermitian (canonicalMass (N := N) sample))
          (canonicalFrozenFreeModePosition sample time) site
  rw [← hsite]
  rw [← mul_assoc,
    inv_mul_cancel₀
      (Real.sqrt_ne_zero'.2
        ((canonicalMass (N := N) sample).mass_pos site)), one_mul]

/-! ## Taking the physical forward difference -/

theorem bondVector_inverseSqrt_signedFrameReconstruction
    (m : Lattice.PositiveMassConfig N)
    (coefficient : OrderedModeIndex N → Real)
    (bond : Lattice.Site N) :
    bondVector
        (inverseSqrtMassTransform m
          (WithLp.toLp 2
            (signedFrameReconstruction (harmonicHermitian m) coefficient))) bond =
      ∑ mode : OrderedModeIndex N,
        coefficient mode * signedOrderedRawEdgeMode m mode bond := by
  let reconstructed : Lattice.Configuration N :=
    signedFrameReconstruction (harmonicHermitian m) coefficient
  have hdiag :
      Matrix.mulVec
          (Matrix.diagonal (fun site : Lattice.Site N ↦
            (Real.sqrt (m.mass site))⁻¹)) reconstructed =
        fun site ↦ (Real.sqrt (m.mass site))⁻¹ * reconstructed site := by
    ext site
    rw [Matrix.mulVec_diagonal]
  have hlinear :
      Matrix.mulVec (massWeightedDifferenceMatrix m) reconstructed =
        fun site ↦ ∑ mode : OrderedModeIndex N,
          coefficient mode * signedOrderedRawEdgeMode m mode site := by
    ext site
    unfold reconstructed signedFrameReconstruction
      signedOrderedRawEdgeMode Matrix.mulVec dotProduct
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro mode _hmode
    apply Finset.sum_congr rfl
    intro coordinate _hcoordinate
    ring
  calc
    bondVector
        (inverseSqrtMassTransform m
          (WithLp.toLp 2 reconstructed)) bond =
        Matrix.mulVec differenceMatrix
          (fun site ↦ (Real.sqrt (m.mass site))⁻¹ *
            reconstructed site) bond := by
      rw [bondVector_apply]
      rw [show
        asConfiguration
            (inverseSqrtMassTransform m (WithLp.toLp 2 reconstructed)) =
          (fun site ↦
            (Real.sqrt (m.mass site))⁻¹ * reconstructed site) by
          funext site
          exact inverseSqrtMassTransform_apply
            m (WithLp.toLp 2 reconstructed) site]
      exact (congrFun
        (differenceMatrix_mulVec
          (fun site ↦ (Real.sqrt (m.mass site))⁻¹ *
            reconstructed site)) bond).symm
    _ = Matrix.mulVec differenceMatrix
        (Matrix.mulVec
          (Matrix.diagonal (fun site : Lattice.Site N ↦
            (Real.sqrt (m.mass site))⁻¹)) reconstructed) bond := by
      rw [hdiag]
    _ = Matrix.mulVec (massWeightedDifferenceMatrix m)
        reconstructed bond := by
      unfold massWeightedDifferenceMatrix
      rw [Matrix.mulVec_mulVec]
    _ = ∑ mode : OrderedModeIndex N,
        coefficient mode * signedOrderedRawEdgeMode m mode bond :=
      congrFun hlinear bond

theorem phaseCoordinate_mul_signedRawEdge_eq_signedHaarTerm
    (m : Lattice.PositiveMassConfig N)
    (phase : UnitAddTorus (OrderedModeIndex N))
    (time : Real) (bond : Lattice.Site N) (mode : OrderedModeIndex N) :
    phaseCoordinate (frozenTwoBandEnergy N mode)
        (orderedModeFrequency (harmonicHermitian m) mode)
        (physicalFreePhaseEvolution
          (orderedModeFrequency (harmonicHermitian m)) time phase mode) *
      signedOrderedRawEdgeMode m mode bond =
        signedFrozenBondCoefficient m bond mode *
          fixedTimeHaarCarrier
            (orderedModeFrequency (harmonicHermitian m) mode)
            (-time) (phase mode) := by
  by_cases hlast : mode = lastOrderedIndex (ι := Lattice.Site N)
  · subst mode
    simp [phaseCoordinate, frozenTwoBandEnergy,
      signedFrozenBondCoefficient, signedNormalizedEdgeFrame]
  · rw [fixedTimeHaarCarrier_neg_time_eq_physicalFreePhase]
    unfold phaseCoordinate signedFrozenBondCoefficient
      signedNormalizedEdgeFrame
    simp only [if_neg hlast]
    ring

theorem canonicalFrozenFreePhysicalBond_eq_signedHaar
    (sample : CanonicalSample) (time : Real) (bond : Lattice.Site N) :
    bondVector (canonicalFrozenFreePhysicalPosition sample time) bond =
      signedHaarBondField (canonicalMass (N := N) sample) bond
        (orderedPhaseBlockFromSequence (N := N) sample.2) (-time) := by
  unfold canonicalFrozenFreePhysicalPosition
  rw [bondVector_inverseSqrt_signedFrameReconstruction]
  unfold signedHaarBondField fixedTimeHaarScalarSum
  apply Finset.sum_congr rfl
  intro mode _hmode
  have hfrequencyFun :
      orderedFrequencySample canonicalIIDMassPhaseEnsemble sample =
        orderedModeFrequency
          (harmonicHermitian (canonicalMass (N := N) sample)) := by
    rfl
  have hphaseFun :
      (fun k ↦ orderedPhaseSample canonicalIIDMassPhaseEnsemble sample k) =
        orderedPhaseBlockFromSequence (N := N) sample.2 := by
    rfl
  unfold canonicalFrozenFreeModePosition canonicalFrozenFreePhase
  rw [hfrequencyFun, hphaseFun]
  simpa [harmonicHermitianSample, harmonicHermitian, canonicalMass] using
    (phaseCoordinate_mul_signedRawEdge_eq_signedHaarTerm
      (canonicalMass (N := N) sample)
      (orderedPhaseBlockFromSequence (N := N) sample.2)
      time bond mode)

theorem rawCanonicalFrozenMass_eq_canonicalMass
    (sample : CanonicalSample) :
    rawCanonicalFrozenMass (N := N) sample.1 =
      canonicalMass (N := N) sample := by
  rw [Lattice.PositiveMassConfig.mk.injEq]
  rfl

/-- The actual canonical `g = 0` physical bond is the V3 measurable signed
Haar field at the same displayed physical time. -/
theorem canonicalFreeFlowBond_eq_physicalSignedHaar
    (hN : 3 ≤ N) (kappa beta : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (sample : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) sample)))
    (time : Real) (bond : Lattice.Site N) :
    bondVector
        (canonicalFlowPosition (N := N)
          kappa beta 0 hbeta (1 / 4) (sample, time)) bond =
      physicalSignedHaarBondField
        (rawCanonicalFrozenMass (N := N) sample.1) bond
        (orderedPhaseBlockFromSequence (N := N) sample.2) time := by
  rw [canonicalFreeFlowPosition_eq_explicit
    hN kappa beta hbeta sample hsimple time,
    canonicalFrozenFreePhysicalBond_eq_signedHaar]
  rw [rawCanonicalFrozenMass_eq_canonicalMass]
  rfl

#print axioms canonicalFreeFlowOrderedModalPosition_eq_explicit
#print axioms canonicalFreeFlowPosition_eq_explicit
#print axioms canonicalFrozenFreePhysicalBond_eq_signedHaar
#print axioms canonicalFreeFlowBond_eq_physicalSignedHaar

end

end ArchonPhysics.R32CanonicalPhysicalFreeBondIdentificationV2
