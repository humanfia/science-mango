import ArchonPhysics.EqualMassPeriodicFPUTActualRootedEffectiveCoefficient
import ArchonPhysics.EqualMassPeriodicFPUTCanonicalTwoToTwoShell
import ArchonPhysics.EqualMassPeriodicFPUTCanonicalUmklappCompactTest
import ArchonPhysics.EqualMassPeriodicFPUTDirectSectorClosure

/-!
# An explicit local collision-rate certificate

This file combines one reachable actual rooted effective diagram with its
canonical two-to-two shell and one transverse canonical Umklapp chart.  The
result is a strictly positive local collision-rate witness and a corresponding
compact-test collision limit.  It is deliberately local and does not define
or assume a global kinetic kernel.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTExplicitCollisionKernelCertificate

open Set
open ArchonPhysics
open ArchonPhysics.CleanCycleAcousticCountEnvelope
open ArchonPhysics.ComplexFourierBranchAmplitude
open ArchonPhysics.EqualMassPeriodicFPUTActualEffectiveDiagramEnumeration
open ArchonPhysics.EqualMassPeriodicFPUTActualFirstNormalForm
open ArchonPhysics.EqualMassPeriodicFPUTActualRootedEffectiveCoefficient
open ArchonPhysics.EqualMassPeriodicFPUTCanonicalTwoToTwoShell
open ArchonPhysics.EqualMassPeriodicFPUTCanonicalUmklappCompactTest
open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTDirectSectorClosure
open ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge
open ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex
open ArchonPhysics.EqualMassPeriodicFPUTFourierHamiltonian
open ArchonPhysics.EqualMassPeriodicFPUTInteractionPicture
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell
open ArchonPhysics.EqualMassPeriodicFPUTUmklappCollisionChartAdapter
open ArchonPhysics.EqualMassPeriodicFPUTUmklappFiniteAtlas
open ArchonPhysics.EqualMassPeriodicFPUTUmklappOnShellJacobian
open ArchonPhysics.EqualMassPeriodicFPUTUmklappTransversality
open ArchonPhysics.Lattice
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.FinitePhaseMonomials
open Filter MeasureTheory Topology

noncomputable section

/-! ## Nonvanishing of the actual rooted effective coefficient -/

theorem cleanCycleModeEnergy_ne_zero_of_mode_ne_zero
    {N : Nat} [NeZero N] {mode : Site N} (hmode : mode ≠ 0) :
    cleanCycleModeEnergy N mode ≠ 0 := by
  have hfrequency := equalMassFourierFrequency_pos_of_ne_zero hmode
  have hsquare := equalMassFourierFrequency_sq N mode
  nlinarith

theorem bondFourierSymbol_ne_zero_of_mode_ne_zero
    {N : Nat} [NeZero N] {mode : Site N} (hmode : mode ≠ 0) :
    bondFourierSymbol N mode ≠ 0 := by
  intro hzero
  have hproduct := outgoing_mul_bond_eq_neg_modeEnergy N mode
  rw [hzero, mul_zero] at hproduct
  have hcast : (cleanCycleModeEnergy N mode : Complex) = 0 := by
    simpa using hproduct.symm
  apply cleanCycleModeEnergy_ne_zero_of_mode_ne_zero hmode
  exact_mod_cast hcast

theorem outgoingFourierSymbol_ne_zero_of_mode_ne_zero
    {N : Nat} [NeZero N] {mode : Site N} (hmode : mode ≠ 0) :
    outgoingFourierSymbol N mode ≠ 0 := by
  intro hzero
  have hproduct := outgoing_mul_bond_eq_neg_modeEnergy N mode
  rw [hzero, zero_mul] at hproduct
  have hcast : (cleanCycleModeEnergy N mode : Complex) = 0 := by
    simpa using hproduct.symm
  apply cleanCycleModeEnergy_ne_zero_of_mode_ne_zero hmode
  exact_mod_cast hcast

theorem pureAlphaQuadraticFourierCoefficient_ne_zero
    {N : Nat} [NeZero N] {alpha : Real} (halpha : alpha ≠ 0)
    {output left : Site N}
    (houtput : output ≠ 0) (hleft : left ≠ 0)
    (hright : output - left ≠ 0) :
    pureAlphaQuadraticFourierCoefficient N alpha output left ≠ 0 := by
  unfold pureAlphaQuadraticFourierCoefficient
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (by exact_mod_cast halpha)
        (outgoingFourierSymbol_ne_zero_of_mode_ne_zero houtput))
      (bondFourierSymbol_ne_zero_of_mode_ne_zero hleft))
    (bondFourierSymbol_ne_zero_of_mode_ne_zero hright)

theorem equalMassQuadraticBranchVertex_ne_zero
    {N : Nat} [NeZero N] {alpha : Real} (halpha : alpha ≠ 0)
    {output left : Site N}
    (houtput : output ≠ 0) (hleft : left ≠ 0)
    (hright : output - left ≠ 0) (outputSign : PhaseSign) :
    equalMassQuadraticBranchVertex alpha output left outputSign ≠ 0 := by
  have hsign : (phaseSignReal outputSign : Complex) ≠ 0 := by
    cases outputSign <;> norm_num [phaseSignReal]
  have hsqrtOutput :
      Real.sqrt (2 * equalMassFourierFrequency N output) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2
      (mul_pos (by norm_num) (equalMassFourierFrequency_pos_of_ne_zero houtput)))
  have hsqrtLeft :
      Real.sqrt (2 * equalMassFourierFrequency N left) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2
      (mul_pos (by norm_num) (equalMassFourierFrequency_pos_of_ne_zero hleft)))
  have hsqrtRight :
      Real.sqrt (2 * equalMassFourierFrequency N (output - left)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2
      (mul_pos (by norm_num) (equalMassFourierFrequency_pos_of_ne_zero hright)))
  unfold equalMassQuadraticBranchVertex
  apply div_ne_zero
  · apply div_ne_zero
    · apply div_ne_zero
      · exact mul_ne_zero (mul_ne_zero hsign Complex.I_ne_zero)
          (pureAlphaQuadraticFourierCoefficient_ne_zero
            halpha houtput hleft hright)
      · exact_mod_cast hsqrtOutput
    · exact_mod_cast hsqrtLeft
  · exact_mod_cast hsqrtRight

theorem actualQuadraticVertex_ne_zero_of_supported
    {N : Nat} [NeZero N] {alpha : Real} (halpha : alpha ≠ 0)
    {output left right : ActualInteractionBranchMode N}
    (hsupported : ActualQuadraticMomentumSupported output left right) :
    actualQuadraticVertex N alpha output left right ≠ 0 := by
  rw [actualQuadraticVertex_eq_of_supported alpha hsupported]
  apply equalMassQuadraticBranchVertex_ne_zero halpha
  · exact actualBranchRawMode_ne_zero output
  · exact actualBranchRawMode_ne_zero left
  · rw [← rightRawMode_eq_output_sub_left_of_supported hsupported]
    exact actualBranchRawMode_ne_zero right

theorem actualRootedTwoVertexNumerator_ne_zero_of_active
    {N : Nat} [NeZero N] {alpha : Real} (halpha : alpha ≠ 0)
    (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N)
    (hactive : IsActiveActualCubicFeedback out index) :
    actualRootedTwoVertexNumerator N alpha out index ≠ 0 := by
  unfold actualRootedTwoVertexNumerator
  exact mul_ne_zero
    (actualQuadraticVertex_ne_zero_of_supported halpha hactive.1)
    (actualQuadraticVertex_ne_zero_of_supported halpha hactive.2)

theorem actualSwappedEffectiveFourWaveCoefficient_ne_zero_of_active
    {N : Nat} [NeZero N] {alpha : Real} (halpha : alpha ≠ 0)
    (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N)
    (hactive : IsActiveActualCubicFeedback out index) :
    actualSwappedEffectiveFourWaveCoefficient N alpha out index ≠ 0 := by
  unfold actualSwappedEffectiveFourWaveCoefficient
  apply div_ne_zero
  · exact actualRootedTwoVertexNumerator_ne_zero_of_active
      halpha out index hactive
  · apply mul_ne_zero Complex.I_ne_zero
    exact_mod_cast actualQuadraticMismatch_ne_zero N out
      (feedbackOuterLeft index) (feedbackOuterRight index)

theorem reachableActualSwappedEffectiveFourWaveCoefficient_ne_zero
    {N : Nat} [NeZero N] {alpha : Real} (halpha : alpha ≠ 0)
    (out : ActualInteractionBranchMode N)
    (diagram : ActiveFeedbackEffectiveDiagramImage N out) :
    reachableActualSwappedEffectiveFourWaveCoefficient
      N alpha out diagram ≠ 0 := by
  unfold reachableActualSwappedEffectiveFourWaveCoefficient
  exact actualSwappedEffectiveFourWaveCoefficient_ne_zero_of_active
    halpha out (reachableActualFeedbackIndex out diagram).1
      (reachableActualFeedbackIndex out diagram).2

/-! ## Canonical grid shell attached to a reachable actual diagram -/

def reachableEffectiveDiagram
    {N : Nat} [NeZero N] {out : ActualInteractionBranchMode N}
    (diagram : ActiveFeedbackEffectiveDiagramImage N out) :
    EffectiveFourWaveDiagram N :=
  diagram.1.1

theorem reachableEffectiveDiagram_momentumSupported
    {N : Nat} [NeZero N] {out : ActualInteractionBranchMode N}
    (diagram : ActiveFeedbackEffectiveDiagramImage N out) :
    IsTwoVertexMomentumSupported (reachableEffectiveDiagram diagram) :=
  diagram.1.2.1

theorem canonicalExternalMode_ne_zero
    {N : Nat} [NeZero N] {out : ActualInteractionBranchMode N}
    (diagram : ActiveFeedbackEffectiveDiagramImage N out) (slot : Fin 4) :
    canonicalTwoToTwoExternalModes (reachableEffectiveDiagram diagram) slot ≠ 0 := by
  unfold canonicalTwoToTwoExternalModes
  have htotal : ∀ index : Fin 4,
      totalFourWaveModes (reachableEffectiveDiagram diagram) index ≠ 0 := by
    intro index
    fin_cases index
    · simpa [reachableEffectiveDiagram, outputMomentum] using
        diagram.1.2.2 0
    · simpa [reachableEffectiveDiagram, spectatorMomentum] using
        diagram.1.2.2 2
    · simpa [reachableEffectiveDiagram, innerLeftMomentum] using
        diagram.1.2.2 3
    · simpa [reachableEffectiveDiagram, innerRightMomentum] using
        diagram.1.2.2 4
  exact htotal _

def canonicalDiagramGridK₀
    {N : Nat} [NeZero N] {out : ActualInteractionBranchMode N}
    (diagram : ActiveFeedbackEffectiveDiagramImage N out) : Real :=
  gridWaveNumber N (outputMomentum (reachableEffectiveDiagram diagram))

def canonicalDiagramGridK₁
    {N : Nat} [NeZero N] {out : ActualInteractionBranchMode N}
    (diagram : ActiveFeedbackEffectiveDiagramImage N out) : Real :=
  gridWaveNumber N
    (canonicalTwoToTwoExternalModes (reachableEffectiveDiagram diagram) 1)

def canonicalDiagramGridK₂
    {N : Nat} [NeZero N] {out : ActualInteractionBranchMode N}
    (diagram : ActiveFeedbackEffectiveDiagramImage N out) : Real :=
  gridWaveNumber N
    (canonicalTwoToTwoExternalModes (reachableEffectiveDiagram diagram) 2)

theorem canonicalDiagramGridK₀_pos
    {N : Nat} [NeZero N] {out : ActualInteractionBranchMode N}
    (diagram : ActiveFeedbackEffectiveDiagramImage N out) :
    0 < canonicalDiagramGridK₀ diagram := by
  apply gridWaveNumber_pos_of_ne_zero
  simpa [reachableEffectiveDiagram, outputMomentum] using diagram.1.2.2 0

theorem canonicalDiagramGridK₁_pos
    {N : Nat} [NeZero N] {out : ActualInteractionBranchMode N}
    (diagram : ActiveFeedbackEffectiveDiagramImage N out) :
    0 < canonicalDiagramGridK₁ diagram :=
  gridWaveNumber_pos_of_ne_zero (canonicalExternalMode_ne_zero diagram 1)

theorem canonicalDiagramGridK₀_lt_two_pi
    {N : Nat} [NeZero N] {out : ActualInteractionBranchMode N}
    (diagram : ActiveFeedbackEffectiveDiagramImage N out) :
    canonicalDiagramGridK₀ diagram < 2 * Real.pi :=
  gridWaveNumber_lt_two_pi N _

theorem canonicalDiagramGridK₁_lt_two_pi
    {N : Nat} [NeZero N] {out : ActualInteractionBranchMode N}
    (diagram : ActiveFeedbackEffectiveDiagramImage N out) :
    canonicalDiagramGridK₁ diagram < 2 * Real.pi :=
  gridWaveNumber_lt_two_pi N _

/-! ## Weighted local density and its exact positivity obstruction -/

def actualRootedLocalCollisionDensity
    {N : Nat} [NeZero N] (alpha : Real)
    (out : ActualInteractionBranchMode N)
    (diagram : ActiveFeedbackEffectiveDiagramImage N out)
    (x : Real) : Real :=
  Complex.normSq
      (reachableActualSwappedEffectiveFourWaveCoefficient
        N alpha out diagram) *
    canonicalPositiveUmklappTentDensity
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram) x

def actualRootedLocalCollisionMark
    {N : Nat} [NeZero N] (alpha : Real)
    (out : ActualInteractionBranchMode N)
    (diagram : ActiveFeedbackEffectiveDiagramImage N out)
    (z : Real) : Real :=
  umklappDensityInducedMark
    (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)
    (actualRootedLocalCollisionDensity alpha out diagram) z

def actualRootedLocalCollisionRate
    {N : Nat} [NeZero N] (alpha : Real)
    (out : ActualInteractionBranchMode N)
    (diagram : ActiveFeedbackEffectiveDiagramImage N out) : Real :=
  actualRootedLocalCollisionDensity alpha out diagram 0

theorem canonicalPositiveUmklappTentDensity_zero_pos
    {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁) :
    0 < canonicalPositiveUmklappTentDensity k₀ k₁ 0 := by
  have hstraddle := canonicalPositiveMismatchImage_straddles_zero
    hk₀0 hk₀2pi hk₁0 hk₁2pi hdisc
  unfold canonicalPositiveUmklappTentDensity compactIntervalTentDensity
  rw [max_eq_right]
  · nlinarith [hstraddle.1, hstraddle.2]
  · exact (mul_pos (by linarith [hstraddle.1])
      (by linarith [hstraddle.2])).le

/-- Exact obstruction theorem: once the transverse chart exists, the local
rate is positive precisely when the actual rooted effective coefficient is
nonzero. -/
theorem actualRootedLocalCollisionRate_pos_iff
    {N : Nat} [NeZero N] (alpha : Real)
    (out : ActualInteractionBranchMode N)
    (diagram : ActiveFeedbackEffectiveDiagramImage N out)
    (hdisc : 0 < umklappTransverseDiscriminant
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)) :
    0 < actualRootedLocalCollisionRate alpha out diagram ↔
      reachableActualSwappedEffectiveFourWaveCoefficient
        N alpha out diagram ≠ 0 := by
  unfold actualRootedLocalCollisionRate actualRootedLocalCollisionDensity
  rw [mul_pos_iff]
  have htPos := canonicalPositiveUmklappTentDensity_zero_pos
    (canonicalDiagramGridK₀_pos diagram)
    (canonicalDiagramGridK₀_lt_two_pi diagram)
    (canonicalDiagramGridK₁_pos diagram)
    (canonicalDiagramGridK₁_lt_two_pi diagram) hdisc
  constructor
  · rintro (hcoefficient | himpossible)
    · exact (Complex.normSq_pos.mp hcoefficient.1)
    · linarith [Complex.normSq_nonneg
        (reachableActualSwappedEffectiveFourWaveCoefficient
          N alpha out diagram), htPos]
  · intro hcoefficient
    exact Or.inl ⟨Complex.normSq_pos.mpr hcoefficient, htPos⟩

theorem actualRootedLocalCollisionRate_pos
    {N : Nat} [NeZero N] {alpha : Real} (halpha : alpha ≠ 0)
    (out : ActualInteractionBranchMode N)
    (diagram : ActiveFeedbackEffectiveDiagramImage N out)
    (hdisc : 0 < umklappTransverseDiscriminant
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)) :
    0 < actualRootedLocalCollisionRate alpha out diagram :=
  (actualRootedLocalCollisionRate_pos_iff alpha out diagram hdisc).2
    (reachableActualSwappedEffectiveFourWaveCoefficient_ne_zero
      halpha out diagram)

theorem actualRootedLocalCollisionDensity_data
    {N : Nat} [NeZero N] (alpha : Real)
    (out : ActualInteractionBranchMode N)
    (diagram : ActiveFeedbackEffectiveDiagramImage N out)
    (hdisc : 0 < umklappTransverseDiscriminant
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)) :
    UmklappCompactTestDensityData
      (umklappPositiveArcsineBranch
        (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)
      (actualRootedLocalCollisionDensity alpha out diagram) := by
  have tentData := canonicalPositiveUmklappTentDensity_data
    (canonicalDiagramGridK₀_pos diagram)
    (canonicalDiagramGridK₀_lt_two_pi diagram)
    (canonicalDiagramGridK₁_pos diagram)
    (canonicalDiagramGridK₁_lt_two_pi diagram) hdisc
  constructor
  · exact continuous_const.mul tentData.density_continuous
  · intro x hx
    apply tentData.density_support
    intro hzero
    apply hx
    simp [actualRootedLocalCollisionDensity, hzero]

theorem tendsto_actualRootedLocalCollision
    {N : Nat} [NeZero N] (alpha : Real)
    (out : ActualInteractionBranchMode N)
    (diagram : ActiveFeedbackEffectiveDiagramImage N out)
    (hdisc : 0 < umklappTransverseDiscriminant
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)) :
    Tendsto
      (fun T : Real ↦ ∫ z in
        umklappArcsineLocalLeft
            (umklappPositiveArcsineBranch
              (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
            (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)..
          umklappArcsineLocalRight
            (umklappPositiveArcsineBranch
              (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
            (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram),
        normalizedFiniteTimeResonanceKernel
            (umklappReducedFourWaveMismatch
              (canonicalDiagramGridK₀ diagram)
              (canonicalDiagramGridK₁ diagram) z) T *
          actualRootedLocalCollisionMark alpha out diagram z)
      atTop (nhds (actualRootedLocalCollisionRate alpha out diagram)) := by
  exact tendsto_canonicalPositiveUmklappCompactTest
    (canonicalDiagramGridK₀_pos diagram)
    (canonicalDiagramGridK₀_lt_two_pi diagram)
    (canonicalDiagramGridK₁_pos diagram)
    (canonicalDiagramGridK₁_lt_two_pi diagram) hdisc
    (actualRootedLocalCollisionDensity_data alpha out diagram hdisc)

/-! ## Certificate tying the discrete shell to the selected continuum root -/

structure ExplicitCollisionKernelCertificate
    {N : Nat} [NeZero N] (alpha : Real)
    (out : ActualInteractionBranchMode N)
    (diagram : ActiveFeedbackEffectiveDiagramImage N out) : Prop where
  coupling_ne_zero : alpha ≠ 0
  twoToTwo_sector :
    IsExternalTwoToTwoSignSector (reachableEffectiveDiagram diagram)
  transverse : 0 < umklappTransverseDiscriminant
    (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)
  root_alignment : canonicalDiagramGridK₂ diagram =
    umklappArcsineRoot
      (umklappPositiveArcsineBranch
        (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)
  umklapp_grid_branch :
    reducedTwoToTwoMismatch
        (outputMomentum (reachableEffectiveDiagram diagram))
        (canonicalTwoToTwoExternalModes (reachableEffectiveDiagram diagram) 1)
        (canonicalTwoToTwoExternalModes (reachableEffectiveDiagram diagram) 2) =
      umklappReducedFourWaveMismatch
        (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)
        (canonicalDiagramGridK₂ diagram)

theorem ExplicitCollisionKernelCertificate.canonicalShellModeThree
    {N : Nat} [NeZero N] {alpha : Real}
    {out : ActualInteractionBranchMode N}
    {diagram : ActiveFeedbackEffectiveDiagramImage N out}
    (certificate : ExplicitCollisionKernelCertificate alpha out diagram) :
    shellModeThree
        (canonicalTwoToTwoMomentumShell (reachableEffectiveDiagram diagram)) =
      canonicalTwoToTwoExternalModes (reachableEffectiveDiagram diagram) 3 :=
  shellModeThree_canonicalTwoToTwoMomentumShell
    (reachableEffectiveDiagram diagram)
    (reachableEffectiveDiagram_momentumSupported diagram)
    certificate.twoToTwo_sector

theorem ExplicitCollisionKernelCertificate.discreteShell_resonant
    {N : Nat} [NeZero N] {alpha : Real}
    {out : ActualInteractionBranchMode N}
    {diagram : ActiveFeedbackEffectiveDiagramImage N out}
    (certificate : ExplicitCollisionKernelCertificate alpha out diagram) :
    reducedTwoToTwoMismatch
        (outputMomentum (reachableEffectiveDiagram diagram))
        (canonicalTwoToTwoExternalModes (reachableEffectiveDiagram diagram) 1)
        (canonicalTwoToTwoExternalModes (reachableEffectiveDiagram diagram) 2) = 0 := by
  rw [certificate.umklapp_grid_branch, certificate.root_alignment]
  exact umklappArcsineRoot_resonant certificate.transverse _

theorem ExplicitCollisionKernelCertificate.rate_pos
    {N : Nat} [NeZero N] {alpha : Real}
    {out : ActualInteractionBranchMode N}
    {diagram : ActiveFeedbackEffectiveDiagramImage N out}
    (certificate : ExplicitCollisionKernelCertificate alpha out diagram) :
    0 < actualRootedLocalCollisionRate alpha out diagram :=
  actualRootedLocalCollisionRate_pos certificate.coupling_ne_zero
    out diagram certificate.transverse

theorem ExplicitCollisionKernelCertificate.collision_limit
    {N : Nat} [NeZero N] {alpha : Real}
    {out : ActualInteractionBranchMode N}
    {diagram : ActiveFeedbackEffectiveDiagramImage N out}
    (certificate : ExplicitCollisionKernelCertificate alpha out diagram) :
    Tendsto
      (fun T : Real ↦ ∫ z in
        umklappArcsineLocalLeft
            (umklappPositiveArcsineBranch
              (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
            (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)..
          umklappArcsineLocalRight
            (umklappPositiveArcsineBranch
              (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
            (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram),
        normalizedFiniteTimeResonanceKernel
            (umklappReducedFourWaveMismatch
              (canonicalDiagramGridK₀ diagram)
              (canonicalDiagramGridK₁ diagram) z) T *
          actualRootedLocalCollisionMark alpha out diagram z)
      atTop (nhds (actualRootedLocalCollisionRate alpha out diagram)) :=
  tendsto_actualRootedLocalCollision alpha out diagram certificate.transverse

end

end ArchonPhysics.EqualMassPeriodicFPUTExplicitCollisionKernelCertificate
