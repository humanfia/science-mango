import ArchonPhysics.PhyslibFPUTReHaarizedEndpointPropagation
import ArchonPhysics.PhyslibFPUTDerivedReferenceBlockwiseKineticShadowing

/-!
# Propagated endpoint couplings close blockwise FPUT kinetic shadowing

This module composes the deterministic one-block endpoint propagation with
canonical-Haar blockwise kinetic shadowing.  For every kinetic block the
input is a re-Haarized initial coupling, stability of the actual block, and
second-Picard consistency.  The final endpoint coupling is derived; it is not
a field of the family below.

After identifying the second moments of the constructed endpoint laws with
the coherent actual chain and the canonical Haar reference endpoints, both
scalar endpoint errors have one explicit cubic envelope.  Consequently the
existing exact finite-character calculation supplies the reference kinetic
residual and yields kinetic-time shadowing.
-/

namespace ArchonPhysics.PhyslibFPUTPropagatedEndpointBlockwiseKineticShadowing

open Filter
open Topology
open MeasureTheory
open ArchonPhysics
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualHaarSecondOrderEnergyDrift
open ArchonPhysics.PhyslibFPUTCouplingMultiblockRestart
open ArchonPhysics.PhyslibFPUTBlockwiseReHaarizedKineticShadowing
open ArchonPhysics.PhyslibFPUTReHaarizedEndpointPropagation
open ArchonPhysics.PhyslibFPUTDerivedReferenceBlockwiseKineticShadowing
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound

noncomputable section

/-! ## A family whose final endpoint control is derived -/

/-- Independently re-Haarized probabilistic data for every block of one
coherent actual moment chain.

The only dynamical estimates in the data are initial re-Haarization,
one-block stability, and second-Picard consistency, all contained in
`ReHaarizedEndpointPropagationData`.  In particular there is no final
endpoint coupling field and no kinetic-residual field. -/
structure FPUTPropagatedEndpointBlockwiseMomentFamily
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (M : Real)
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta T : Real)
    (observed : Lattice.Site N)
    (g : Nat → Real) (E : Nat → Nat → Real) (Q : Real → Real)
    (Cref Cinitial Cpicard A : Real) where
  energy : Nat → Nat → Lattice.Site N → Real
  blockData : Nat → Nat → ReHaarizedEndpointPropagationData mu M
  Cinitial_nonneg : 0 ≤ Cinitial
  Cpicard_nonneg : 0 ≤ Cpicard
  A_nonneg : 0 ≤ A
  couplingWindow : ∀ n, |g n| ≤ 1
  initialDelta_cubic : ∀ n j,
    (blockData n j).initialDelta ≤ Cinitial * |g n| ^ 3
  picardDelta_cubic : ∀ n j,
    (blockData n j).picardDelta ≤ Cpicard * |g n| ^ 3
  flowAmplification_le : ∀ n j,
    (blockData n j).flowAmplification ≤ A
  actualInitialMoment : ∀ n j,
    ∫ z, Complex.normSq z ∂(blockData n j).toAmplitudeCouplingRestartCertificate.actualLaw 0 =
      E n j
  actualFinalMoment : ∀ n j,
    ∫ z, Complex.normSq z ∂(blockData n j).toAmplitudeCouplingRestartCertificate.actualLaw 1 =
      E n (j + 1)
  referenceInitialMoment : ∀ n j,
    ∫ z, Complex.normSq z ∂(blockData n j).toAmplitudeCouplingRestartCertificate.referenceLaw 0 =
      canonicalHaarBlockInitial m (energy n j) observed
  referenceFinalMoment : ∀ n j,
    ∫ z, Complex.normSq z ∂(blockData n j).toAmplitudeCouplingRestartCertificate.referenceLaw 1 =
      canonicalHaarBlockFinal m kappa beta (g n) (energy n j) T observed
  collision_compatibility : ∀ n j,
    Q (canonicalHaarBlockInitial m (energy n j) observed) =
      normalizedSecondOrderHaarBroadening
        m kappa beta (energy n j) observed T
  finiteCharacterEnvelope : ∀ n j,
    physlibHaarEnergyDriftC3 m kappa beta
          (phaseEnergyRadius (energy n j) (modeFrequency m)) T observed +
        physlibHaarEnergyDriftC4 m kappa beta
          (phaseEnergyRadius (energy n j) (modeFrequency m)) T observed ≤
      Cref

/-! The present family is an abstract scalar-amplitude block closure.  Since
`ReHaarizedEndpointPropagationData` propagates `Complex → Complex` maps, a
separate full-state adapter is still required to instantiate it with the
coupled all-mode Hamiltonian FPUT flow. -/

namespace FPUTPropagatedEndpointBlockwiseMomentFamily

variable {Omega : Type*} [MeasurableSpace Omega]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  {M : Real}
  {N : Nat} [NeZero N]
  {m : Lattice.PositiveMassConfig N} {kappa beta T : Real}
  {observed : Lattice.Site N}
  {g : Nat → Real} {E : Nat → Nat → Real} {Q : Real → Real}
  {Cref Cinitial Cpicard A : Real}

/-- One common (deliberately generous) cubic constant for both endpoints. -/
def couplingConstant
    (_family : FPUTPropagatedEndpointBlockwiseMomentFamily
      mu M m kappa beta T observed g E Q Cref Cinitial Cpicard A) : Real :=
  2 * M * Cinitial + 2 * M * (A * Cinitial + Cpicard)

theorem M_nonneg
    (family : FPUTPropagatedEndpointBlockwiseMomentFamily
      mu M m kappa beta T observed g E Q Cref Cinitial Cpicard A) :
    0 ≤ M :=
  (family.blockData 0 0).M_nonneg

theorem couplingConstant_nonneg
    (family : FPUTPropagatedEndpointBlockwiseMomentFamily
      mu M m kappa beta T observed g E Q Cref Cinitial Cpicard A) :
    0 ≤ family.couplingConstant := by
  unfold couplingConstant
  have htwoM : 0 ≤ 2 * M := mul_nonneg (by norm_num) family.M_nonneg
  exact add_nonneg
    (mul_nonneg htwoM family.Cinitial_nonneg)
    (mul_nonneg htwoM (add_nonneg
      (mul_nonneg family.A_nonneg family.Cinitial_nonneg)
      family.Cpicard_nonneg))

/-- Initial scalar moment control follows from the initial common-source
coupling and its cubic radius. -/
theorem initial_endpoint_control
    (family : FPUTPropagatedEndpointBlockwiseMomentFamily
      mu M m kappa beta T observed g E Q Cref Cinitial Cpicard A)
    (n j : Nat) :
    |E n j - canonicalHaarBlockInitial m (family.energy n j) observed| ≤
      family.couplingConstant * |g n| ^ 3 := by
  let data := family.blockData n j
  let certificate := data.toAmplitudeCouplingRestartCertificate
  have hmoment :
      |∫ z, Complex.normSq z ∂certificate.actualLaw 0 -
          ∫ z, Complex.normSq z ∂certificate.referenceLaw 0| ≤
        2 * M * data.initialDelta :=
    (data.endpoint_second_fourth_moment_errors).1.1
  have hscaled :
      2 * M * data.initialDelta ≤
        2 * M * (Cinitial * |g n| ^ 3) :=
    mul_le_mul_of_nonneg_left (family.initialDelta_cubic n j)
      (mul_nonneg (by norm_num) family.M_nonneg)
  have hcomponent :
      2 * M * (Cinitial * |g n| ^ 3) ≤
        family.couplingConstant * |g n| ^ 3 := by
    unfold couplingConstant
    have htail : 0 ≤ 2 * M * (A * Cinitial + Cpicard) :=
      mul_nonneg (mul_nonneg (by norm_num) family.M_nonneg)
        (add_nonneg
          (mul_nonneg family.A_nonneg family.Cinitial_nonneg)
          family.Cpicard_nonneg)
    calc
      2 * M * (Cinitial * |g n| ^ 3) =
          (2 * M * Cinitial) * |g n| ^ 3 := by ring
      _ ≤ (2 * M * Cinitial + 2 * M * (A * Cinitial + Cpicard)) *
          |g n| ^ 3 :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right htail)
          (pow_nonneg (abs_nonneg _) _)
  rw [family.actualInitialMoment n j, family.referenceInitialMoment n j] at hmoment
  exact hmoment.trans (hscaled.trans hcomponent)

/-- The endpoint-one scalar moment control is derived from propagation.
There is no endpoint-one closeness hypothesis in the family. -/
theorem final_endpoint_control
    (family : FPUTPropagatedEndpointBlockwiseMomentFamily
      mu M m kappa beta T observed g E Q Cref Cinitial Cpicard A)
    (n j : Nat) :
    |E n (j + 1) -
        canonicalHaarBlockFinal m kappa beta (g n)
          (family.energy n j) T observed| ≤
      family.couplingConstant * |g n| ^ 3 := by
  let data := family.blockData n j
  let certificate := data.toAmplitudeCouplingRestartCertificate
  have hmoment :
      |∫ z, Complex.normSq z ∂certificate.actualLaw 1 -
          ∫ z, Complex.normSq z ∂certificate.referenceLaw 1| ≤
        2 * M * data.finalDelta :=
    (data.endpoint_second_fourth_moment_errors).2.1
  have hdelta :
      data.finalDelta ≤
        (data.flowAmplification * Cinitial + Cpicard) * |g n| ^ 3 :=
    data.finalDelta_le_abs_cube
      (family.initialDelta_cubic n j) (family.picardDelta_cubic n j)
  have hflowC :
      data.flowAmplification * Cinitial ≤ A * Cinitial :=
    mul_le_mul_of_nonneg_right (family.flowAmplification_le n j)
      family.Cinitial_nonneg
  have hdeltaUniform :
      data.finalDelta ≤
        (A * Cinitial + Cpicard) * |g n| ^ 3 := by
    exact hdelta.trans (mul_le_mul_of_nonneg_right
      (add_le_add hflowC le_rfl) (pow_nonneg (abs_nonneg _) _))
  have hscaled :
      2 * M * data.finalDelta ≤
        2 * M * ((A * Cinitial + Cpicard) * |g n| ^ 3) :=
    mul_le_mul_of_nonneg_left hdeltaUniform
      (mul_nonneg (by norm_num) family.M_nonneg)
  have hcomponent :
      2 * M * ((A * Cinitial + Cpicard) * |g n| ^ 3) ≤
        family.couplingConstant * |g n| ^ 3 := by
    unfold couplingConstant
    have hhead : 0 ≤ 2 * M * Cinitial :=
      mul_nonneg (mul_nonneg (by norm_num) family.M_nonneg)
        family.Cinitial_nonneg
    calc
      2 * M * ((A * Cinitial + Cpicard) * |g n| ^ 3) =
          (2 * M * (A * Cinitial + Cpicard)) * |g n| ^ 3 := by ring
      _ ≤ (2 * M * Cinitial + 2 * M * (A * Cinitial + Cpicard)) *
          |g n| ^ 3 :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hhead)
          (pow_nonneg (abs_nonneg _) _)
  rw [family.actualFinalMoment n j, family.referenceFinalMoment n j] at hmoment
  exact hmoment.trans (hscaled.trans hcomponent)

/-- Forget the probabilistic realization after deriving both scalar endpoint
controls.  This constructs exactly the residual-free canonical Haar
certificate used by kinetic-time shadowing. -/
def toCanonicalHaarBlockwiseMomentCertificate
    (family : FPUTPropagatedEndpointBlockwiseMomentFamily
      mu M m kappa beta T observed g E Q Cref Cinitial Cpicard A) :
    FPUTCanonicalHaarBlockwiseMomentCertificate
      m kappa beta T observed g E Q Cref family.couplingConstant where
  energy := family.energy
  couplingWindow := family.couplingWindow
  initial_endpoint_control := family.initial_endpoint_control
  final_endpoint_control := family.final_endpoint_control
  collision_compatibility := family.collision_compatibility
  finiteCharacterEnvelope := family.finiteCharacterEnvelope

/-- A finite-block quantitative estimate underlying the asymptotic kinetic
time theorem.  Its residual is not assumed: the endpoint propagation and
canonical finite-character calculation construct it through the two
forgetful certificate maps. -/
theorem actual_propagatedEndpoint_kineticEuler_shadowing_uniform_bound
    (family : FPUTPropagatedEndpointBlockwiseMomentFamily
      mu M m kappa beta T observed g E Q Cref Cinitial Cpicard A)
    (hT : 0 < T) (homega : 0 < modeFrequency m observed)
    (L : Real) (hL : 0 ≤ L)
    (hQ : ∀ x y, |Q x - Q y| ≤ L * |x - y|)
    (n : Nat) (V : Nat → Real)
    (hkinetic : IsKineticEulerTrajectory V (g n ^ 2 * T) Q)
    (K : Nat) :
    let blockwise := family.toCanonicalHaarBlockwiseMomentCertificate
      |>.toBlockwiseReHaarizedMomentCertificate hT homega
    |E n K - V K| ≤
      (|E n 0 - V 0| +
          (K : Real) * blockwise.actualResidualDefect L n) *
        Real.exp (L * (g n ^ 2 * T) * (K : Real)) := by
  dsimp only
  let canonical := family.toCanonicalHaarBlockwiseMomentCertificate
  let blockwise := canonical.toBlockwiseReHaarizedMomentCertificate hT homega
  have hCref : 0 ≤ Cref := canonical.Cref_nonneg
  have hdefect0 : 0 ≤ blockwise.actualResidualDefect L n :=
    blockwise.actualResidualDefect_nonneg hT.le hCref
      family.couplingConstant_nonneg hL n
  exact moment_kineticEuler_shadowing_uniform_bound
    (E n) V Q (g n ^ 2 * T) L
    (blockwise.actualResidualDefect L n)
    (fun _ ↦ blockwise.actualResidualDefect L n)
    (mul_nonneg (sq_nonneg _) hT.le) hL
    (fun _ ↦ hdefect0) (fun _ ↦ le_rfl) hkinetic
    (fun j ↦ blockwise.actual_is_momentKineticEulerResidual
      hT.le hL hQ n j)
    hQ K

/-! ## Kinetic-time consequence -/

/-- Kinetic-time moment shadowing with the final endpoint coupling derived
from the re-Haarized initial coupling, block stability, and second-Picard
consistency. -/
theorem actual_propagatedEndpoint_kineticEuler_shadowing_tendsto_zero
    (family : FPUTPropagatedEndpointBlockwiseMomentFamily
      mu M m kappa beta T observed g E Q Cref Cinitial Cpicard A)
    (hT : 0 < T) (homega : 0 < modeFrequency m observed)
    (L : Real) (hL : 0 ≤ L)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : ∀ᶠ n in atTop, g n ≠ 0)
    (V : Nat → Nat → Real) (K : Nat → Nat) (tau : Real)
    (hQ : ∀ x y, |Q x - Q y| ≤ L * |x - y|)
    (hkinetic : ∀ n,
      IsKineticEulerTrajectory (V n) (g n ^ 2 * T) Q)
    (hkineticBudget : ∀ n,
      (g n ^ 2 * T) * (K n : Real) ≤ tau)
    (hinitial : Tendsto (fun n ↦ |E n 0 - V n 0|)
      atTop (nhds 0)) :
    Tendsto (fun n ↦ |E n (K n) - V n (K n)|)
      atTop (nhds 0) := by
  exact family.toCanonicalHaarBlockwiseMomentCertificate
    |>.actual_canonicalHaarBlockwise_kineticEuler_shadowing_tendsto_zero
      hT homega family.couplingConstant_nonneg L hL hg hg0 V K tau
      hQ hkinetic hkineticBudget hinitial

end FPUTPropagatedEndpointBlockwiseMomentFamily

end

end ArchonPhysics.PhyslibFPUTPropagatedEndpointBlockwiseKineticShadowing
