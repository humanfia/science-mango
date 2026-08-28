import ArchonPhysics.PhyslibFPUTFullStateEndpointCertificate
import ArchonPhysics.PhyslibFPUTSecondPicardFullStateEndpointAdapter
import ArchonPhysics.PhyslibFPUTDerivedReferenceBlockwiseKineticShadowing

/-!
# Full-state re-Haarization closes blockwise FPUT kinetic shadowing

This module composes the type-correct full-state endpoint certificate with
the canonical-Haar reference-block calculation.  For each kinetic block, the
actual and re-Haarized data live in an arbitrary full state space `X`; only
the observed modal amplitudes are complex-valued.  The final amplitude
coupling is derived from

* a quantitative coupling of the full initial states,
* Lipschitz control of the initial observable and actual block observable,
  and
* second-Picard consistency at the re-Haarized state.

The endpoint laws then give cubic second-moment control.  The exact
finite-character theorem derives the reference kinetic residual, so neither
a final coupling nor any kinetic residual is a field of the family below.

`PhyslibFPUTSecondPicardFullStateEndpointAdapter` supplies the physical
Hamiltonian-to-second-Picard consistency estimate.  A concrete application
must still identify its Hamiltonian states and endpoint observables with the
abstract maps in `FullStateEndpointPropagationData`; this module does not
claim that realization bridge automatically.
-/

namespace ArchonPhysics.PhyslibFPUTFullStateBlockwiseKineticShadowing

open Filter
open Topology
open MeasureTheory
open ArchonPhysics
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualHaarSecondOrderEnergyDrift
open ArchonPhysics.PhyslibFPUTBlockwiseReHaarizedKineticShadowing
open ArchonPhysics.PhyslibFPUTCoupledRestartKineticResidual
open ArchonPhysics.PhyslibFPUTDerivedReferenceBlockwiseKineticShadowing
open ArchonPhysics.PhyslibFPUTFullStateEndpointCertificate
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound

noncomputable section

/-! ## Residual-free full-state block family -/

/-- Independently re-Haarized full-state data for every block of a coherent
actual second-moment chain.

The family contains only an initial state coupling and its cubic scale,
standard Lipschitz endpoint propagation (inside `blockData`), a cubic
second-Picard radius, endpoint-law identifications, collision compatibility,
and a uniform finite-character envelope.  In particular, it has no final
coupling field and no actual or reference residual field. -/
structure FPUTFullStateBlockwiseMomentFamily
    {Omega X : Type*} [MeasurableSpace Omega] [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (M : Real)
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta T : Real)
    (observed : Lattice.Site N)
    (g : Nat → Real) (E : Nat → Nat → Real) (Q : Real → Real)
    (Cref Cstate Cpicard : Real)
    (Ainitial Aflow : NNReal) where
  energy : Nat → Nat → Lattice.Site N → Real
  blockData : Nat → Nat →
    FullStateEndpointPropagationData Omega X mu M
  Cstate_nonneg : 0 ≤ Cstate
  Cpicard_nonneg : 0 ≤ Cpicard
  couplingWindow : ∀ n, |g n| ≤ 1
  stateDelta_cubic : ∀ n j,
    (blockData n j).stateDelta ≤ Cstate * |g n| ^ 3
  picardDelta_cubic : ∀ n j,
    (blockData n j).picardDelta ≤ Cpicard * |g n| ^ 3
  initialObservableAmplification_le : ∀ n j,
    (blockData n j).initialObservableAmplification ≤ Ainitial
  flowAmplification_le : ∀ n j,
    (blockData n j).flowAmplification ≤ Aflow
  actualInitialMoment : ∀ n j,
    ∫ z, Complex.normSq z ∂
        (blockData n j).toAmplitudeCouplingRestartCertificate.actualLaw 0 =
      E n j
  actualFinalMoment : ∀ n j,
    ∫ z, Complex.normSq z ∂
        (blockData n j).toAmplitudeCouplingRestartCertificate.actualLaw 1 =
      E n (j + 1)
  referenceInitialMoment : ∀ n j,
    ∫ z, Complex.normSq z ∂
        (blockData n j).toAmplitudeCouplingRestartCertificate.referenceLaw 0 =
      canonicalHaarBlockInitial m (energy n j) observed
  referenceFinalMoment : ∀ n j,
    ∫ z, Complex.normSq z ∂
        (blockData n j).toAmplitudeCouplingRestartCertificate.referenceLaw 1 =
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

namespace FPUTFullStateBlockwiseMomentFamily

variable {Omega X : Type*} [MeasurableSpace Omega] [PseudoMetricSpace X]
  [MeasurableSpace X] [BorelSpace X]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  {M : Real}
  {N : Nat} [NeZero N]
  {m : Lattice.PositiveMassConfig N} {kappa beta T : Real}
  {observed : Lattice.Site N}
  {g : Nat → Real} {E : Nat → Nat → Real} {Q : Real → Real}
  {Cref Cstate Cpicard : Real}
  {Ainitial Aflow : NNReal}

/-- One explicit cubic second-moment envelope valid at both endpoints. -/
def couplingConstant
    (_family : FPUTFullStateBlockwiseMomentFamily (Omega := Omega) (X := X)
      mu M m kappa beta T observed g E Q Cref Cstate Cpicard
        Ainitial Aflow) : Real :=
  2 * M * ((Ainitial : Real) * Cstate) +
    2 * M * ((Aflow : Real) * Cstate + Cpicard)

theorem M_nonneg
    (family : FPUTFullStateBlockwiseMomentFamily (Omega := Omega) (X := X)
      mu M m kappa beta T observed g E Q Cref Cstate Cpicard
        Ainitial Aflow) :
    0 ≤ M :=
  (family.blockData 0 0).M_nonneg

theorem couplingConstant_nonneg
    (family : FPUTFullStateBlockwiseMomentFamily (Omega := Omega) (X := X)
      mu M m kappa beta T observed g E Q Cref Cstate Cpicard
        Ainitial Aflow) :
    0 ≤ family.couplingConstant := by
  unfold couplingConstant
  have htwoM : 0 ≤ 2 * M :=
    mul_nonneg (by norm_num) family.M_nonneg
  exact add_nonneg
    (mul_nonneg htwoM
      (mul_nonneg Ainitial.coe_nonneg family.Cstate_nonneg))
    (mul_nonneg htwoM (add_nonneg
      (mul_nonneg Aflow.coe_nonneg family.Cstate_nonneg)
      family.Cpicard_nonneg))

/-- The initial full-state RPA coupling implies the required initial
second-moment control. -/
theorem initial_endpoint_control
    (family : FPUTFullStateBlockwiseMomentFamily (Omega := Omega) (X := X)
      mu M m kappa beta T observed g E Q Cref Cstate Cpicard
        Ainitial Aflow)
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
  have hdelta :
      data.initialDelta ≤
        ((data.initialObservableAmplification : Real) * Cstate) *
          |g n| ^ 3 :=
    data.initialDelta_le_abs_cube (family.stateDelta_cubic n j)
  have hamp :
      (data.initialObservableAmplification : Real) * Cstate ≤
        (Ainitial : Real) * Cstate :=
    mul_le_mul_of_nonneg_right
      (by exact_mod_cast family.initialObservableAmplification_le n j)
      family.Cstate_nonneg
  have hdeltaUniform :
      data.initialDelta ≤
        ((Ainitial : Real) * Cstate) * |g n| ^ 3 :=
    hdelta.trans (mul_le_mul_of_nonneg_right hamp
      (pow_nonneg (abs_nonneg _) _))
  have hscaled :
      2 * M * data.initialDelta ≤
        2 * M * (((Ainitial : Real) * Cstate) * |g n| ^ 3) :=
    mul_le_mul_of_nonneg_left hdeltaUniform
      (mul_nonneg (by norm_num) family.M_nonneg)
  have hcomponent :
      2 * M * (((Ainitial : Real) * Cstate) * |g n| ^ 3) ≤
        family.couplingConstant * |g n| ^ 3 := by
    unfold couplingConstant
    have htail :
        0 ≤ 2 * M * ((Aflow : Real) * Cstate + Cpicard) :=
      mul_nonneg (mul_nonneg (by norm_num) family.M_nonneg)
        (add_nonneg
          (mul_nonneg Aflow.coe_nonneg family.Cstate_nonneg)
          family.Cpicard_nonneg)
    calc
      2 * M * (((Ainitial : Real) * Cstate) * |g n| ^ 3) =
          (2 * M * ((Ainitial : Real) * Cstate)) * |g n| ^ 3 := by ring
      _ ≤ (2 * M * ((Ainitial : Real) * Cstate) +
            2 * M * ((Aflow : Real) * Cstate + Cpicard)) * |g n| ^ 3 :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right htail)
          (pow_nonneg (abs_nonneg _) _)
  rw [family.actualInitialMoment n j,
    family.referenceInitialMoment n j] at hmoment
  exact hmoment.trans (hscaled.trans hcomponent)

/-- The final second-moment control is derived by full-state Lipschitz
propagation and second-Picard consistency; it is not family input. -/
theorem final_endpoint_control
    (family : FPUTFullStateBlockwiseMomentFamily (Omega := Omega) (X := X)
      mu M m kappa beta T observed g E Q Cref Cstate Cpicard
        Ainitial Aflow)
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
        ((data.flowAmplification : Real) * Cstate + Cpicard) *
          |g n| ^ 3 :=
    data.finalDelta_le_abs_cube
      (family.stateDelta_cubic n j) (family.picardDelta_cubic n j)
  have hamp :
      (data.flowAmplification : Real) * Cstate ≤
        (Aflow : Real) * Cstate :=
    mul_le_mul_of_nonneg_right
      (by exact_mod_cast family.flowAmplification_le n j)
      family.Cstate_nonneg
  have hdeltaUniform :
      data.finalDelta ≤
        ((Aflow : Real) * Cstate + Cpicard) * |g n| ^ 3 :=
    hdelta.trans (mul_le_mul_of_nonneg_right
      (add_le_add hamp le_rfl) (pow_nonneg (abs_nonneg _) _))
  have hscaled :
      2 * M * data.finalDelta ≤
        2 * M *
          (((Aflow : Real) * Cstate + Cpicard) * |g n| ^ 3) :=
    mul_le_mul_of_nonneg_left hdeltaUniform
      (mul_nonneg (by norm_num) family.M_nonneg)
  have hcomponent :
      2 * M * (((Aflow : Real) * Cstate + Cpicard) * |g n| ^ 3) ≤
        family.couplingConstant * |g n| ^ 3 := by
    unfold couplingConstant
    have hhead :
        0 ≤ 2 * M * ((Ainitial : Real) * Cstate) :=
      mul_nonneg (mul_nonneg (by norm_num) family.M_nonneg)
        (mul_nonneg Ainitial.coe_nonneg family.Cstate_nonneg)
    calc
      2 * M * (((Aflow : Real) * Cstate + Cpicard) * |g n| ^ 3) =
          (2 * M * ((Aflow : Real) * Cstate + Cpicard)) * |g n| ^ 3 := by
            ring
      _ ≤ (2 * M * ((Ainitial : Real) * Cstate) +
            2 * M * ((Aflow : Real) * Cstate + Cpicard)) * |g n| ^ 3 :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hhead)
          (pow_nonneg (abs_nonneg _) _)
  rw [family.actualFinalMoment n j,
    family.referenceFinalMoment n j] at hmoment
  exact hmoment.trans (hscaled.trans hcomponent)

/-- Forget the full-state probability realization after deriving both
endpoint controls.  The resulting canonical-Haar certificate has no residual
fields. -/
def toCanonicalHaarBlockwiseMomentCertificate
    (family : FPUTFullStateBlockwiseMomentFamily (Omega := Omega) (X := X)
      mu M m kappa beta T observed g E Q Cref Cstate Cpicard
        Ainitial Aflow) :
    FPUTCanonicalHaarBlockwiseMomentCertificate
      m kappa beta T observed g E Q Cref family.couplingConstant where
  energy := family.energy
  couplingWindow := family.couplingWindow
  initial_endpoint_control := family.initial_endpoint_control
  final_endpoint_control := family.final_endpoint_control
  collision_compatibility := family.collision_compatibility
  finiteCharacterEnvelope := family.finiteCharacterEnvelope

/-! ## Finite-block and kinetic-time consequences -/

/-- The completely expanded cubic residual envelope used in one block. -/
def explicitActualResidualDefect
    (family : FPUTFullStateBlockwiseMomentFamily (Omega := Omega) (X := X)
      mu M m kappa beta T observed g E Q Cref Cstate Cpicard
        Ainitial Aflow)
    (L : Real) (n : Nat) : Real :=
  Cref * |g n| ^ 3 + family.couplingConstant * |g n| ^ 3 +
    (1 + (g n ^ 2 * T) * L) *
      (family.couplingConstant * |g n| ^ 3)

/-- The abstract residual produced by the two certificate maps is definitionally
the displayed cubic endpoint-transfer expression. -/
theorem actualResidualDefect_eq_explicit
    (family : FPUTFullStateBlockwiseMomentFamily (Omega := Omega) (X := X)
      mu M m kappa beta T observed g E Q Cref Cstate Cpicard
        Ainitial Aflow)
    (hT : 0 < T) (homega : 0 < modeFrequency m observed)
    (L : Real) (n : Nat) :
    let blockwise := family.toCanonicalHaarBlockwiseMomentCertificate
      |>.toBlockwiseReHaarizedMomentCertificate hT homega
    blockwise.actualResidualDefect L n =
      family.explicitActualResidualDefect L n := by
  rfl

/-- Explicit finite-`K` shadowing.  Both the endpoint radius and reference
remainder are visible cubic expressions; neither is an assumption. -/
theorem actual_fullState_kineticEuler_shadowing_uniform_bound
    (family : FPUTFullStateBlockwiseMomentFamily (Omega := Omega) (X := X)
      mu M m kappa beta T observed g E Q Cref Cstate Cpicard
        Ainitial Aflow)
    (hT : 0 < T) (homega : 0 < modeFrequency m observed)
    (L : Real) (hL : 0 ≤ L)
    (hQ : ∀ x y, |Q x - Q y| ≤ L * |x - y|)
    (n : Nat) (V : Nat → Real)
    (hkinetic : IsKineticEulerTrajectory V (g n ^ 2 * T) Q)
    (K : Nat) :
    |E n K - V K| ≤
      (|E n 0 - V 0| +
          (K : Real) * family.explicitActualResidualDefect L n) *
        Real.exp (L * (g n ^ 2 * T) * (K : Real)) := by
  let canonical := family.toCanonicalHaarBlockwiseMomentCertificate
  let blockwise := canonical.toBlockwiseReHaarizedMomentCertificate hT homega
  have hCref : 0 ≤ Cref := canonical.Cref_nonneg
  have hdefect0 : 0 ≤ blockwise.actualResidualDefect L n :=
    blockwise.actualResidualDefect_nonneg hT.le hCref
      family.couplingConstant_nonneg hL n
  have hbound := moment_kineticEuler_shadowing_uniform_bound
    (E n) V Q (g n ^ 2 * T) L
    (blockwise.actualResidualDefect L n)
    (fun _ ↦ blockwise.actualResidualDefect L n)
    (mul_nonneg (sq_nonneg _) hT.le) hL
    (fun _ ↦ hdefect0) (fun _ ↦ le_rfl) hkinetic
    (fun j ↦ blockwise.actual_is_momentKineticEulerResidual
      hT.le hL hQ n j)
    hQ K
  have heq : blockwise.actualResidualDefect L n =
      family.explicitActualResidualDefect L n := by
    rfl
  rw [← heq]
  exact hbound

/-- Kinetic-time moment shadowing from full-state quantitative RPA restart
data.  The sole asymptotic smallness mechanism is the derived cubic endpoint
and reference error divided by the quadratic kinetic step. -/
theorem actual_fullState_kineticEuler_shadowing_tendsto_zero
    (family : FPUTFullStateBlockwiseMomentFamily (Omega := Omega) (X := X)
      mu M m kappa beta T observed g E Q Cref Cstate Cpicard
        Ainitial Aflow)
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

end FPUTFullStateBlockwiseMomentFamily

end

end ArchonPhysics.PhyslibFPUTFullStateBlockwiseKineticShadowing
