import ArchonPhysics.PhyslibFPUTProbabilisticFullStateEndpointCertificate
import ArchonPhysics.PhyslibFPUTDerivedReferenceBlockwiseKineticShadowing

/-!
# Probabilistic full-state FPUT blockwise kinetic shadowing

This module lifts the one-block probabilistic full-state endpoint certificate
to a family of independently re-Haarized blocks.  At every `(n,j)` the
full-state coupling is required only outside its own measurable bad event.
Neither a final-state coupling nor a kinetic residual is assumed.

The blockwise hypothesis remains explicit: the state radius, second-Picard
radius, and bad-event probability are bounded by constants times `|g n|^3`.
The one-block endpoint theorem therefore gives the actual/reference second
moment controls, including the bad-event contribution.  These controls build
the existing canonical-Haar moment certificate, whose exact finite-character
calculation supplies the reference residual and hence the actual kinetic
shadowing theorem.

This is an adapter for a quantitative probabilistic RPA hypothesis; it does
not prove that the nonlinear Hamiltonian flow generates that hypothesis.

For clarity, the module also retains the individual bad events.  A finite
union bound shows that the probability that any of the first `K` block
couplings fails is at most `K * Cfailure * |g n|^3`.  On a kinetic window
`g_n^2 T K <= tau`, this is at most
`(tau / T) * Cfailure * |g n|`, i.e. `O(|g n|)`.
-/

namespace ArchonPhysics.PhyslibFPUTProbabilisticFullStateBlockwiseKineticShadowing

open Filter
open Topology
open MeasureTheory
open ArchonPhysics
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualHaarSecondOrderEnergyDrift
open ArchonPhysics.PhyslibFPUTBlockwiseReHaarizedKineticShadowing
open ArchonPhysics.PhyslibFPUTDerivedReferenceBlockwiseKineticShadowing
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing
open ArchonPhysics.PhyslibFPUTProbabilisticFullStateEndpointCertificate
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound

noncomputable section

/-- Independently re-Haarized probabilistic full-state data for every block of
a coherent actual second-moment chain.

The `failureProbability_cubic` field bounds the probability budget stored in
each one-block certificate; it is not a conclusion about Hamiltonian RPA
generation.  Endpoint-law and scalar collision identifications are likewise
kept transparent. -/
structure FPUTProbabilisticFullStateBlockwiseMomentFamily
    {Omega X : Type*} [MeasurableSpace Omega] [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (M : Real)
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta T : Real)
    (observed : Lattice.Site N)
    (g : Nat → Real) (E : Nat → Nat → Real) (Q : Real → Real)
    (Cref Cstate Cpicard Cfailure : Real)
    (Ainitial Aflow : NNReal) where
  energy : Nat → Nat → Lattice.Site N → Real
  blockData : Nat → Nat →
    ProbabilisticFullStateEndpointPropagationData Omega X mu M
  Cstate_nonneg : 0 ≤ Cstate
  Cpicard_nonneg : 0 ≤ Cpicard
  Cfailure_nonneg : 0 ≤ Cfailure
  couplingWindow : ∀ n, |g n| ≤ 1
  stateDelta_cubic : ∀ n j,
    (blockData n j).stateDelta ≤ Cstate * |g n| ^ 3
  picardDelta_cubic : ∀ n j,
    (blockData n j).picardDelta ≤ Cpicard * |g n| ^ 3
  failureProbability_cubic : ∀ n j,
    (blockData n j).failureProbability ≤ Cfailure * |g n| ^ 3
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

namespace FPUTProbabilisticFullStateBlockwiseMomentFamily

variable {Omega X : Type*} [MeasurableSpace Omega] [PseudoMetricSpace X]
  [MeasurableSpace X] [BorelSpace X]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  {M : Real}
  {N : Nat} [NeZero N]
  {m : Lattice.PositiveMassConfig N} {kappa beta T : Real}
  {observed : Lattice.Site N}
  {g : Nat → Real} {E : Nat → Nat → Real} {Q : Real → Real}
  {Cref Cstate Cpicard Cfailure : Real}
  {Ainitial Aflow : NNReal}

/-- Cubic second-moment coefficient at the initial endpoint, including the
bad-event contribution. -/
def initialCouplingConstant
    (_family : FPUTProbabilisticFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m kappa beta T observed g E Q
        Cref Cstate Cpicard Cfailure Ainitial Aflow) : Real :=
  2 * M * ((Ainitial : Real) * Cstate) + 2 * M ^ 2 * Cfailure

/-- Cubic second-moment coefficient at the propagated endpoint, including the
same block's bad-event contribution. -/
def finalCouplingConstant
    (_family : FPUTProbabilisticFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m kappa beta T observed g E Q
        Cref Cstate Cpicard Cfailure Ainitial Aflow) : Real :=
  2 * M * ((Aflow : Real) * Cstate + Cpicard) +
    2 * M ^ 2 * Cfailure

/-- One common cubic coefficient which controls both endpoints.  The sum is
slightly coarse but keeps every deterministic and probabilistic contribution
visible. -/
def couplingConstant
    (family : FPUTProbabilisticFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m kappa beta T observed g E Q
        Cref Cstate Cpicard Cfailure Ainitial Aflow) : Real :=
  family.initialCouplingConstant + family.finalCouplingConstant

theorem M_nonneg
    (family : FPUTProbabilisticFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m kappa beta T observed g E Q
        Cref Cstate Cpicard Cfailure Ainitial Aflow) :
    0 ≤ M :=
  (family.blockData 0 0).M_nonneg

theorem initialCouplingConstant_nonneg
    (family : FPUTProbabilisticFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m kappa beta T observed g E Q
        Cref Cstate Cpicard Cfailure Ainitial Aflow) :
    0 ≤ family.initialCouplingConstant := by
  unfold initialCouplingConstant
  exact add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) family.M_nonneg)
      (mul_nonneg Ainitial.coe_nonneg family.Cstate_nonneg))
    (mul_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg M)) family.Cfailure_nonneg)

theorem finalCouplingConstant_nonneg
    (family : FPUTProbabilisticFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m kappa beta T observed g E Q
        Cref Cstate Cpicard Cfailure Ainitial Aflow) :
    0 ≤ family.finalCouplingConstant := by
  unfold finalCouplingConstant
  exact add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) family.M_nonneg)
      (add_nonneg
        (mul_nonneg Aflow.coe_nonneg family.Cstate_nonneg)
        family.Cpicard_nonneg))
    (mul_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg M)) family.Cfailure_nonneg)

theorem couplingConstant_nonneg
    (family : FPUTProbabilisticFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m kappa beta T observed g E Q
        Cref Cstate Cpicard Cfailure Ainitial Aflow) :
    0 ≤ family.couplingConstant :=
  add_nonneg family.initialCouplingConstant_nonneg
    family.finalCouplingConstant_nonneg

/-- The per-block probability budget, retaining the block index instead of
silently replacing the probabilistic coupling by a uniform one. -/
theorem block_bad_probability_le_abs_cube
    (family : FPUTProbabilisticFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m kappa beta T observed g E Q
        Cref Cstate Cpicard Cfailure Ainitial Aflow)
    (n j : Nat) :
    mu.real (family.blockData n j).bad ≤ Cfailure * |g n| ^ 3 :=
  (family.blockData n j).bad_probability.trans
    (family.failureProbability_cubic n j)

/-- The initial probabilistic full-state RPA coupling implies the required
initial second-moment control, with the bad-event term included. -/
theorem initial_endpoint_control
    (family : FPUTProbabilisticFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m kappa beta T observed g E Q
        Cref Cstate Cpicard Cfailure Ainitial Aflow)
    (n j : Nat) :
    |E n j - canonicalHaarBlockInitial m (family.energy n j) observed| ≤
      family.couplingConstant * |g n| ^ 3 := by
  let data := family.blockData n j
  let certificate := data.toAmplitudeCouplingRestartCertificate
  have hmoment :
      |∫ z, Complex.normSq z ∂certificate.actualLaw 0 -
          ∫ z, Complex.normSq z ∂certificate.referenceLaw 0| ≤
        (2 * M * ((data.initialObservableAmplification : Real) * Cstate) +
          2 * M ^ 2 * Cfailure) * |g n| ^ 3 :=
    (data.endpoint_second_fourth_moment_errors_le_abs_cube
      (family.stateDelta_cubic n j) (family.picardDelta_cubic n j)
        (family.failureProbability_cubic n j)).1.1
  have hamp :
      (data.initialObservableAmplification : Real) * Cstate ≤
        (Ainitial : Real) * Cstate :=
    mul_le_mul_of_nonneg_right
      (by exact_mod_cast family.initialObservableAmplification_le n j)
      family.Cstate_nonneg
  have hcoefficient :
      2 * M * ((data.initialObservableAmplification : Real) * Cstate) +
          2 * M ^ 2 * Cfailure ≤ family.couplingConstant := by
    have hfirst :
        2 * M * ((data.initialObservableAmplification : Real) * Cstate) +
            2 * M ^ 2 * Cfailure ≤ family.initialCouplingConstant := by
      unfold initialCouplingConstant
      exact add_le_add
        (mul_le_mul_of_nonneg_left hamp
          (mul_nonneg (by norm_num) family.M_nonneg)) le_rfl
    exact hfirst.trans
      (le_add_of_nonneg_right family.finalCouplingConstant_nonneg)
  rw [family.actualInitialMoment n j,
    family.referenceInitialMoment n j] at hmoment
  exact hmoment.trans
    (mul_le_mul_of_nonneg_right hcoefficient
      (pow_nonneg (abs_nonneg _) _))

/-- The final second-moment control is derived from good-event state coupling,
Hamiltonian block Lipschitzness, deterministic second-Picard consistency, and
the explicit bad-event budget.  It is not a family input. -/
theorem final_endpoint_control
    (family : FPUTProbabilisticFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m kappa beta T observed g E Q
        Cref Cstate Cpicard Cfailure Ainitial Aflow)
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
        (2 * M *
            ((data.flowAmplification : Real) * Cstate + Cpicard) +
          2 * M ^ 2 * Cfailure) * |g n| ^ 3 :=
    (data.endpoint_second_fourth_moment_errors_le_abs_cube
      (family.stateDelta_cubic n j) (family.picardDelta_cubic n j)
        (family.failureProbability_cubic n j)).2.1
  have hamp :
      (data.flowAmplification : Real) * Cstate ≤
        (Aflow : Real) * Cstate :=
    mul_le_mul_of_nonneg_right
      (by exact_mod_cast family.flowAmplification_le n j)
      family.Cstate_nonneg
  have hcoefficient :
      2 * M * ((data.flowAmplification : Real) * Cstate + Cpicard) +
          2 * M ^ 2 * Cfailure ≤ family.couplingConstant := by
    have hfinal :
        2 * M * ((data.flowAmplification : Real) * Cstate + Cpicard) +
            2 * M ^ 2 * Cfailure ≤ family.finalCouplingConstant := by
      unfold finalCouplingConstant
      exact add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add hamp le_rfl)
          (mul_nonneg (by norm_num) family.M_nonneg)) le_rfl
    exact hfinal.trans
      (le_add_of_nonneg_left family.initialCouplingConstant_nonneg)
  rw [family.actualFinalMoment n j,
    family.referenceFinalMoment n j] at hmoment
  exact hmoment.trans
    (mul_le_mul_of_nonneg_right hcoefficient
      (pow_nonneg (abs_nonneg _) _))

/-- Forget the probability realization only after its bad-event moment costs
have been incorporated in both endpoint estimates.  This is the adapter into
the existing residual-free canonical-Haar chain. -/
def toCanonicalHaarBlockwiseMomentCertificate
    (family : FPUTProbabilisticFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m kappa beta T observed g E Q
        Cref Cstate Cpicard Cfailure Ainitial Aflow) :
    FPUTCanonicalHaarBlockwiseMomentCertificate
      m kappa beta T observed g E Q Cref family.couplingConstant where
  energy := family.energy
  couplingWindow := family.couplingWindow
  initial_endpoint_control := family.initial_endpoint_control
  final_endpoint_control := family.final_endpoint_control
  collision_compatibility := family.collision_compatibility
  finiteCharacterEnvelope := family.finiteCharacterEnvelope

/-- Adapter all the way to the existing blockwise residual certificate.  The
reference and actual residuals remain derived theorems. -/
def toBlockwiseReHaarizedMomentCertificate
    (family : FPUTProbabilisticFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m kappa beta T observed g E Q
        Cref Cstate Cpicard Cfailure Ainitial Aflow)
    (hT : 0 < T) (homega : 0 < modeFrequency m observed) :
    FPUTBlockwiseReHaarizedMomentCertificate
      g T E Q Cref family.couplingConstant :=
  family.toCanonicalHaarBlockwiseMomentCertificate
    |>.toBlockwiseReHaarizedMomentCertificate hT homega

/-- The actual scalar kinetic residual obtained from the probabilistic
full-state family.  It is a consequence, not a field. -/
theorem actual_is_momentKineticEulerResidual
    (family : FPUTProbabilisticFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m kappa beta T observed g E Q
        Cref Cstate Cpicard Cfailure Ainitial Aflow)
    (hT : 0 < T) (homega : 0 < modeFrequency m observed)
    {L : Real} (hL : 0 ≤ L)
    (hQ : ∀ x y, |Q x - Q y| ≤ L * |x - y|)
    (n j : Nat) :
    MomentKineticEulerResidual
      (E n j) (E n (j + 1)) (g n ^ 2 * T) (Q (E n j))
      (family.toBlockwiseReHaarizedMomentCertificate hT homega
        |>.actualResidualDefect L n) :=
  family.toBlockwiseReHaarizedMomentCertificate hT homega
    |>.actual_is_momentKineticEulerResidual hT.le hL hQ n j

/-- The existing scalar kinetic-time shadowing theorem applies after the
probabilistic endpoint costs have been absorbed into `couplingConstant`. -/
theorem actual_probabilisticFullState_kineticEuler_shadowing_tendsto_zero
    (family : FPUTProbabilisticFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m kappa beta T observed g E Q
        Cref Cstate Cpicard Cfailure Ainitial Aflow)
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
      hT homega family.couplingConstant_nonneg L hL hg hg0 V K tau hQ
        hkinetic hkineticBudget hinitial

/-! ## Finite-horizon joint bad event -/

/-- The event that at least one of the first `K` block couplings fails. -/
def firstKBad
    (family : FPUTProbabilisticFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m kappa beta T observed g E Q
        Cref Cstate Cpicard Cfailure Ainitial Aflow)
    (n K : Nat) : Set Omega :=
  ⋃ j ∈ Finset.range K, (family.blockData n j).bad

theorem firstKBad_measurable
    (family : FPUTProbabilisticFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m kappa beta T observed g E Q
        Cref Cstate Cpicard Cfailure Ainitial Aflow)
    (n K : Nat) : MeasurableSet (family.firstKBad n K) := by
  unfold firstKBad
  exact MeasurableSet.biUnion (Finset.countable_toSet _) fun j _ ↦
    (family.blockData n j).bad_measurable

/-- Outside the finite union, every one of the first `K` blockwise state
couplings is valid. -/
theorem initial_state_near_of_not_mem_firstKBad
    (family : FPUTProbabilisticFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m kappa beta T observed g E Q
        Cref Cstate Cpicard Cfailure Ainitial Aflow)
    {n K : Nat} {omega : Omega} (homega : omega ∉ family.firstKBad n K)
    {j : Nat} (hj : j < K) :
    dist ((family.blockData n j).actualInitial omega)
        ((family.blockData n j).referenceInitial omega) ≤
      (family.blockData n j).stateDelta := by
  apply (family.blockData n j).initial_state_near_on_good
  intro hbad
  apply homega
  unfold firstKBad
  exact Set.mem_iUnion_of_mem j
    (Set.mem_iUnion_of_mem (Finset.mem_range.mpr hj) hbad)

/-- Finite union bound with the individual per-block probability budget kept
visible. -/
theorem firstKBad_probability_le_abs_cube
    (family : FPUTProbabilisticFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m kappa beta T observed g E Q
        Cref Cstate Cpicard Cfailure Ainitial Aflow)
    (n K : Nat) :
    mu.real (family.firstKBad n K) ≤
      (K : Real) * Cfailure * |g n| ^ 3 := by
  unfold firstKBad
  calc
    mu.real (⋃ j ∈ Finset.range K, (family.blockData n j).bad) ≤
        ∑ j ∈ Finset.range K, mu.real (family.blockData n j).bad :=
      measureReal_biUnion_finset_le (Finset.range K)
        (fun j ↦ (family.blockData n j).bad)
    _ ≤ ∑ _j ∈ Finset.range K, Cfailure * |g n| ^ 3 := by
      exact Finset.sum_le_sum fun j _ ↦ family.block_bad_probability_le_abs_cube n j
    _ = (K : Real) * Cfailure * |g n| ^ 3 := by
      simp [Finset.card_range]
      ring

/-- Across an inverse-square kinetic window, the union-bound failure budget is
linear in `|g n|`. -/
theorem firstKBad_probability_le_kineticTime_linear
    (family : FPUTProbabilisticFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m kappa beta T observed g E Q
        Cref Cstate Cpicard Cfailure Ainitial Aflow)
    (hT : 0 < T) (n K : Nat) (tau : Real)
    (hbudget : (g n ^ 2 * T) * (K : Real) ≤ tau) :
    mu.real (family.firstKBad n K) ≤
      (tau / T) * Cfailure * |g n| := by
  have hblockBudget : (K : Real) * |g n| ^ 2 ≤ tau / T := by
    apply (le_div_iff₀ hT).2
    calc
      (K : Real) * |g n| ^ 2 * T =
          (g n ^ 2 * T) * (K : Real) := by rw [sq_abs]; ring
      _ ≤ tau := hbudget
  have hscale : 0 ≤ Cfailure * |g n| :=
    mul_nonneg family.Cfailure_nonneg (abs_nonneg _)
  calc
    mu.real (family.firstKBad n K) ≤
        (K : Real) * Cfailure * |g n| ^ 3 :=
      family.firstKBad_probability_le_abs_cube n K
    _ = ((K : Real) * |g n| ^ 2) * (Cfailure * |g n|) := by ring
    _ ≤ (tau / T) * (Cfailure * |g n|) :=
      mul_le_mul_of_nonneg_right hblockBudget hscale
    _ = (tau / T) * Cfailure * |g n| := by ring

end FPUTProbabilisticFullStateBlockwiseMomentFamily

end

end ArchonPhysics.PhyslibFPUTProbabilisticFullStateBlockwiseKineticShadowing
