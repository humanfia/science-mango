import ArchonPhysics.PhyslibFPUTProbabilisticEnergyProfileJointScaling

/-!
# Consumer: joint mode-count/block-count/coupling probability scaling

This consumer checks both the abstract varying-mode-count theorem and the
fixed-volume specialization of the probabilistic full-state energy-profile
adapter.  The varying-volume small parameter remains explicit.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTProbabilisticEnergyProfileJointScaling

open Filter
open Topology
open MeasureTheory
open ArchonPhysics
open ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing
open ArchonPhysics.PhyslibFPUTProbabilisticFullStateEnergyProfileAdapter
open ArchonPhysics.PhyslibFPUTProbabilisticEnergyProfileJointScaling
open FPUTProbabilisticFullStateEnergyProfileBlockwiseAdapter

noncomputable section

variable {badProbability : Nat → Real}
  {modeCount blockCount : Nat → Nat}
  {g : Nat → Real} {Cfailure : Real}

theorem problem_joint_failure_probability_epsilon
    (certificate : JointModeBlockFailureScalingCertificate
      badProbability modeCount blockCount g Cfailure)
    (n : Nat) {epsilon : Real}
    (hsmall :
      (modeCount n : Real) * (blockCount n : Real) *
          Cfailure * |g n| ^ 3 ≤ epsilon) :
    badProbability n ≤ epsilon :=
  certificate.badProbability_le_epsilon n hsmall

theorem problem_joint_failure_probability_tendsto
    (certificate : JointModeBlockFailureScalingCertificate
      badProbability modeCount blockCount g Cfailure)
    (hscale : Tendsto
      (fun n ↦ (modeCount n : Real) * (blockCount n : Real) *
        Cfailure * |g n| ^ 3) atTop (nhds 0)) :
    Tendsto badProbability atTop (nhds 0) :=
  certificate.badProbability_tendsto_zero_of_jointScale hscale

theorem problem_joint_failure_probability_kinetic_mode_bound
    (certificate : JointModeBlockFailureScalingCertificate
      badProbability modeCount blockCount g Cfailure)
    {T : Real} (hT : 0 < T) (n : Nat) (tau : Real)
    (hkineticBudget :
      (g n ^ 2 * T) * (blockCount n : Real) ≤ tau) :
    badProbability n ≤
      (modeCount n : Real) * (tau / T) * Cfailure * |g n| :=
  certificate.badProbability_le_kineticTime_modeCoupling
    hT n tau hkineticBudget

theorem problem_joint_failure_probability_kinetic_tendsto
    (certificate : JointModeBlockFailureScalingCertificate
      badProbability modeCount blockCount g Cfailure)
    {T tau : Real} (hT : 0 < T) (htau : 0 ≤ tau)
    (hkineticBudget : ∀ n,
      (g n ^ 2 * T) * (blockCount n : Real) ≤ tau)
    (hmodeCoupling : Tendsto
      (fun n ↦ (modeCount n : Real) * |g n|) atTop (nhds 0)) :
    Tendsto badProbability atTop (nhds 0) :=
  certificate.badProbability_tendsto_zero_of_kineticBudget
    hT htau hkineticBudget hmodeCoupling

variable {Omega X : Type*} [MeasurableSpace Omega]
  [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {mu : Measure Omega} [IsProbabilityMeasure mu] {M : Real}
  {N : Nat} [NeZero N]
  {m : Lattice.PositiveMassConfig N} {kappa beta T : Real}
  {E : Nat → Nat → PositiveEnergyProfile m}
  {Cref Ccoupling : Real}

theorem problem_profile_adapter_joint_scaling_certificate
    (adapter : FPUTProbabilisticFullStateEnergyProfileBlockwiseAdapter
      (Omega := Omega) (X := X) mu M m kappa beta T g E
        Cref Ccoupling Cfailure)
    (K : Nat → Nat) :
    JointModeBlockFailureScalingCertificate
      (fun n ↦ mu.real (adapter.firstKAllModesBad n (K n)))
      (fun _ ↦ Fintype.card (PositiveFrequencyMode m)) K g Cfailure :=
  toJointModeBlockFailureScalingCertificate adapter K

theorem problem_profile_adapter_joint_epsilon
    (adapter : FPUTProbabilisticFullStateEnergyProfileBlockwiseAdapter
      (Omega := Omega) (X := X) mu M m kappa beta T g E
        Cref Ccoupling Cfailure)
    (n K : Nat) (epsilon : Real)
    (hsmall :
      (Fintype.card (PositiveFrequencyMode m) : Real) * (K : Real) *
          Cfailure * |g n| ^ 3 ≤ epsilon) :
    mu.real (adapter.firstKAllModesBad n K) ≤ epsilon :=
  firstKAllModesBad_probability_le_epsilon adapter n K epsilon hsmall

theorem problem_profile_adapter_kinetic_mode_bound
    (adapter : FPUTProbabilisticFullStateEnergyProfileBlockwiseAdapter
      (Omega := Omega) (X := X) mu M m kappa beta T g E
        Cref Ccoupling Cfailure)
    (hT : 0 < T) (n K : Nat) (tau : Real)
    (hkineticBudget : (g n ^ 2 * T) * (K : Real) ≤ tau) :
    mu.real (adapter.firstKAllModesBad n K) ≤
      (Fintype.card (PositiveFrequencyMode m) : Real) *
        (tau / T) * Cfailure * |g n| :=
  firstKAllModesBad_probability_le_kineticTime_modeCoupling
    adapter hT n K tau hkineticBudget

theorem problem_profile_adapter_fixed_volume_tendsto
    (adapter : FPUTProbabilisticFullStateEnergyProfileBlockwiseAdapter
      (Omega := Omega) (X := X) mu M m kappa beta T g E
        Cref Ccoupling Cfailure)
    (K : Nat → Nat) {tau : Real} (hT : 0 < T) (htau : 0 ≤ tau)
    (hkineticBudget : ∀ n,
      (g n ^ 2 * T) * (K n : Real) ≤ tau)
    (hg : Tendsto g atTop (nhds 0)) :
    Tendsto (fun n ↦ mu.real (adapter.firstKAllModesBad n (K n)))
      atTop (nhds 0) :=
  firstKAllModesBad_probability_tendsto_zero_fixedVolume
    adapter K hT htau hkineticBudget hg

#print axioms problem_joint_failure_probability_epsilon
#print axioms problem_joint_failure_probability_tendsto
#print axioms problem_joint_failure_probability_kinetic_mode_bound
#print axioms problem_joint_failure_probability_kinetic_tendsto
#print axioms problem_profile_adapter_joint_scaling_certificate
#print axioms problem_profile_adapter_joint_epsilon
#print axioms problem_profile_adapter_kinetic_mode_bound
#print axioms problem_profile_adapter_fixed_volume_tendsto

end


end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTProbabilisticEnergyProfileJointScaling
