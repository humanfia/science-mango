import ArchonPhysics.PhyslibFPUTProbabilisticFullStateBlockwiseKineticShadowing

/-!
# Consumer: probabilistic full-state blockwise FPUT shadowing

This consumer checks the family adapter from per-block probabilistic RPA
certificates to the existing canonical-Haar residual and kinetic-shadowing
chain.  It also checks the finite-horizon union bound and its `O(|g|)` kinetic
window specialization.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTProbabilisticFullStateBlockwiseKineticShadowing

open Filter
open Topology
open MeasureTheory
open ArchonPhysics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTBlockwiseReHaarizedKineticShadowing
open ArchonPhysics.PhyslibFPUTDerivedReferenceBlockwiseKineticShadowing
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing
open ArchonPhysics.PhyslibFPUTProbabilisticFullStateBlockwiseKineticShadowing

noncomputable section

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

def problem_probabilistic_full_state_blockwise_moment_adapter
    (family : FPUTProbabilisticFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m kappa beta T observed g E Q
        Cref Cstate Cpicard Cfailure Ainitial Aflow) :
    FPUTCanonicalHaarBlockwiseMomentCertificate
      m kappa beta T observed g E Q Cref family.couplingConstant :=
  family.toCanonicalHaarBlockwiseMomentCertificate

theorem problem_probabilistic_full_state_blockwise_endpoint_controls
    (family : FPUTProbabilisticFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m kappa beta T observed g E Q
        Cref Cstate Cpicard Cfailure Ainitial Aflow)
    (n j : Nat) :
    (|E n j - canonicalHaarBlockInitial m (family.energy n j) observed| ≤
      family.couplingConstant * |g n| ^ 3) ∧
    (|E n (j + 1) -
        canonicalHaarBlockFinal m kappa beta (g n)
          (family.energy n j) T observed| ≤
      family.couplingConstant * |g n| ^ 3) :=
  ⟨family.initial_endpoint_control n j,
    family.final_endpoint_control n j⟩

theorem problem_probabilistic_full_state_block_bad_probability
    (family : FPUTProbabilisticFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m kappa beta T observed g E Q
        Cref Cstate Cpicard Cfailure Ainitial Aflow)
    (n j : Nat) :
    mu.real (family.blockData n j).bad ≤ Cfailure * |g n| ^ 3 :=
  family.block_bad_probability_le_abs_cube n j

theorem problem_probabilistic_full_state_blockwise_actual_residual
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
  family.actual_is_momentKineticEulerResidual hT homega hL hQ n j

theorem problem_probabilistic_full_state_blockwise_kinetic_shadowing
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
      atTop (nhds 0) :=
  family.actual_probabilisticFullState_kineticEuler_shadowing_tendsto_zero
    hT homega L hL hg hg0 V K tau hQ hkinetic hkineticBudget hinitial

theorem problem_probabilistic_full_state_firstK_union_bound
    (family : FPUTProbabilisticFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m kappa beta T observed g E Q
        Cref Cstate Cpicard Cfailure Ainitial Aflow)
    (n K : Nat) :
    MeasurableSet (family.firstKBad n K) ∧
    mu.real (family.firstKBad n K) ≤
      (K : Real) * Cfailure * |g n| ^ 3 :=
  ⟨family.firstKBad_measurable n K,
    family.firstKBad_probability_le_abs_cube n K⟩

theorem problem_probabilistic_full_state_kinetic_window_union_bound
    (family : FPUTProbabilisticFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m kappa beta T observed g E Q
        Cref Cstate Cpicard Cfailure Ainitial Aflow)
    (hT : 0 < T) (n K : Nat) (tau : Real)
    (hbudget : (g n ^ 2 * T) * (K : Real) ≤ tau) :
    mu.real (family.firstKBad n K) ≤
      (tau / T) * Cfailure * |g n| :=
  family.firstKBad_probability_le_kineticTime_linear
    hT n K tau hbudget

#print axioms problem_probabilistic_full_state_blockwise_moment_adapter
#print axioms problem_probabilistic_full_state_blockwise_endpoint_controls
#print axioms problem_probabilistic_full_state_block_bad_probability
#print axioms problem_probabilistic_full_state_blockwise_actual_residual
#print axioms problem_probabilistic_full_state_blockwise_kinetic_shadowing
#print axioms problem_probabilistic_full_state_firstK_union_bound
#print axioms problem_probabilistic_full_state_kinetic_window_union_bound

end


end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTProbabilisticFullStateBlockwiseKineticShadowing
