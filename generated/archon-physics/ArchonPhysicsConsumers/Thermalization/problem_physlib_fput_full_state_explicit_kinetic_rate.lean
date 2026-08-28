import ArchonPhysics.PhyslibFPUTFullStateExplicitKineticRate

/-!
# Consumer: explicit inverse-square FPUT kinetic-time rate

This gate locks the quantitative consequence of the full-state restart
certificate: cubic error per block, inverse-square many blocks, hence a
linear-in-`|g|` accumulated error below fixed kinetic time.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTFullStateExplicitKineticRate

open MeasureTheory
open ArchonPhysics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTFullStateBlockwiseKineticShadowing
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing

noncomputable section

#check FPUTFullStateBlockwiseMomentFamily.kineticTimeCubicConstant
#check FPUTFullStateBlockwiseMomentFamily.kineticTimeCubicConstant_nonneg
#check FPUTFullStateBlockwiseMomentFamily.explicitActualResidualDefect_le_abs_cube
#check FPUTFullStateBlockwiseMomentFamily.cumulative_defect_le_kineticTime_linear
#check FPUTFullStateBlockwiseMomentFamily.actual_fullState_kineticTime_explicit_linear_bound

/-- Consumer-facing Fermi-golden-rule window: `g^2 T K ≤ tau` converts the
derived cubic one-block defect into an explicit linear-in-`|g|` error. -/
theorem full_state_inverse_square_kinetic_window_contract
    {Omega X : Type*} [MeasurableSpace Omega] [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {M : Real}
    {N : Nat} [NeZero N]
    {m : Lattice.PositiveMassConfig N} {kappa beta T : Real}
    {observed : Lattice.Site N}
    {g : Nat → Real} {E : Nat → Nat → Real} {Q : Real → Real}
    {Cref Cstate Cpicard : Real} {Ainitial Aflow : NNReal}
    (family : FPUTFullStateBlockwiseMomentFamily (Omega := Omega) (X := X)
      mu M m kappa beta T observed g E Q Cref Cstate Cpicard
        Ainitial Aflow)
    (hT : 0 < T) (homega : 0 < modeFrequency m observed)
    (L : Real) (hL : 0 ≤ L)
    (hQ : ∀ x y, |Q x - Q y| ≤ L * |x - y|)
    (n : Nat) (hg : |g n| ≤ 1)
    (V : Nat → Real)
    (hkinetic : IsKineticEulerTrajectory V (g n ^ 2 * T) Q)
    (K : Nat) (tau : Real)
    (hbudget : (g n ^ 2 * T) * (K : Real) ≤ tau) :
    |E n K - V K| ≤
      (|E n 0 - V 0| +
          (tau / T) * family.kineticTimeCubicConstant L * |g n|) *
        Real.exp (L * tau) :=
  family.actual_fullState_kineticTime_explicit_linear_bound
    hT homega L hL hQ n hg V hkinetic K tau hbudget

#print axioms FPUTFullStateBlockwiseMomentFamily.kineticTimeCubicConstant_nonneg
#print axioms FPUTFullStateBlockwiseMomentFamily.explicitActualResidualDefect_le_abs_cube
#print axioms FPUTFullStateBlockwiseMomentFamily.cumulative_defect_le_kineticTime_linear
#print axioms FPUTFullStateBlockwiseMomentFamily.actual_fullState_kineticTime_explicit_linear_bound
#print axioms full_state_inverse_square_kinetic_window_contract

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTFullStateExplicitKineticRate
