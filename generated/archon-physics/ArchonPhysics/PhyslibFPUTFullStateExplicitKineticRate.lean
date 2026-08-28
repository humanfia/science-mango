import ArchonPhysics.PhyslibFPUTFullStateBlockwiseKineticShadowing

/-!
# Explicit inverse-square kinetic-time rate for full-state FPUT blocks

This module turns the finite-block full-state shadowing inequality into a
single quantitative estimate on a kinetic window.  The one-block defect is
`O(|g|^3)`, while at most `O(|g|^-2)` blocks fit below a fixed kinetic-time
budget.  Their accumulated contribution is therefore explicitly `O(|g|)`.
-/

namespace ArchonPhysics.PhyslibFPUTFullStateBlockwiseKineticShadowing

open MeasureTheory
open ArchonPhysics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTFullStateBlockwiseKineticShadowing
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing

noncomputable section

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

/-- The transparent coefficient multiplying the cubic one-block defect. -/
def kineticTimeCubicConstant
    (family : FPUTFullStateBlockwiseMomentFamily (Omega := Omega) (X := X)
      mu M m kappa beta T observed g E Q Cref Cstate Cpicard
        Ainitial Aflow)
    (L : Real) : Real :=
  Cref + (2 + T * L) * family.couplingConstant

theorem kineticTimeCubicConstant_nonneg
    (family : FPUTFullStateBlockwiseMomentFamily (Omega := Omega) (X := X)
      mu M m kappa beta T observed g E Q Cref Cstate Cpicard
        Ainitial Aflow)
    (hT : 0 ≤ T) (L : Real) (hL : 0 ≤ L) :
    0 ≤ family.kineticTimeCubicConstant L := by
  unfold kineticTimeCubicConstant
  have hCref : 0 ≤ Cref :=
    family.toCanonicalHaarBlockwiseMomentCertificate.Cref_nonneg
  have hfactor : 0 ≤ 2 + T * L :=
    add_nonneg (by norm_num) (mul_nonneg hT hL)
  exact add_nonneg hCref
    (mul_nonneg hfactor family.couplingConstant_nonneg)

/-- On the weak-coupling window `|g| ≤ 1`, the fully expanded actual
one-block residual has a uniform cubic envelope. -/
theorem explicitActualResidualDefect_le_abs_cube
    (family : FPUTFullStateBlockwiseMomentFamily (Omega := Omega) (X := X)
      mu M m kappa beta T observed g E Q Cref Cstate Cpicard
        Ainitial Aflow)
    (hT : 0 ≤ T) (L : Real) (hL : 0 ≤ L)
    (n : Nat) (hg : |g n| ≤ 1) :
    family.explicitActualResidualDefect L n ≤
      family.kineticTimeCubicConstant L * |g n| ^ 3 := by
  have hgsqAbs : |g n| ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (1 - |g n|), abs_nonneg (g n)]
  have hgsq : g n ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using hgsqAbs
  have hgsqT : g n ^ 2 * T ≤ T := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hgsq hT
  have hgsqTL : (g n ^ 2 * T) * L ≤ T * L :=
    mul_le_mul_of_nonneg_right hgsqT hL
  have hfactor : 1 + (g n ^ 2 * T) * L ≤ 1 + T * L :=
    by linarith
  have hcouplingCube :
      0 ≤ family.couplingConstant * |g n| ^ 3 :=
    mul_nonneg family.couplingConstant_nonneg
      (pow_nonneg (abs_nonneg _) _)
  unfold explicitActualResidualDefect kineticTimeCubicConstant
  calc
    Cref * |g n| ^ 3 + family.couplingConstant * |g n| ^ 3 +
          (1 + (g n ^ 2 * T) * L) *
            (family.couplingConstant * |g n| ^ 3)
        ≤ Cref * |g n| ^ 3 + family.couplingConstant * |g n| ^ 3 +
          (1 + T * L) * (family.couplingConstant * |g n| ^ 3) :=
      add_le_add_right
        (mul_le_mul_of_nonneg_right hfactor hcouplingCube) _
    _ = (Cref + (2 + T * L) * family.couplingConstant) *
          |g n| ^ 3 := by ring

/-- At most inverse-square many cubic block defects accumulate to a linear
weak-coupling error under a fixed kinetic-time budget. -/
theorem cumulative_defect_le_kineticTime_linear
    (family : FPUTFullStateBlockwiseMomentFamily (Omega := Omega) (X := X)
      mu M m kappa beta T observed g E Q Cref Cstate Cpicard
        Ainitial Aflow)
    (hT : 0 < T) (L : Real) (hL : 0 ≤ L)
    (n K : Nat) (hg : |g n| ≤ 1)
    (tau : Real) (hbudget :
      (g n ^ 2 * T) * (K : Real) ≤ tau) :
    (K : Real) * family.explicitActualResidualDefect L n ≤
      (tau / T) * family.kineticTimeCubicConstant L * |g n| := by
  have hdefect := family.explicitActualResidualDefect_le_abs_cube
    hT.le L hL n hg
  have hK : 0 ≤ (K : Real) := Nat.cast_nonneg K
  have hdefectSum :
      (K : Real) * family.explicitActualResidualDefect L n ≤
        (K : Real) *
          (family.kineticTimeCubicConstant L * |g n| ^ 3) :=
    mul_le_mul_of_nonneg_left hdefect hK
  have hbudgetAbs :
      (|g n| ^ 2 * T) * (K : Real) ≤ tau := by
    simpa only [sq_abs] using hbudget
  have hblockBudget :
      (K : Real) * |g n| ^ 2 ≤ tau / T := by
    apply (le_div_iff₀ hT).2
    calc
      (K : Real) * |g n| ^ 2 * T =
          (|g n| ^ 2 * T) * (K : Real) := by ring
      _ ≤ tau := hbudgetAbs
  have hC : 0 ≤ family.kineticTimeCubicConstant L :=
    family.kineticTimeCubicConstant_nonneg hT.le L hL
  have hscale : 0 ≤ family.kineticTimeCubicConstant L * |g n| :=
    mul_nonneg hC (abs_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_right hblockBudget hscale
  calc
    (K : Real) * family.explicitActualResidualDefect L n ≤
        (K : Real) *
          (family.kineticTimeCubicConstant L * |g n| ^ 3) := hdefectSum
    _ = ((K : Real) * |g n| ^ 2) *
          (family.kineticTimeCubicConstant L * |g n|) := by ring
    _ ≤ (tau / T) *
          (family.kineticTimeCubicConstant L * |g n|) := hscaled
    _ = (tau / T) * family.kineticTimeCubicConstant L * |g n| := by ring

/-- Concrete finite-time Fermi-golden-rule estimate: on the window
`g^2 T K ≤ tau`, the accumulated microscopic error is `O(|g|)` and the
stability multiplier is at most `exp (L tau)`. -/
theorem actual_fullState_kineticTime_explicit_linear_bound
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
        Real.exp (L * tau) := by
  have hbase := family.actual_fullState_kineticEuler_shadowing_uniform_bound
    hT homega L hL hQ n V hkinetic K
  have hsum := family.cumulative_defect_le_kineticTime_linear
    hT L hL n K hg tau hbudget
  have hprefactor :
      |E n 0 - V 0| +
          (K : Real) * family.explicitActualResidualDefect L n ≤
        |E n 0 - V 0| +
          (tau / T) * family.kineticTimeCubicConstant L * |g n| :=
    add_le_add_right hsum _
  have hexponent :
      L * (g n ^ 2 * T) * (K : Real) ≤ L * tau := by
    calc
      L * (g n ^ 2 * T) * (K : Real) =
          L * ((g n ^ 2 * T) * (K : Real)) := by ring
      _ ≤ L * tau := mul_le_mul_of_nonneg_left hbudget hL
  have hexp :
      Real.exp (L * (g n ^ 2 * T) * (K : Real)) ≤
        Real.exp (L * tau) :=
    Real.exp_le_exp.mpr hexponent
  have htau : 0 ≤ tau := by
    exact (mul_nonneg
      (mul_nonneg (sq_nonneg _) hT.le) (Nat.cast_nonneg K)).trans hbudget
  have htargetPrefactor :
      0 ≤ |E n 0 - V 0| +
          (tau / T) * family.kineticTimeCubicConstant L * |g n| := by
    exact add_nonneg (abs_nonneg _)
      (mul_nonneg
        (mul_nonneg (div_nonneg htau hT.le)
          (family.kineticTimeCubicConstant_nonneg hT.le L hL))
        (abs_nonneg _))
  calc
    |E n K - V K| ≤
        (|E n 0 - V 0| +
            (K : Real) * family.explicitActualResidualDefect L n) *
          Real.exp (L * (g n ^ 2 * T) * (K : Real)) := hbase
    _ ≤ (|E n 0 - V 0| +
            (tau / T) * family.kineticTimeCubicConstant L * |g n|) *
          Real.exp (L * (g n ^ 2 * T) * (K : Real)) :=
      mul_le_mul_of_nonneg_right hprefactor (Real.exp_nonneg _)
    _ ≤ (|E n 0 - V 0| +
            (tau / T) * family.kineticTimeCubicConstant L * |g n|) *
          Real.exp (L * tau) :=
      mul_le_mul_of_nonneg_left hexp htargetPrefactor

end FPUTFullStateBlockwiseMomentFamily

end

end ArchonPhysics.PhyslibFPUTFullStateBlockwiseKineticShadowing
