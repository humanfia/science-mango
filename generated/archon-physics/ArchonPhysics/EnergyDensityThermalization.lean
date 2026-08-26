import ArchonPhysics.HamiltonianScaling
import ArchonPhysics.ThermalizationTransfer

/-!
# Energy-density form of the kinetic thermalization window

This module is an algebraic transfer layer.  It rewrites the already-defined
`g² T_eq` window using the effective coupling
`g = λ ε^((n - 2) / 2)`.  It does not assert a microscopic thermalization law;
the probabilistic corollary consumes an existing `HighProbabilityG2Bounds`
certificate.

All hitting times and window endpoints remain in `ENNReal`.  Consequently an
infinite equilibration time is never converted to the real number zero.
-/

namespace ArchonPhysics.EnergyDensityThermalization

open Filter MeasureTheory Set Topology
open scoped ENNReal
open ArchonPhysics.HamiltonianScaling
open ArchonPhysics.ThermalizationTransfer

noncomputable section

/-- The energy-density expression for the inverse square effective coupling. -/
def inverseSquareEnergyScale (lambda epsilon : Real) (n : Nat) : ENNReal :=
  ENNReal.ofReal
    (lambda⁻¹ ^ 2 * epsilon ^ (-((n - 2 : Nat) : Int)))

/-- A positive energy density and nonzero bare coupling give nonzero effective coupling. -/
theorem effectiveCoupling_ne_zero (lambda epsilon : Real) (n : Nat)
    (hepsilon : 0 < epsilon) (hlambda : lambda ≠ 0) :
    effectiveCoupling lambda epsilon n ≠ 0 := by
  exact mul_ne_zero hlambda
    (ne_of_gt (Real.rpow_pos_of_pos hepsilon (((n : Real) - 2) / 2)))

/-- The verified real inverse-square law, embedded losslessly into `ENNReal`. -/
theorem inv_ofReal_effectiveCoupling_sq_eq_inverseSquareEnergyScale
    (lambda epsilon : Real) (n : Nat) (hn : 3 ≤ n)
    (hepsilon : 0 < epsilon) (hlambda : lambda ≠ 0) :
    (ENNReal.ofReal ((effectiveCoupling lambda epsilon n) ^ 2))⁻¹ =
      inverseSquareEnergyScale lambda epsilon n := by
  have hg : effectiveCoupling lambda epsilon n ≠ 0 :=
    effectiveCoupling_ne_zero lambda epsilon n hepsilon hlambda
  have hg_sq_pos : 0 < (effectiveCoupling lambda epsilon n) ^ 2 :=
    sq_pos_of_ne_zero hg
  calc
    (ENNReal.ofReal ((effectiveCoupling lambda epsilon n) ^ 2))⁻¹ =
        ENNReal.ofReal (((effectiveCoupling lambda epsilon n) ^ 2)⁻¹) :=
      (ENNReal.ofReal_inv_of_pos hg_sq_pos).symm
    _ = ENNReal.ofReal ((effectiveCoupling lambda epsilon n)⁻¹ ^ 2) := by
      rw [inv_pow]
    _ = inverseSquareEnergyScale lambda epsilon n := by
      rw [effectiveCoupling_inv_sq lambda epsilon n hn hepsilon hlambda]
      rfl

/--
The two-sided window for the unscaled hitting time after substituting the
energy-dependent coupling.  Multiplication is in `ENNReal`, so `T_eq = ⊤`
retains its extended-real meaning.
-/
def energyDensityWindowEvent {Omega : Type*}
    (equilibrationTime : Nat → Real → Omega → ENNReal)
    (lower upper : Real) (N : Nat) (lambda epsilon : Real) (n : Nat) :
    Set Omega :=
  equilibrationTime N (effectiveCoupling lambda epsilon n) ⁻¹'
    Icc
      (inverseSquareEnergyScale lambda epsilon n * ENNReal.ofReal lower)
      (inverseSquareEnergyScale lambda epsilon n * ENNReal.ofReal upper)

/-- The energy-density window is measurable whenever the hitting time is measurable. -/
theorem measurableSet_energyDensityWindowEvent {Omega : Type*}
    [MeasurableSpace Omega]
    (equilibrationTime : Nat → Real → Omega → ENNReal)
    (lower upper : Real) (N : Nat) (lambda epsilon : Real) (n : Nat)
    (hT : Measurable
      (equilibrationTime N (effectiveCoupling lambda epsilon n))) :
    MeasurableSet (energyDensityWindowEvent equilibrationTime lower upper
      N lambda epsilon n) := by
  exact measurableSet_Icc.preimage hT

/--
At positive energy density, nonzero bare coupling, and degree at least three,
the `g² T_eq` window is exactly the corresponding inverse-square
energy-density window for `T_eq`.
-/
theorem scalingWindowEvent_effectiveCoupling_eq_energyDensityWindowEvent
    {Omega : Type*}
    (equilibrationTime : Nat → Real → Omega → ENNReal)
    (lower upper : Real) (N : Nat) (lambda epsilon : Real) (n : Nat)
    (hn : 3 ≤ n) (hepsilon : 0 < epsilon) (hlambda : lambda ≠ 0) :
    scalingWindowEvent equilibrationTime lower upper N
        (effectiveCoupling lambda epsilon n) =
      energyDensityWindowEvent equilibrationTime lower upper N
        lambda epsilon n := by
  have hg : effectiveCoupling lambda epsilon n ≠ 0 :=
    effectiveCoupling_ne_zero lambda epsilon n hepsilon hlambda
  have hfactor_ne_zero :
      ENNReal.ofReal ((effectiveCoupling lambda epsilon n) ^ 2) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_ne_zero hg)
  have hfactor_ne_top :
      ENNReal.ofReal ((effectiveCoupling lambda epsilon n) ^ 2) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hscale :
      (ENNReal.ofReal ((effectiveCoupling lambda epsilon n) ^ 2))⁻¹ =
        inverseSquareEnergyScale lambda epsilon n :=
    inv_ofReal_effectiveCoupling_sq_eq_inverseSquareEnergyScale
      lambda epsilon n hn hepsilon hlambda
  ext omega
  change
    (ENNReal.ofReal lower ≤
          ENNReal.ofReal ((effectiveCoupling lambda epsilon n) ^ 2) *
            equilibrationTime N (effectiveCoupling lambda epsilon n) omega ∧
        ENNReal.ofReal ((effectiveCoupling lambda epsilon n) ^ 2) *
            equilibrationTime N (effectiveCoupling lambda epsilon n) omega ≤
          ENNReal.ofReal upper) ↔
      (inverseSquareEnergyScale lambda epsilon n * ENNReal.ofReal lower ≤
          equilibrationTime N (effectiveCoupling lambda epsilon n) omega ∧
        equilibrationTime N (effectiveCoupling lambda epsilon n) omega ≤
          inverseSquareEnergyScale lambda epsilon n * ENNReal.ofReal upper)
  constructor
  · rintro ⟨hlower, hupper⟩
    constructor
    · rw [← hscale]
      exact (ENNReal.inv_mul_le_iff hfactor_ne_zero hfactor_ne_top).2 hlower
    · rw [← hscale]
      exact (ENNReal.mul_le_iff_le_inv hfactor_ne_zero hfactor_ne_top).1 hupper
  · rintro ⟨hlower, hupper⟩
    rw [← hscale] at hlower hupper
    exact ⟨(ENNReal.inv_mul_le_iff hfactor_ne_zero hfactor_ne_top).1 hlower,
      (ENNReal.mul_le_iff_le_inv hfactor_ne_zero hfactor_ne_top).2 hupper⟩

/-- Effective-coupling scaling preserves an infinite equilibration time. -/
theorem scaledEquilibrationTime_effectiveCoupling_eq_top_iff
    {Omega : Type*}
    (equilibrationTime : Nat → Real → Omega → ENNReal)
    (N : Nat) (lambda epsilon : Real) (n : Nat) (omega : Omega)
    (hepsilon : 0 < epsilon) (hlambda : lambda ≠ 0) :
    scaledEquilibrationTime equilibrationTime N
        (effectiveCoupling lambda epsilon n) omega = ⊤ ↔
      equilibrationTime N (effectiveCoupling lambda epsilon n) omega = ⊤ := by
  exact scaledEquilibrationTime_eq_top_iff equilibrationTime N
    (effectiveCoupling lambda epsilon n) omega
    (effectiveCoupling_ne_zero lambda epsilon n hepsilon hlambda)

/--
Conditional energy-density corollary of an already established high-probability
`g⁻²` law.  The hypothesis `hcoupling` identifies the admitted weak-coupling
path with the effective coupling of the supplied positive energy-density path.
-/
theorem HighProbabilityG2Bounds.energyDensity_corollary
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P]
    (equilibrationTime : Nat → Real → Omega → ENNReal)
    (sizeCutoff : Real → Nat) (lower upper : Real)
    (h : HighProbabilityG2Bounds P equilibrationTime sizeCutoff lower upper)
    (lambda : Real) (n : Nat) (hn : 3 ≤ n) (hlambda : lambda ≠ 0)
    (s : AdmissibleJointLimit sizeCutoff) (epsilon : Nat → Real)
    (hepsilon : ∀ j, 0 < epsilon j)
    (hcoupling : ∀ j,
      s.coupling j = effectiveCoupling lambda (epsilon j) n) :
    Tendsto
      (fun j => P (energyDensityWindowEvent equilibrationTime lower upper
        (s.systemSize j) lambda (epsilon j) n))
      atTop (nhds 1) := by
  have hevent (j : Nat) :
      scalingWindowEvent equilibrationTime lower upper
          (s.systemSize j) (s.coupling j) =
        energyDensityWindowEvent equilibrationTime lower upper
          (s.systemSize j) lambda (epsilon j) n := by
    rw [hcoupling j]
    exact scalingWindowEvent_effectiveCoupling_eq_energyDensityWindowEvent
      equilibrationTime lower upper (s.systemSize j) lambda (epsilon j) n
      hn (hepsilon j) hlambda
  simpa only [hevent] using h.law s

end

end ArchonPhysics.EnergyDensityThermalization
