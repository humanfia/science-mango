import ArchonPhysics.PhyslibHamiltonDuhamel

/-!
# Exact two-time Duhamel formula for a Physlib Hamilton trajectory

`PhyslibHamiltonDuhamel` derives the exact interaction-picture formula from
time zero.  Kinetic-block and restart arguments need the corresponding
identity between arbitrary real times `t0` and `t1`.  This module obtains that
identity directly from the same concrete finite Hamilton equations and the
fundamental theorem of calculus.

The source remains the verified finite three-leg and four-leg tensor contraction.
Its interval integrability is discharged by differentiability of the physical
trajectory.  No kinetic equation, random-phase closure, collision kernel, or
limiting hypothesis occurs here.
-/

namespace ArchonPhysics.PhyslibHamiltonTwoTimeDuhamel

open Set
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.InteractionPictureDuhamel
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibHamiltonDuhamel

noncomputable section

/-- Exact interaction-picture Duhamel identity on an arbitrary oriented
interval `[t0, t1]` for one positive-frequency mode of a differentiable
trajectory satisfying the concrete coercive lattice Hamilton equations. -/
theorem interactionPicture_physlibMode_eq_base_add_integral
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (k : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (homega : 0 < modeFrequency m k) (t0 t1 : Real) :
    phaseRenormalize (modeFrequency m k * t1)
        (physlibModeAmplitude m k p q t1) =
      phaseRenormalize (modeFrequency m k * t0)
          (physlibModeAmplitude m k p q t0) +
        ∫ s in t0..t1, physlibModeRotatedSource m kappa beta g k q s := by
  have hDerivative : ∀ s ∈ uIcc t0 t1,
      HasDerivAt
        (fun tau ↦ phaseRenormalize (modeFrequency m k * tau)
          (physlibModeAmplitude m k p q tau))
        (physlibModeRotatedSource m kappa beta g k q s) s := by
    intro s _hs
    have hAmplitude := hasDerivAt_physlibModeAmplitude
      m kappa beta g k p q hp hq hHamilton homega s
    change HasDerivAt
      (fun tau ↦ phaseRenormalize (modeFrequency m k * tau)
        (physlibModeAmplitude m k p q tau))
      (phaseFactor (modeFrequency m k * s) *
        forcedModeSource (modeFrequency m k)
          (physlibModeTensorForce m kappa beta g k q s)) s
    exact hasDerivAt_interactionPicture
      (Omega := modeFrequency m k)
      (a := physlibModeAmplitude m k p q)
      (F := fun tau ↦ forcedModeSource (modeFrequency m k)
        (physlibModeTensorForce m kappa beta g k q tau))
      hAmplitude
  have hIntegrable : IntervalIntegrable
      (physlibModeRotatedSource m kappa beta g k q)
      MeasureTheory.volume t0 t1 :=
    intervalIntegrable_physlibModeRotatedSource
      m kappa beta g k q hq t0 t1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s ↦ phaseRenormalize (modeFrequency m k * s)
      (physlibModeAmplitude m k p q s))
    (f' := physlibModeRotatedSource m kappa beta g k q)
    hDerivative hIntegrable
  rw [hFTC]
  abel

/-- Equivalent Schrödinger-picture formula on the same arbitrary time
interval. -/
theorem physlibModeAmplitude_eq_inversePhase_base_add_integral
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (k : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (homega : 0 < modeFrequency m k) (t0 t1 : Real) :
    physlibModeAmplitude m k p q t1 =
      phaseRenormalize (-(modeFrequency m k * t1))
        (phaseRenormalize (modeFrequency m k * t0)
            (physlibModeAmplitude m k p q t0) +
          ∫ s in t0..t1,
            physlibModeRotatedSource m kappa beta g k q s) := by
  rw [← interactionPicture_physlibMode_eq_base_add_integral
    m kappa beta g k p q hp hq hHamilton homega t0 t1]
  simp

end

end ArchonPhysics.PhyslibHamiltonTwoTimeDuhamel
