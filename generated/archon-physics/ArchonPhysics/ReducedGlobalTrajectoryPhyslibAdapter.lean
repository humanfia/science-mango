import ArchonPhysics.CanonicalReducedParametricGlobalFlow
import ArchonPhysics.PhyslibHamiltonDerivativeBridge

/-!
# From a genuine reduced global trajectory to a Physlib Hamilton solution

The coercive global-existence modules construct real-parameter integral
curves in the translation-reduced phase space.  Physlib instead asks for two
curves on its one-dimensional `Time` space.  This file performs that change
of parameter and proves the actual `SatisfiesHamiltonEquations` predicate.

No solution certificate or additional equation is assumed: both Physlib
Hamilton equations are derived from the reduced integral-curve identity.
-/

namespace ArchonPhysics.ReducedGlobalTrajectoryPhyslibAdapter

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ConcreteHamiltonGradients
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open Time

noncomputable section

/-- Physical position path on Physlib's `Time`, obtained from a reduced
real-parameter trajectory. -/
def physlibPositionPathOfReducedTrajectory
    {N : Nat} [NeZero N] {m : Lattice.PositiveMassConfig N}
    (z : Real → ReducedPhaseSpace m) : Time → HilbertConfiguration N :=
  fun t ↦ ((z (Time.toRealCLE t)).1 : HilbertConfiguration N)

/-- Physical canonical-momentum path on Physlib's `Time`. -/
def physlibMomentumPathOfReducedTrajectory
    {N : Nat} [NeZero N] {m : Lattice.PositiveMassConfig N}
    (z : Real → ReducedPhaseSpace m) : Time → HilbertConfiguration N :=
  fun t ↦ ((z (Time.toRealCLE t)).2 : HilbertConfiguration N)

@[simp] theorem realReparametrize_physlibPositionPathOfReducedTrajectory
    {N : Nat} [NeZero N] {m : Lattice.PositiveMassConfig N}
    (z : Real → ReducedPhaseSpace m) (time : Real) :
    realReparametrize (physlibPositionPathOfReducedTrajectory z) time =
      ((z time).1 : HilbertConfiguration N) := by
  unfold realReparametrize physlibPositionPathOfReducedTrajectory
  rw [ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem realReparametrize_physlibMomentumPathOfReducedTrajectory
    {N : Nat} [NeZero N] {m : Lattice.PositiveMassConfig N}
    (z : Real → ReducedPhaseSpace m) (time : Real) :
    realReparametrize (physlibMomentumPathOfReducedTrajectory z) time =
      ((z time).2 : HilbertConfiguration N) := by
  unfold realReparametrize physlibMomentumPathOfReducedTrajectory
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- Differentiating after the canonical map `Time → Real` recovers the
original real derivative because the unit time vector has real coordinate
one. -/
theorem timeDeriv_comp_toRealCLE_eq
    {E : Type} [NormedAddCommGroup E] [NormedSpace Real E]
    (w : Real → E) (t : Time) (v : E)
    (hw : HasDerivAt w v (Time.toRealCLE t)) :
    Time.deriv (fun s : Time ↦ w (Time.toRealCLE s)) t = v := by
  have hcomp := hw.hasFDerivAt.comp t
    (Time.toRealCLE : Time →L[Real] Real).hasFDerivAt
  have hone : Time.toRealCLE (1 : Time) = (1 : Real) := by
    change (1 : Time).val = (1 : Real)
    exact Time.one_val
  have happ := congrArg
    (fun L : Time →L[Real] E ↦ L (1 : Time)) hcomp.fderiv
  simpa [Time.deriv_eq, Function.comp_def, hone] using happ

theorem hasDerivAt_reducedPosition_coe
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (kappa beta g : Real) {z : Real → ReducedPhaseSpace m} {time : Real}
    (hz : HasDerivAt z
      (reducedVectorField m kappa beta g (z time)) time) :
    HasDerivAt (fun s ↦ ((z s).1 : HilbertConfiguration N))
      ((reducedVelocity m (z time).2 : ReducedPositionSpace m) :
        HilbertConfiguration N) time := by
  have hqSub : HasDerivAt (fun s ↦ (z s).1)
      (reducedVelocity m (z time).2) time := by
    simpa [reducedVectorField] using hz.hasFDerivAt.fst.hasDerivAt
  exact (ReducedPositionSpace m).subtypeL.hasFDerivAt.comp_hasDerivAt
    time hqSub

theorem hasDerivAt_reducedMomentum_coe
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (kappa beta g : Real) {z : Real → ReducedPhaseSpace m} {time : Real}
    (hz : HasDerivAt z
      (reducedVectorField m kappa beta g (z time)) time) :
    HasDerivAt (fun s ↦ ((z s).2 : HilbertConfiguration N))
      ((-reducedPotentialGradient m kappa beta g (z time).1 :
          ReducedMomentumSpace N) : HilbertConfiguration N) time := by
  have hpSub : HasDerivAt (fun s ↦ (z s).2)
      (-reducedPotentialGradient m kappa beta g (z time).1) time := by
    simpa [reducedVectorField] using hz.hasFDerivAt.snd.hasDerivAt
  exact (ReducedMomentumSpace N).subtypeL.hasFDerivAt.comp_hasDerivAt
    time hpSub

theorem differentiable_physlibPositionPathOfReducedTrajectory
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (kappa beta g : Real) (z : Real → ReducedPhaseSpace m)
    (hz : ∀ time, HasDerivAt z
      (reducedVectorField m kappa beta g (z time)) time) :
    Differentiable Real (physlibPositionPathOfReducedTrajectory z) := by
  intro t
  exact ((hasDerivAt_reducedPosition_coe m kappa beta g
    (hz (Time.toRealCLE t))).hasFDerivAt.comp t
      (Time.toRealCLE : Time →L[Real] Real).hasFDerivAt).differentiableAt

theorem differentiable_physlibMomentumPathOfReducedTrajectory
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (kappa beta g : Real) (z : Real → ReducedPhaseSpace m)
    (hz : ∀ time, HasDerivAt z
      (reducedVectorField m kappa beta g (z time)) time) :
    Differentiable Real (physlibMomentumPathOfReducedTrajectory z) := by
  intro t
  exact ((hasDerivAt_reducedMomentum_coe m kappa beta g
    (hz (Time.toRealCLE t))).hasFDerivAt.comp t
      (Time.toRealCLE : Time →L[Real] Real).hasFDerivAt).differentiableAt

/-- A genuine reduced integral curve becomes a genuine Physlib Hamilton
solution, with no separately supplied solution predicate. -/
theorem satisfiesHamiltonEquations_physlibPathsOfReducedTrajectory
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (kappa beta g : Real) (z : Real → ReducedPhaseSpace m)
    (hz : ∀ time, HasDerivAt z
      (reducedVectorField m kappa beta g (z time)) time) :
    SatisfiesHamiltonEquations m kappa beta g
      (physlibMomentumPathOfReducedTrajectory z)
      (physlibPositionPathOfReducedTrajectory z) := by
  rw [satisfiesHamiltonEquations_iff_explicit]
  constructor
  · intro t
    have hderiv := timeDeriv_comp_toRealCLE_eq
      (fun time ↦ ((z time).1 : HilbertConfiguration N)) t
      ((reducedVelocity m (z (Time.toRealCLE t)).2 :
          ReducedPositionSpace m) : HilbertConfiguration N)
      (hasDerivAt_reducedPosition_coe m kappa beta g
        (hz (Time.toRealCLE t)))
    change Time.deriv
      (fun s : Time ↦ ((z (Time.toRealCLE s)).1 : HilbertConfiguration N)) t =
        inverseMassMomentum m
          ((z (Time.toRealCLE t)).2 : HilbertConfiguration N)
    simpa only [reducedVelocity_coe] using hderiv
  · intro t
    have hderiv := timeDeriv_comp_toRealCLE_eq
      (fun time ↦ ((z time).2 : HilbertConfiguration N)) t
      ((-reducedPotentialGradient m kappa beta g
          (z (Time.toRealCLE t)).1 : ReducedMomentumSpace N) :
        HilbertConfiguration N)
      (hasDerivAt_reducedMomentum_coe m kappa beta g
        (hz (Time.toRealCLE t)))
    change Time.deriv
      (fun s : Time ↦ ((z (Time.toRealCLE s)).2 : HilbertConfiguration N)) t =
        -potentialGradient kappa beta g
          ((z (Time.toRealCLE t)).1 : HilbertConfiguration N)
    calc
      Time.deriv
          (fun s : Time ↦
            ((z (Time.toRealCLE s)).2 : HilbertConfiguration N)) t =
          ((-reducedPotentialGradient m kappa beta g
              (z (Time.toRealCLE t)).1 : ReducedMomentumSpace N) :
            HilbertConfiguration N) := hderiv
      _ = -potentialGradient kappa beta g
          ((z (Time.toRealCLE t)).1 : HilbertConfiguration N) := by
        rw [Submodule.coe_neg, reducedPotentialGradient_coe]

/-- The reduced position subtype supplies the physical mass gauge after the
canonical real reparametrization. -/
theorem massGauge_realReparametrize_physlibPositionPath
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (z : Real → ReducedPhaseSpace m) (time : Real) :
    ∑ i, m.mass i *
        asConfiguration
          (realReparametrize
            (physlibPositionPathOfReducedTrajectory z) time) i = 0 := by
  rw [realReparametrize_physlibPositionPathOfReducedTrajectory]
  simpa [asConfiguration] using
    (mem_reducedPositionSpace_iff m
      ((z time).1 : HilbertConfiguration N)).1 (z time).1.property

/-- The physical Hamiltonian of the lifted paths is definitionally the
reduced Hamiltonian at the same real time. -/
theorem hamiltonian_realReparametrize_physlibPaths_eq_reducedHamiltonian
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (kappa beta g : Real) (z : Real → ReducedPhaseSpace m) (time : Real) :
    CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration
          (realReparametrize
            (physlibMomentumPathOfReducedTrajectory z) time))
        (asConfiguration
          (realReparametrize
            (physlibPositionPathOfReducedTrajectory z) time)) =
      reducedHamiltonian m kappa beta g (z time) := by
  rw [realReparametrize_physlibMomentumPathOfReducedTrajectory,
    realReparametrize_physlibPositionPathOfReducedTrajectory]
  rfl

end

end ArchonPhysics.ReducedGlobalTrajectoryPhyslibAdapter
