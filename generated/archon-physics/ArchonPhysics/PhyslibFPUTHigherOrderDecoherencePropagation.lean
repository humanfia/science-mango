import ArchonPhysics.PhyslibFPUTCoercivePositiveTimeCumulantHierarchy
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Quantitative propagation criterion for higher-order FPUT decoherence

Pairwise phase decorrelation is not a random-phase approximation.  The
relevant objects at arbitrary fixed order are the mixed connected cumulants.
The full coercive alpha-beta Hamiltonian gives an exact evolution equation
for every such cumulant; this file converts a quantitative bound on that
exact hierarchy source into a quantitative bound on the cumulant itself.

If a connected cumulant vanishes initially and its exact source is bounded
by `epsilon` on the segment from `0` to `time`, then its norm at `time` is at
most `epsilon * |time|`.  Consequently, on a sequence of kinetic scales,
`epsilon_N * |time_N| -> 0` is a sufficient fixed-order decoherence
criterion.

The source bound is deliberately an explicit premise.  Establishing it for
the nonresonant high-order garden while separately controlling recollisions
and retaining charge-balanced/resonant clusters is the research-level
microscopic step.  Nothing here assumes re-Haarization, a Markov process, or
the kinetic equation.
-/

namespace ArchonPhysics.PhyslibFPUTHigherOrderDecoherencePropagation

open Filter
open Topology

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTCoercivePositiveTimeCumulantHierarchy
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy

noncomputable section

/-! ## Abstract derivative-to-decoherence estimate -/

/-- A uniform bound on the exact cumulant source controls the change of the
connected cumulant on the whole (positive or negative) time segment. -/
theorem norm_connectedCumulant_sub_zero_le_of_source_bound
    (cumulant source : Real → Complex) (time epsilon : Real)
    (hderiv : ∀ s ∈ Set.uIcc 0 time,
      HasDerivAt cumulant (source s) s)
    (hsource : ∀ s ∈ Set.uIcc 0 time, ‖source s‖ ≤ epsilon) :
    ‖cumulant time - cumulant 0‖ ≤ epsilon * |time| := by
  have hwithin : ∀ s ∈ Set.uIcc 0 time,
      HasDerivWithinAt cumulant (source s) (Set.uIcc 0 time) s := by
    intro s hs
    exact (hderiv s hs).hasDerivWithinAt
  have hbound :=
    (convex_uIcc 0 time).norm_image_sub_le_of_norm_hasDerivWithin_le
      hwithin hsource Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [Real.norm_eq_abs] using hbound

/-- If the selected connected sector vanishes initially, the same source
bound is an explicit quantitative approximate-RPA estimate at that order. -/
theorem norm_connectedCumulant_le_of_initial_eq_zero
    (cumulant source : Real → Complex) (time epsilon : Real)
    (hzero : cumulant 0 = 0)
    (hderiv : ∀ s ∈ Set.uIcc 0 time,
      HasDerivAt cumulant (source s) s)
    (hsource : ∀ s ∈ Set.uIcc 0 time, ‖source s‖ ≤ epsilon) :
    ‖cumulant time‖ ≤ epsilon * |time| := by
  simpa [hzero] using
    norm_connectedCumulant_sub_zero_le_of_source_bound
      cumulant source time epsilon hderiv hsource

/-- Thermodynamic/kinetic-scale version: arbitrary fixed-order connected
cumulants tend to zero whenever their exact hierarchy source times the
observation time tends to zero. -/
theorem connectedCumulant_tendsto_zero_of_source_timescale_tendsto_zero
    (cumulant source : Nat → Real → Complex)
    (time epsilon : Nat → Real)
    (hzero : ∀ n, cumulant n 0 = 0)
    (hderiv : ∀ n s, s ∈ Set.uIcc 0 (time n) →
      HasDerivAt (cumulant n) (source n s) s)
    (hsource : ∀ n s, s ∈ Set.uIcc 0 (time n) →
      ‖source n s‖ ≤ epsilon n)
    (hvanish : Tendsto (fun n ↦ epsilon n * |time n|)
      atTop (nhds 0)) :
    Tendsto (fun n ↦ cumulant n (time n)) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero
  · intro n
    exact norm_nonneg _
  · intro n
    exact norm_connectedCumulant_le_of_initial_eq_zero
      (cumulant n) (source n) (time n) (epsilon n)
      (hzero n) (hderiv n) (hsource n)
  · exact hvanish

/-! ## Actual full alpha-beta FPUT specialization -/

variable {I Omega : Type*}
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype Omega]

/-- For an actual finite ensemble of full coercive alpha-beta FPUT
trajectories, a bound on the exact one-slot hierarchy source gives the
arbitrary-order connected-cumulant change bound.  The cardinality of `I` is
the joint order, so this is not restricted to the two-point example. -/
theorem norm_actualFiniteCoerciveEnsembleConnectedCumulant_sub_zero_le
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (kappa beta g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (hp : ∀ omega, Differentiable Real (p omega))
    (hq : ∀ omega, Differentiable Real (q omega))
    (hHamilton : ∀ omega,
      SatisfiesHamiltonEquations (mass omega) kappa beta g
        (p omega) (q omega))
    (homega : ∀ omega i,
      0 < modeFrequency (mass omega) (entry i).2)
    (time epsilon : Real)
    (hsource : ∀ s ∈ Set.uIcc 0 time,
      ‖actualFiniteCoerciveEnsembleConnectedCumulantHierarchySource
        weight mass kappa beta g entry p q s‖ ≤ epsilon) :
    ‖actualFiniteCubicEnsembleConnectedCumulant
        weight mass entry p q time -
      actualFiniteCubicEnsembleConnectedCumulant
        weight mass entry p q 0‖ ≤ epsilon * |time| := by
  apply norm_connectedCumulant_sub_zero_le_of_source_bound
  · intro s _hs
    exact hasDerivAt_actualFiniteCoerciveEnsembleConnectedCumulant
      weight mass kappa beta g entry p q hp hq hHamilton homega s
  · exact hsource

/-- The actual arbitrary-order approximate-RPA endpoint when the selected
nonresonant connected cumulant is initially zero.  Balanced and truly
resonant sectors are not covered by the `hzero` premise and are therefore
not erased by this theorem. -/
theorem norm_actualFiniteCoerciveEnsembleConnectedCumulant_le_of_initial_eq_zero
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (kappa beta g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (hp : ∀ omega, Differentiable Real (p omega))
    (hq : ∀ omega, Differentiable Real (q omega))
    (hHamilton : ∀ omega,
      SatisfiesHamiltonEquations (mass omega) kappa beta g
        (p omega) (q omega))
    (homega : ∀ omega i,
      0 < modeFrequency (mass omega) (entry i).2)
    (hzero : actualFiniteCubicEnsembleConnectedCumulant
      weight mass entry p q 0 = 0)
    (time epsilon : Real)
    (hsource : ∀ s ∈ Set.uIcc 0 time,
      ‖actualFiniteCoerciveEnsembleConnectedCumulantHierarchySource
        weight mass kappa beta g entry p q s‖ ≤ epsilon) :
    ‖actualFiniteCubicEnsembleConnectedCumulant
      weight mass entry p q time‖ ≤ epsilon * |time| := by
  simpa [hzero] using
    norm_actualFiniteCoerciveEnsembleConnectedCumulant_sub_zero_le
      weight mass kappa beta g entry p q hp hq hHamilton homega
      time epsilon hsource

end

end ArchonPhysics.PhyslibFPUTHigherOrderDecoherencePropagation
