import ArchonPhysics.PhyslibFPUTActualEnsembleNormalization
import ArchonPhysics.PhaseRenormalization

/-!
# Finite-ensemble bounds for actual FPUT block moments

This file discharges the elementary finite-ensemble part of the uniform
block-moment premise used by higher-order cluster estimates.  Nonnegative
weights of total mass one turn pointwise slot envelopes into the sharp finite
product bound

`‖moment(block)‖ ≤ ∏ i ∈ block, envelope i`.

A common amplitude envelope `A` gives the simpler bound `A ^ block.card`.
The final theorem allows all ensemble data to vary with an arbitrary system
index while retaining one fixed cluster and one common `A`, and therefore
produces an explicit system-uniform bound.

The current coercive-energy API controls configurations on energy shells but
does not expose a direct theorem bounding every positive-frequency
`physlibModeAmplitude` uniformly for the general trajectories used here.
Accordingly, the pointwise modal-amplitude envelope remains the sole
transparent dynamical premise.  No energy estimate, RPA closure, or decay is
invented in this module.
-/

namespace ArchonPhysics.PhyslibFPUTActualFiniteEnsembleMomentBound

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibHamiltonDuhamel

noncomputable section

variable {I Omega : Type*}
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype Omega] [DecidableEq Omega]

omit [Fintype I] [DecidableEq I] [Nonempty I] in
/-- A pointwise envelope on every displayed slot bounds one signed block
monomial by the product of those envelopes. -/
theorem norm_signedBlockMonomial_le_prod_slotEnvelope
    (path : I → Real → Complex) (block : Finset I) (time : Real)
    (slotEnvelope : I → Real)
    (_henvelope : ∀ i ∈ block, 0 ≤ slotEnvelope i)
    (hpath : ∀ i ∈ block, ‖path i time‖ ≤ slotEnvelope i) :
    ‖signedBlockMonomial path block time‖ ≤
      ∏ i ∈ block, slotEnvelope i := by
  unfold signedBlockMonomial
  calc
    ‖∏ i ∈ block, path i time‖ =
        ∏ i ∈ block, ‖path i time‖ := by
      exact Complex.norm_prod block (fun i ↦ path i time)
    _ ≤ ∏ i ∈ block, slotEnvelope i := by
      apply Finset.prod_le_prod
      · intro i hi
        exact norm_nonneg (path i time)
      · intro i hi
        exact hpath i hi

omit [Fintype I] [DecidableEq I] [Nonempty I] [DecidableEq Omega] in
/-- A normalized nonnegative finite ensemble inherits the product slot
envelope from its individual samples. -/
theorem norm_finiteWeightedBlockMoment_le_prod_slotEnvelope
    (weight : Omega → Real)
    (path : Omega → I → Real → Complex)
    (block : Finset I) (time : Real)
    (slotEnvelope : I → Real)
    (hweightNonneg : ∀ omega, 0 ≤ weight omega)
    (hweightSum : ∑ omega, weight omega = 1)
    (henvelope : ∀ i ∈ block, 0 ≤ slotEnvelope i)
    (hpath : ∀ omega i, i ∈ block →
      ‖path omega i time‖ ≤ slotEnvelope i) :
    ‖finiteWeightedBlockMoment weight path block time‖ ≤
      ∏ i ∈ block, slotEnvelope i := by
  unfold finiteWeightedBlockMoment
  calc
    ‖∑ omega, (weight omega : Complex) *
        signedBlockMonomial (path omega) block time‖ ≤
      ∑ omega, ‖(weight omega : Complex) *
        signedBlockMonomial (path omega) block time‖ :=
      norm_sum_le _ _
    _ = ∑ omega, weight omega *
        ‖signedBlockMonomial (path omega) block time‖ := by
      apply Finset.sum_congr rfl
      intro omega homega
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (hweightNonneg omega)]
    _ ≤ ∑ omega, weight omega *
        (∏ i ∈ block, slotEnvelope i) := by
      apply Finset.sum_le_sum
      intro omega homega
      exact mul_le_mul_of_nonneg_left
        (norm_signedBlockMonomial_le_prod_slotEnvelope
          (path omega) block time slotEnvelope henvelope
          (fun i hi ↦ hpath omega i hi))
        (hweightNonneg omega)
    _ = ∏ i ∈ block, slotEnvelope i := by
      rw [← Finset.sum_mul, hweightSum, one_mul]

omit [Fintype I] [DecidableEq I] [Nonempty I] [DecidableEq Omega] in
/-- A common nonnegative slot envelope gives the cardinality-power bound. -/
theorem norm_finiteWeightedBlockMoment_le_pow_card
    (weight : Omega → Real)
    (path : Omega → I → Real → Complex)
    (block : Finset I) (time A : Real)
    (hweightNonneg : ∀ omega, 0 ≤ weight omega)
    (hweightSum : ∑ omega, weight omega = 1)
    (hA : 0 ≤ A)
    (hpath : ∀ omega i, i ∈ block → ‖path omega i time‖ ≤ A) :
    ‖finiteWeightedBlockMoment weight path block time‖ ≤
      A ^ block.card := by
  simpa using
    (norm_finiteWeightedBlockMoment_le_prod_slotEnvelope
      weight path block time (fun _ ↦ A)
      hweightNonneg hweightSum (fun _ _ ↦ hA) hpath)

omit [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype Omega] [DecidableEq Omega] in
/-- Phase rotation and phase-sign action preserve the norm, so the actual
signed interaction path has exactly the norm of the underlying modal
amplitude. -/
theorem norm_signedPhyslibInteractionModePath_eq_modeAmplitude
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (sign : PhaseSign)
    (mode : Lattice.Site N)
    (p q : Time → HilbertConfiguration N) (time : Real) :
    ‖signedPhyslibInteractionModePath m sign mode p q time‖ =
      ‖physlibModeAmplitude m mode p q time‖ := by
  unfold signedPhyslibInteractionModePath physlibInteractionModePath
  cases sign <;> simp [phaseSignActComplex]

omit [Fintype I] [DecidableEq I] [Nonempty I] [DecidableEq Omega] in
/-- Actual finite-ensemble specialization of the sharp slot-product bound. -/
theorem norm_actualFiniteCubicEnsembleBlockMoment_le_prod_slotEnvelope
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (block : Finset I) (time : Real)
    (slotEnvelope : I → Real)
    (hweightNonneg : ∀ omega, 0 ≤ weight omega)
    (hweightSum : ∑ omega, weight omega = 1)
    (henvelope : ∀ i ∈ block, 0 ≤ slotEnvelope i)
    (hpath : ∀ omega i, i ∈ block →
      ‖actualFiniteCubicEnsemblePath mass entry p q omega i time‖ ≤
        slotEnvelope i) :
    ‖actualFiniteCubicEnsembleBlockMoment
        weight mass entry p q block time‖ ≤
      ∏ i ∈ block, slotEnvelope i := by
  unfold actualFiniteCubicEnsembleBlockMoment
  exact norm_finiteWeightedBlockMoment_le_prod_slotEnvelope
    weight (actualFiniteCubicEnsemblePath mass entry p q)
      block time slotEnvelope hweightNonneg hweightSum
      henvelope hpath

omit [Fintype I] [DecidableEq I] [Nonempty I] [DecidableEq Omega] in
/-- The same actual moment bound stated directly from a modal-amplitude
envelope, using norm preservation of the interaction-picture phase and sign. -/
theorem norm_actualFiniteCubicEnsembleBlockMoment_le_prod_of_modeAmplitude
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (block : Finset I) (time : Real)
    (slotEnvelope : I → Real)
    (hweightNonneg : ∀ omega, 0 ≤ weight omega)
    (hweightSum : ∑ omega, weight omega = 1)
    (henvelope : ∀ i ∈ block, 0 ≤ slotEnvelope i)
    (hamplitude : ∀ omega i, i ∈ block →
      ‖physlibModeAmplitude (mass omega) (entry i).2
        (p omega) (q omega) time‖ ≤ slotEnvelope i) :
    ‖actualFiniteCubicEnsembleBlockMoment
        weight mass entry p q block time‖ ≤
      ∏ i ∈ block, slotEnvelope i := by
  apply norm_actualFiniteCubicEnsembleBlockMoment_le_prod_slotEnvelope
    weight mass entry p q block time slotEnvelope
      hweightNonneg hweightSum henvelope
  intro omega i hi
  rw [actualFiniteCubicEnsemblePath,
    norm_signedPhyslibInteractionModePath_eq_modeAmplitude]
  exact hamplitude omega i hi

omit [Fintype I] [DecidableEq I] [Nonempty I] [DecidableEq Omega] in
/-- A uniform actual signed-path envelope gives the explicit `A^card`
moment bound. -/
theorem norm_actualFiniteCubicEnsembleBlockMoment_le_pow_card
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (block : Finset I) (time A : Real)
    (hweightNonneg : ∀ omega, 0 ≤ weight omega)
    (hweightSum : ∑ omega, weight omega = 1)
    (hA : 0 ≤ A)
    (hpath : ∀ omega i, i ∈ block →
      ‖actualFiniteCubicEnsemblePath mass entry p q omega i time‖ ≤ A) :
    ‖actualFiniteCubicEnsembleBlockMoment
        weight mass entry p q block time‖ ≤ A ^ block.card := by
  simpa using
    (norm_actualFiniteCubicEnsembleBlockMoment_le_prod_slotEnvelope
      weight mass entry p q block time (fun _ ↦ A)
      hweightNonneg hweightSum (fun _ _ ↦ hA) hpath)

omit [Fintype I] [DecidableEq I] [Nonempty I] [DecidableEq Omega] in
/-- Unit path norms directly discharge the commonly used `hmoment ≤ 1`
premise for one fixed block. -/
theorem norm_actualFiniteCubicEnsembleBlockMoment_le_one
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (block : Finset I) (time : Real)
    (hweightNonneg : ∀ omega, 0 ≤ weight omega)
    (hweightSum : ∑ omega, weight omega = 1)
    (hpath : ∀ omega i, i ∈ block →
      ‖actualFiniteCubicEnsemblePath mass entry p q omega i time‖ ≤ 1) :
    ‖actualFiniteCubicEnsembleBlockMoment
      weight mass entry p q block time‖ ≤ 1 := by
  simpa using
    (norm_actualFiniteCubicEnsembleBlockMoment_le_pow_card
      weight mass entry p q block time 1 hweightNonneg hweightSum
      (by norm_num) hpath)

omit [Fintype I] [DecidableEq I] [Nonempty I] [DecidableEq Omega] in
/-- For a fixed cluster, one common signed-path envelope over an arbitrary
family of finite systems supplies an explicit system-uniform moment bound. -/
theorem exists_systemUniform_actualFiniteCubicEnsembleBlockMoment_bound
    {System : Type*} {N : Nat} [NeZero N]
    (weight : System → Omega → Real)
    (mass : System → Omega → Lattice.PositiveMassConfig N)
    (entry : System → I → PhaseSign × Lattice.Site N)
    (p q : System → Omega → Time → HilbertConfiguration N)
    (cluster : Finset I) (kineticTime : System → Real) (A : Real)
    (hweightNonneg : ∀ system omega, 0 ≤ weight system omega)
    (hweightSum : ∀ system, ∑ omega, weight system omega = 1)
    (hA : 0 ≤ A)
    (hpath : ∀ system omega i, i ∈ cluster →
      ‖actualFiniteCubicEnsemblePath
        (mass system) (entry system) (p system) (q system)
          omega i (kineticTime system)‖ ≤ A) :
    ∃ bound : Real, 0 ≤ bound ∧ ∀ system,
      ‖actualFiniteCubicEnsembleBlockMoment
        (weight system) (mass system) (entry system)
          (p system) (q system) cluster (kineticTime system)‖ ≤ bound := by
  refine ⟨A ^ cluster.card, pow_nonneg hA _, ?_⟩
  intro system
  exact norm_actualFiniteCubicEnsembleBlockMoment_le_pow_card
    (weight system) (mass system) (entry system)
      (p system) (q system) cluster (kineticTime system) A
      (hweightNonneg system) (hweightSum system) hA
      (fun omega i hi ↦ hpath system omega i hi)

end

end ArchonPhysics.PhyslibFPUTActualFiniteEnsembleMomentBound
