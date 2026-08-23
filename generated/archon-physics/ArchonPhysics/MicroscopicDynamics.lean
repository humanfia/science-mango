import Mathlib
import ArchonPhysics.HamiltonianScaling

/-!
# Finite microscopic Hamiltonian dynamics

This candidate module proves local Picard--Lindelof well-posedness and the
deterministic conservation laws of the finite periodic polynomial chain.  It
asserts neither global existence nor any kinetic-limit or thermalization claim.
-/

namespace ArchonPhysics.MicroscopicDynamics

open Filter
open scoped BigOperators Topology

noncomputable section

/-- Position--momentum phase space of the finite periodic chain, ordered as `(q, p)`. -/
abbrev PhaseSpace (N : Nat) : Type :=
  Lattice.Configuration N × Lattice.Configuration N

/-- The degree-`n` single-bond potential `x²/2 + λ xⁿ/n`. -/
def interactionPotential (n : Nat) (lambda x : Real) : Real :=
  x ^ 2 / 2 + (lambda / (n : Real)) * x ^ n

/-- The derivative formula `x + λ xⁿ⁻¹` for a nonzero degree `n`. -/
def interactionForce (n : Nat) (lambda x : Real) : Real :=
  x + lambda * x ^ (n - 1)

/-- The periodic nearest-neighbour force acting on every lattice site. -/
def latticeForce {N : Nat} (n : Nat) (lambda : Real)
    (q : Lattice.Configuration N) : Lattice.Configuration N :=
  Lattice.forwardDifference (fun i =>
    interactionForce n lambda (Lattice.forwardDifference q (i - 1)))

/-- The autonomous microscopic vector field on `(q, p)` phase space. -/
def microscopicVectorField {N : Nat} (m : Lattice.PositiveMassConfig N)
    (n : Nat) (lambda : Real) : PhaseSpace N → PhaseSpace N :=
  fun z => (Lattice.inverseMassAction m z.2, latticeForce n lambda z.1)

/-- The concrete vector-valued Hamilton ODE holds at the specified time. -/
def IsClassicalSolutionAt {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (n : Nat) (lambda : Real)
    (z : Real → PhaseSpace N) (t : Real) : Prop :=
  HasDerivAt z (microscopicVectorField m n lambda (z t)) t

/-- A classical solution of the microscopic vector field defined for every real time. -/
def IsGlobalClassicalSolution {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (n : Nat) (lambda : Real)
    (z : Real → PhaseSpace N) : Prop :=
  ∀ t, IsClassicalSolutionAt m n lambda z t

/-- The existing finite lattice Hamiltonian evaluated on phase space ordered as `(q, p)`. -/
def hamiltonianEnergy {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (n : Nat) (lambda : Real)
    (z : PhaseSpace N) : Real :=
  HamiltonianScaling.latticeHamiltonian m n lambda z.2 z.1

/-- Total canonical momentum of a finite periodic-chain state. -/
def totalMomentum {N : Nat} [NeZero N] (z : PhaseSpace N) : Real :=
  ∑ i, z.2 i

/-- Pointwise expansion of the outgoing-minus-incoming nearest-neighbour force. -/
theorem latticeForce_apply {N : Nat} (n : Nat) (lambda : Real)
    (q : Lattice.Configuration N) (i : Lattice.Site N) :
    latticeForce n lambda q i =
      interactionForce n lambda (Lattice.forwardDifference q i) -
        interactionForce n lambda (Lattice.forwardDifference q (i - 1)) := by
  simp [latticeForce, Lattice.forwardDifference]

/-- Internal nearest-neighbour forces sum to zero on the periodic chain. -/
theorem sum_latticeForce {N : Nat} [NeZero N] (n : Nat) (lambda : Real)
    (q : Lattice.Configuration N) :
    ∑ i, latticeForce n lambda q i = 0 := by
  exact Lattice.sum_forwardDifference (fun i =>
    interactionForce n lambda (Lattice.forwardDifference q (i - 1)))

/-- The finite microscopic vector field is continuously differentiable. -/
theorem microscopicVectorField_contDiff {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (n : Nat) (lambda : Real) :
    ContDiff Real 1 (microscopicVectorField m n lambda) := by
  unfold microscopicVectorField latticeForce interactionForce
  unfold Lattice.inverseMassAction Lattice.forwardDifference
  fun_prop

/--
For every initial state and time, the concrete microscopic ODE has a solution on
a nontrivial symmetric interval and the resulting solution germ is unique.
-/
theorem exists_unique_local_solution_germ {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (n : Nat) (lambda : Real)
    (t₀ : Real) (z₀ : PhaseSpace N) :
    ∃ ε : Real, 0 < ε ∧ ∃ z : Real → PhaseSpace N,
      z t₀ = z₀ ∧
      (∀ t ∈ Set.Icc (t₀ - ε) (t₀ + ε),
        HasDerivWithinAt z (microscopicVectorField m n lambda (z t))
          (Set.Icc (t₀ - ε) (t₀ + ε)) t) ∧
      ∀ y : Real → PhaseSpace N,
        y t₀ = z₀ →
        (∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt y (microscopicVectorField m n lambda (y t)) t) →
        z =ᶠ[nhds t₀] y := by
  obtain ⟨ε, hε, a, r, L, K, hr, hPL⟩ :=
    IsPicardLindelof.of_contDiffAt_one
      (microscopicVectorField_contDiff m n lambda).contDiffAt
  let t₀' : Set.Icc (t₀ - ε) (t₀ + ε) :=
    ⟨t₀, ⟨sub_le_self t₀ hε.le, le_add_of_nonneg_right hε.le⟩⟩
  have hPL₀ : IsPicardLindelof (fun _ => microscopicVectorField m n lambda)
      t₀' z₀ a r L K := hPL t₀
  have hz₀ball : z₀ ∈ Metric.closedBall z₀ (r : Real) := by
    exact Metric.mem_closedBall_self (NNReal.coe_nonneg r)
  obtain ⟨z, hz₀, hzderiv⟩ :=
    hPL₀.exists_eq_forall_mem_Icc_hasDerivWithinAt hz₀ball
  refine ⟨ε, hε, z, ?_, hzderiv, ?_⟩
  · simpa [t₀'] using hz₀
  intro y hy₀ hyderiv
  have hleft : t₀ - ε < t₀ := sub_lt_self t₀ hε
  have hright : t₀ < t₀ + ε := lt_add_of_pos_right t₀ hε
  have hIcc : Set.Icc (t₀ - ε) (t₀ + ε) ∈ nhds t₀ :=
    Icc_mem_nhds hleft hright
  have hIoo : Set.Ioo (t₀ - ε) (t₀ + ε) ∈ nhds t₀ :=
    Ioo_mem_nhds hleft hright
  have ha : 0 < (a : Real) := by
    have hbound := hPL₀.mul_max_le
    have hr' : 0 < (r : Real) := by exact_mod_cast hr
    have hL : 0 ≤ (L : Real) := NNReal.coe_nonneg L
    have hmax :
        0 ≤ max ((t₀ + ε) - t₀) (t₀ - (t₀ - ε)) := by
      calc
        0 ≤ ε := hε.le
        _ = (t₀ + ε) - t₀ := by ring
        _ ≤ max ((t₀ + ε) - t₀) (t₀ - (t₀ - ε)) := le_max_left _ _
    have hprod :
        0 ≤ (L : Real) * max ((t₀ + ε) - t₀) (t₀ - (t₀ - ε)) :=
      mul_nonneg hL hmax
    nlinarith
  have hzderiv_eventually :
      ∀ᶠ t in nhds t₀,
        HasDerivAt z (microscopicVectorField m n lambda (z t)) t := by
    filter_upwards [hIoo] with t ht
    exact (hzderiv t ⟨ht.1.le, ht.2.le⟩).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  have hzcont : ContinuousAt z t₀ := by
    have h := (hzderiv t₀ ⟨hleft.le, hright.le⟩).hasDerivAt hIcc
    exact h.continuousAt
  have hzball :
      ∀ᶠ t in nhds t₀, z t ∈ Metric.closedBall z₀ (a : Real) := by
    have hopen : z ⁻¹' Metric.ball z₀ (a : Real) ∈ nhds t₀ := by
      apply hzcont.preimage_mem_nhds
      rw [show z t₀ = z₀ by simpa [t₀'] using hz₀]
      exact Metric.ball_mem_nhds z₀ ha
    filter_upwards [hopen] with t ht
    exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp ht).le
  have hyderiv_eventually :
      ∀ᶠ t in nhds t₀,
        HasDerivAt y (microscopicVectorField m n lambda (y t)) t := by
    filter_upwards [hIoo] with t ht
    exact hyderiv t ht
  have hycont : ContinuousAt y t₀ :=
    (hyderiv t₀ ⟨hleft, hright⟩).continuousAt
  have hyball :
      ∀ᶠ t in nhds t₀, y t ∈ Metric.closedBall z₀ (a : Real) := by
    have hopen : y ⁻¹' Metric.ball z₀ (a : Real) ∈ nhds t₀ := by
      apply hycont.preimage_mem_nhds
      rw [hy₀]
      exact Metric.ball_mem_nhds z₀ ha
    filter_upwards [hopen] with t ht
    exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp ht).le
  apply ODE_solution_unique_of_eventually
    (s := fun _ => Metric.closedBall z₀ (a : Real)) (K := K)
  · filter_upwards [hIcc] with t ht
    exact hPL₀.lipschitzOnWith t ht
  · exact hzderiv_eventually.and hzball
  · exact hyderiv_eventually.and hyball
  · exact (show z t₀ = z₀ by simpa [t₀'] using hz₀).trans hy₀.symm

private theorem solutionAt_hasDerivAt_position {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (n : Nat) (lambda : Real)
    (z : Real → PhaseSpace N) (t : Real)
    (h : IsClassicalSolutionAt m n lambda z t) :
    HasDerivAt (fun s => (z s).1) (Lattice.inverseMassAction m (z t).2) t := by
  simpa [IsClassicalSolutionAt, microscopicVectorField] using
    h.hasFDerivAt.fst.hasDerivAt

private theorem solutionAt_hasDerivAt_momentum {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (n : Nat) (lambda : Real)
    (z : Real → PhaseSpace N) (t : Real)
    (h : IsClassicalSolutionAt m n lambda z t) :
    HasDerivAt (fun s => (z s).2) (latticeForce n lambda (z t).1) t := by
  simpa [IsClassicalSolutionAt, microscopicVectorField] using
    h.hasFDerivAt.snd.hasDerivAt

/-- Total momentum has derivative zero whenever the concrete microscopic ODE holds. -/
theorem totalMomentum_hasDerivAt_zero_at {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (n : Nat) (lambda : Real)
    (z : Real → PhaseSpace N) (t : Real)
    (h : IsClassicalSolutionAt m n lambda z t) :
    HasDerivAt (fun s => totalMomentum (z s)) 0 t := by
  have hp := hasDerivAt_pi.mp
    (solutionAt_hasDerivAt_momentum m n lambda z t h)
  have hsum : HasDerivAt (fun s => ∑ i : Lattice.Site N, (z s).2 i)
      (∑ i : Lattice.Site N, latticeForce n lambda (z t).1 i) t :=
    HasDerivAt.fun_sum fun i _ => hp i
  simpa only [totalMomentum, sum_latticeForce] using hsum

private theorem interactionPotential_comp_hasDerivAt (n : Nat) (lambda : Real)
    (hn : 1 ≤ n) {r : Real → Real} {r' x : Real}
    (h : HasDerivAt r r' x) :
    HasDerivAt (fun s => interactionPotential n lambda (r s))
      (interactionForce n lambda (r x) * r') x := by
  have hn0 : (n : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hraw :=
    ((h.pow 2).div_const 2).add
      ((h.pow n).const_mul (lambda / (n : Real)))
  have hraw' :
      HasDerivAt (fun s => interactionPotential n lambda (r s))
        (((2 : Real) * r x ^ (2 - 1) * r') / 2 +
          (lambda / (n : Real)) * ((n : Real) * r x ^ (n - 1) * r')) x := by
    simpa only [interactionPotential, Pi.add_apply, Pi.mul_apply, Pi.pow_apply] using! hraw
  apply hraw'.congr_deriv
  unfold interactionForce
  field_simp [hn0]
  ring

private theorem power_balance {N : Nat} [NeZero N] (n : Nat) (lambda : Real)
    (q v : Lattice.Configuration N) :
    (∑ i, v i * latticeForce n lambda q i) +
        ∑ i, interactionForce n lambda (Lattice.forwardDifference q i) *
          Lattice.forwardDifference v i = 0 := by
  have hshift :
      (∑ i : Lattice.Site N,
          interactionForce n lambda (Lattice.forwardDifference q i) * v (i + 1)) =
        ∑ i : Lattice.Site N,
          v i * interactionForce n lambda (Lattice.forwardDifference q (i - 1)) := by
    exact Fintype.sum_equiv (Equiv.addRight 1)
      (fun i : Lattice.Site N =>
        interactionForce n lambda (Lattice.forwardDifference q i) * v (i + 1))
      (fun i : Lattice.Site N =>
        v i * interactionForce n lambda (Lattice.forwardDifference q (i - 1)))
      (fun i => by simp; ring)
  change
    (∑ i, v i * latticeForce n lambda q i) +
      ∑ i, interactionForce n lambda (Lattice.forwardDifference q i) *
        (v (i + 1) - v i) = 0
  simp_rw [latticeForce_apply, mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hshift]
  have hcomm :
      (∑ i : Lattice.Site N,
          v i * interactionForce n lambda (Lattice.forwardDifference q i)) =
        ∑ i : Lattice.Site N,
          interactionForce n lambda (Lattice.forwardDifference q i) * v i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hcomm]
  ring

/-- The finite lattice Hamiltonian has derivative zero whenever the vector ODE holds. -/
theorem hamiltonianEnergy_hasDerivAt_zero_at {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (n : Nat) (lambda : Real)
    (hn : 1 ≤ n) (z : Real → PhaseSpace N) (t : Real)
    (h : IsClassicalSolutionAt m n lambda z t) :
    HasDerivAt (fun s => hamiltonianEnergy m n lambda (z s)) 0 t := by
  let v : Lattice.Configuration N :=
    Lattice.inverseMassAction m (z t).2
  have hq := hasDerivAt_pi.mp
    (solutionAt_hasDerivAt_position m n lambda z t h)
  have hp := hasDerivAt_pi.mp
    (solutionAt_hasDerivAt_momentum m n lambda z t h)
  have hsite (i : Lattice.Site N) :
      HasDerivAt
        (fun s =>
          (z s).2 i ^ 2 / (2 * m.mass i) +
            interactionPotential n lambda
              (Lattice.forwardDifference (z s).1 i))
        (v i * latticeForce n lambda (z t).1 i +
          interactionForce n lambda
            (Lattice.forwardDifference (z t).1 i) *
              Lattice.forwardDifference v i) t := by
    have hm0 : m.mass i ≠ 0 := ne_of_gt (m.mass_pos i)
    have hkinRaw := (hp i).pow 2 |>.div_const (2 * m.mass i)
    have hkin :
        HasDerivAt (fun s => (z s).2 i ^ 2 / (2 * m.mass i))
          (v i * latticeForce n lambda (z t).1 i) t := by
      have hkin' :
          HasDerivAt (fun s => (z s).2 i ^ 2 / (2 * m.mass i))
            (((2 : Real) * (z t).2 i ^ (2 - 1) *
              latticeForce n lambda (z t).1 i) / (2 * m.mass i)) t := by
        simpa only [Pi.pow_apply] using! hkinRaw
      apply hkin'.congr_deriv
      unfold v Lattice.inverseMassAction
      field_simp [hm0]
      ring
    have hdifference :
        HasDerivAt
          (fun s => Lattice.forwardDifference (z s).1 i)
          (Lattice.forwardDifference v i) t := by
      simpa only [Lattice.forwardDifference] using!
        (hq (i + 1)).sub (hq i)
    exact hkin.add
      (interactionPotential_comp_hasDerivAt n lambda hn hdifference)
  have hsum := HasDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) => hsite i
  have hzero :
      (∑ i : Lattice.Site N,
          (v i * latticeForce n lambda (z t).1 i +
            interactionForce n lambda
              (Lattice.forwardDifference (z t).1 i) *
                Lattice.forwardDifference v i)) = 0 := by
    simpa only [Finset.sum_add_distrib] using
      power_balance n lambda (z t).1 v
  have hsumZero := hsum.congr_deriv hzero
  simpa only [hamiltonianEnergy, HamiltonianScaling.latticeHamiltonian,
    interactionPotential, add_assoc] using! hsumZero

/-- Energy agrees at the endpoints of any segment carrying the microscopic ODE. -/
theorem hamiltonianEnergy_eq_of_forall_mem_uIcc {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (n : Nat) (lambda : Real)
    (hn : 1 ≤ n) (z : Real → PhaseSpace N) (s t : Real)
    (h : ∀ u ∈ Set.uIcc s t, IsClassicalSolutionAt m n lambda z u) :
    hamiltonianEnergy m n lambda (z s) =
      hamiltonianEnergy m n lambda (z t) := by
  let E : Real → Real := fun u => hamiltonianEnergy m n lambda (z u)
  have hewithin : ∀ u ∈ Set.uIcc s t,
      HasDerivWithinAt E 0 (Set.uIcc s t) u := by
    intro u hu
    exact (hamiltonianEnergy_hasDerivAt_zero_at m n lambda hn z u
      (h u hu)).hasDerivWithinAt
  have hbound := (convex_uIcc s t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (C := 0) hewithin (fun _ _ => by simp) Set.left_mem_uIcc Set.right_mem_uIcc
  have hrev : E t = E s := by
    simpa only [norm_zero, zero_mul, norm_le_zero_iff, sub_eq_zero] using hbound
  exact hrev.symm

/-- Total momentum agrees at the endpoints of any segment carrying the microscopic ODE. -/
theorem totalMomentum_eq_of_forall_mem_uIcc {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (n : Nat) (lambda : Real)
    (z : Real → PhaseSpace N) (s t : Real)
    (h : ∀ u ∈ Set.uIcc s t, IsClassicalSolutionAt m n lambda z u) :
    totalMomentum (z s) = totalMomentum (z t) := by
  let P : Real → Real := fun u => totalMomentum (z u)
  have hpwithin : ∀ u ∈ Set.uIcc s t,
      HasDerivWithinAt P 0 (Set.uIcc s t) u := by
    intro u hu
    exact (totalMomentum_hasDerivAt_zero_at m n lambda z u
      (h u hu)).hasDerivWithinAt
  have hbound := (convex_uIcc s t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (C := 0) hpwithin (fun _ _ => by simp) Set.left_mem_uIcc Set.right_mem_uIcc
  have hrev : P t = P s := by
    simpa only [norm_zero, zero_mul, norm_le_zero_iff, sub_eq_zero] using hbound
  exact hrev.symm

end

end ArchonPhysics.MicroscopicDynamics

