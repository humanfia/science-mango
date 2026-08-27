import ArchonPhysics.FiniteThreeWaveCollisionNetwork
import ArchonPhysics.RandomMassPositiveCollisionData

/-!
# Exact three-wave collision networks for one random-mass realization

For one supplied positive-mass configuration, this module selects the ordered
positive triples in the decay channel `(+,-,-)` whose exact ordered frequency
mismatch vanishes.  These triples form a finite collision network.  Its rates
are the existing basis-free normalized squared interaction weights.

The construction may be empty, and its active graph may fail the explicit
balance-rigidity condition used in the equality case.  No theorem below proves
nonemptiness, graph rigidity, rate lower bounds, large-`N` stability, a kernel
limit, kinetic relaxation, or microscopic thermalization.
-/

namespace ArchonPhysics.RandomMassThreeWaveCollisionNetwork

open scoped Matrix

open ArchonPhysics
open ArchonPhysics.FiniteThreeWaveCollisionNetwork
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ThreeWaveCollisionAlgebra

noncomputable section

/-! ## Global nonnegativity of the basis-free ordered weight -/

variable {ι bond : Type*}
variable [Fintype ι] [DecidableEq ι]

/-- The ordered eigenvalue at `k` is isolated from every other ordered index. -/
def IsolatedOrderedMode (A : HermitianMatrix ι)
    (k : Fin (Fintype.card ι)) : Prop :=
  ∀ j, j ≠ k → orderedEigenvalue A j ≠ orderedEigenvalue A k

/-- The Lagrange projector acts as the rank-one eigenprojector when only the
selected ordered eigenvalue is assumed isolated. -/
theorem orderedModeProjector_mulVec_eigenvectorBasis_of_isolated
    (A : HermitianMatrix ι) {k : Fin (Fintype.card ι)}
    (hisolated : IsolatedOrderedMode A k)
    (r : Fin (Fintype.card ι)) :
    orderedModeProjector A k *ᵥ
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) =
      if r = k then ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) else 0 := by
  rw [orderedModeProjector, listProduct_mulVec_eigenvectorBasis]
  split_ifs with hrk
  · subst r
    have hprod :
        (((Finset.univ.erase k).toList.map
          (orderedModeRatio A k k))).prod = 1 := by
      apply List.prod_eq_one
      intro z hz
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
      have hjk : j ≠ k := by simpa using hj
      have hne : orderedEigenvalue A k - orderedEigenvalue A j ≠ 0 :=
        sub_ne_zero.mpr (hisolated j hjk).symm
      exact div_self hne
    rw [hprod, one_smul]
  · have hrmem : r ∈ (Finset.univ.erase k).toList := by
      simp [hrk]
    have hzero : orderedModeRatio A k r r = 0 := by
      simp [orderedModeRatio]
    have hzmem :
        (0 : Real) ∈ ((Finset.univ.erase k).toList.map
          (orderedModeRatio A k r)) :=
      List.mem_map.mpr ⟨r, hrmem, hzero⟩
    rw [List.prod_eq_zero hzmem, zero_smul]

/-- At an isolated ordered eigenvalue, the totalized Lagrange formula is the
rank-one outer product of Mathlib's corresponding eigenvector. -/
theorem orderedModeProjector_eq_vecMulVec_of_isolated
    (A : HermitianMatrix ι) {k : Fin (Fintype.card ι)}
    (hisolated : IsolatedOrderedMode A k) :
    orderedModeProjector A k =
      Matrix.vecMulVec
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k))
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k)) := by
  apply matrix_eq_of_mulVec_eigenvectorBasis_eq A
  intro r
  rw [orderedModeProjector_mulVec_eigenvectorBasis_of_isolated A hisolated]
  rw [Matrix.vecMulVec_mulVec]
  have hdot :
      ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k)) ⬝ᵥ
          ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) =
        if r = k then 1 else 0 := by
    have hinner := A.2.eigenvectorBasis.inner_eq_ite
      (orderedIndexEquiv r) (orderedIndexEquiv k)
    simpa [EuclideanSpace.inner_eq_star_dotProduct, eq_comm] using hinner
  rw [hdot]
  by_cases hr : r = k
  · subst r
    simp
  · simp [hr]

/-- If the selected ordered eigenvalue is repeated, totalized inversion makes
its Lagrange projector identically zero. -/
theorem orderedModeProjector_eq_zero_of_repeated
    (A : HermitianMatrix ι) {k j : Fin (Fintype.card ι)}
    (hjk : j ≠ k) (heq : orderedEigenvalue A j = orderedEigenvalue A k) :
    orderedModeProjector A k = 0 := by
  apply matrix_eq_of_mulVec_eigenvectorBasis_eq A
  intro r
  rw [orderedModeProjector, listProduct_mulVec_eigenvectorBasis]
  have hjmem : j ∈ (Finset.univ.erase k).toList := by
    simp [hjk]
  have hzero : orderedModeRatio A k r j = 0 := by
    unfold orderedModeRatio
    rw [heq]
    simp
  have hzmem :
      (0 : Real) ∈ ((Finset.univ.erase k).toList.map
        (orderedModeRatio A k r)) :=
    List.mem_map.mpr ⟨j, hjmem, hzero⟩
  rw [List.prod_eq_zero hzmem, zero_smul]
  simp

/-- Every totalized ordered Lagrange projector is either zero or its canonical
rank-one eigenprojector. -/
theorem orderedModeProjector_eq_zero_or_vecMulVec
    (A : HermitianMatrix ι) (k : Fin (Fintype.card ι)) :
    orderedModeProjector A k = 0 ∨
      orderedModeProjector A k =
        Matrix.vecMulVec
          ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k))
          ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k)) := by
  classical
  by_cases hisolated : IsolatedOrderedMode A k
  · exact Or.inr (orderedModeProjector_eq_vecMulVec_of_isolated A hisolated)
  · left
    have hrepeat : ∃ j, ∃ _ : j ≠ k,
        orderedEigenvalue A j = orderedEigenvalue A k := by
      simpa only [IsolatedOrderedMode, not_forall, Classical.not_imp,
        not_ne_iff] using hisolated
    obtain ⟨j, hjk, heq⟩ := hrepeat
    exact orderedModeProjector_eq_zero_of_repeated A hjk heq

/-- The projector formula for a squared ordered interaction is globally
nonnegative, including at spectral degeneracies. -/
theorem orderedInteractionWeightSq_nonneg
    [Fintype bond] {n : Nat} (B : Matrix bond ι Real)
    (A : HermitianMatrix ι)
    (modes : Fin n → Fin (Fintype.card ι)) :
    0 ≤ orderedInteractionWeightSq B A modes := by
  classical
  by_cases hall : ∀ r, orderedModeProjector A (modes r) =
      Matrix.vecMulVec
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv (modes r)))
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv (modes r)))
  · have hkernel (r : Fin n) (j l : bond) :
        projectedBondKernel B A (modes r) j l =
          (B *ᵥ ⇑(A.2.eigenvectorBasis
            (orderedIndexEquiv (modes r)))) j *
          (B *ᵥ ⇑(A.2.eigenvectorBasis
            (orderedIndexEquiv (modes r)))) l := by
      unfold projectedBondKernel
      rw [hall r, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
        Matrix.vecMul_transpose]
      rfl
    have hsquare : orderedInteractionWeightSq B A modes =
        (∑ j, ∏ r,
          (B *ᵥ ⇑(A.2.eigenvectorBasis
            (orderedIndexEquiv (modes r)))) j) ^ 2 := by
      unfold orderedInteractionWeightSq
      simp_rw [hkernel]
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [← Finset.prod_mul_distrib]
    rw [hsquare]
    positivity
  · have hexists : ∃ r, orderedModeProjector A (modes r) ≠
        Matrix.vecMulVec
          ⇑(A.2.eigenvectorBasis (orderedIndexEquiv (modes r)))
          ⇑(A.2.eigenvectorBasis (orderedIndexEquiv (modes r))) := by
      simpa only [not_forall] using hall
    obtain ⟨r, hr⟩ := hexists
    have hzero : orderedModeProjector A (modes r) = 0 := by
      rcases orderedModeProjector_eq_zero_or_vecMulVec A (modes r) with hz | houter
      · exact hz
      · exact (hr houter).elim
    have hkernel (j l : bond) :
        projectedBondKernel B A (modes r) j l = 0 := by
      simp [projectedBondKernel, hzero]
    have hproduct (j l : bond) :
        (∏ s, projectedBondKernel B A (modes s) j l) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ r) (hkernel j l)
    unfold orderedInteractionWeightSq
    simp_rw [hproduct]
    simp

/-- Consequently the frequency-normalized basis-free harmonic interaction
weight is nonnegative for every positive-mass realization and ordered tuple. -/
theorem harmonicOrderedNormalizedInteractionWeight_nonneg
    {N n : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : Fin n → Fin (Fintype.card (Lattice.Site N))) :
    0 ≤ harmonicOrderedNormalizedInteractionWeight m modes := by
  unfold harmonicOrderedNormalizedInteractionWeight
    harmonicOrderedInteractionWeightSq
  apply mul_nonneg
  · exact orderedInteractionWeightSq_nonneg _ _ _
  · apply Finset.prod_nonneg
    intro r _
    exact inv_nonneg.mpr
      (mul_nonneg zero_le_two (Real.sqrt_nonneg _))

/-! ## The exact positive decay network of one realization -/

/-- Fixed decay-channel signs `(+,-,-)`. -/
def decayInteractionSign (r : Fin 3) : InteractionSign :=
  if r = 0 then .plus else .minus

/-- In the decay channel, the ordered signed mismatch is exactly
`ω₀ - ω₁ - ω₂`. -/
theorem orderedThreeWaveMismatch_decay_eq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) :
    orderedThreeWaveMismatch m decayInteractionSign modes =
      orderedModeFrequency (harmonicHermitian m) (modes 0) -
        orderedModeFrequency (harmonicHermitian m) (modes 1) -
        orderedModeFrequency (harmonicHermitian m) (modes 2) := by
  unfold orderedThreeWaveMismatch decayInteractionSign
  rw [Fin.sum_univ_three]
  simp
  ring

/-- Strictly positive ordered modes of one realization. -/
abbrev PositiveOrderedMode {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) :=
  {k : OrderedModeIndex N // k ∈ orderedPositiveModeIndices m}

/-- Ordered positive triples in exact `(+,-,-)` frequency resonance.  This
finite type is allowed to be empty. -/
def ExactResonantPositiveTriad {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) :=
  {modes : OrderedModeTriple N //
    IsPositiveOrderedTriple m modes ∧
      orderedThreeWaveMismatch m decayInteractionSign modes = 0}

noncomputable instance exactResonantPositiveTriadFintype
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    Fintype (ExactResonantPositiveTriad m) := by
  classical
  exact Fintype.ofFinset
    (Finset.univ.filter fun modes : OrderedModeTriple N =>
      IsPositiveOrderedTriple m modes ∧
        orderedThreeWaveMismatch m decayInteractionSign modes = 0)
    (by
      intro modes
      change
        (modes ∈ Finset.univ.filter (fun x : OrderedModeTriple N =>
          IsPositiveOrderedTriple m x ∧
            orderedThreeWaveMismatch m decayInteractionSign x = 0)) ↔
          IsPositiveOrderedTriple m modes ∧
            orderedThreeWaveMismatch m decayInteractionSign modes = 0
      simp)

/-- Incidence network of all exact positive decay triads. -/
def exactResonanceNetwork {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) :
    Network (PositiveOrderedMode m) (ExactResonantPositiveTriad m) where
  mode₁ := fun a => ⟨a.1 0, a.2.1 0⟩
  mode₂ := fun a => ⟨a.1 1, a.2.1 1⟩
  mode₃ := fun a => ⟨a.1 2, a.2.1 2⟩

/-- Physical ordered frequency on the positive-mode subtype. -/
def positiveOrderedFrequency {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : PositiveOrderedMode m) : Real :=
  orderedModeFrequency (harmonicHermitian m) k.1

/-- Basis-free normalized squared vertex used as the exact-network rate. -/
def exactResonanceRate {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (a : ExactResonantPositiveTriad m) : Real :=
  harmonicOrderedNormalizedInteractionWeight m a.1

/-- Every rate of the exact network is nonnegative. -/
theorem exactResonanceRate_nonneg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (a : ExactResonantPositiveTriad m) :
    0 ≤ exactResonanceRate m a :=
  harmonicOrderedNormalizedInteractionWeight_nonneg m a.1

/-- The subtype proof of zero decay mismatch supplies the additive frequency
resonance required by the abstract finite-network theorem. -/
theorem exactResonanceNetwork_frequency_resonance
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (a : ExactResonantPositiveTriad m) :
    positiveOrderedFrequency m ((exactResonanceNetwork m).mode₁ a) =
      positiveOrderedFrequency m ((exactResonanceNetwork m).mode₂ a) +
      positiveOrderedFrequency m ((exactResonanceNetwork m).mode₃ a) := by
  have hzero := a.2.2
  rw [orderedThreeWaveMismatch_decay_eq] at hzero
  change orderedModeFrequency (harmonicHermitian m) (a.1 0) =
    orderedModeFrequency (harmonicHermitian m) (a.1 1) +
      orderedModeFrequency (harmonicHermitian m) (a.1 2)
  linarith

/-- The actual finite exact-resonance network conserves its ordered harmonic
energy for every supplied action vector. -/
theorem exactResonanceNetwork_totalEnergySlope_eq_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (action : PositiveOrderedMode m → Real) :
    totalEnergySlope (exactResonanceNetwork m)
      (positiveOrderedFrequency m) (exactResonanceRate m) action = 0 :=
  totalEnergySlope_eq_zero_of_resonance
    (exactResonanceNetwork m) (positiveOrderedFrequency m)
    (exactResonanceRate m) action
    (exactResonanceNetwork_frequency_resonance m)

/-- Positive actions give nonnegative total logarithmic-entropy production in
the actual exact-resonance network. -/
theorem exactResonanceNetwork_totalLogEntropyProduction_nonneg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (action : PositiveOrderedMode m → Real)
    (haction : ∀ k, 0 < action k) :
    0 ≤ totalLogEntropyProduction (exactResonanceNetwork m)
      (exactResonanceRate m) action :=
  totalLogEntropyProduction_nonneg
    (exactResonanceNetwork m) (exactResonanceRate m) action
    (exactResonanceRate_nonneg m) haction

/-- Equality of the total entropy production balances every exact triad whose
basis-free interaction weight is strictly positive. -/
theorem exactResonanceNetwork_active_inverseActionBalance
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (action : PositiveOrderedMode m → Real)
    (haction : ∀ k, 0 < action k)
    (hzero : totalLogEntropyProduction (exactResonanceNetwork m)
      (exactResonanceRate m) action = 0)
    (a : ExactResonantPositiveTriad m) (ha_active : 0 < exactResonanceRate m a) :
    inverseActionMismatch
      (action ((exactResonanceNetwork m).mode₁ a))
      (action ((exactResonanceNetwork m).mode₂ a))
      (action ((exactResonanceNetwork m).mode₃ a)) = 0 :=
  inverseActionBalance_of_totalLogEntropyProduction_eq_zero
    (exactResonanceNetwork m) (exactResonanceRate m) action
    (exactResonanceRate_nonneg m) haction hzero a ha_active

/-- Active exact triads are precisely the exact positive resonant triads with
strictly positive basis-free interaction weight.  This type may be empty. -/
def ActiveExactResonantPositiveTriad {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) :=
  {a : ExactResonantPositiveTriad m // 0 < exactResonanceRate m a}

noncomputable instance activeExactResonantPositiveTriadFintype
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    Fintype (ActiveExactResonantPositiveTriad m) := by
  classical
  exact Fintype.ofFinset
    (Finset.univ.filter fun a : ExactResonantPositiveTriad m =>
      0 < exactResonanceRate m a)
    (by
      intro a
      change
        (a ∈ Finset.univ.filter (fun b : ExactResonantPositiveTriad m =>
          0 < exactResonanceRate m b)) ↔ 0 < exactResonanceRate m a
      simp)

/-- The exact-resonance network restricted to active triads. -/
def activeExactResonanceNetwork {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) :
    Network (PositiveOrderedMode m) (ActiveExactResonantPositiveTriad m) where
  mode₁ := fun a => (exactResonanceNetwork m).mode₁ a.1
  mode₂ := fun a => (exactResonanceNetwork m).mode₂ a.1
  mode₃ := fun a => (exactResonanceNetwork m).mode₃ a.1

/-- Rate on the active exact-resonance network. -/
def activeExactResonanceRate {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (a : ActiveExactResonantPositiveTriad m) : Real :=
  exactResonanceRate m a.1

theorem activeExactResonanceRate_pos
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (a : ActiveExactResonantPositiveTriad m) :
    0 < activeExactResonanceRate m a :=
  a.2

theorem activeExactResonanceNetwork_frequency_resonance
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (a : ActiveExactResonantPositiveTriad m) :
    positiveOrderedFrequency m ((activeExactResonanceNetwork m).mode₁ a) =
      positiveOrderedFrequency m ((activeExactResonanceNetwork m).mode₂ a) +
      positiveOrderedFrequency m ((activeExactResonanceNetwork m).mode₃ a) :=
  exactResonanceNetwork_frequency_resonance m a.1

/-- Under the separately supplied active-graph rigidity hypothesis, the
network equality case identifies inverse actions with frequency.  No theorem
here establishes this rigidity for a frozen realization. -/
theorem activeExactResonanceNetwork_entropy_eq_zero_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (action : PositiveOrderedMode m → Real)
    (haction : ∀ k, 0 < action k)
    (hrigid : FrequencyBalanceRigid (activeExactResonanceNetwork m)
      (positiveOrderedFrequency m)) :
    totalLogEntropyProduction (activeExactResonanceNetwork m)
        (activeExactResonanceRate m) action = 0 ↔
      ∃ scale : Real, ∀ k, (action k)⁻¹ =
        scale * positiveOrderedFrequency m k :=
  totalLogEntropyProduction_eq_zero_iff_inverseAction_proportional
    (activeExactResonanceNetwork m) (positiveOrderedFrequency m)
    (activeExactResonanceRate m) action
    (activeExactResonanceNetwork_frequency_resonance m) hrigid
    (activeExactResonanceRate_pos m) haction

end


end ArchonPhysics.RandomMassThreeWaveCollisionNetwork
