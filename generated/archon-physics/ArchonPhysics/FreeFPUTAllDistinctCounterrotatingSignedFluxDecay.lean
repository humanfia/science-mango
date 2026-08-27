import ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
import ArchonPhysics.FreeFPUTCounterrotatingFiniteTimeDecay

/-!
# Counterrotating part of the all-distinct signed flux

The exact all-distinct signed-flux sum retains all four input-sign sectors.
This module separates the all-plus counterrotating sector from its complement
on the same canonical representative set.  At fixed positive observed
frequency, its complete finite-volume contribution has an explicit
inverse-time bound.

The static constant below is kept as a literal finite sum.  No uniformity in
the lattice size or acoustic frequency is asserted.
-/

namespace ArchonPhysics.FreeFPUTAllDistinctCounterrotatingSignedFluxDecay

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTCounterrotatingFiniteTimeDecay
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.SignedThreeWaveCollisionFlux

noncomputable section

/-- A quadratic representative belongs to the counterrotating sector when
its complete three-leg collision sign is all plus. -/
def CounterrotatingQuadraticRepresentative
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N) : Prop :=
  quadraticCollisionSign q = counterrotatingThreeWaveSign

private theorem phaseSignToInputInteractionSign_binary_eq_plus_iff
    (sign : Fin 2) :
    phaseSignToInputInteractionSign (binaryPhaseSign sign) = .plus ↔
      sign = 1 := by
  fin_cases sign <;>
    simp [binaryPhaseSign, phaseSignToInputInteractionSign]

/-- In binary phase coordinates, the all-plus sector is exactly the term
with two conjugate input characters. -/
theorem counterrotatingQuadraticRepresentative_iff_signs_one
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N) :
    CounterrotatingQuadraticRepresentative q ↔
      q.2.1 = 1 ∧ q.2.2 = 1 := by
  constructor
  · intro hcounter
    have hcounter' := hcounter
    unfold CounterrotatingQuadraticRepresentative at hcounter'
    have hleft :
        phaseSignToInputInteractionSign (binaryPhaseSign q.2.1) =
          .plus := by
      have hsign := congrFun hcounter' (1 : Fin 3)
      simpa [quadraticCollisionSign, quadraticInputInteractionSign,
        counterrotatingThreeWaveSign] using hsign
    have hright :
        phaseSignToInputInteractionSign (binaryPhaseSign q.2.2) =
          .plus := by
      have hsign := congrFun hcounter' (Fin.succ (1 : Fin 2))
      change phaseSignToInputInteractionSign
        (binaryPhaseSign q.2.2) = .plus at hsign
      exact hsign
    exact ⟨
      (phaseSignToInputInteractionSign_binary_eq_plus_iff q.2.1).1 hleft,
      (phaseSignToInputInteractionSign_binary_eq_plus_iff q.2.2).1 hright⟩
  · rintro ⟨hleft, hright⟩
    unfold CounterrotatingQuadraticRepresentative
    funext r
    fin_cases r
    · rfl
    · change phaseSignToInputInteractionSign
        (binaryPhaseSign q.2.1) = .plus
      rw [hleft]
      rfl
    · change phaseSignToInputInteractionSign
        (binaryPhaseSign q.2.2) = .plus
      rw [hright]
      rfl

/-- Positive all-distinct representatives in the all-plus sector. -/
def positiveAllDistinctCounterrotatingRepresentatives
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) : Finset (QuadraticPhaseTerm N) := by
  classical
  exact (positiveAllDistinctQuadraticSwapRepresentatives m observed).filter
    CounterrotatingQuadraticRepresentative

@[simp] theorem mem_positiveAllDistinctCounterrotatingRepresentatives_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N) :
    q ∈ positiveAllDistinctCounterrotatingRepresentatives m observed ↔
      q ∈ positiveAllDistinctQuadraticSwapRepresentatives m observed ∧
        q.2.1 = 1 ∧ q.2.2 = 1 := by
  classical
  simp [positiveAllDistinctCounterrotatingRepresentatives,
    counterrotatingQuadraticRepresentative_iff_signs_one]

/-- Complementary positive all-distinct representatives. -/
def positiveAllDistinctNoncounterrotatingRepresentatives
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) : Finset (QuadraticPhaseTerm N) := by
  classical
  exact (positiveAllDistinctQuadraticSwapRepresentatives m observed).filter
    fun q ↦ ¬ CounterrotatingQuadraticRepresentative q

/-- The signed-flux summand attached to one canonical representative. -/
def allDistinctRepresentativeSignedFluxTerm
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) : Real :=
  4 * finiteTimeCollisionKernel m kappa
      (quadraticCollisionSign q) time
      (quadraticCollisionModes observed q) *
    quadraticSignedCollisionFlux q
      (modeAction energy (modeFrequency m)) observed

/-- Counterrotating part of the representative signed flux. -/
def allDistinctCounterrotatingSignedFluxSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ q ∈ positiveAllDistinctCounterrotatingRepresentatives m observed,
    allDistinctRepresentativeSignedFluxTerm
      m kappa time energy observed q

/-- Noncounterrotating complement of the representative signed flux. -/
def allDistinctNoncounterrotatingSignedFluxSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ q ∈ positiveAllDistinctNoncounterrotatingRepresentatives m observed,
    allDistinctRepresentativeSignedFluxTerm
      m kappa time energy observed q

/-- Exact partition of the all-distinct signed flux into the all-plus sector
and its complement. -/
theorem allDistinctRepresentativeSignedFluxSum_eq_noncounterrotating_add_counterrotating
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    allDistinctRepresentativeSignedFluxSum
        m kappa time energy observed =
      allDistinctNoncounterrotatingSignedFluxSum
          m kappa time energy observed +
        allDistinctCounterrotatingSignedFluxSum
          m kappa time energy observed := by
  classical
  unfold allDistinctRepresentativeSignedFluxSum
    allDistinctNoncounterrotatingSignedFluxSum
    allDistinctCounterrotatingSignedFluxSum
    positiveAllDistinctNoncounterrotatingRepresentatives
    positiveAllDistinctCounterrotatingRepresentatives
    allDistinctRepresentativeSignedFluxTerm
  simpa only [add_comm] using (Finset.sum_filter_add_sum_filter_not
    (positiveAllDistinctQuadraticSwapRepresentatives m observed)
    CounterrotatingQuadraticRepresentative
    (fun q ↦
      4 * finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q) *
        quadraticSignedCollisionFlux q
          (modeAction energy (modeFrequency m)) observed)).symm

/-- In the all-plus sector the signed collision bracket is a sum of three
nonnegative action products. -/
theorem quadraticSignedCollisionFlux_nonneg_of_counterrotating
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (hcounter : CounterrotatingQuadraticRepresentative q) :
    0 ≤ quadraticSignedCollisionFlux q
      (modeAction energy (modeFrequency m)) observed := by
  have hinput : quadraticInputInteractionSign q = fun _ ↦ .plus := by
    funext r
    have hsign := congrFun hcounter r.succ
    simpa [CounterrotatingQuadraticRepresentative,
      quadraticCollisionSign, counterrotatingThreeWaveSign] using hsign
  rw [quadraticSignedCollisionFlux, hinput,
    signedThreeWaveCollisionFlux_plus_plus]
  have haction (mode : Lattice.Site N) :
      0 ≤ modeAction energy (modeFrequency m) mode :=
    div_nonneg (henergy mode) (modeFrequency_nonneg m mode)
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (haction (q.1 0)) (haction (q.1 1)))
      (mul_nonneg (haction observed) (haction (q.1 1))))
    (mul_nonneg (haction observed) (haction (q.1 0)))

/-- Static finite-volume mass multiplying the universal inverse-time tail
in the counterrotating signed-flux estimate. -/
def allDistinctCounterrotatingStaticFluxMass
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ q ∈ positiveAllDistinctCounterrotatingRepresentatives m observed,
    4 * (kappa ^ 2 *
      normalizedInteractionWeight m (quadraticCollisionModes observed q)) *
      quadraticSignedCollisionFlux q
        (modeAction energy (modeFrequency m)) observed

/-- The complete positive all-distinct counterrotating signed flux is
nonnegative for a nonnegative energy profile. -/
theorem allDistinctCounterrotatingSignedFluxSum_nonneg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (henergy : ∀ mode, 0 ≤ energy mode) :
    0 ≤ allDistinctCounterrotatingSignedFluxSum
      m kappa time energy observed := by
  classical
  unfold allDistinctCounterrotatingSignedFluxSum
    allDistinctRepresentativeSignedFluxTerm
  apply Finset.sum_nonneg
  intro q hq
  exact mul_nonneg
    (mul_nonneg (by norm_num)
      (finiteTimeCollisionKernel_nonneg m kappa
        (quadraticCollisionSign q) time
        (quadraticCollisionModes observed q)))
    (quadraticSignedCollisionFlux_nonneg_of_counterrotating
      m energy observed q henergy (Finset.mem_filter.mp hq).2)

/-- Fixed-volume inverse-time estimate for the entire all-plus branch of the
all-distinct representative signed flux. -/
theorem allDistinctCounterrotatingSignedFluxSum_le_inverseTime
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (homega : 0 < modeFrequency m observed)
    (henergy : ∀ mode, 0 ≤ energy mode) :
    allDistinctCounterrotatingSignedFluxSum
        m kappa time energy observed ≤
      allDistinctCounterrotatingStaticFluxMass
          m kappa energy observed *
        ((2 / modeFrequency m observed) ^ 2 / time) := by
  classical
  unfold allDistinctCounterrotatingSignedFluxSum
    allDistinctCounterrotatingStaticFluxMass
    allDistinctRepresentativeSignedFluxTerm
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro q hq
  have hcounter := (Finset.mem_filter.mp hq).2
  have hflux := quadraticSignedCollisionFlux_nonneg_of_counterrotating
    m energy observed q henergy hcounter
  have hkernel :
      finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q) ≤
        (kappa ^ 2 * normalizedInteractionWeight m
          (quadraticCollisionModes observed q)) *
          ((2 / modeFrequency m observed) ^ 2 / time) := by
    rw [hcounter]
    exact finiteTimeCollisionKernel_counterrotating_le
      m kappa (quadraticCollisionModes observed q) htime homega
  calc
    4 * finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q) *
        quadraticSignedCollisionFlux q
          (modeAction energy (modeFrequency m)) observed =
      finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q) *
        (4 * quadraticSignedCollisionFlux q
          (modeAction energy (modeFrequency m)) observed) := by ring
    _ ≤ ((kappa ^ 2 * normalizedInteractionWeight m
            (quadraticCollisionModes observed q)) *
          ((2 / modeFrequency m observed) ^ 2 / time)) *
        (4 * quadraticSignedCollisionFlux q
          (modeAction energy (modeFrequency m)) observed) :=
      mul_le_mul_of_nonneg_right hkernel (mul_nonneg (by norm_num) hflux)
    _ = (4 * (kappa ^ 2 * normalizedInteractionWeight m
            (quadraticCollisionModes observed q)) *
          quadraticSignedCollisionFlux q
            (modeAction energy (modeFrequency m)) observed) *
        ((2 / modeFrequency m observed) ^ 2 / time) := by ring

/-- Absolute-value form of the same estimate. -/
theorem abs_allDistinctCounterrotatingSignedFluxSum_le_inverseTime
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (homega : 0 < modeFrequency m observed)
    (henergy : ∀ mode, 0 ≤ energy mode) :
    |allDistinctCounterrotatingSignedFluxSum
        m kappa time energy observed| ≤
      allDistinctCounterrotatingStaticFluxMass
          m kappa energy observed *
        ((2 / modeFrequency m observed) ^ 2 / time) := by
  rw [abs_of_nonneg
    (allDistinctCounterrotatingSignedFluxSum_nonneg
      m kappa time energy observed henergy)]
  exact allDistinctCounterrotatingSignedFluxSum_le_inverseTime
    m kappa energy observed htime homega henergy

end

end ArchonPhysics.FreeFPUTAllDistinctCounterrotatingSignedFluxDecay
