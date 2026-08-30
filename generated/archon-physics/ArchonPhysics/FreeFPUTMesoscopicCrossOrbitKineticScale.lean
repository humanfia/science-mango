import ArchonPhysics.FreeFPUTCrossOrbitLinearVolumeBound
import ArchonPhysics.NormalizedModalEnergySoftMass

/-!
# Mesoscopic FPUT block scale for the cross-orbit remainder

The deterministic zero-charge cross-orbit estimate is `O(N / T)` relative
to the quadratic kinetic signal.  This module chooses the explicit joint
volume/coupling block length

`T(N,g) = sqrt N / |g|`.

For nonzero `g`, both the kinetic Euler step `g^2 T(N,g)` and the coherence
ratio `N / T(N,g)` are exactly `|g| sqrt N`.  Hence the joint scaling
`|g| sqrt N -> 0` gives a genuine mesoscopic window: one block is short on
the kinetic scale while the cross-swap-orbit coherent contribution is
`o(g^2)` for output modes with a fixed positive frequency floor.

This removes one finite-first-Picard coherence obstruction.  It does not
propagate RPA between blocks, control acoustic output modes, replace the free
orbit by the nonlinear orbit, or identify the thermodynamic collision kernel.
-/

namespace ArchonPhysics.FreeFPUTMesoscopicCrossOrbitKineticScale

open ArchonPhysics
open ArchonPhysics.ActualActiveExactFiniteCollisionModel
open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.FreeFPUTCrossOrbitLinearVolumeBound
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FiniteLogActionEquipartitionControl
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.HardSoftRayleighJeansL1Gluing
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.NormalizedModalEnergySoftMass
open ArchonPhysics.RandomMassPositiveCollisionData
open Filter Topology
open ArchonPhysics.RandomMassPositiveSoftModeFraction
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.SoftSectorL1Control

noncomputable section

/-- Explicit mesoscopic block length between the microscopic and kinetic
time scales. -/
def mesoscopicFPUTBlockTime (N : Nat) (g : Real) : Real :=
  Real.sqrt (N : Real) / |g|

theorem mesoscopicFPUTBlockTime_pos
    {N : Nat} [NeZero N] {g : Real} (hg : g ≠ 0) :
    0 < mesoscopicFPUTBlockTime N g := by
  unfold mesoscopicFPUTBlockTime
  exact div_pos (Real.sqrt_pos.2 (by exact_mod_cast NeZero.pos N))
    (abs_pos.mpr hg)

/-- On the mesoscopic schedule, one quadratic kinetic Euler step is exactly
the joint scale `|g| sqrt N`. -/
theorem couplingSq_mul_mesoscopicFPUTBlockTime
    {N : Nat} [NeZero N] {g : Real} (hg : g ≠ 0) :
    g ^ 2 * mesoscopicFPUTBlockTime N g =
      |g| * Real.sqrt (N : Real) := by
  unfold mesoscopicFPUTBlockTime
  have habs : |g| ≠ 0 := abs_ne_zero.mpr hg
  rw [show g ^ 2 = |g| ^ 2 by exact (sq_abs g).symm]
  field_simp [habs]

/-- On the same schedule, the volume-to-time coherence ratio is the very
same joint scale. -/
theorem volume_div_mesoscopicFPUTBlockTime
    {N : Nat} [NeZero N] {g : Real} (hg : g ≠ 0) :
    (N : Real) / mesoscopicFPUTBlockTime N g =
      |g| * Real.sqrt (N : Real) := by
  unfold mesoscopicFPUTBlockTime
  have habs : |g| ≠ 0 := abs_ne_zero.mpr hg
  have hsqrt : Real.sqrt (N : Real) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast NeZero.pos N))
  field_simp [habs, hsqrt]
  rw [Real.sq_sqrt (by positivity : (0 : Real) ≤ N)]

/-- Finite-volume physical form: after division by the natural quadratic
coupling factor, the cross-orbit remainder on the mesoscopic block is bounded
by the joint scale `|g| sqrt N`, with the acoustic output frequency kept
explicit. -/
theorem normalized_crossOrbit_le_mesoscopicJointScale
    {N : Nat} [NeZero N]
    (kappa g : Real) (hkappa : kappa ≠ 0) (hg : g ≠ 0)
    (m : Lattice.PositiveMassConfig N)
    (q : OrderedModeIndex N) (energy : Lattice.Site N → Real)
    (energyBound : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (henergyBoundNonneg : 0 ≤ energyBound)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (henergyBound : ∀ mode, energy mode ≤ energyBound)
    (hfrequency : 0 < orderedModeFrequency (harmonicHermitian m) q) :
    |(freeQuadraticCrossSwapOrbitCoherentRemainder
        (physicalQuadraticCoupling kappa g m (orderedIndexEquiv q))
        m (orderedIndexEquiv q)
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
        (mesoscopicFPUTBlockTime N g)).re| / (kappa * g) ^ 2 ≤
      (2 * energyBound ^ 2 /
          orderedModeFrequency (harmonicHermitian m) q) *
        (|g| * Real.sqrt (N : Real)) := by
  have htime : 0 < mesoscopicFPUTBlockTime N g :=
    mesoscopicFPUTBlockTime_pos hg
  have hmain := abs_re_physical_crossOrbit_le_energy_linearVolume
    kappa g m q energy energyBound hsimple henergyBoundNonneg
      henergy henergyBound hfrequency htime
  have hcouplingSq : 0 < (kappa * g) ^ 2 :=
    sq_pos_of_ne_zero (mul_ne_zero hkappa hg)
  apply (div_le_iff₀ hcouplingSq).2
  calc
    |(freeQuadraticCrossSwapOrbitCoherentRemainder
        (physicalQuadraticCoupling kappa g m (orderedIndexEquiv q))
        m (orderedIndexEquiv q)
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
        (mesoscopicFPUTBlockTime N g)).re| ≤
        2 * (N : Real) * (kappa * g) ^ 2 * energyBound ^ 2 /
          (orderedModeFrequency (harmonicHermitian m) q *
            mesoscopicFPUTBlockTime N g) := hmain
    _ = ((2 * energyBound ^ 2 /
          orderedModeFrequency (harmonicHermitian m) q) *
        (|g| * Real.sqrt (N : Real))) * (kappa * g) ^ 2 := by
      rw [← volume_div_mesoscopicFPUTBlockTime hg]
      field_simp [hfrequency.ne', htime.ne']

/-- Varying-volume hard-mode conclusion.  If `|g_N| sqrt N -> 0`, then the
mesoscopic cross-orbit remainder is `o((kappa*g_N)^2)`. -/
theorem normalized_crossOrbit_tendsto_zero_at_mesoscopicScale
    (N : Nat → Nat) [hN : ∀ n, NeZero (N n)]
    (kappa : Real) (hkappa : kappa ≠ 0)
    (g : Nat → Real) (hg : ∀ n, g n ≠ 0)
    (m : ∀ n, Lattice.PositiveMassConfig (N n))
    (q : ∀ n, OrderedModeIndex (N n))
    (energy : ∀ n, Lattice.Site (N n) → Real)
    (energyBound frequencyLower : Real)
    (henergyBoundNonneg : 0 ≤ energyBound)
    (hfrequencyLower : 0 < frequencyLower)
    (hsimple : ∀ n, SimpleOrderedSpectrum (harmonicHermitian (m n)))
    (henergy : ∀ n mode, 0 ≤ energy n mode)
    (henergyBound : ∀ n mode, energy n mode ≤ energyBound)
    (hfrequency : ∀ n, frequencyLower ≤
      orderedModeFrequency (harmonicHermitian (m n)) (q n))
    (hjoint : Tendsto
      (fun n ↦ |g n| * Real.sqrt (N n : Real)) atTop (nhds 0)) :
    Tendsto
      (fun n ↦
        |(freeQuadraticCrossSwapOrbitCoherentRemainder
            (physicalQuadraticCoupling kappa (g n) (m n)
              (orderedIndexEquiv (q n)))
            (m n) (orderedIndexEquiv (q n))
            (phaseEnergyRadius (energy n) (modeFrequency (m n)))
            (modeFrequency (m n))
            (mesoscopicFPUTBlockTime (N n) (g n))).re| /
          (kappa * g n) ^ 2)
      atTop (nhds 0) := by
  let C : Real := 2 * energyBound ^ 2 / frequencyLower
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  apply squeeze_zero
    (g := fun n => C * (|g n| * Real.sqrt (N n : Real)))
  · intro n
    positivity
  · intro n
    have hfreqPos : 0 <
        orderedModeFrequency (harmonicHermitian (m n)) (q n) :=
      hfrequencyLower.trans_le (hfrequency n)
    have hbase := normalized_crossOrbit_le_mesoscopicJointScale
      kappa (g n) hkappa (hg n) (m n) (q n) (energy n) energyBound
      (hsimple n) henergyBoundNonneg (henergy n) (henergyBound n) hfreqPos
    refine hbase.trans ?_
    apply mul_le_mul_of_nonneg_right ?_
      (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
    apply div_le_div_of_nonneg_left (by positivity)
    · exact hfrequencyLower
    · exact hfrequency n
  · simpa [C] using (tendsto_const_nhds.mul hjoint)

/-! ## Hard/soft all-mode bridge -/

/-- The hard positive-mode cross-orbit budget, averaged by the number of all
positive modes.  Averaging by the full positive-mode count is the
normalization appropriate for an all-mode `L1` error. -/
def positiveOrderedHardMeanNormalizedCrossOrbitRemainder
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (energy : Lattice.Site N → Real) (cutoff : Real) : Real :=
  sectorWeight
      (Finset.univ \ positiveOrderedSoftFrequencySector m cutoff)
      (fun q : PositiveOrderedMode m ↦
        |(freeQuadraticCrossSwapOrbitCoherentRemainder
            (physicalQuadraticCoupling kappa g m
              (orderedIndexEquiv q.1))
            m (orderedIndexEquiv q.1)
            (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
            (mesoscopicFPUTBlockTime N g)).re| / (kappa * g) ^ 2) /
    (Fintype.card (PositiveOrderedMode m) : Real)

/-- Every output in the hard complement has frequency at least `cutoff`.
Consequently the full-mode mean of the proved cross-orbit remainders costs
only `1 / cutoff`; no uniform acoustic gap is assumed. -/
theorem positiveOrderedHardMeanNormalizedCrossOrbitRemainder_le
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (kappa g : Real) (hkappa : kappa ≠ 0) (hg : g ≠ 0)
    (m : Lattice.PositiveMassConfig N)
    (energy : Lattice.Site N → Real) (energyBound cutoff : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (henergyBoundNonneg : 0 ≤ energyBound)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (henergyBound : ∀ mode, energy mode ≤ energyBound)
    (hcutoff : 0 < cutoff) :
    positiveOrderedHardMeanNormalizedCrossOrbitRemainder
        kappa g m energy cutoff ≤
      (2 * energyBound ^ 2 / cutoff) *
        (|g| * Real.sqrt (N : Real)) := by
  classical
  let hard := Finset.univ \ positiveOrderedSoftFrequencySector m cutoff
  let remainder : PositiveOrderedMode m → Real := fun q ↦
    |(freeQuadraticCrossSwapOrbitCoherentRemainder
        (physicalQuadraticCoupling kappa g m (orderedIndexEquiv q.1))
        m (orderedIndexEquiv q.1)
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
        (mesoscopicFPUTBlockTime N g)).re| / (kappa * g) ^ 2
  let bound := (2 * energyBound ^ 2 / cutoff) *
    (|g| * Real.sqrt (N : Real))
  have hcardNat : 0 < Fintype.card (PositiveOrderedMode m) := by
    rw [card_positiveOrderedMode_eq_sub_one m hsimple]
    omega
  have hcard : 0 < (Fintype.card (PositiveOrderedMode m) : Real) := by
    exact_mod_cast hcardNat
  have hboundNonneg : 0 ≤ bound := by
    dsimp [bound]
    positivity
  have hpoint : ∀ q ∈ hard, remainder q ≤ bound := by
    intro q hq
    have hqNotSoft : q ∉ positiveOrderedSoftFrequencySector m cutoff :=
      (Finset.mem_sdiff.mp hq).2
    have hfrequencyCutoff : cutoff ≤ positiveOrderedFrequency m q := by
      simpa [positiveOrderedSoftFrequencySector] using hqNotSoft
    have hfrequencyPos : 0 <
        orderedModeFrequency (harmonicHermitian m) q.1 := by
      exact positiveOrderedFrequency_pos m q
    have hbase := normalized_crossOrbit_le_mesoscopicJointScale
      kappa g hkappa hg m q.1 energy energyBound hsimple
        henergyBoundNonneg henergy henergyBound hfrequencyPos
    change remainder q ≤ bound
    refine hbase.trans ?_
    dsimp [bound]
    apply mul_le_mul_of_nonneg_right ?_
      (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
    apply div_le_div_of_nonneg_left (by positivity)
    · exact hcutoff
    · exact hfrequencyCutoff
  have hsum : sectorWeight hard remainder ≤ (hard.card : Real) * bound := by
    unfold sectorWeight
    calc
      (∑ q ∈ hard, remainder q) ≤ ∑ _q ∈ hard, bound :=
        Finset.sum_le_sum hpoint
      _ = (hard.card : Real) * bound := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have hhardCard : (hard.card : Real) ≤
      (Fintype.card (PositiveOrderedMode m) : Real) := by
    exact_mod_cast Finset.card_le_univ hard
  unfold positiveOrderedHardMeanNormalizedCrossOrbitRemainder
  change sectorWeight hard remainder /
      (Fintype.card (PositiveOrderedMode m) : Real) ≤ bound
  calc
    sectorWeight hard remainder /
        (Fintype.card (PositiveOrderedMode m) : Real) ≤
        ((hard.card : Real) * bound) /
          (Fintype.card (PositiveOrderedMode m) : Real) :=
      div_le_div_of_nonneg_right hsum hcard.le
    _ ≤ ((Fintype.card (PositiveOrderedMode m) : Real) * bound) /
          (Fintype.card (PositiveOrderedMode m) : Real) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hhardCard hboundNonneg) hcard.le
    _ = bound := by field_simp [ne_of_gt hcard]


/-- Finite hard/soft gluing with every proved error displayed explicitly.

The hypothesis `hhardDeficitComparison` is intentionally not discharged here:
it is the still-missing dynamical statement comparing the hard-sector
Rayleigh--Jeans deficit of `action` with the averaged free cross-orbit
remainder built from `energy`.  Everything after that comparison is a
deterministic consequence of the proved hard remainder, soft energy-mass,
soft mode-count, and hard/soft normalization estimates. -/
theorem positiveOrdered_l1Distance_uniform_le_mesoscopicBudget_of_hardDeficitComparison
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N) (omega : Omega)
    (kappa g : Real) (hkappa : kappa ≠ 0) (hg : g ≠ 0)
    (action : PositiveOrderedMode
      (ensemble.restrictPositiveMass (N := N) omega) → Real)
    (energy : Lattice.Site N → Real)
    (energyBound cutoff radius energyPerModeFloor : Real)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega)))
    (hcutoff : 0 < cutoff) (hcutoffOne : cutoff ≤ 1)
    (hradius : 0 ≤ radius)
    (henergyPerModeFloor : 0 < energyPerModeFloor)
    (henergyBoundNonneg : 0 ≤ energyBound)
    (haction : ∀ i, 0 ≤ action i ∧ action i ≤ radius)
    (htotalEnergy :
      energyPerModeFloor *
          (Fintype.card (PositiveOrderedMode
            (ensemble.restrictPositiveMass (N := N) omega)) : Real) ≤
        totalWeight (fun i =>
          positiveOrderedFrequency
              (ensemble.restrictPositiveMass (N := N) omega) i * action i))
    (henergy : ∀ mode, 0 ≤ energy mode)
    (henergyBound : ∀ mode, energy mode ≤ energyBound)
    (hhard :
      (Finset.univ \ positiveOrderedSoftFrequencySector
        (ensemble.restrictPositiveMass (N := N) omega) cutoff).Nonempty)
    (hhardMass : 0 <
      sectorWeight
        (Finset.univ \ positiveOrderedSoftFrequencySector
          (ensemble.restrictPositiveMass (N := N) omega) cutoff)
        (normalizedModalEnergyWeights
          (positiveOrderedFrequency
            (ensemble.restrictPositiveMass (N := N) omega)) action))
    (hhardDeficitComparison :
      normalizedSectorL1Deficit
          (Finset.univ \ positiveOrderedSoftFrequencySector
            (ensemble.restrictPositiveMass (N := N) omega) cutoff)
          (normalizedModalEnergyWeights
            (positiveOrderedFrequency
              (ensemble.restrictPositiveMass (N := N) omega)) action) ≤
        positiveOrderedHardMeanNormalizedCrossOrbitRemainder
          kappa g (ensemble.restrictPositiveMass (N := N) omega)
            energy cutoff) :
    l1Distance
        (normalizedModalEnergyWeights
          (positiveOrderedFrequency
            (ensemble.restrictPositiveMass (N := N) omega)) action)
        (uniformWeights : PositiveOrderedMode
          (ensemble.restrictPositiveMass (N := N) omega) → Real) ≤
      (2 * energyBound ^ 2) *
          ((|g| * Real.sqrt (N : Real)) / cutoff) +
        ((2 * radius / energyPerModeFloor) * cutoff ^ 2 + 2 * cutoff) +
        ((2 * radius / energyPerModeFloor) * cutoff ^ 2 + 2 * cutoff) := by
  classical
  let m := ensemble.restrictPositiveMass (N := N) omega
  let soft := positiveOrderedSoftFrequencySector m cutoff
  let hard := Finset.univ \ soft
  let profile :=
    normalizedModalEnergyWeights (positiveOrderedFrequency m) action
  have hcardNat : 0 < Fintype.card (PositiveOrderedMode m) := by
    rw [card_positiveOrderedMode_eq_sub_one m hsimple]
    omega
  have hcard : 0 < (Fintype.card (PositiveOrderedMode m) : Real) := by
    exact_mod_cast hcardNat
  let _ : Nonempty (PositiveOrderedMode m) :=
    Fintype.card_pos_iff.mp hcardNat
  have htotalPositive : 0 <
      totalWeight (fun i => positiveOrderedFrequency m i * action i) :=
    (mul_pos henergyPerModeFloor hcard).trans_le htotalEnergy
  have hprofileNonnegative : ∀ i, 0 ≤ profile i := by
    intro i
    dsimp [profile, normalizedModalEnergyWeights, normalizedWeights]
    exact div_nonneg
      (mul_nonneg (positiveOrderedFrequency_pos m i).le (haction i).1)
      htotalPositive.le
  have hprofileTotal : totalWeight profile = 1 := by
    simpa [profile, normalizedModalEnergyWeights, totalWeight] using
      (sum_normalizedWeights
        (fun i => positiveOrderedFrequency m i * action i) htotalPositive)
  have hhard' : hard.Nonempty := by
    simpa [hard, soft, m] using hhard
  have hhardMass' : 0 < sectorWeight hard profile := by
    simpa [hard, soft, profile, m] using hhardMass
  have hbase :=
    l1Distance_uniform_le_hardNormalized_add_two_soft
      soft profile hprofileNonnegative hprofileTotal hhard' hhardMass'
  have hmean :
      positiveOrderedHardMeanNormalizedCrossOrbitRemainder
          kappa g m energy cutoff ≤
        (2 * energyBound ^ 2 / cutoff) *
          (|g| * Real.sqrt (N : Real)) :=
    positiveOrderedHardMeanNormalizedCrossOrbitRemainder_le
      hN kappa g hkappa hg m energy energyBound cutoff hsimple
        henergyBoundNonneg henergy henergyBound hcutoff
  have hhardDeficit :
      normalizedSectorL1Deficit hard profile ≤
        (2 * energyBound ^ 2) *
          ((|g| * Real.sqrt (N : Real)) / cutoff) := by
    have hcomparison :
        normalizedSectorL1Deficit hard profile ≤
          positiveOrderedHardMeanNormalizedCrossOrbitRemainder
            kappa g m energy cutoff := by
      simpa [hard, soft, profile, m] using hhardDeficitComparison
    calc
      normalizedSectorL1Deficit hard profile ≤
          positiveOrderedHardMeanNormalizedCrossOrbitRemainder
            kappa g m energy cutoff := hcomparison
      _ ≤ (2 * energyBound ^ 2 / cutoff) *
          (|g| * Real.sqrt (N : Real)) := hmean
      _ = (2 * energyBound ^ 2) *
          ((|g| * Real.sqrt (N : Real)) / cutoff) := by ring
  have hsoftMass :
      sectorWeight soft profile ≤
        (2 * radius / energyPerModeFloor) * cutoff ^ 2 := by
    simpa [soft, profile, m] using
      positiveOrderedSoft_normalizedModalEnergyWeight_le_two_mul_sq
        ensemble hN omega hsimple action hcutoff hcutoffOne hradius
          henergyPerModeFloor haction htotalEnergy
  have hsoftFraction :
      (soft.card : Real) /
          (Fintype.card (PositiveOrderedMode m) : Real) ≤
        2 * cutoff := by
    simpa [soft, m] using
      positiveOrderedSoftFrequencySector_card_div_positiveModes_le_two_mul
        ensemble hN omega hsimple hcutoff hcutoffOne
  change l1Distance profile
      (uniformWeights : PositiveOrderedMode m → Real) ≤ _
  calc
    l1Distance profile
        (uniformWeights : PositiveOrderedMode m → Real) ≤
      normalizedSectorL1Deficit hard profile +
        (sectorWeight soft profile +
          (soft.card : Real) /
            (Fintype.card (PositiveOrderedMode m) : Real)) +
        (sectorWeight soft profile +
          (soft.card : Real) /
            (Fintype.card (PositiveOrderedMode m) : Real)) := by
      simpa [hard] using hbase
    _ ≤ (2 * energyBound ^ 2) *
          ((|g| * Real.sqrt (N : Real)) / cutoff) +
        ((2 * radius / energyPerModeFloor) * cutoff ^ 2 + 2 * cutoff) +
        ((2 * radius / energyPerModeFloor) * cutoff ^ 2 + 2 * cutoff) := by
      gcongr


/-- Conditional all-mode thermodynamic conclusion at a shrinking acoustic
cutoff.  The proved error budget vanishes under
`cutoff_n → 0` and `(|g_n| * sqrt N_n) / cutoff_n → 0`.

The pointwise hypotheses `hhardDeficitComparison` remain the missing
dynamical bridge; this theorem only consumes them and does not assert
hard-band relaxation, nonlinear/free-orbit replacement, or inter-block RPA
propagation. -/
theorem positiveOrdered_l1Distance_tendsto_zero_of_hardDeficitComparison_and_jointScaling
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (N : Nat → Nat) [hNzero : ∀ n, NeZero (N n)]
    (hN : ∀ n, 2 ≤ N n)
    (kappa : Real) (hkappa : kappa ≠ 0)
    (g : Nat → Real) (hg : ∀ n, g n ≠ 0)
    (action : ∀ n, PositiveOrderedMode
      (ensemble.restrictPositiveMass (N := N n) omega) → Real)
    (energy : ∀ n, Lattice.Site (N n) → Real)
    (energyBound radius energyPerModeFloor : Real)
    (henergyBoundNonneg : 0 ≤ energyBound)
    (hradius : 0 ≤ radius)
    (henergyPerModeFloor : 0 < energyPerModeFloor)
    (cutoff : Nat → Real)
    (hcutoff : ∀ n, 0 < cutoff n)
    (hcutoffOne : ∀ n, cutoff n ≤ 1)
    (hsimple : ∀ n, SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := N n) omega)))
    (haction : ∀ n i, 0 ≤ action n i ∧ action n i ≤ radius)
    (htotalEnergy : ∀ n,
      energyPerModeFloor *
          (Fintype.card (PositiveOrderedMode
            (ensemble.restrictPositiveMass (N := N n) omega)) : Real) ≤
        totalWeight (fun i =>
          positiveOrderedFrequency
              (ensemble.restrictPositiveMass (N := N n) omega) i *
            action n i))
    (henergy : ∀ n mode, 0 ≤ energy n mode)
    (henergyBound : ∀ n mode, energy n mode ≤ energyBound)
    (hhard : ∀ n,
      (Finset.univ \ positiveOrderedSoftFrequencySector
        (ensemble.restrictPositiveMass (N := N n) omega)
          (cutoff n)).Nonempty)
    (hhardMass : ∀ n, 0 <
      sectorWeight
        (Finset.univ \ positiveOrderedSoftFrequencySector
          (ensemble.restrictPositiveMass (N := N n) omega) (cutoff n))
        (normalizedModalEnergyWeights
          (positiveOrderedFrequency
            (ensemble.restrictPositiveMass (N := N n) omega))
          (action n)))
    (hhardDeficitComparison : ∀ n,
      normalizedSectorL1Deficit
          (Finset.univ \ positiveOrderedSoftFrequencySector
            (ensemble.restrictPositiveMass (N := N n) omega) (cutoff n))
          (normalizedModalEnergyWeights
            (positiveOrderedFrequency
              (ensemble.restrictPositiveMass (N := N n) omega))
            (action n)) ≤
        positiveOrderedHardMeanNormalizedCrossOrbitRemainder
          kappa (g n)
            (ensemble.restrictPositiveMass (N := N n) omega)
            (energy n) (cutoff n))
    (hcutoffZero : Tendsto cutoff atTop (nhds 0))
    (hjointOverCutoff : Tendsto
      (fun n ↦
        (|g n| * Real.sqrt (N n : Real)) / cutoff n)
      atTop (nhds 0)) :
    Tendsto
      (fun n ↦
        l1Distance
          (normalizedModalEnergyWeights
            (positiveOrderedFrequency
              (ensemble.restrictPositiveMass (N := N n) omega))
            (action n))
          (uniformWeights : PositiveOrderedMode
            (ensemble.restrictPositiveMass (N := N n) omega) → Real))
      atTop (nhds 0) := by
  apply squeeze_zero
    (g := fun n ↦
      (2 * energyBound ^ 2) *
          ((|g n| * Real.sqrt (N n : Real)) / cutoff n) +
        ((2 * radius / energyPerModeFloor) * cutoff n ^ 2 +
          2 * cutoff n) +
        ((2 * radius / energyPerModeFloor) * cutoff n ^ 2 +
          2 * cutoff n))
  · intro n
    unfold l1Distance
    exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  · intro n
    exact
      positiveOrdered_l1Distance_uniform_le_mesoscopicBudget_of_hardDeficitComparison
        ensemble (hN n) omega kappa (g n) hkappa (hg n)
          (action n) (energy n) energyBound (cutoff n) radius
          energyPerModeFloor (hsimple n) (hcutoff n) (hcutoffOne n)
          hradius henergyPerModeFloor henergyBoundNonneg (haction n)
          (htotalEnergy n) (henergy n) (henergyBound n) (hhard n)
          (hhardMass n) (hhardDeficitComparison n)
  · have hhardZero : Tendsto
        (fun n ↦
          (2 * energyBound ^ 2) *
            ((|g n| * Real.sqrt (N n : Real)) / cutoff n))
        atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hjointOverCutoff)
    have hsoftMassZero : Tendsto
        (fun n ↦
          (2 * radius / energyPerModeFloor) * cutoff n ^ 2)
        atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul (hcutoffZero.pow 2))
    have hsoftFractionZero : Tendsto
        (fun n ↦ 2 * cutoff n) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hcutoffZero)
    have hsoftZero : Tendsto
        (fun n ↦
          (2 * radius / energyPerModeFloor) * cutoff n ^ 2 +
            2 * cutoff n)
        atTop (nhds 0) := by
      simpa using hsoftMassZero.add hsoftFractionZero
    simpa only [add_zero] using (hhardZero.add hsoftZero).add hsoftZero
end

end ArchonPhysics.FreeFPUTMesoscopicCrossOrbitKineticScale
