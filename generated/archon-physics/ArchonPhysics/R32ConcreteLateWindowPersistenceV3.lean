import ArchonPhysics.CanonicalRandomMassPhaseThermalizationObservable
import ArchonPhysics.GlobalRandomMassModalObservable
import ArchonPhysics.OrderedTranslationLastMode
import ArchonPhysics.R32LateWindowNormalizationStability
import ArchonPhysics.R32ModalEnergyL1Stability
import ArchonPhysics.RandomMassPhaseLateWindowObservable

/-!
# R32: concrete late-window persistence from harmonic-state stability

This Add-only corrected version makes every physical ordered-mode index use
the alias belonging to `RandomMassPositiveLateWindowObservable` and opens the
namespaces which own the harmonic matrix, reduced physical modal energy, and
canonical phase initial sample.  It connects the exact reduced and canonical
late-window observables to the frozen two-band profile.

The deterministic conclusion is

`1 / 8 - (2 / energyFloor) * epsilon <= distance`.

Thus `epsilon <= energyFloor / 32` preserves a gap of at least `1 / 16`.
No hitting-time, persistence-event, probability, kinetic-limit, or
thermalization assertion is introduced here.
-/

namespace ArchonPhysics.R32ConcreteLateWindowPersistenceV3

open Set
open ArchonPhysics
open ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow
open ArchonPhysics.CanonicalRandomMassPhaseThermalizationObservable
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.FiniteModalEnergyL1Stability
open ArchonPhysics.GlobalRandomMassModalObservable
open ArchonPhysics.GlobalReducedParametricFlowAdapter
open ArchonPhysics.LateWindowL1Stability
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedPositiveInitialEnergyProfile
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.ParametricLocalHamiltonianFlow
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPhaseLateWindowObservable
open ArchonPhysics.RandomMassPositiveLateWindowObservable
open ArchonPhysics.RandomMassReducedPhaseInitialData
open ArchonPhysics.R32FrozenEnergyDilution
open ArchonPhysics.R32LateWindowNormalizationStability
open ArchonPhysics.R32ModalEnergyL1Stability
open MeasureTheory

noncomputable section

/-! ## Deterministic frozen-sector identifications -/

/-- The frozen profile vanishes outside the positive sector of every simple
positive-mass harmonic spectrum. -/
theorem frozenTwoBandEnergy_eq_zero_of_not_mem_positive
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (k : ArchonPhysics.RandomMassPositiveLateWindowObservable.OrderedModeIndex N)
    (hk : k ∉ positiveModeIndices (harmonicHermitian m)) :
    frozenTwoBandEnergy N k = 0 := by
  rw [positiveModeIndices_eq_univ_erase_last m hsimple] at hk
  have hlast : k = lastOrderedIndex (ι := Lattice.Site N) := by
    simpa using hk
  subst k
  simp [frozenTwoBandEnergy]

/-- The deterministic positive-uniform profile is exactly the
realization-dependent mask used by the physical reduced observable. -/
theorem frozenPositiveUniformEnergy_eq_positiveModeMask
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m)) :
    frozenPositiveUniformEnergy N =
      fun k :
          ArchonPhysics.RandomMassPositiveLateWindowObservable.OrderedModeIndex N =>
        if k ∈ positiveModeIndices (harmonicHermitian m) then
          ((N - 1 : Nat) : Real)⁻¹
        else 0 := by
  funext k
  symm
  rw [positiveModeIndices_eq_univ_erase_last m hsimple]
  have hlast : orderedModeIndexEquivFin N
      (lastOrderedIndex (ι := Lattice.Site N)) = lastSiteOrderedIndex N := by
    apply Fin.ext
    simp [orderedModeIndexEquivFin, lastOrderedIndex, lastSiteOrderedIndex]
  by_cases hk : k = lastOrderedIndex (ι := Lattice.Site N)
  · subst k
    simp [frozenPositiveUniformEnergy, hlast]
  · simp only [Finset.mem_erase, ne_eq, hk, not_false_eq_true,
      Finset.mem_univ, and_self, if_true]
    unfold frozenPositiveUniformEnergy orderedPositiveUniformWeight
    rw [if_pos]
    have hkval : k.val < Fintype.card (Lattice.Site N) - 1 := by
      have hkne : k.val ≠ Fintype.card (Lattice.Site N) - 1 := by
        intro heq
        apply hk
        apply Fin.ext
        simpa [lastOrderedIndex] using heq
      omega
    simpa [orderedModeIndexEquivFin] using hkval

/-! ## Harmonic-state error to raw late-window error -/

/-- If two modal vectors have common norm ceiling `M` and distance at most
`stateError`, the quadratic state-error expression is at most
`M * stateError`. -/
theorem harmonicStateQuadraticError_le_of_bounds
    {Mode : Type} [Fintype Mode]
    (W Wfree : Mode -> Complex) (M stateError : Real)
    (hM : 0 <= M) (hstateError : 0 <= stateError)
    (hW : phaseSpaceL2Norm W <= M)
    (hWfree : phaseSpaceL2Norm Wfree <= M)
    (hdistance : phaseSpaceL2Distance W Wfree <= stateError) :
    (1 / 2 : Real) * phaseSpaceL2Distance W Wfree *
        (phaseSpaceL2Norm W + phaseSpaceL2Norm Wfree) <=
      M * stateError := by
  have hnorm_nonneg :
      0 <= phaseSpaceL2Norm W + phaseSpaceL2Norm Wfree :=
    add_nonneg (amplitudeL2Norm_nonneg W) (amplitudeL2Norm_nonneg Wfree)
  calc
    (1 / 2 : Real) * phaseSpaceL2Distance W Wfree *
        (phaseSpaceL2Norm W + phaseSpaceL2Norm Wfree) <=
        (1 / 2 : Real) * stateError * (M + M) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hdistance (by norm_num))
        (add_le_add hW hWfree) hnorm_nonneg
        (mul_nonneg (by norm_num) hstateError)
    _ = M * stateError := by ring

/-- Uniform pointwise quadratic harmonic-state control transfers to raw
`l1` closeness of the exact positive-mode late-window profile to the frozen
profile. -/
theorem reducedPositiveLateWindow_raw_close_frozen
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (z zFree : Real -> ReducedPhaseSpace m)
    (mu T epsilon : Real)
    (hmu : 0 <= mu) (hmuOne : mu < 1) (hT : 0 < T)
    (hepsilon : 0 <= epsilon)
    (hExactIntegrable : forall k :
        ArchonPhysics.RandomMassPositiveLateWindowObservable.OrderedModeIndex N,
      IntervalIntegrable
        (fun t => reducedTrajectoryPositiveEnergyProfile m z t k)
        volume (mu * T) T)
    (hFreeEnergy : forall t k,
      reducedPhysicalOrderedModeEnergy m (zFree t) k =
        frozenTwoBandEnergy N k)
    (hState : ∀ t ∈ Icc (mu * T) T,
      (1 / 2 : Real) *
          phaseSpaceL2Distance
            (reducedOrderedHarmonicPhaseVector m (z t))
            (reducedOrderedHarmonicPhaseVector m (zFree t)) *
          (phaseSpaceL2Norm
              (reducedOrderedHarmonicPhaseVector m (z t)) +
            phaseSpaceL2Norm
              (reducedOrderedHarmonicPhaseVector m (zFree t))) <=
        epsilon) :
    l1Distance
        (lateWindowAverage
          (reducedTrajectoryPositiveEnergyProfile m z) mu T)
        (frozenTwoBandEnergy N) <= epsilon := by
  let E : Real ->
      ArchonPhysics.RandomMassPositiveLateWindowObservable.OrderedModeIndex N ->
        Real :=
    reducedTrajectoryPositiveEnergyProfile m z
  let K : Real ->
      ArchonPhysics.RandomMassPositiveLateWindowObservable.OrderedModeIndex N ->
        Real :=
    fun _ => frozenTwoBandEnergy N
  have hpointwise : ∀ t ∈ Icc (mu * T) T,
      l1Distance (E t) (K t) <= epsilon := by
    intro t ht
    have hfull := reducedPhysicalOrderedModeEnergy_l1_le
      m hsimple (z t) (zFree t)
    calc
      l1Distance (E t) (K t) <=
          ∑ k :
              ArchonPhysics.RandomMassPositiveLateWindowObservable.OrderedModeIndex N,
            |reducedPhysicalOrderedModeEnergy m (z t) k -
              reducedPhysicalOrderedModeEnergy m (zFree t) k| := by
        unfold l1Distance
        apply Finset.sum_le_sum
        intro k _hk
        by_cases hkpos : k ∈ positiveModeIndices (harmonicHermitian m)
        · simp [E, K, reducedTrajectoryPositiveEnergyProfile, hkpos,
            hFreeEnergy t k]
        · have hkzero := frozenTwoBandEnergy_eq_zero_of_not_mem_positive
            m hsimple k hkpos
          simp [E, K, reducedTrajectoryPositiveEnergyProfile, hkpos, hkzero]
      _ <= (1 / 2 : Real) *
          phaseSpaceL2Distance
            (reducedOrderedHarmonicPhaseVector m (z t))
            (reducedOrderedHarmonicPhaseVector m (zFree t)) *
          (phaseSpaceL2Norm
              (reducedOrderedHarmonicPhaseVector m (z t)) +
            phaseSpaceL2Norm
              (reducedOrderedHarmonicPhaseVector m (zFree t))) := hfull
      _ <= epsilon := hState t ht
  have hE : forall k :
      ArchonPhysics.RandomMassPositiveLateWindowObservable.OrderedModeIndex N,
      IntervalIntegrable (fun t => E t k) volume (mu * T) T := by
    intro k
    exact hExactIntegrable k
  have hK : forall k :
      ArchonPhysics.RandomMassPositiveLateWindowObservable.OrderedModeIndex N,
      IntervalIntegrable (fun t => K t k) volume (mu * T) T := by
    intro k
    exact intervalIntegrable_const
  have hdiff : forall k :
      ArchonPhysics.RandomMassPositiveLateWindowObservable.OrderedModeIndex N,
      IntervalIntegrable (fun t => |E t k - K t k|)
        volume (mu * T) T := by
    intro k
    exact ((hE k).sub (hK k)).abs
  have hsum : IntervalIntegrable
      (fun t => ∑ k :
        ArchonPhysics.RandomMassPositiveLateWindowObservable.OrderedModeIndex N,
          |E t k - K t k|)
      volume (mu * T) T := by
    let term :
        ArchonPhysics.RandomMassPositiveLateWindowObservable.OrderedModeIndex N →
          ℝ → ℝ := fun k t => |E t k - K t k|
    have hterm (k :
        ArchonPhysics.RandomMassPositiveLateWindowObservable.OrderedModeIndex N) :
        IntervalIntegrable (term k) volume (mu * T) T := by
      exact hdiff k
    have hfinite (s : Finset
        (ArchonPhysics.RandomMassPositiveLateWindowObservable.OrderedModeIndex N)) :
        IntervalIntegrable (fun t => ∑ k ∈ s, term k t)
          volume (mu * T) T := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
          simpa [ha] using (hterm a).add ih
    simpa [term] using hfinite Finset.univ
  have hinterval : mu * T <= T := by
    calc
      mu * T <= 1 * T :=
        mul_le_mul_of_nonneg_right hmuOne.le hT.le
      _ = T := one_mul T
  have hintegrated : windowIntegratedL1Error E K mu T <=
      ((1 - mu) * T) * epsilon := by
    calc
      windowIntegratedL1Error E K mu T =
          ∫ t in mu * T..T,
            ∑ k :
              ArchonPhysics.RandomMassPositiveLateWindowObservable.OrderedModeIndex N,
              |E t k - K t k| := by
        unfold windowIntegratedL1Error
        symm
        exact intervalIntegral.integral_finsetSum
          (fun k _hk => hdiff k)
      _ <= ∫ _t in mu * T..T, epsilon := by
        exact intervalIntegral.integral_mono_on hinterval hsum
          intervalIntegrable_const hpointwise
      _ = ((1 - mu) * T) * epsilon := by
        simp only [intervalIntegral.integral_const, smul_eq_mul]
        ring
  have hraw := l1Distance_lateWindowAverage_le_epsilon
    E K mu T epsilon hmu hmuOne hT hepsilon hE hK hintegrated
  have hconstant : lateWindowAverage K mu T = frozenTwoBandEnergy N := by
    funext k
    unfold lateWindowAverage K
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    have hwindow : (1 - mu) * T ≠ 0 :=
      ne_of_gt (mul_pos (sub_pos.mpr hmuOne) hT)
    rw [show T - mu * T = (1 - mu) * T by ring,
      ← mul_assoc, inv_mul_cancel₀ hwindow, one_mul]
  rw [hconstant] at hraw
  exact hraw

/-! ## Reduced and canonical exact lower bounds -/

/-- Exact reduced physical late-window lower bound with an explicit supplied
denominator floor. -/
theorem reducedTrajectoryPositiveLateWindowL1Distance_lower
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (z zFree : Real -> ReducedPhaseSpace m)
    (mu T energyFloor epsilon : Real)
    (hmu : 0 <= mu) (hmuOne : mu < 1) (hT : 0 < T)
    (hepsilon : 0 <= epsilon) (hfloor : 0 < energyFloor)
    (hExactIntegrable : forall k :
        ArchonPhysics.RandomMassPositiveLateWindowObservable.OrderedModeIndex N,
      IntervalIntegrable
        (fun t => reducedTrajectoryPositiveEnergyProfile m z t k)
        volume (mu * T) T)
    (hFreeEnergy : forall t k,
      reducedPhysicalOrderedModeEnergy m (zFree t) k =
        frozenTwoBandEnergy N k)
    (hState : ∀ t ∈ Icc (mu * T) T,
      (1 / 2 : Real) *
          phaseSpaceL2Distance
            (reducedOrderedHarmonicPhaseVector m (z t))
            (reducedOrderedHarmonicPhaseVector m (zFree t)) *
          (phaseSpaceL2Norm
              (reducedOrderedHarmonicPhaseVector m (z t)) +
            phaseSpaceL2Norm
              (reducedOrderedHarmonicPhaseVector m (zFree t))) <=
        epsilon)
    (hDenominator : energyFloor <=
      totalWeight
        (lateWindowAverage
          (reducedTrajectoryPositiveEnergyProfile m z) mu T)) :
    (1 / 8 : Real) - (2 / energyFloor) * epsilon <=
      reducedTrajectoryPositiveLateWindowL1Distance m z mu T := by
  have hraw := reducedPositiveLateWindow_raw_close_frozen
    hN m hsimple z zFree mu T epsilon hmu hmuOne hT hepsilon
    hExactIntegrable hFreeEnergy hState
  have hlower := normalized_windowProfile_distance_from_uniform_lower
    hN
    (fun _U : Real =>
      lateWindowAverage (reducedTrajectoryPositiveEnergyProfile m z) mu T)
    ({T} : Set Real) energyFloor epsilon hfloor
    (by
      intro _U _hU
      exact hDenominator)
    (by
      intro _U _hU
      exact hraw)
    T (Set.mem_singleton T)
  rw [frozenPositiveUniformEnergy_eq_positiveModeMask m hsimple] at hlower
  simpa [reducedTrajectoryPositiveLateWindowL1Distance] using hlower

/-- Exact canonical wrapper, discharged through the repository's existing
sampled/reduced physical observable equality. -/
theorem canonicalFrozenLateWindowL1Distance_lower
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
          (N := N) omega)))
    (z zFree : Real -> ReducedPhaseSpace
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega))
    (mu T energyFloor epsilon : Real)
    (hmu : 0 <= mu) (hmuOne : mu < 1) (hT : 0 < T)
    (hepsilon : 0 <= epsilon) (hfloor : 0 < energyFloor)
    (hmatch : forall t,
      canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta
          (canonicalPhaseInitialSample
            (N := N) kappa beta g (1 / 4) omega, t) =
        embedReducedPoint
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega) kappa beta g (z t))
    (hExactIntegrable : forall k :
        ArchonPhysics.RandomMassPositiveLateWindowObservable.OrderedModeIndex N,
      IntervalIntegrable
        (fun t => reducedTrajectoryPositiveEnergyProfile
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega) z t k)
        volume (mu * T) T)
    (hFreeEnergy : forall t k,
      reducedPhysicalOrderedModeEnergy
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega) (zFree t) k =
        frozenTwoBandEnergy N k)
    (hState : ∀ t ∈ Icc (mu * T) T,
      (1 / 2 : Real) *
          phaseSpaceL2Distance
            (reducedOrderedHarmonicPhaseVector
              (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
                (N := N) omega) (z t))
            (reducedOrderedHarmonicPhaseVector
              (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
                (N := N) omega) (zFree t)) *
          (phaseSpaceL2Norm
              (reducedOrderedHarmonicPhaseVector
                (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
                  (N := N) omega) (z t)) +
            phaseSpaceL2Norm
              (reducedOrderedHarmonicPhaseVector
                (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
                  (N := N) omega) (zFree t))) <=
        epsilon)
    (hDenominator : energyFloor <=
      totalWeight
        (lateWindowAverage
          (reducedTrajectoryPositiveEnergyProfile
            (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
              (N := N) omega) z) mu T)) :
    (1 / 8 : Real) - (2 / energyFloor) * epsilon <=
      canonicalFrozenLateWindowL1Distance
        (N := N) kappa beta g hbeta (1 / 4) mu T omega := by
  let m := canonicalIIDMassPhaseEnsemble.restrictPositiveMass
    (N := N) omega
  have hlower := reducedTrajectoryPositiveLateWindowL1Distance_lower
    hN m hsimple z zFree mu T energyFloor epsilon hmu hmuOne hT
    hepsilon hfloor hExactIntegrable hFreeEnergy hState hDenominator
  have hobservable :
      canonicalFrozenLateWindowL1Distance
          (N := N) kappa beta g hbeta (1 / 4) mu T omega =
        reducedTrajectoryPositiveLateWindowL1Distance m z mu T := by
    exact sampledPositiveLateWindowL1Distance_eq_reduced_of_match
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
      (canonicalPhaseInitialSample (N := N) kappa beta g (1 / 4))
      (canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta)
      kappa beta g omega z hmatch mu T
  rw [hobservable]
  exact hlower

/-- If `epsilon <= energyFloor / 32`, the exact canonical observable remains
at least `1 / 16` away from positive-mode equipartition. -/
theorem one_sixteenth_le_canonicalFrozenLateWindowL1Distance
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
          (N := N) omega)))
    (z zFree : Real -> ReducedPhaseSpace
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega))
    (mu T energyFloor epsilon : Real)
    (hmu : 0 <= mu) (hmuOne : mu < 1) (hT : 0 < T)
    (hepsilon : 0 <= epsilon) (hfloor : 0 < energyFloor)
    (hmatch : forall t,
      canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta
          (canonicalPhaseInitialSample
            (N := N) kappa beta g (1 / 4) omega, t) =
        embedReducedPoint
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega) kappa beta g (z t))
    (hExactIntegrable : forall k :
        ArchonPhysics.RandomMassPositiveLateWindowObservable.OrderedModeIndex N,
      IntervalIntegrable
        (fun t => reducedTrajectoryPositiveEnergyProfile
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega) z t k)
        volume (mu * T) T)
    (hFreeEnergy : forall t k,
      reducedPhysicalOrderedModeEnergy
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega) (zFree t) k =
        frozenTwoBandEnergy N k)
    (hState : ∀ t ∈ Icc (mu * T) T,
      (1 / 2 : Real) *
          phaseSpaceL2Distance
            (reducedOrderedHarmonicPhaseVector
              (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
                (N := N) omega) (z t))
            (reducedOrderedHarmonicPhaseVector
              (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
                (N := N) omega) (zFree t)) *
          (phaseSpaceL2Norm
              (reducedOrderedHarmonicPhaseVector
                (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
                  (N := N) omega) (z t)) +
            phaseSpaceL2Norm
              (reducedOrderedHarmonicPhaseVector
                (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
                  (N := N) omega) (zFree t))) <=
        epsilon)
    (hDenominator : energyFloor <=
      totalWeight
        (lateWindowAverage
          (reducedTrajectoryPositiveEnergyProfile
            (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
              (N := N) omega) z) mu T))
    (hbudget : epsilon <= energyFloor / 32) :
    (1 / 16 : Real) <=
      canonicalFrozenLateWindowL1Distance
        (N := N) kappa beta g hbeta (1 / 4) mu T omega := by
  have hlower := canonicalFrozenLateWindowL1Distance_lower
    hN kappa beta g hbeta omega hsimple z zFree mu T energyFloor epsilon
    hmu hmuOne hT hepsilon hfloor hmatch hExactIntegrable hFreeEnergy
    hState hDenominator
  have hnormalizedBudget :
      (2 / energyFloor) * epsilon <= (1 / 16 : Real) := by
    calc
      (2 / energyFloor) * epsilon <=
          (2 / energyFloor) * (energyFloor / 32) := by
        exact mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = (1 / 16 : Real) := by
        field_simp [ne_of_gt hfloor]
        norm_num
  linarith

/-! ## Norm-ceiling canonical corollary -/

/-- Distance and common norm bounds imply the exact quadratic state premise
with error `M * stateError`. -/
theorem canonicalFrozenLateWindowL1Distance_lower_of_distance_norm_bounds
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
          (N := N) omega)))
    (z zFree : Real -> ReducedPhaseSpace
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega))
    (mu T energyFloor M stateError : Real)
    (hmu : 0 <= mu) (hmuOne : mu < 1) (hT : 0 < T)
    (hM : 0 <= M) (hstateError : 0 <= stateError)
    (hfloor : 0 < energyFloor)
    (hmatch : forall t,
      canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta
          (canonicalPhaseInitialSample
            (N := N) kappa beta g (1 / 4) omega, t) =
        embedReducedPoint
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega) kappa beta g (z t))
    (hExactIntegrable : forall k :
        ArchonPhysics.RandomMassPositiveLateWindowObservable.OrderedModeIndex N,
      IntervalIntegrable
        (fun t => reducedTrajectoryPositiveEnergyProfile
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega) z t k)
        volume (mu * T) T)
    (hFreeEnergy : forall t k,
      reducedPhysicalOrderedModeEnergy
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega) (zFree t) k =
        frozenTwoBandEnergy N k)
    (hDistance : ∀ t ∈ Icc (mu * T) T,
      phaseSpaceL2Distance
          (reducedOrderedHarmonicPhaseVector
            (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
              (N := N) omega) (z t))
          (reducedOrderedHarmonicPhaseVector
            (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
              (N := N) omega) (zFree t)) <= stateError)
    (hExactNorm : ∀ t ∈ Icc (mu * T) T,
      phaseSpaceL2Norm
        (reducedOrderedHarmonicPhaseVector
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega) (z t)) <= M)
    (hFreeNorm : ∀ t ∈ Icc (mu * T) T,
      phaseSpaceL2Norm
        (reducedOrderedHarmonicPhaseVector
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega) (zFree t)) <= M)
    (hDenominator : energyFloor <=
      totalWeight
        (lateWindowAverage
          (reducedTrajectoryPositiveEnergyProfile
            (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
              (N := N) omega) z) mu T)) :
    (1 / 8 : Real) - (2 / energyFloor) * (M * stateError) <=
      canonicalFrozenLateWindowL1Distance
        (N := N) kappa beta g hbeta (1 / 4) mu T omega := by
  have hState : ∀ t ∈ Icc (mu * T) T,
      (1 / 2 : Real) *
          phaseSpaceL2Distance
            (reducedOrderedHarmonicPhaseVector
              (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
                (N := N) omega) (z t))
            (reducedOrderedHarmonicPhaseVector
              (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
                (N := N) omega) (zFree t)) *
          (phaseSpaceL2Norm
              (reducedOrderedHarmonicPhaseVector
                (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
                  (N := N) omega) (z t)) +
            phaseSpaceL2Norm
              (reducedOrderedHarmonicPhaseVector
                (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
                  (N := N) omega) (zFree t))) <=
        M * stateError := by
    intro t ht
    exact harmonicStateQuadraticError_le_of_bounds
      (reducedOrderedHarmonicPhaseVector
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
          (N := N) omega) (z t))
      (reducedOrderedHarmonicPhaseVector
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
          (N := N) omega) (zFree t))
      M stateError hM hstateError (hExactNorm t ht) (hFreeNorm t ht)
      (hDistance t ht)
  exact canonicalFrozenLateWindowL1Distance_lower
    hN kappa beta g hbeta omega hsimple z zFree mu T energyFloor
    (M * stateError) hmu hmuOne hT (mul_nonneg hM hstateError)
    hfloor hmatch hExactIntegrable hFreeEnergy hState hDenominator

#print axioms frozenPositiveUniformEnergy_eq_positiveModeMask
#print axioms reducedPositiveLateWindow_raw_close_frozen
#print axioms reducedTrajectoryPositiveLateWindowL1Distance_lower
#print axioms canonicalFrozenLateWindowL1Distance_lower
#print axioms one_sixteenth_le_canonicalFrozenLateWindowL1Distance
#print axioms canonicalFrozenLateWindowL1Distance_lower_of_distance_norm_bounds

end

end ArchonPhysics.R32ConcreteLateWindowPersistenceV3
