import ArchonPhysics.ProbabilisticHittingTransfer

/-!
# Real windows as a convergence-in-probability basis in `ENNReal`

At a finite positive target `ENNReal.ofReal a`, symmetric real windows form a
cofinal family of neighborhoods.  This module turns probability-one limits on
all sufficiently small such windows into the general measurable-neighborhood
definition `ThermalizationTransfer.ConvergesInProbabilityTo`.
-/

namespace ArchonPhysics.ENNRealWindowConvergence

open Filter MeasureTheory Set Topology
open ArchonPhysics.ThermalizationTransfer
open ArchonPhysics.ProbabilisticHittingTransfer

noncomputable section

/-- Every neighborhood of a finite positive `ENNReal.ofReal a` contains a
closed window induced by some real `epsilon` with `0 < epsilon < a`. -/
theorem exists_real_Icc_subset_of_mem_nhds
    (a : Real) (ha : 0 < a) {U : Set ENNReal}
    (hU : U ∈ 𝓝 (ENNReal.ofReal a)) :
    ∃ epsilon : Real, 0 < epsilon ∧ epsilon < a ∧
      Icc (ENNReal.ofReal (a - epsilon))
        (ENNReal.ofReal (a + epsilon)) ⊆ U := by
  have htarget_ne_top : ENNReal.ofReal a ≠ ⊤ := ENNReal.ofReal_ne_top
  obtain ⟨radius, hradius_pos, hradius_subset⟩ :=
    (ENNReal.hasBasis_nhds_of_ne_top htarget_ne_top).mem_iff.mp hU
  let finiteRadius : ENNReal := min radius 1
  have hfiniteRadius_pos : 0 < finiteRadius := by
    exact lt_min hradius_pos zero_lt_one
  have hfiniteRadius_ne_top : finiteRadius ≠ ⊤ := by
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right radius 1)
  have hfiniteRadius_le : finiteRadius ≤ radius := min_le_left radius 1
  have hfiniteRadius_toReal_pos : 0 < finiteRadius.toReal :=
    ENNReal.toReal_pos (ne_of_gt hfiniteRadius_pos) hfiniteRadius_ne_top
  let epsilon : Real := min (a / 2) (finiteRadius.toReal / 2)
  have hepsilon_pos : 0 < epsilon := by
    exact lt_min (half_pos ha) (half_pos hfiniteRadius_toReal_pos)
  have hepsilon_lt : epsilon < a := by
    exact (min_le_left _ _).trans_lt (half_lt_self ha)
  have hepsilon_nonneg : 0 ≤ epsilon := le_of_lt hepsilon_pos
  have hepsilon_le_toReal : epsilon ≤ finiteRadius.toReal := by
    exact (min_le_right _ _).trans
      (half_le_self ENNReal.toReal_nonneg)
  have hofReal_epsilon_le_radius :
      ENNReal.ofReal epsilon ≤ radius := by
    exact (ENNReal.ofReal_le_of_le_toReal hepsilon_le_toReal).trans
      hfiniteRadius_le
  refine ⟨epsilon, hepsilon_pos, hepsilon_lt, ?_⟩
  intro y hy
  apply hradius_subset
  constructor
  · calc
      ENNReal.ofReal a - radius ≤
          ENNReal.ofReal a - ENNReal.ofReal epsilon :=
        tsub_le_tsub_left hofReal_epsilon_le_radius _
      _ = ENNReal.ofReal (a - epsilon) :=
        (ENNReal.ofReal_sub a hepsilon_nonneg).symm
      _ ≤ y := hy.1
  · calc
      y ≤ ENNReal.ofReal (a + epsilon) := hy.2
      _ = ENNReal.ofReal a + ENNReal.ofReal epsilon :=
        ENNReal.ofReal_add (le_of_lt ha) hepsilon_nonneg
      _ ≤ ENNReal.ofReal a + radius :=
        add_le_add (le_refl _) hofReal_epsilon_le_radius

/--
Measurable random variables whose probability tends to one on every
sufficiently small real window converge in probability to the finite positive
target.
-/
theorem convergesInProbabilityTo_of_tendsto_real_windows
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P]
    (X : Nat → Omega → ENNReal) (a : Real) (ha : 0 < a)
    (hX_measurable : ∀ j, Measurable (X j))
    (hwindow : ∀ epsilon, 0 < epsilon → epsilon < a →
      Tendsto
        (fun j => P (X j ⁻¹'
          Icc (ENNReal.ofReal (a - epsilon))
            (ENNReal.ofReal (a + epsilon))))
        atTop (nhds 1)) :
    ConvergesInProbabilityTo P X (ENNReal.ofReal a) := by
  refine ⟨hX_measurable, ?_⟩
  intro U _hU_measurable hU
  obtain ⟨epsilon, hepsilon_pos, hepsilon_lt, hsubset⟩ :=
    exists_real_Icc_subset_of_mem_nhds a ha hU
  apply tendsto_measure_superset_atTop_one P
    (fun j => X j ⁻¹'
      Icc (ENNReal.ofReal (a - epsilon))
        (ENNReal.ofReal (a + epsilon)))
    (fun j => X j ⁻¹' U)
    (hwindow epsilon hepsilon_pos hepsilon_lt)
  intro j
  exact preimage_mono hsubset

/--
Full convergence-in-probability corollary for the random stable hitting-time
transfer.  Its inputs remain the robust crossing and the upstream local-error
certificate; no hitting-time convergence conclusion is assumed.
-/
theorem random_local_uniform_error_implies_hitting_time_convergence
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P]
    {limit : Real → Real} (approximation : Nat → Omega → Real → Real)
    (localUniformError : Real → Nat → Omega → ENNReal)
    (delta tauStar : Real)
    (hcross : RobustKineticFirstCrossing limit delta tauStar)
    (herror : ∀ T, 0 < T →
      ConvergesInProbabilityTo P (localUniformError T) 0)
    (hcontrols : ∀ T eta, 0 < T → 0 < eta →
      ∀ n omega,
        localUniformError T n omega < ENNReal.ofReal eta →
          UniformlyCloseOnNonnegativeWindow
            (approximation n omega) limit T eta)
    (hittingTime_measurable : ∀ n, Measurable
      (fun omega => distanceThresholdHittingTime
        (approximation n omega) delta)) :
    ConvergesInProbabilityTo P
      (fun n omega => distanceThresholdHittingTime
        (approximation n omega) delta)
      (ENNReal.ofReal tauStar) := by
  apply convergesInProbabilityTo_of_tendsto_real_windows P
    (fun n omega => distanceThresholdHittingTime
      (approximation n omega) delta)
    tauStar hcross.tauStar_pos hittingTime_measurable
  intro epsilon hepsilon_pos hepsilon_lt
  simpa only [hittingTimeWindowEvent, ENNReal.ofReal] using
    (random_local_uniform_error_implies_hitting_window
      P approximation localUniformError delta tauStar hcross herror hcontrols
      epsilon hepsilon_pos hepsilon_lt)

/-- Joint-limit constructor: real kinetic windows along every admissible path
upgrade to the existing `G2TeqConvergesInProbability` interface. -/
theorem g2TeqConvergesInProbability_of_tendsto_real_windows
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P]
    (equilibrationTime : Nat → Real → Omega → ENNReal)
    (sizeCutoff : Real → Nat) (kineticTime : Real)
    (hkineticTime_pos : 0 < kineticTime)
    (equilibrationTime_measurable :
      ∀ N g, Measurable (equilibrationTime N g))
    (hwindow : ∀ s : AdmissibleJointLimit sizeCutoff,
      ∀ epsilon, 0 < epsilon → epsilon < kineticTime →
        Tendsto
          (fun j => P (scalingWindowEvent equilibrationTime
            (kineticTime - epsilon) (kineticTime + epsilon)
            (s.systemSize j) (s.coupling j)))
          atTop (nhds 1)) :
    G2TeqConvergesInProbability P equilibrationTime
      sizeCutoff kineticTime := by
  refine ⟨hkineticTime_pos, equilibrationTime_measurable, ?_⟩
  intro s
  apply convergesInProbabilityTo_of_tendsto_real_windows P
    (fun j omega => scaledEquilibrationTime equilibrationTime
      (s.systemSize j) (s.coupling j) omega)
    kineticTime hkineticTime_pos
  · intro j
    exact measurable_scaledEquilibrationTime equilibrationTime
      (s.systemSize j) (s.coupling j)
      (equilibrationTime_measurable (s.systemSize j) (s.coupling j))
  · intro epsilon hepsilon_pos hepsilon_lt
    simpa only [scalingWindowEvent] using
      hwindow s epsilon hepsilon_pos hepsilon_lt

end

end ArchonPhysics.ENNRealWindowConvergence
