import ArchonPhysics.ProbabilityJointLimitDiagonalization

/-!
# Parameterized test-level probability diagonalization

For every fixed positive real parameter `g`, suppose that `X g N` converges
in measure to `target g` as the volume index `N` tends to infinity.  This
module chooses one deterministic volume cutoff at each `g` for the *tested
observable itself*.  Above that cutoff, the probability of an error at least
`g` is smaller than `g`.

Consequently the bad-event probabilities vanish along every
`AdmissibleJointLimit` for the selected cutoff.  This is a test-level
diagonalization.  In particular, it uses no quantitative comparison between
an ambient weak-topology pseudometric and a bounded-Lipschitz error.
-/

namespace ArchonPhysics.ParameterizedTestProbabilityDiagonalization

open ArchonPhysics.QualitativeJointLimitDiagonalization
open ArchonPhysics.ThermalizationTransfer
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega E : Type*} [MeasurableSpace Omega] [PseudoMetricSpace E]

/-- Failure of the parameter-matched approximation at distance tolerance
`g`. -/
def parameterizedTestBadEvent
    (X : Real -> Nat -> Omega -> E)
    (target : Real -> Omega -> E)
    (N : Nat) (g : Real) : Set Omega :=
  {omega | g <= dist (X g N omega) (target g omega)}

/-- At every fixed positive parameter, convergence in measure makes the
probability of the parameter-matched bad event tend to zero with volume. -/
theorem parameterizedTestBadEvent_probability_tendsto_zero
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Real -> Nat -> Omega -> E)
    (target : Real -> Omega -> E)
    (hX : forall g, 0 < g ->
      TendstoInMeasure mu (X g) atTop (target g))
    {g : Real} (hg : 0 < g) :
    Tendsto
      (fun N => mu.real (parameterizedTestBadEvent X target N g))
      atTop (nhds 0) := by
  simpa only [parameterizedTestBadEvent] using
    ((tendstoInMeasure_iff_measureReal_dist.mp (hX g hg)) g hg)

/-- A deterministic volume cutoff selected separately for each positive
real parameter.  Its value at nonpositive parameters is irrelevant. -/
def parameterizedTestSizeCutoff
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Real -> Nat -> Omega -> E)
    (target : Real -> Omega -> E)
    (hX : forall g, 0 < g ->
      TendstoInMeasure mu (X g) atTop (target g)) : Real -> Nat :=
  fun g => if hg : 0 < g then
    vanishingErrorCutoff
      (fun N => mu.real (parameterizedTestBadEvent X target N g))
      (parameterizedTestBadEvent_probability_tendsto_zero
        mu X target hX hg)
      g
  else 0

/-- Above the selected parameter-dependent cutoff, the probability of an
error at least `g` is strictly smaller than `g`. -/
theorem parameterizedTestBadEvent_probability_lt_of_cutoff
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Real -> Nat -> Omega -> E)
    (target : Real -> Omega -> E)
    (hX : forall g, 0 < g ->
      TendstoInMeasure mu (X g) atTop (target g))
    {g : Real} (hg : 0 < g) {N : Nat}
    (hN : parameterizedTestSizeCutoff mu X target hX g <= N) :
    mu.real (parameterizedTestBadEvent X target N g) < g := by
  unfold parameterizedTestSizeCutoff at hN
  rw [dif_pos hg] at hN
  exact error_lt_of_vanishingErrorCutoff
    (fun M => mu.real (parameterizedTestBadEvent X target M g))
    (parameterizedTestBadEvent_probability_tendsto_zero
      mu X target hX hg)
    hg hN

/-- Every path admitted by the selected cutoff eventually has bad-event
probability at most its current coupling. -/
theorem eventually_parameterizedTestBadEvent_probability_le_coupling
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Real -> Nat -> Omega -> E)
    (target : Real -> Omega -> E)
    (hX : forall g, 0 < g ->
      TendstoInMeasure mu (X g) atTop (target g))
    (s : AdmissibleJointLimit
      (parameterizedTestSizeCutoff mu X target hX)) :
    ∀ᶠ j in atTop,
      mu.real (parameterizedTestBadEvent X target
        (s.systemSize j) (s.coupling j)) <= s.coupling j := by
  filter_upwards [s.eventually_sizeCutoff] with j hj
  exact (parameterizedTestBadEvent_probability_lt_of_cutoff
    mu X target hX (s.coupling_pos j) hj).le

/-- The parameter-matched bad-event probabilities vanish along every
admitted weak-coupling/large-volume path. -/
theorem parameterizedTestBadEvent_probability_along_jointLimit_tendsto_zero
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Real -> Nat -> Omega -> E)
    (target : Real -> Omega -> E)
    (hX : forall g, 0 < g ->
      TendstoInMeasure mu (X g) atTop (target g))
    (s : AdmissibleJointLimit
      (parameterizedTestSizeCutoff mu X target hX)) :
    Tendsto
      (fun j => mu.real (parameterizedTestBadEvent X target
        (s.systemSize j) (s.coupling j)))
      atTop (nhds 0) := by
  have hcoupling : Tendsto s.coupling atTop (nhds 0) :=
    s.coupling_tendsto_zero.mono_right inf_le_left
  exact squeeze_zero'
    (Eventually.of_forall fun _j => measureReal_nonneg)
    (eventually_parameterizedTestBadEvent_probability_le_coupling
      mu X target hX s)
    hcoupling

/-- Bundled existence form.  The selected cutoff is qualitative and may
grow arbitrarily fast as `g -> 0`; no uniform-in-parameter rate is claimed. -/
theorem exists_sizeCutoff_for_parameterizedTest_jointLimit
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Real -> Nat -> Omega -> E)
    (target : Real -> Omega -> E)
    (hX : forall g, 0 < g ->
      TendstoInMeasure mu (X g) atTop (target g)) :
    exists sizeCutoff : Real -> Nat,
      forall s : AdmissibleJointLimit sizeCutoff,
        (∀ᶠ j in atTop,
          mu.real (parameterizedTestBadEvent X target
            (s.systemSize j) (s.coupling j)) <= s.coupling j) /\
        Tendsto
          (fun j => mu.real (parameterizedTestBadEvent X target
            (s.systemSize j) (s.coupling j)))
          atTop (nhds 0) := by
  refine ⟨parameterizedTestSizeCutoff mu X target hX, ?_⟩
  intro s
  exact ⟨eventually_parameterizedTestBadEvent_probability_le_coupling
      mu X target hX s,
    parameterizedTestBadEvent_probability_along_jointLimit_tendsto_zero
      mu X target hX s⟩

end

end ArchonPhysics.ParameterizedTestProbabilityDiagonalization
