import ArchonPhysics.ThermalizationTransfer

/-!
# Qualitative joint-limit diagonalization

A qualitative thermodynamic error `error N -> 0` is enough to absorb an
arbitrarily large nonnegative weak-coupling amplification.  At each positive
coupling `g`, choose the volume cutoff after which

`error N < g / (amplification g + 1)`.

Every joint limit admitted by this cutoff then satisfies
`amplification g * error N <= g` eventually.  No convergence rate for the
thermodynamic error and no boundedness of the amplification are required.
-/

namespace ArchonPhysics.QualitativeJointLimitDiagonalization

open ArchonPhysics.ThermalizationTransfer
open Filter Set Topology

noncomputable section

private theorem exists_tailCutoff
    (error : Nat -> Real)
    (herror : Tendsto error atTop (nhds 0))
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    exists cutoff : Nat, forall N, cutoff <= N -> error N < epsilon := by
  have heventually : ∀ᶠ N in atTop, error N < epsilon :=
    herror.eventually (Iio_mem_nhds hepsilon)
  exact eventually_atTop.1 heventually

/-- A concrete tail index for a positive tolerance.  At nonpositive
tolerances its value is irrelevant and is fixed to zero. -/
def vanishingErrorCutoff
    (error : Nat -> Real)
    (herror : Tendsto error atTop (nhds 0))
    (epsilon : Real) : Nat :=
  if hepsilon : 0 < epsilon then
    Classical.choose (exists_tailCutoff error herror hepsilon)
  else 0

theorem error_lt_of_vanishingErrorCutoff
    (error : Nat -> Real)
    (herror : Tendsto error atTop (nhds 0))
    {epsilon : Real} (hepsilon : 0 < epsilon)
    {N : Nat} (hN : vanishingErrorCutoff error herror epsilon <= N) :
    error N < epsilon := by
  unfold vanishingErrorCutoff at hN
  rw [dif_pos hepsilon] at hN
  exact (Classical.choose_spec
    (exists_tailCutoff error herror hepsilon)) N hN

/-- The pointwise diagonal cutoff.  It depends on the requested coupling but
requires no monotonicity or boundedness of `amplification`. -/
def qualitativeJointSizeCutoff
    (error : Nat -> Real) (amplification : Real -> Real)
    (herror : Tendsto error atTop (nhds 0)) : Real -> Nat :=
  fun g => vanishingErrorCutoff error herror
    (g / (amplification g + 1))

/-- Above the diagonal cutoff, a nonnegative amplification of the error is
bounded by the positive coupling itself. -/
theorem amplification_mul_error_le_coupling_of_cutoff
    (error : Nat -> Real) (amplification : Real -> Real)
    (herror : Tendsto error atTop (nhds 0))
    (hamplification : forall g, 0 <= amplification g)
    {g : Real} (hg : 0 < g) {N : Nat}
    (hN : qualitativeJointSizeCutoff error amplification herror g <= N) :
    amplification g * error N <= g := by
  have hdenominator : 0 < amplification g + 1 := by
    linarith [hamplification g]
  have htolerance : 0 < g / (amplification g + 1) :=
    div_pos hg hdenominator
  have herrorBound : error N < g / (amplification g + 1) := by
    exact error_lt_of_vanishingErrorCutoff error herror htolerance hN
  calc
    amplification g * error N <=
        amplification g * (g / (amplification g + 1)) :=
      mul_le_mul_of_nonneg_left (le_of_lt herrorBound) (hamplification g)
    _ = (amplification g * g) / (amplification g + 1) := by ring
    _ <= g := by
      rw [div_le_iff₀ hdenominator]
      nlinarith [hamplification g, hg]

/-- Every path admitted by the diagonal cutoff eventually obeys the desired
amplified-error estimate. -/
theorem eventually_amplification_mul_error_le_coupling
    (error : Nat -> Real) (amplification : Real -> Real)
    (herror : Tendsto error atTop (nhds 0))
    (hamplification : forall g, 0 <= amplification g)
    (s : AdmissibleJointLimit
      (qualitativeJointSizeCutoff error amplification herror)) :
    ∀ᶠ j in atTop,
      amplification (s.coupling j) * error (s.systemSize j) <=
        s.coupling j := by
  filter_upwards [s.eventually_sizeCutoff] with j hj
  exact amplification_mul_error_le_coupling_of_cutoff
    error amplification herror hamplification (s.coupling_pos j) hj

/-- The original qualitative thermodynamic error still tends to zero along
every admissible joint path because its system size tends to infinity. -/
theorem error_along_admissibleJointLimit_tendsto_zero
    (error : Nat -> Real) (amplification : Real -> Real)
    (herror : Tendsto error atTop (nhds 0))
    (s : AdmissibleJointLimit
      (qualitativeJointSizeCutoff error amplification herror)) :
    Tendsto (fun j => error (s.systemSize j)) atTop (nhds 0) := by
  exact herror.comp s.systemSize_tendsto_atTop

/-- The amplified error tends to zero without any boundedness hypothesis on
the amplification. -/
theorem amplification_mul_error_along_admissibleJointLimit_tendsto_zero
    (error : Nat -> Real) (amplification : Real -> Real)
    (herror_nonneg : forall N, 0 <= error N)
    (herror : Tendsto error atTop (nhds 0))
    (hamplification : forall g, 0 <= amplification g)
    (s : AdmissibleJointLimit
      (qualitativeJointSizeCutoff error amplification herror)) :
    Tendsto
      (fun j => amplification (s.coupling j) * error (s.systemSize j))
      atTop (nhds 0) := by
  have hcoupling : Tendsto s.coupling atTop (nhds 0) :=
    s.coupling_tendsto_zero.mono_right inf_le_left
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun j =>
      mul_nonneg (hamplification (s.coupling j))
        (herror_nonneg (s.systemSize j)))
    (eventually_amplification_mul_error_le_coupling
      error amplification herror hamplification s)
    hcoupling

/-- Bundled existential form: a qualitative error limit constructs one size
cutoff that works for every admitted weak-coupling/large-volume path. -/
theorem exists_sizeCutoff_for_qualitative_jointLimit
    (error : Nat -> Real) (amplification : Real -> Real)
    (herror_nonneg : forall N, 0 <= error N)
    (herror : Tendsto error atTop (nhds 0))
    (hamplification : forall g, 0 <= amplification g) :
    exists sizeCutoff : Real -> Nat,
      forall s : AdmissibleJointLimit sizeCutoff,
        Tendsto (fun j => error (s.systemSize j)) atTop (nhds 0) /\
        (∀ᶠ j in atTop,
          amplification (s.coupling j) * error (s.systemSize j) <=
            s.coupling j) /\
        Tendsto
          (fun j => amplification (s.coupling j) * error (s.systemSize j))
          atTop (nhds 0) := by
  refine ⟨qualitativeJointSizeCutoff error amplification herror, ?_⟩
  intro s
  exact ⟨error_along_admissibleJointLimit_tendsto_zero
      error amplification herror s,
    eventually_amplification_mul_error_le_coupling
      error amplification herror hamplification s,
    amplification_mul_error_along_admissibleJointLimit_tendsto_zero
      error amplification herror_nonneg herror hamplification s⟩

end

end ArchonPhysics.QualitativeJointLimitDiagonalization
