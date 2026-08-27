import ArchonPhysics.LennardJonesAlphaBetaFlowStability

/-!
# Consumer: conditional LJ / alpha-beta flow stability on a kinetic window

This consumer inserts the proved all-mode Lennard--Jones higher-remainder
bound into the generic Gronwall interface.  For the paper mass support
`m_i >= 4/5`, a tube-confined exact trajectory supplies a phase-space
residual of per-mode RMS size `O(g^3)`.

The resulting exact/alpha-beta state error is `O(g)` at time `L/g^2` only
under the explicitly displayed effective stability hypothesis
`kappa * g^2`.  A fixed `O(1)` Lipschitz rate yields the exponential barrier
proved in the core module instead.
-/

namespace ArchonPhysicsConsumers.Thermalization.LennardJonesAlphaBetaFlowStability

open Real Set
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.LennardJonesKineticTimeForceRemainder
open ArchonPhysics.LennardJonesModalRemainderKineticBound
open ArchonPhysics.LennardJonesModalRemainderMeanSquareBound
open ArchonPhysics.LennardJonesStoppedHigherRemainderProbability
open ArchonPhysics.LennardJonesAlphaBetaFlowStability

noncomputable section

/-- Inject the LJ force remainder into the momentum component of first-order
phase space.  The position component is zero because the exact and retained
kinematic equations agree. -/
def phaseSpaceHigherResidual
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r0 g : Real)
    (q : Real -> HilbertConfiguration N) :
    Real -> (HilbertConfiguration N × HilbertConfiguration N) :=
  fun t => (0, modalHigherResidualVector m depth r0 g (q t))

/-- On the paper mass support and the LJ tube, the raw phase-space residual
has norm at most `C * g^3 * sqrt N`; equivalently its per-mode RMS norm is
bounded by the volume-independent coefficient `C * g^3`. -/
theorem paperMassSupport_phaseSpaceHigherResidual_norm_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hmass : forall i, (4 / 5 : Real) <= m.mass i)
    {depth r0 g rho amplitudeBound : Real}
    (hdepth : 0 < depth) (hr0 : 0 < r0) (hg : 0 < g)
    (hrho0 : 0 <= rho) (hrho1 : rho < 1)
    (hAmplitude : 0 <= amplitudeBound)
    (q : Real -> HilbertConfiguration N) (t : Real)
    (htube : forall i : Lattice.Site N,
      |g * Lattice.forwardDifference (asConfiguration (q t)) i| <= rho * r0)
    (hamplitude : forall i : Lattice.Site N,
      |Lattice.forwardDifference (asConfiguration (q t)) i| <= amplitudeBound) :
    ‖phaseSpaceHigherResidual m depth r0 g q t‖ <=
      (higherRemainderRMSCoefficient (4 / 5 : Real)
        r0 rho amplitudeBound * Real.sqrt N) * g ^ 3 := by
  have hN : 0 < (N : Real) := by
    exact_mod_cast NeZero.pos N
  have hsqrtN : 0 < Real.sqrt (N : Real) := Real.sqrt_pos.2 hN
  have hrms := modalHigherResidualRMS_le_g_cubed
    m (4 / 5 : Real) (by norm_num) hmass hdepth hr0 hg
      hrho0 hrho1 hAmplitude (q t) htube hamplitude
  unfold modalHigherResidualRMS at hrms
  have hraw := (div_le_iff₀ hsqrtN).mp hrms
  simpa [phaseSpaceHigherResidual, mul_assoc, mul_left_comm,
    mul_comm] using hraw

/-- The exact hypotheses which turn the concrete LJ remainder estimate into
a first-order exact/alpha-beta flow comparison.  The Hamilton equations and
the effective `kappa * g^2` retained-field stability remain visible inputs. -/
theorem paperMassSupport_flowComparisonData_of_tube
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hmass : forall i, (4 / 5 : Real) <= m.mass i)
    {depth r0 g rho L amplitudeBound kappa : Real}
    (hdepth : 0 < depth) (hr0 : 0 < r0) (hg : 0 < g)
    (hrho0 : 0 <= rho) (hrho1 : rho < 1)
    (hL : 0 <= L) (hAmplitude : 0 <= amplitudeBound)
    (q : Real -> HilbertConfiguration N)
    (exactFlow alphaBetaFlow :
      Real -> (HilbertConfiguration N × HilbertConfiguration N))
    (retainedField : Real ->
      (HilbertConfiguration N × HilbertConfiguration N) ->
      (HilbertConfiguration N × HilbertConfiguration N))
    (hkappa : 0 <= kappa)
    (hexactContinuous : ContinuousOn exactFlow
      (Icc 0 (kineticWindowTime g L)))
    (halphaBetaContinuous : ContinuousOn alphaBetaFlow
      (Icc 0 (kineticWindowTime g L)))
    (hexactEquation : ∀ t ∈ Ico 0 (kineticWindowTime g L),
      HasDerivWithinAt exactFlow
        (retainedField t (exactFlow t) +
          phaseSpaceHigherResidual m depth r0 g q t) (Ici t) t)
    (halphaBetaEquation : ∀ t ∈ Ico 0 (kineticWindowTime g L),
      HasDerivWithinAt alphaBetaFlow
        (retainedField t (alphaBetaFlow t)) (Ici t) t)
    (hinitial : exactFlow 0 = alphaBetaFlow 0)
    (hstability : ∀ t ∈ Ico 0 (kineticWindowTime g L),
      ‖retainedField t (exactFlow t) - retainedField t (alphaBetaFlow t)‖ <=
        (kappa * g ^ 2) * ‖exactFlow t - alphaBetaFlow t‖)
    (htube : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      forall i : Lattice.Site N,
        |g * Lattice.forwardDifference (asConfiguration (q t)) i| <= rho * r0)
    (hamplitude : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      forall i : Lattice.Site N,
        |Lattice.forwardDifference (asConfiguration (q t)) i| <= amplitudeBound) :
    FlowComparisonData exactFlow alphaBetaFlow
      (phaseSpaceHigherResidual m depth r0 g q) retainedField
      g L (kappa * g ^ 2)
      (higherRemainderRMSCoefficient (4 / 5 : Real)
        r0 rho amplitudeBound * Real.sqrt N) := by
  refine
    { coupling_pos := hg
      horizon_nonneg := hL
      lipschitzRate_nonneg := mul_nonneg hkappa (sq_nonneg g)
      residualCoefficient_nonneg := mul_nonneg
        (higherRemainderRMSCoefficient_nonneg _ _ _ _)
        (Real.sqrt_nonneg _)
      exact_continuous := hexactContinuous
      alphaBeta_continuous := halphaBetaContinuous
      exact_equation := hexactEquation
      alphaBeta_equation := halphaBetaEquation
      same_initial_state := hinitial
      retainedField_stability := hstability
      higherResidual_bound := ?_ }
  intro t ht
  have htIcc : t ∈ Icc 0 (kineticWindowTime g L) :=
    ⟨ht.1, ht.2.le⟩
  exact paperMassSupport_phaseSpaceHigherResidual_norm_le
    m hmass hdepth hr0 hg hrho0 hrho1 hAmplitude q t
      (htube t htIcc) (hamplitude t htIcc)

/-- Conditional F3 closure for the higher LJ Taylor remainder: if the
retained alpha-beta phase flow has effective stability rate `kappa * g^2`,
then its per-mode RMS distance from the exact LJ phase flow is `O(g)` on the
kinetic window. -/
theorem problem_paperLJ_perMode_stateError_le_g
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hmass : forall i, (4 / 5 : Real) <= m.mass i)
    {depth r0 g rho L amplitudeBound kappa : Real}
    (hdepth : 0 < depth) (hr0 : 0 < r0) (hg : 0 < g)
    (hrho0 : 0 <= rho) (hrho1 : rho < 1)
    (hL : 0 <= L) (hAmplitude : 0 <= amplitudeBound)
    (q : Real -> HilbertConfiguration N)
    (exactFlow alphaBetaFlow :
      Real -> (HilbertConfiguration N × HilbertConfiguration N))
    (retainedField : Real ->
      (HilbertConfiguration N × HilbertConfiguration N) ->
      (HilbertConfiguration N × HilbertConfiguration N))
    (hkappa : 0 < kappa)
    (hexactContinuous : ContinuousOn exactFlow
      (Icc 0 (kineticWindowTime g L)))
    (halphaBetaContinuous : ContinuousOn alphaBetaFlow
      (Icc 0 (kineticWindowTime g L)))
    (hexactEquation : ∀ t ∈ Ico 0 (kineticWindowTime g L),
      HasDerivWithinAt exactFlow
        (retainedField t (exactFlow t) +
          phaseSpaceHigherResidual m depth r0 g q t) (Ici t) t)
    (halphaBetaEquation : ∀ t ∈ Ico 0 (kineticWindowTime g L),
      HasDerivWithinAt alphaBetaFlow
        (retainedField t (alphaBetaFlow t)) (Ici t) t)
    (hinitial : exactFlow 0 = alphaBetaFlow 0)
    (hstability : ∀ t ∈ Ico 0 (kineticWindowTime g L),
      ‖retainedField t (exactFlow t) - retainedField t (alphaBetaFlow t)‖ <=
        (kappa * g ^ 2) * ‖exactFlow t - alphaBetaFlow t‖)
    (htube : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      forall i : Lattice.Site N,
        |g * Lattice.forwardDifference (asConfiguration (q t)) i| <= rho * r0)
    (hamplitude : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      forall i : Lattice.Site N,
        |Lattice.forwardDifference (asConfiguration (q t)) i| <= amplitudeBound) :
    ‖exactFlow (kineticWindowTime g L) -
        alphaBetaFlow (kineticWindowTime g L)‖ / Real.sqrt N <=
      (higherRemainderRMSCoefficient (4 / 5 : Real)
        r0 rho amplitudeBound / kappa) *
        (Real.exp (kappa * L) - 1) * g := by
  have hN : 0 < (N : Real) := by
    exact_mod_cast NeZero.pos N
  have hsqrtN : 0 < Real.sqrt (N : Real) := Real.sqrt_pos.2 hN
  have data := paperMassSupport_flowComparisonData_of_tube
    m hmass hdepth hr0 hg hrho0 hrho1 hL hAmplitude q
      exactFlow alphaBetaFlow retainedField hkappa.le
      hexactContinuous halphaBetaContinuous hexactEquation
      halphaBetaEquation hinitial hstability htube hamplitude
  exact kineticWindow_stateError_div_scale_le_of_effectiveRate
    hkappa hsqrtN data

/-- If the same comparison is available only with a fixed positive rate `K`,
the certified error contains the explicit `exp (K * L / g^2)` barrier. -/
theorem problem_fixedRate_exponential_barrier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {exactFlow alphaBetaFlow higherResidual : Real -> E}
    {retainedField : Real -> E -> E}
    {g L K residualCoefficient : Real}
    (hK : 0 < K)
    (data : FlowComparisonData exactFlow alphaBetaFlow higherResidual
      retainedField g L K residualCoefficient) :
    ‖exactFlow (kineticWindowTime g L) -
        alphaBetaFlow (kineticWindowTime g L)‖ <=
      fixedRateKineticBarrier K residualCoefficient g L := by
  exact kineticWindow_stateError_le_fixedRateBarrier hK data

/-- Paper-mass-support local-uniform closure.  Under the same explicit tube,
Hamilton-equation, and effective `kappa * g^2` retained-flow stability
hypotheses, the per-mode RMS LJ/alpha-beta state error is uniformly `O(g)`
for every `t` in the full physical kinetic window. -/
theorem problem_paperLJ_perMode_stateError_uniform_le_g
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hmass : forall i, (4 / 5 : Real) <= m.mass i)
    {depth r0 g rho L amplitudeBound kappa : Real}
    (hdepth : 0 < depth) (hr0 : 0 < r0) (hg : 0 < g)
    (hrho0 : 0 <= rho) (hrho1 : rho < 1)
    (hL : 0 <= L) (hAmplitude : 0 <= amplitudeBound)
    (q : Real -> HilbertConfiguration N)
    (exactFlow alphaBetaFlow :
      Real -> (HilbertConfiguration N × HilbertConfiguration N))
    (retainedField : Real ->
      (HilbertConfiguration N × HilbertConfiguration N) ->
      (HilbertConfiguration N × HilbertConfiguration N))
    (hkappa : 0 < kappa)
    (hexactContinuous : ContinuousOn exactFlow
      (Icc 0 (kineticWindowTime g L)))
    (halphaBetaContinuous : ContinuousOn alphaBetaFlow
      (Icc 0 (kineticWindowTime g L)))
    (hexactEquation : ∀ t ∈ Ico 0 (kineticWindowTime g L),
      HasDerivWithinAt exactFlow
        (retainedField t (exactFlow t) +
          phaseSpaceHigherResidual m depth r0 g q t) (Ici t) t)
    (halphaBetaEquation : ∀ t ∈ Ico 0 (kineticWindowTime g L),
      HasDerivWithinAt alphaBetaFlow
        (retainedField t (alphaBetaFlow t)) (Ici t) t)
    (hinitial : exactFlow 0 = alphaBetaFlow 0)
    (hstability : ∀ t ∈ Ico 0 (kineticWindowTime g L),
      ‖retainedField t (exactFlow t) - retainedField t (alphaBetaFlow t)‖ <=
        (kappa * g ^ 2) * ‖exactFlow t - alphaBetaFlow t‖)
    (htube : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      forall i : Lattice.Site N,
        |g * Lattice.forwardDifference (asConfiguration (q t)) i| <= rho * r0)
    (hamplitude : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      forall i : Lattice.Site N,
        |Lattice.forwardDifference (asConfiguration (q t)) i| <= amplitudeBound)
    {t : Real} (ht : t ∈ Icc 0 (kineticWindowTime g L)) :
    ‖exactFlow t - alphaBetaFlow t‖ / Real.sqrt N <=
      (higherRemainderRMSCoefficient (4 / 5 : Real)
        r0 rho amplitudeBound / kappa) *
        (Real.exp (kappa * L) - 1) * g := by
  have hN : 0 < (N : Real) := by
    exact_mod_cast NeZero.pos N
  have hsqrtN : 0 < Real.sqrt (N : Real) := Real.sqrt_pos.2 hN
  have data := paperMassSupport_flowComparisonData_of_tube
    m hmass hdepth hr0 hg hrho0 hrho1 hL hAmplitude q
      exactFlow alphaBetaFlow retainedField hkappa.le
      hexactContinuous halphaBetaContinuous hexactEquation
      halphaBetaEquation hinitial hstability htube hamplitude
  exact kineticWindow_stateError_div_scale_le_of_effectiveRate_uniform
    hkappa hsqrtN data ht

#print axioms problem_paperLJ_perMode_stateError_uniform_le_g
#print axioms paperMassSupport_phaseSpaceHigherResidual_norm_le
#print axioms paperMassSupport_flowComparisonData_of_tube
#print axioms problem_paperLJ_perMode_stateError_le_g
#print axioms problem_fixedRate_exponential_barrier
#print axioms FlowComparisonData.stateError_le_gronwall
#print axioms kineticWindow_stateError_le_of_effectiveRate
#print axioms kineticWindow_stateError_le_of_effectiveRate_uniform
#print axioms kineticWindow_stateError_div_scale_le_of_effectiveRate_uniform
#print axioms kineticWindow_stateError_le_fixedRateBarrier

end

end ArchonPhysicsConsumers.Thermalization.LennardJonesAlphaBetaFlowStability
