import ArchonPhysics.LennardJonesStoppedHigherRemainderProbability
import Mathlib.Analysis.ODE.Gronwall

/-!
# Kinetic-window stability of the LJ / FPUT alpha-beta truncation

This module isolates the deterministic stability input needed to turn the
`O(g^3)` Lennard--Jones force remainder into an `O(g)` state error on the
kinetic time window `0 <= t <= L / g^2`.

The key point is deliberately transparent.  If the retained alpha-beta
vector field has effective Lipschitz rate `kappa * g^2`, Gronwall gives

`error(L / g^2) <= (C / kappa) * (exp (kappa * L) - 1) * g`.

If one knows only a fixed rate `K = O(1)`, the same argument gives the much
weaker bound

`(C / K) * g^3 * (exp (K * L / g^2) - 1)`.

Thus the already proved higher LJ remainder estimate does not by itself
close the long kinetic window: one must additionally prove an effective
`O(g^2)` stability rate (or exploit a more refined dispersive/normal-form
argument).  The hypotheses below are model-pluggable and make that remaining
input explicit; no global LJ flow or hidden stability assumption is asserted.
-/

namespace ArchonPhysics.LennardJonesAlphaBetaFlowStability

open Real Set
open ArchonPhysics.LennardJonesKineticTimeForceRemainder

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

/-- Exact and retained trajectories together with the precise local inputs
needed for their Gronwall comparison on the kinetic window.

`higherResidual` is the part of the exact LJ vector field beyond the retained
alpha-beta jet.  `retainedField_stability` is required only along the two
supplied trajectories, rather than globally on phase space. -/
structure FlowComparisonData
    (exactFlow alphaBetaFlow higherResidual : Real -> E)
    (retainedField : Real -> E -> E)
    (g L lipschitzRate residualCoefficient : Real) : Prop where
  coupling_pos : 0 < g
  horizon_nonneg : 0 <= L
  lipschitzRate_nonneg : 0 <= lipschitzRate
  residualCoefficient_nonneg : 0 <= residualCoefficient
  exact_continuous : ContinuousOn exactFlow
    (Icc 0 (kineticWindowTime g L))
  alphaBeta_continuous : ContinuousOn alphaBetaFlow
    (Icc 0 (kineticWindowTime g L))
  exact_equation : ∀ t ∈ Ico 0 (kineticWindowTime g L),
    HasDerivWithinAt exactFlow
      (retainedField t (exactFlow t) + higherResidual t) (Ici t) t
  alphaBeta_equation : ∀ t ∈ Ico 0 (kineticWindowTime g L),
    HasDerivWithinAt alphaBetaFlow
      (retainedField t (alphaBetaFlow t)) (Ici t) t
  same_initial_state : exactFlow 0 = alphaBetaFlow 0
  retainedField_stability : ∀ t ∈ Ico 0 (kineticWindowTime g L),
    ‖retainedField t (exactFlow t) - retainedField t (alphaBetaFlow t)‖ <=
      lipschitzRate * ‖exactFlow t - alphaBetaFlow t‖
  higherResidual_bound : ∀ t ∈ Ico 0 (kineticWindowTime g L),
    ‖higherResidual t‖ <= residualCoefficient * g ^ 3

theorem kineticWindowTime_nonneg
    {g L : Real} (_hg : 0 < g) (hL : 0 <= L) :
    0 <= kineticWindowTime g L := by
  unfold kineticWindowTime
  exact div_nonneg hL (sq_nonneg g)

/-- The trajectory difference satisfies the standard Gronwall bound.  This
lemma is the exact point at which the retained-flow stability hypothesis and
the higher-remainder estimate enter. -/
theorem FlowComparisonData.stateError_le_gronwall
    {exactFlow alphaBetaFlow higherResidual : Real -> E}
    {retainedField : Real -> E -> E}
    {g L lipschitzRate residualCoefficient : Real}
    (data : FlowComparisonData exactFlow alphaBetaFlow higherResidual
      retainedField g L lipschitzRate residualCoefficient)
    {t : Real} (ht : t ∈ Icc 0 (kineticWindowTime g L)) :
    ‖exactFlow t - alphaBetaFlow t‖ <=
      gronwallBound 0 lipschitzRate (residualCoefficient * g ^ 3) t := by
  have hderiv : ∀ s ∈ Ico 0 (kineticWindowTime g L),
      HasDerivWithinAt (fun u => exactFlow u - alphaBetaFlow u)
        ((retainedField s (exactFlow s) + higherResidual s) -
          retainedField s (alphaBetaFlow s)) (Ici s) s := by
    intro s hs
    exact (data.exact_equation s hs).sub (data.alphaBeta_equation s hs)
  have hbound : ∀ s ∈ Ico 0 (kineticWindowTime g L),
      ‖(retainedField s (exactFlow s) + higherResidual s) -
          retainedField s (alphaBetaFlow s)‖ <=
        lipschitzRate * ‖exactFlow s - alphaBetaFlow s‖ +
          residualCoefficient * g ^ 3 := by
    intro s hs
    calc
      ‖(retainedField s (exactFlow s) + higherResidual s) -
          retainedField s (alphaBetaFlow s)‖ =
          ‖(retainedField s (exactFlow s) -
            retainedField s (alphaBetaFlow s)) + higherResidual s‖ := by
              congr 1
              abel
      _ <= ‖retainedField s (exactFlow s) -
            retainedField s (alphaBetaFlow s)‖ + ‖higherResidual s‖ :=
        norm_add_le _ _
      _ <= lipschitzRate * ‖exactFlow s - alphaBetaFlow s‖ +
          residualCoefficient * g ^ 3 :=
        add_le_add (data.retainedField_stability s hs)
          (data.higherResidual_bound s hs)
  have hmain : ∀ x ∈ Icc 0 (kineticWindowTime g L),
      ‖exactFlow x - alphaBetaFlow x‖ <=
        gronwallBound 0 lipschitzRate (residualCoefficient * g ^ 3)
          (x - 0) := by
    apply norm_le_gronwallBound_of_norm_deriv_right_le
    · exact data.exact_continuous.fun_sub data.alphaBeta_continuous
    · exact hderiv
    · simp [data.same_initial_state]
    · exact hbound
  have h := hmain t ht
  simpa using h

/-- With effective Lipschitz rate `kappa * g^2`, the kinetic-window state
error is `O(g)` with a coefficient independent of `g`. -/
theorem kineticWindow_stateError_le_of_effectiveRate
    {exactFlow alphaBetaFlow higherResidual : Real -> E}
    {retainedField : Real -> E -> E}
    {g L kappa residualCoefficient : Real}
    (hkappa : 0 < kappa)
    (data : FlowComparisonData exactFlow alphaBetaFlow higherResidual
      retainedField g L (kappa * g ^ 2) residualCoefficient) :
    ‖exactFlow (kineticWindowTime g L) -
        alphaBetaFlow (kineticWindowTime g L)‖ <=
      (residualCoefficient / kappa) * (exp (kappa * L) - 1) * g := by
  have htime : 0 <= kineticWindowTime g L :=
    kineticWindowTime_nonneg data.coupling_pos data.horizon_nonneg
  have h := data.stateError_le_gronwall
    (t := kineticWindowTime g L) ⟨htime, le_rfl⟩
  calc
    ‖exactFlow (kineticWindowTime g L) -
        alphaBetaFlow (kineticWindowTime g L)‖ <=
        gronwallBound 0 (kappa * g ^ 2)
          (residualCoefficient * g ^ 3) (kineticWindowTime g L) := h
    _ = (residualCoefficient / kappa) *
        (exp (kappa * L) - 1) * g := by
      rw [gronwallBound_of_K_ne_0
        (mul_ne_zero hkappa.ne' (pow_ne_zero 2 data.coupling_pos.ne'))]
      unfold kineticWindowTime
      field_simp [hkappa.ne', data.coupling_pos.ne']
      ; ring

/-- Degenerate zero-rate version: direct integration also gives `C * L * g`.
This is the continuous `kappa -> 0` counterpart of the preceding estimate. -/
theorem kineticWindow_stateError_le_of_zeroRate
    {exactFlow alphaBetaFlow higherResidual : Real -> E}
    {retainedField : Real -> E -> E}
    {g L residualCoefficient : Real}
    (data : FlowComparisonData exactFlow alphaBetaFlow higherResidual
      retainedField g L 0 residualCoefficient) :
    ‖exactFlow (kineticWindowTime g L) -
        alphaBetaFlow (kineticWindowTime g L)‖ <=
      residualCoefficient * L * g := by
  have htime : 0 <= kineticWindowTime g L :=
    kineticWindowTime_nonneg data.coupling_pos data.horizon_nonneg
  have h := data.stateError_le_gronwall
    (t := kineticWindowTime g L) ⟨htime, le_rfl⟩
  calc
    ‖exactFlow (kineticWindowTime g L) -
        alphaBetaFlow (kineticWindowTime g L)‖ <=
        gronwallBound 0 0 (residualCoefficient * g ^ 3)
          (kineticWindowTime g L) := h
    _ = residualCoefficient * L * g := by
      rw [congrFun (gronwallBound_K0 0 (residualCoefficient * g ^ 3))
        (kineticWindowTime g L)]
      unfold kineticWindowTime
      field_simp [data.coupling_pos.ne']
      ; ring

/-- The exact Gronwall expression produced when only a fixed `O(1)`
Lipschitz rate is available. -/
def fixedRateKineticBarrier
    (K residualCoefficient g L : Real) : Real :=
  (residualCoefficient / K) * g ^ 3 *
    (exp (K * L / g ^ 2) - 1)

/-- With only a fixed positive Lipschitz rate, the kinetic-window comparison
contains `exp (K * L / g^2)`.  This theorem records the obstruction rather
than silently treating it as an `O(g)` coefficient. -/
theorem kineticWindow_stateError_le_fixedRateBarrier
    {exactFlow alphaBetaFlow higherResidual : Real -> E}
    {retainedField : Real -> E -> E}
    {g L K residualCoefficient : Real}
    (hK : 0 < K)
    (data : FlowComparisonData exactFlow alphaBetaFlow higherResidual
      retainedField g L K residualCoefficient) :
    ‖exactFlow (kineticWindowTime g L) -
        alphaBetaFlow (kineticWindowTime g L)‖ <=
      fixedRateKineticBarrier K residualCoefficient g L := by
  have htime : 0 <= kineticWindowTime g L :=
    kineticWindowTime_nonneg data.coupling_pos data.horizon_nonneg
  have h := data.stateError_le_gronwall
    (t := kineticWindowTime g L) ⟨htime, le_rfl⟩
  calc
    ‖exactFlow (kineticWindowTime g L) -
        alphaBetaFlow (kineticWindowTime g L)‖ <=
        gronwallBound 0 K (residualCoefficient * g ^ 3)
          (kineticWindowTime g L) := h
    _ = fixedRateKineticBarrier K residualCoefficient g L := by
      rw [gronwallBound_of_K_ne_0 hK.ne']
      unfold fixedRateKineticBarrier kineticWindowTime
      field_simp [hK.ne', data.coupling_pos.ne']
      ; ring

/-- Volume-normalized form.  If the raw residual norm is
`C * volumeScale * g^3`, then division by the same positive scale removes
the volume factor and retains the `O(g)` kinetic-window estimate. -/
theorem kineticWindow_stateError_div_scale_le_of_effectiveRate
    {exactFlow alphaBetaFlow higherResidual : Real -> E}
    {retainedField : Real -> E -> E}
    {g L kappa residualCoefficient volumeScale : Real}
    (hkappa : 0 < kappa) (hscale : 0 < volumeScale)
    (data : FlowComparisonData exactFlow alphaBetaFlow higherResidual
      retainedField g L (kappa * g ^ 2)
        (residualCoefficient * volumeScale)) :
    ‖exactFlow (kineticWindowTime g L) -
        alphaBetaFlow (kineticWindowTime g L)‖ / volumeScale <=
      (residualCoefficient / kappa) * (exp (kappa * L) - 1) * g := by
  have hraw := kineticWindow_stateError_le_of_effectiveRate hkappa data
  apply (div_le_iff₀ hscale).2
  calc
    ‖exactFlow (kineticWindowTime g L) -
        alphaBetaFlow (kineticWindowTime g L)‖ <=
      ((residualCoefficient * volumeScale) / kappa) *
        (exp (kappa * L) - 1) * g := hraw
    _ = (residualCoefficient / kappa) *
        (exp (kappa * L) - 1) * g * volumeScale := by ring

/-! ## Local-uniform kinetic-window bounds -/

/-- Local-uniform version of the effective-rate comparison.  The same
`O(g)` coefficient controls every physical time in `[0, L / g^2]`, not only
the right endpoint. -/
theorem kineticWindow_stateError_le_of_effectiveRate_uniform
    {exactFlow alphaBetaFlow higherResidual : Real -> E}
    {retainedField : Real -> E -> E}
    {g L kappa residualCoefficient : Real}
    (hkappa : 0 < kappa)
    (data : FlowComparisonData exactFlow alphaBetaFlow higherResidual
      retainedField g L (kappa * g ^ 2) residualCoefficient)
    {t : Real} (ht : t ∈ Icc 0 (kineticWindowTime g L)) :
    ‖exactFlow t - alphaBetaFlow t‖ <=
      (residualCoefficient / kappa) * (exp (kappa * L) - 1) * g := by
  have hmono : Monotone
      (gronwallBound 0 (kappa * g ^ 2) (residualCoefficient * g ^ 3)) :=
    gronwallBound_mono (by norm_num)
      (mul_nonneg data.residualCoefficient_nonneg
        (pow_nonneg data.coupling_pos.le 3))
      data.lipschitzRate_nonneg
  calc
    ‖exactFlow t - alphaBetaFlow t‖ <=
        gronwallBound 0 (kappa * g ^ 2)
          (residualCoefficient * g ^ 3) t :=
      data.stateError_le_gronwall ht
    _ <= gronwallBound 0 (kappa * g ^ 2)
          (residualCoefficient * g ^ 3) (kineticWindowTime g L) :=
      hmono ht.2
    _ = (residualCoefficient / kappa) *
        (exp (kappa * L) - 1) * g := by
      rw [gronwallBound_of_K_ne_0
        (mul_ne_zero hkappa.ne' (pow_ne_zero 2 data.coupling_pos.ne'))]
      unfold kineticWindowTime
      field_simp [hkappa.ne', data.coupling_pos.ne']
      ; ring

/-- Volume-normalized local-uniform version.  A raw residual bound
`C * volumeScale * g^3` gives a uniform per-volume state error of order `g`
throughout the full kinetic window. -/
theorem kineticWindow_stateError_div_scale_le_of_effectiveRate_uniform
    {exactFlow alphaBetaFlow higherResidual : Real -> E}
    {retainedField : Real -> E -> E}
    {g L kappa residualCoefficient volumeScale : Real}
    (hkappa : 0 < kappa) (hscale : 0 < volumeScale)
    (data : FlowComparisonData exactFlow alphaBetaFlow higherResidual
      retainedField g L (kappa * g ^ 2)
        (residualCoefficient * volumeScale))
    {t : Real} (ht : t ∈ Icc 0 (kineticWindowTime g L)) :
    ‖exactFlow t - alphaBetaFlow t‖ / volumeScale <=
      (residualCoefficient / kappa) * (exp (kappa * L) - 1) * g := by
  have hraw := kineticWindow_stateError_le_of_effectiveRate_uniform
    hkappa data ht
  apply (div_le_iff₀ hscale).2
  calc
    ‖exactFlow t - alphaBetaFlow t‖ <=
      ((residualCoefficient * volumeScale) / kappa) *
        (exp (kappa * L) - 1) * g := hraw
    _ = (residualCoefficient / kappa) *
        (exp (kappa * L) - 1) * g * volumeScale := by ring

end

end ArchonPhysics.LennardJonesAlphaBetaFlowStability
