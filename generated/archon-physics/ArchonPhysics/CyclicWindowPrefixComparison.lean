import ArchonPhysics.ComplexFiniteWindowIIDAllVolumeStrongLaw

/-!
# Cyclic versus ordinary iid window averages

Restricting the first `N` coordinates of an infinite iid sequence to a
periodic chain only changes the last `W` starting windows: all earlier
length-`W` windows do not wrap around the periodic cut.  This file gives the
deterministic norm estimate needed to replace a cyclic local-kernel average
by the ordinary sliding-window average used by the strong law.
-/

namespace ArchonPhysics.CyclicWindowPrefixComparison

open ArchonPhysics
open ArchonPhysics.ComplexFiniteWindowIIDAllVolumeStrongLaw
open ArchonPhysics.FiniteWindowIIDStrongLaw
open ArchonPhysics.RandomEnsemble
open Filter Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The length-`W` window beginning at `start`, read cyclically from the first
`N` coordinates of the infinite mass sequence. -/
def cyclicMassWindow (ensemble : IIDMassPhaseEnsemble Omega)
    (N W start : Nat) (omega : Omega) : Fin W -> Real :=
  fun j => ensemble.mass ((start + j.val) % N) omega

/-- Complex spatial average of all `N` cyclic starting windows. -/
def cyclicComplexWindowAverage (ensemble : IIDMassPhaseEnsemble Omega)
    (N W : Nat) (f : (Fin W -> Real) -> Complex)
    (omega : Omega) : Complex :=
  (∑ start ∈ Finset.range N,
    f (cyclicMassWindow ensemble N W start omega)) / (N : Real)

/-- Before the final `W` possible starting sites, a cyclic window is exactly
the ordinary nonwrapping iid window. -/
theorem cyclicMassWindow_eq_massWindow_of_add_le
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N W start : Nat} (hwindow : start + W <= N) (omega : Omega) :
    cyclicMassWindow ensemble N W start omega =
      massWindow ensemble W start 0 omega := by
  funext j
  unfold cyclicMassWindow massWindow
  have hlt : start + j.val < N := by
    omega
  rw [Nat.mod_eq_of_lt hlt]
  simp

/-- Uniform deterministic cut estimate.  At most `W` starting windows can
wrap, and each difference has norm at most `2*C`. -/
theorem norm_cyclicComplexWindowAverage_sub_complexSpatialAverage_le
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N W : Nat} (hN : 0 < N) (hWN : W <= N)
    (f : (Fin W -> Real) -> Complex) (C : Real)
    (hbound : ∀ x : Fin W -> Real,
      (∀ j, x j ∈ massSupport) -> ‖f x‖ <= C)
    (omega : Omega) :
    ‖cyclicComplexWindowAverage ensemble N W f omega -
        complexSpatialAverage ensemble W f N omega‖ <=
      (2 * C * (W : Real)) / (N : Real) := by
  let d : Nat -> Complex := fun start =>
    f (cyclicMassWindow ensemble N W start omega) -
      f (massWindow ensemble W start 0 omega)
  have hsupportCyclic (start : Nat) (j : Fin W) :
      cyclicMassWindow ensemble N W start omega j ∈ massSupport :=
    ensemble.mass_mem_support ((start + j.val) % N) omega
  have hsupportLinear (start : Nat) (j : Fin W) :
      massWindow ensemble W start 0 omega j ∈ massSupport :=
    massWindow_mem_support ensemble W start 0 omega j
  have hdnorm (start : Nat) : ‖d start‖ <= 2 * C := by
    calc
      ‖d start‖ <=
          ‖f (cyclicMassWindow ensemble N W start omega)‖ +
            ‖f (massWindow ensemble W start 0 omega)‖ := norm_sub_le _ _
      _ <= C + C := add_le_add
        (hbound _ (hsupportCyclic start))
        (hbound _ (hsupportLinear start))
      _ = 2 * C := by ring
  have hboundarySubset : Finset.Ico (N - W) N ⊆ Finset.range N := by
    intro i hi
    simp only [Finset.mem_Ico, Finset.mem_range] at hi ⊢
    exact hi.2
  have hsumBoundary :
      (∑ start ∈ Finset.range N, d start) =
        ∑ start ∈ Finset.Ico (N - W) N, d start := by
    symm
    apply Finset.sum_subset hboundarySubset
    intro start hstartRange hstartOutside
    have hstartLt : start < N := Finset.mem_range.mp hstartRange
    have hstartBefore : start < N - W := by
      by_contra hnot
      apply hstartOutside
      simp only [Finset.mem_Ico]
      exact ⟨Nat.le_of_not_gt hnot, hstartLt⟩
    have hwindow : start + W <= N := by omega
    unfold d
    rw [cyclicMassWindow_eq_massWindow_of_add_le
      ensemble hwindow omega]
    exact sub_self _
  have hsumNorm :
      ‖∑ start ∈ Finset.range N, d start‖ <= 2 * C * (W : Real) := by
    rw [hsumBoundary]
    calc
      ‖∑ start ∈ Finset.Ico (N - W) N, d start‖ <=
          ∑ start ∈ Finset.Ico (N - W) N, ‖d start‖ := by
        exact (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun start _hstart => le_rfl)
      _ <= ∑ _start ∈ Finset.Ico (N - W) N, 2 * C := by
        exact Finset.sum_le_sum fun start _hstart => hdnorm start
      _ = 2 * C * (W : Real) := by
        simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
        have hsub : N - (N - W) = W := Nat.sub_sub_self hWN
        rw [hsub]
        ring
  have hsumIdentity :
      (∑ start ∈ Finset.range N,
          f (cyclicMassWindow ensemble N W start omega)) -
        (∑ start ∈ Finset.range N,
          f (massWindow ensemble W start 0 omega)) =
        ∑ start ∈ Finset.range N, d start := by
    rw [← Finset.sum_sub_distrib]
  unfold cyclicComplexWindowAverage complexSpatialAverage
    complexWindowObservable
  rw [← sub_div, hsumIdentity, norm_div]
  have hnormN : ‖((N : Real) : Complex)‖ = (N : Real) := by
    simp
  rw [hnormN]
  exact (div_le_div_iff_of_pos_right
    (show (0 : Real) < N by exact_mod_cast hN)).2 hsumNorm

/-- The cyclic finite-volume average has the same limit as the ordinary iid
sliding-window average. -/
theorem tendsto_cyclicComplexWindowAverage_of_complexSpatialAverage
    (ensemble : IIDMassPhaseEnsemble Omega) (W : Nat)
    (f : (Fin W -> Real) -> Complex) (C : Real)
    (hbound : ∀ x : Fin W -> Real,
      (∀ j, x j ∈ massSupport) -> ‖f x‖ <= C)
    (omega : Omega) (L : Complex)
    (hlinear : Tendsto
      (fun N : Nat => complexSpatialAverage ensemble W f N omega)
      atTop (𝓝 L)) :
    Tendsto (fun N : Nat =>
      cyclicComplexWindowAverage ensemble N W f omega) atTop (𝓝 L) := by
  have hupper : Tendsto
      (fun N : Nat => (2 * C * (W : Real)) / (N : Real))
      atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun N : Nat =>
          (2 * C * (W : Real)) / (N : Real)) atTop (𝓝 0))
  have hboundEventually : ∀ᶠ N : Nat in atTop,
      dist (complexSpatialAverage ensemble W f N omega)
        (cyclicComplexWindowAverage ensemble N W f omega) <=
          (2 * C * (W : Real)) / (N : Real) := by
    filter_upwards [eventually_ge_atTop (max W 1)] with N hNlarge
    have hN : 0 < N := by omega
    have hWN : W <= N := by omega
    simpa [dist_eq_norm, norm_sub_rev] using
      norm_cyclicComplexWindowAverage_sub_complexSpatialAverage_le
        ensemble hN hWN f C hbound omega
  have hdist : Tendsto
      (fun N : Nat =>
        dist (complexSpatialAverage ensemble W f N omega)
          (cyclicComplexWindowAverage ensemble N W f omega))
      atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
      hboundEventually hupper
  exact hlinear.congr_dist hdist

end

end ArchonPhysics.CyclicWindowPrefixComparison
