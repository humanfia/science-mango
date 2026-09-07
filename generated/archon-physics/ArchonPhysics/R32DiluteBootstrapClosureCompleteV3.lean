import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# R32 dilute bootstrap closure

This module contains the scalar first-exit argument used after a volume-free
Duhamel estimate.  For

`P(g,a,E,x) = g (a E + 2 a x + x^2)
  + g^2 (a^2 E + 3 a^2 x + 3 a x^2 + x^3)`,

the kinetic window is `T / g^2`, `a = g^4`, and the explicit constants are

`C_T = 2 K T (C + 1) + 1`,

`g₀ = 1 / (4 (K T (C_T^3 + 4 C_T^2 + 5 C_T + C) + 1))`.

The main hypothesis is the literal integral inequality from the Duhamel
estimate.  No bootstrap conclusion is assumed, and no constant depends on a
volume parameter.
-/

namespace ArchonPhysics.R32DiluteBootstrapClosureCompleteV3

open Set MeasureTheory

noncomputable section

/-- The scalar polynomial supplied by the quadratic/cubic Duhamel estimate. -/
def forcingPolynomial (g a E x : Real) : Real :=
  g * (a * E + 2 * a * x + x ^ 2) +
    g ^ 2 * (a ^ 2 * E + 3 * a ^ 2 * x + 3 * a * x ^ 2 + x ^ 3)

/-- The explicit constant in the `O(g^3)` conclusion. -/
def kineticConstant (K C T : Real) : Real :=
  2 * K * T * (C + 1) + 1

/-- The coefficient bounding every term beyond the leading `C g^3`. -/
def residualCoefficient (K C T : Real) : Real :=
  kineticConstant K C T ^ 3 + 4 * kineticConstant K C T ^ 2 +
    5 * kineticConstant K C T + C

/-- An explicit small-coupling threshold for the closure. -/
def couplingThreshold (K C T : Real) : Real :=
  1 / (4 * (K * T * residualCoefficient K C T + 1))

theorem kineticConstant_pos {K C T : Real}
    (hK : 0 <= K) (hC : 0 <= C) (hT : 0 <= T) :
    0 < kineticConstant K C T := by
  unfold kineticConstant
  positivity

theorem residualCoefficient_nonneg {K C T : Real}
    (hK : 0 <= K) (hC : 0 <= C) (hT : 0 <= T) :
    0 <= residualCoefficient K C T := by
  unfold residualCoefficient
  have hB := (kineticConstant_pos hK hC hT).le
  positivity

theorem couplingThreshold_pos {K C T : Real}
    (hK : 0 <= K) (hC : 0 <= C) (hT : 0 <= T) :
    0 < couplingThreshold K C T := by
  unfold couplingThreshold
  have hD := residualCoefficient_nonneg hK hC hT
  positivity

theorem forcingPolynomial_nonneg {g a E x : Real}
    (hg : 0 <= g) (ha : 0 <= a) (hE : 0 <= E) (hx : 0 <= x) :
    0 <= forcingPolynomial g a E x := by
  unfold forcingPolynomial
  positivity

/-- Monotonicity in both the energy and error arguments on the nonnegative
cone. -/
theorem forcingPolynomial_mono {g a E F x y : Real}
    (hg : 0 <= g) (ha : 0 <= a) (_hE : 0 <= E) (hx : 0 <= x)
    (hEF : E <= F) (hxy : x <= y) :
    forcingPolynomial g a E x <= forcingPolynomial g a F y := by
  have hax : a * x <= a * y := mul_le_mul_of_nonneg_left hxy ha
  have haE : a * E <= a * F := mul_le_mul_of_nonneg_left hEF ha
  have ha2E : a ^ 2 * E <= a ^ 2 * F :=
    mul_le_mul_of_nonneg_left hEF (sq_nonneg a)
  have hx2 : x ^ 2 <= y ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hx hxy
  have hx3 : x ^ 3 <= y ^ 3 := by
    have hmul := mul_le_mul hx2 hxy hx (sq_nonneg y)
    simpa [pow_succ] using hmul
  have hax2 : a * x ^ 2 <= a * y ^ 2 :=
    mul_le_mul_of_nonneg_left hx2 ha
  have ha2x : a ^ 2 * x <= a ^ 2 * y :=
    mul_le_mul_of_nonneg_left hxy (sq_nonneg a)
  have hfirst :
      a * E + 2 * a * x + x ^ 2 <= a * F + 2 * a * y + y ^ 2 := by
    nlinarith
  have hsecond :
      a ^ 2 * E + 3 * a ^ 2 * x + 3 * a * x ^ 2 + x ^ 3 <=
        a ^ 2 * F + 3 * a ^ 2 * y + 3 * a * y ^ 2 + y ^ 3 := by
    nlinarith
  unfold forcingPolynomial
  exact add_le_add
    (mul_le_mul_of_nonneg_left hfirst hg)
    (mul_le_mul_of_nonneg_left hsecond (sq_nonneg g))

/-- The explicit threshold yields `g <= 1` and the normalized residual
budget. -/
theorem small_coupling_budget {K C T g : Real}
    (hK : 0 <= K) (hC : 0 <= C) (hT : 0 <= T)
    (hg : 0 < g) (hg0 : g <= couplingThreshold K C T) :
    g <= 1 /\
      (K * T * residualCoefficient K C T) * g ^ 2 <= 1 / 4 := by
  let A := K * T * residualCoefficient K C T
  have hD := residualCoefficient_nonneg hK hC hT
  have hA : 0 <= A := by
    dsimp [A]
    positivity
  have hden : 0 < 4 * (A + 1) := by positivity
  have hgfrac : g <= 1 / (4 * (A + 1)) := by
    simpa [couplingThreshold, A] using hg0
  have hfrac_one : 1 / (4 * (A + 1)) <= 1 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hg_one : g <= 1 := hgfrac.trans hfrac_one
  have hscaled : g * (A + 1) <= 1 / 4 := by
    have h := (le_div_iff₀ hden).1 hgfrac
    nlinarith
  have hgsq : g ^ 2 <= g := by nlinarith [hg.le]
  constructor
  · exact hg_one
  · change A * g ^ 2 <= 1 / 4
    calc
      A * g ^ 2 <= A * g := mul_le_mul_of_nonneg_left hgsq hA
      _ <= (A + 1) * g :=
        mul_le_mul_of_nonneg_right (by linarith) hg.le
      _ = g * (A + 1) := by ring
      _ <= 1 / 4 := hscaled

/-- Abstract continuous first-exit lemma.  Compactness supplies the earliest
point where the positive threshold is reached. -/
theorem continuous_first_exit
    {X : Real -> Real} {H R : Real}
    (hH : 0 <= H) (hR : 0 < R) (hX : Continuous X)
    (hzero : X 0 < R)
    (himprove : ∀ t ∈ Icc (0 : Real) H,
      (∀ s ∈ Icc (0 : Real) t, X s <= R) -> X t < R) :
    ∀ t ∈ Icc (0 : Real) H, X t < R := by
  intro t ht
  by_contra hnot
  have hRt : R <= X t := le_of_not_gt hnot
  have hcont0t : ContinuousOn X (Icc (0 : Real) t) :=
    hX.continuousOn.mono (Icc_subset_Icc_right ht.2)
  have hRimage : R ∈ X '' Icc (0 : Real) t :=
    intermediate_value_Icc ht.1 hcont0t ⟨hzero.le, hRt⟩
  rcases hRimage with ⟨u, hu, hXu⟩
  let exitSet : Set Real := Icc (0 : Real) H ∩ X ⁻¹' ({R} : Set Real)
  have hexit_compact : IsCompact exitSet :=
    isCompact_Icc.inter_right (isClosed_singleton.preimage hX)
  have hu_exit : u ∈ exitSet := by
    refine ⟨⟨hu.1, hu.2.trans ht.2⟩, ?_⟩
    simpa only [mem_preimage, mem_singleton_iff] using hXu
  obtain ⟨τ, hτexit, hτmin⟩ :=
    hexit_compact.exists_isMinOn ⟨u, hu_exit⟩ continuousOn_id
  have hτwindow : τ ∈ Icc (0 : Real) H := hτexit.1
  have hXτ : X τ = R := by
    simpa only [mem_preimage, mem_singleton_iff] using hτexit.2
  have hprior : ∀ s ∈ Icc (0 : Real) τ, X s <= R := by
    intro s hs
    by_contra hsnot
    have hRs : R < X s := lt_of_not_ge hsnot
    have hcont0s : ContinuousOn X (Icc (0 : Real) s) :=
      hX.continuousOn.mono
        (Icc_subset_Icc_right (hs.2.trans hτwindow.2))
    have hRimage_s : R ∈ X '' Icc (0 : Real) s :=
      intermediate_value_Icc hs.1 hcont0s ⟨hzero.le, hRs.le⟩
    rcases hRimage_s with ⟨v, hv, hXv⟩
    have hv_exit : v ∈ exitSet := by
      refine ⟨⟨hv.1, hv.2.trans (hs.2.trans hτwindow.2)⟩, ?_⟩
      simpa only [mem_preimage, mem_singleton_iff] using hXv
    have hτv : τ <= v := hτmin hv_exit
    have hvs_eq : v = s :=
      le_antisymm hv.2 (hs.2.trans hτv)
    rw [hvs_eq] at hXv
    linarith
  have himproved := himprove τ hτwindow hprior
  linarith

theorem continuous_forcingPolynomial (g a E : Real) :
    Continuous (forcingPolynomial g a E) := by
  unfold forcingPolynomial
  fun_prop

/-- The complete polynomial at the bootstrap radius is strictly smaller than
that radius on the inverse-square window. -/
theorem forcingPolynomial_strict_improvement
    {K C T g a E : Real}
    (hK : 0 <= K) (hC : 0 <= C) (hT : 0 <= T)
    (hg : 0 < g) (hg0 : g <= couplingThreshold K C T)
    (ha : a = g ^ 4) (hE0 : 0 <= E) (hEC : E <= C) :
    K * (T / g ^ 2) *
        forcingPolynomial g a E (kineticConstant K C T * g ^ 3) <
      kineticConstant K C T * g ^ 3 := by
  let B := kineticConstant K C T
  let D := residualCoefficient K C T
  have hBpos : 0 < B := by simpa [B] using kineticConstant_pos hK hC hT
  have hB : 0 <= B := hBpos.le
  obtain ⟨hg_one, hbudget⟩ := small_coupling_budget hK hC hT hg hg0
  have hstep (n : Nat) : g ^ (n + 1) <= g ^ n := by
    rw [pow_succ]
    simpa using mul_le_mul_of_nonneg_left hg_one (pow_nonneg hg.le n)
  have hg32 : g ^ 3 <= g ^ 2 := by simpa using hstep 2
  have hg43 : g ^ 4 <= g ^ 3 := by simpa using hstep 3
  have hg54 : g ^ 5 <= g ^ 4 := by simpa using hstep 4
  have hg65 : g ^ 6 <= g ^ 5 := by simpa using hstep 5
  have hg76 : g ^ 7 <= g ^ 6 := by simpa using hstep 6
  have hg87 : g ^ 8 <= g ^ 7 := by simpa using hstep 7
  have hg52 : g ^ 5 <= g ^ 2 := hg54.trans (hg43.trans hg32)
  have hg62 : g ^ 6 <= g ^ 2 := hg65.trans hg52
  have hg72 : g ^ 7 <= g ^ 2 := hg76.trans hg62
  have hg82 : g ^ 8 <= g ^ 2 := hg87.trans hg72
  have hresidual :
      B ^ 2 * g ^ 2 + 2 * B * g ^ 3 + C * g ^ 5 +
          B ^ 3 * g ^ 6 + 3 * B ^ 2 * g ^ 7 + 3 * B * g ^ 8 <=
        D * g ^ 2 := by
    have h3 : 2 * B * g ^ 3 <= 2 * B * g ^ 2 :=
      mul_le_mul_of_nonneg_left hg32 (by positivity)
    have h5 : C * g ^ 5 <= C * g ^ 2 :=
      mul_le_mul_of_nonneg_left hg52 hC
    have h6 : B ^ 3 * g ^ 6 <= B ^ 3 * g ^ 2 :=
      mul_le_mul_of_nonneg_left hg62 (by positivity)
    have h7 : 3 * B ^ 2 * g ^ 7 <= 3 * B ^ 2 * g ^ 2 :=
      mul_le_mul_of_nonneg_left hg72 (by positivity)
    have h8 : 3 * B * g ^ 8 <= 3 * B * g ^ 2 :=
      mul_le_mul_of_nonneg_left hg82 (by positivity)
    dsimp [D, residualCoefficient]
    change _ <= (B ^ 3 + 4 * B ^ 2 + 5 * B + C) * g ^ 2
    nlinarith
  have henergy :
      forcingPolynomial g a E (B * g ^ 3) <=
        forcingPolynomial g (g ^ 4) C (B * g ^ 3) := by
    subst a
    exact forcingPolynomial_mono hg.le (pow_nonneg hg.le 4) hE0
      (mul_nonneg hB (pow_nonneg hg.le 3)) hEC le_rfl
  have hscale : 0 <= K * (T / g ^ 2) := by positivity
  calc
    K * (T / g ^ 2) * forcingPolynomial g a E (B * g ^ 3) <=
        K * (T / g ^ 2) *
          forcingPolynomial g (g ^ 4) C (B * g ^ 3) :=
      mul_le_mul_of_nonneg_left henergy hscale
    _ = K * T * g ^ 3 *
        (C + (B ^ 2 * g ^ 2 + 2 * B * g ^ 3 + C * g ^ 5 +
          B ^ 3 * g ^ 6 + 3 * B ^ 2 * g ^ 7 + 3 * B * g ^ 8)) := by
      unfold forcingPolynomial
      field_simp [hg.ne']
      ring
    _ <= K * T * g ^ 3 * (C + D * g ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ = g ^ 3 * (K * T * C + (K * T * D) * g ^ 2) := by ring
    _ < g ^ 3 * B := by
      apply mul_lt_mul_of_pos_left _ (pow_pos hg 3)
      have hlead : K * T * C <= B / 2 := by
        dsimp [B, kineticConstant]
        have hKT : 0 <= K * T := mul_nonneg hK hT
        nlinarith
      have hB_one : 1 <= B := by
        dsimp [B, kineticConstant]
        have hKT : 0 <= K * T := mul_nonneg hK hT
        have hCp : 0 <= C + 1 := by linarith
        nlinarith [mul_nonneg hKT hCp]
      change K * T * C +
        (K * T * residualCoefficient K C T) * g ^ 2 < B
      nlinarith
    _ = B * g ^ 3 := by ring

/-- A non-circular prefix form of integral domination. -/
def PrefixDuhamelDomination
    (X : Real -> Real) (K g a E H : Real) : Prop :=
  ∀ t ∈ Icc (0 : Real) H, ∀ R : Real, 0 <= R ->
    (∀ s ∈ Icc (0 : Real) t, X s <= R) ->
      X t <= K * t * forcingPolynomial g a E R

theorem dilute_bootstrap_closure_of_prefix_domination
    {X : Real -> Real} {K C T g a E : Real}
    (hK : 0 <= K) (hC : 0 <= C) (hT : 0 <= T)
    (hg : 0 < g) (hg0 : g <= couplingThreshold K C T)
    (ha : a = g ^ 4) (hE0 : 0 <= E) (hEC : E <= C)
    (hX : Continuous X) (hXzero : X 0 = 0)
    (hdom : PrefixDuhamelDomination X K g a E (T / g ^ 2)) :
    ∀ t ∈ Icc (0 : Real) (T / g ^ 2),
      X t <= kineticConstant K C T * g ^ 3 := by
  let H := T / g ^ 2
  let R := kineticConstant K C T * g ^ 3
  have hH : 0 <= H := by
    dsimp [H]
    positivity
  have hR : 0 < R := by
    dsimp [R]
    exact mul_pos (kineticConstant_pos hK hC hT) (pow_pos hg 3)
  have himprove : ∀ t ∈ Icc (0 : Real) H,
      (∀ s ∈ Icc (0 : Real) t, X s <= R) -> X t < R := by
    intro t ht hprefix
    have hPt : 0 <= forcingPolynomial g a E R := by
      apply forcingPolynomial_nonneg hg.le
      · rw [ha]
        positivity
      · exact hE0
      · exact hR.le
    have hKP : 0 <= K * forcingPolynomial g a E R :=
      mul_nonneg hK hPt
    have htime :
        K * t * forcingPolynomial g a E R <=
          K * H * forcingPolynomial g a E R := by
      calc
        K * t * forcingPolynomial g a E R =
            t * (K * forcingPolynomial g a E R) := by ring
        _ <= H * (K * forcingPolynomial g a E R) :=
          mul_le_mul_of_nonneg_right ht.2 hKP
        _ = K * H * forcingPolynomial g a E R := by ring
    have hstrict : K * H * forcingPolynomial g a E R < R := by
      simpa [H, R] using
        forcingPolynomial_strict_improvement hK hC hT hg hg0 ha hE0 hEC
    exact (hdom t ht R hR.le hprefix).trans_lt (htime.trans_lt hstrict)
  have hall := continuous_first_exit hH hR hX
    (by simpa [hXzero] using hR) himprove
  intro t ht
  exact (hall t ht).le

/-- The literal integral inequality implies the prefix domination. -/
theorem prefix_domination_of_intervalIntegral
    {X : Real -> Real} {K g a E H : Real}
    (hK : 0 <= K) (hg : 0 <= g) (ha : 0 <= a) (hE : 0 <= E)
    (hX : Continuous X)
    (hXnonneg : ∀ t ∈ Icc (0 : Real) H, 0 <= X t)
    (hIntegral : ∀ t ∈ Icc (0 : Real) H,
      X t <= K * ∫ s in (0 : Real)..t, forcingPolynomial g a E (X s)) :
    PrefixDuhamelDomination X K g a E H := by
  intro t ht R _hR hprefix
  have hcont : Continuous (fun s : Real => forcingPolynomial g a E (X s)) :=
    (continuous_forcingPolynomial g a E).comp hX
  have hint :
      (∫ s in (0 : Real)..t, forcingPolynomial g a E (X s)) <=
        ∫ _s in (0 : Real)..t, forcingPolynomial g a E R := by
    apply intervalIntegral.integral_mono_on ht.1
      (hcont.intervalIntegrable (0 : Real) t) (by simp)
    intro s hs
    exact forcingPolynomial_mono hg ha hE
      (hXnonneg s ⟨hs.1, hs.2.trans ht.2⟩) le_rfl (hprefix s hs)
  calc
    X t <= K * ∫ s in (0 : Real)..t,
        forcingPolynomial g a E (X s) := hIntegral t ht
    _ <= K * (∫ _s in (0 : Real)..t, forcingPolynomial g a E R) :=
      mul_le_mul_of_nonneg_left hint hK
    _ = K * t * forcingPolynomial g a E R := by simp [mul_assoc]

/-- Main literal-integral closure theorem. -/
theorem dilute_bootstrap_closure
    {X : Real -> Real} {K C T g a E : Real}
    (hK : 0 <= K) (hC : 0 <= C) (hT : 0 <= T)
    (hg : 0 < g) (hg0 : g <= couplingThreshold K C T)
    (ha : a = g ^ 4) (hE0 : 0 <= E) (hEC : E <= C)
    (hX : Continuous X) (hXzero : X 0 = 0)
    (hXnonneg : ∀ t ∈ Icc (0 : Real) (T / g ^ 2), 0 <= X t)
    (hIntegral : ∀ t ∈ Icc (0 : Real) (T / g ^ 2),
      X t <= K * ∫ s in (0 : Real)..t, forcingPolynomial g a E (X s)) :
    ∀ t ∈ Icc (0 : Real) (T / g ^ 2),
      X t <= kineticConstant K C T * g ^ 3 := by
  apply dilute_bootstrap_closure_of_prefix_domination hK hC hT hg hg0
    ha hE0 hEC hX hXzero
  exact prefix_domination_of_intervalIntegral hK hg.le
    (ha.symm ▸ pow_nonneg hg.le 4) hE0 hX hXnonneg hIntegral

/-- Supremum form of `dilute_bootstrap_closure`. -/
theorem dilute_bootstrap_closure_sSup
    {X : Real -> Real} {K C T g a E : Real}
    (hK : 0 <= K) (hC : 0 <= C) (hT : 0 <= T)
    (hg : 0 < g) (hg0 : g <= couplingThreshold K C T)
    (ha : a = g ^ 4) (hE0 : 0 <= E) (hEC : E <= C)
    (hX : Continuous X) (hXzero : X 0 = 0)
    (hXnonneg : ∀ t ∈ Icc (0 : Real) (T / g ^ 2), 0 <= X t)
    (hIntegral : ∀ t ∈ Icc (0 : Real) (T / g ^ 2),
      X t <= K * ∫ s in (0 : Real)..t, forcingPolynomial g a E (X s)) :
    sSup (X '' Icc (0 : Real) (T / g ^ 2)) <=
      kineticConstant K C T * g ^ 3 := by
  apply csSup_le
  · refine ⟨X 0, ⟨0, ?_, rfl⟩⟩
    exact ⟨le_rfl, by positivity⟩
  · rintro y ⟨t, ht, rfl⟩
    exact dilute_bootstrap_closure hK hC hT hg hg0 ha hE0 hEC
      hX hXzero hXnonneg hIntegral t ht

end

end ArchonPhysics.R32DiluteBootstrapClosureCompleteV3
