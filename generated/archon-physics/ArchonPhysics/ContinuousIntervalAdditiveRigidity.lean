import Mathlib

/-!
# Continuous additive rigidity on a compact positive interval

This module proves the local Cauchy-equation statement needed by continuum
three-wave balance arguments.  A function only has to be continuous on
`[0, W]`, and its additivity is only assumed for nonnegative pairs whose sum
stays in that interval.  These local hypotheses already force the function to
be multiplication by one real scalar throughout the interval.

No global additive extension is assumed or constructed.  The proof first
establishes the equation on rational subdivisions of `W`, then closes the
rational parameter set by continuity.
-/

namespace ArchonPhysics.ContinuousIntervalAdditiveRigidity

open Set

private theorem restrictedAdditive_nat_mul
    (weight : Real -> Real) {W x : Real}
    (hW : 0 <= W) (hx : 0 <= x)
    (hadd : forall a, a ∈ Icc (0 : Real) W ->
      forall b, b ∈ Icc (0 : Real) W -> a + b <= W ->
        weight (a + b) = weight a + weight b)
    (n : Nat) (hn : (n : Real) * x <= W) :
    weight ((n : Real) * x) = (n : Real) * weight x := by
  have hzero : weight 0 = 0 := by
    have h := hadd 0 ⟨le_rfl, hW⟩ 0 ⟨le_rfl, hW⟩ (by simpa using hW)
    simp only [zero_add] at h
    linarith
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
      have hnx0 : 0 <= (n : Real) * x :=
        mul_nonneg (Nat.cast_nonneg _) hx
      have hx_le : x <= W := by
        have hcast : (0 : Real) <= n := Nat.cast_nonneg n
        calc
          x <= (n + 1 : Real) * x := by nlinarith
          _ <= W := by exact_mod_cast hn
      have hnx_le : (n : Real) * x <= W := by
        have hcast : (0 : Real) <= n := Nat.cast_nonneg n
        have hcastSucc : (n + 1 : Real) * x <= W := by exact_mod_cast hn
        nlinarith
      have hsum_le : (n : Real) * x + x <= W := by
        simpa only [Nat.cast_succ, add_mul, one_mul] using hn
      rw [show ((Nat.succ n : Nat) : Real) * x =
          (n : Real) * x + x by push_cast; ring]
      rw [hadd ((n : Real) * x) ⟨hnx0, hnx_le⟩
        x ⟨hx, hx_le⟩ hsum_le]
      rw [ih hnx_le]
      push_cast
      ring

private theorem restrictedAdditive_rat_mul
    (weight : Real -> Real) {W : Real}
    (hW : 0 < W)
    (hadd : forall a, a ∈ Icc (0 : Real) W ->
      forall b, b ∈ Icc (0 : Real) W -> a + b <= W ->
        weight (a + b) = weight a + weight b)
    (q : Rat) (hq0 : (0 : Rat) <= q) (hq1 : q <= 1) :
    weight ((q : Real) * W) = (q : Real) * weight W := by
  obtain ⟨a, ha⟩ :=
    Int.eq_ofNat_of_zero_le (Rat.num_nonneg.mpr hq0)
  have hdenPos : (0 : Real) < q.den := by positivity
  have hqrepr : (q : Real) = (a : Real) / (q.den : Real) := by
    have hcast : (a : Real) = (q.num : Real) := by
      exact_mod_cast ha.symm
    rw [hcast]
    exact_mod_cast (Rat.num_div_den q).symm
  let subdivision : Real := W / q.den
  have hsubdivisionNonneg : 0 <= subdivision := by
    dsimp [subdivision]
    positivity
  have hdenSubdivision : (q.den : Real) * subdivision = W := by
    dsimp [subdivision]
    field_simp
  have hden := restrictedAdditive_nat_mul weight hW.le
    hsubdivisionNonneg hadd q.den (by rw [hdenSubdivision])
  have hnumSubdivision :
      (a : Real) * subdivision = (q : Real) * W := by
    rw [hqrepr]
    dsimp [subdivision]
    field_simp
  have hnumBound : (a : Real) * subdivision <= W := by
    rw [hnumSubdivision]
    have hq1Real : (q : Real) <= 1 := by exact_mod_cast hq1
    have hq0Real : (0 : Real) <= q := by exact_mod_cast hq0
    nlinarith
  have hnum := restrictedAdditive_nat_mul weight hW.le
    hsubdivisionNonneg hadd a hnumBound
  rw [hnumSubdivision] at hnum
  rw [hdenSubdivision] at hden
  rw [hnum, hden, hqrepr]
  field_simp

/-- **Restricted continuous Cauchy rigidity.**

If `weight` is continuous on `[0, W]`, `W > 0`, and
`weight (x + y) = weight x + weight y` whenever `x`, `y`, and their sum remain
in the interval, then `weight` is scalar multiplication on the whole interval.
-/
theorem continuousOn_interval_additive_linear
    (weight : Real -> Real) {W : Real} (hW : 0 < W)
    (hcontinuous : ContinuousOn weight (Icc (0 : Real) W))
    (hadd : forall x, x ∈ Icc (0 : Real) W ->
      forall y, y ∈ Icc (0 : Real) W -> x + y <= W ->
        weight (x + y) = weight x + weight y) :
    exists beta : Real, forall x, x ∈ Icc (0 : Real) W ->
      weight x = beta * x := by
  let rationalParameters : Set Real :=
    Icc (0 : Real) 1 ∩ Set.range Rat.cast
  have hnontrivial : (Icc (0 : Real) 1).Nontrivial := by
    refine ⟨0, by norm_num, 1, by norm_num, by norm_num⟩
  have hclosure : closure rationalParameters = Icc (0 : Real) 1 := by
    simpa only [rationalParameters, isClosed_Icc.closure_eq] using
      (closure_ordConnected_inter_rat ordConnected_Icc hnontrivial)
  have hscaled :
      ContinuousOn (fun t : Real => weight (t * W)) (Icc 0 1) := by
    apply hcontinuous.comp (continuousOn_id.mul continuousOn_const)
    intro t ht
    constructor
    · exact mul_nonneg ht.1 hW.le
    · exact (mul_le_mul_of_nonneg_right ht.2 hW.le).trans_eq
        (one_mul W)
  have hlinear :
      ContinuousOn (fun t : Real => t * weight W) (Icc 0 1) :=
    continuousOn_id.mul continuousOn_const
  have hrational : Set.EqOn (fun t : Real => weight (t * W))
      (fun t : Real => t * weight W) rationalParameters := by
    intro t ht
    obtain ⟨q, hq⟩ := ht.2
    subst t
    apply restrictedAdditive_rat_mul weight hW hadd
    · exact_mod_cast ht.1.1
    · exact_mod_cast ht.1.2
  have hall : Set.EqOn (fun t : Real => weight (t * W))
      (fun t : Real => t * weight W) (Icc 0 1) := by
    apply hrational.of_subset_closure hscaled hlinear inter_subset_left
    intro t ht
    rw [hclosure]
    exact ht
  refine ⟨weight W / W, ?_⟩
  intro x hx
  have ht : x / W ∈ Icc (0 : Real) 1 := by
    constructor
    · exact div_nonneg hx.1 hW.le
    · exact (div_le_one hW).mpr hx.2
  have heq := hall ht
  dsimp only at heq
  rw [div_mul_cancel₀ x hW.ne'] at heq
  calc
    weight x = (x / W) * weight W := heq
    _ = (weight W / W) * x := by field_simp

/-- The scalar in restricted continuous Cauchy rigidity is the endpoint slope
`weight W / W`. -/
theorem continuousOn_interval_additive_eq_endpointSlope
    (weight : Real -> Real) {W : Real} (hW : 0 < W)
    (hcontinuous : ContinuousOn weight (Icc (0 : Real) W))
    (hadd : forall x, x ∈ Icc (0 : Real) W ->
      forall y, y ∈ Icc (0 : Real) W -> x + y <= W ->
        weight (x + y) = weight x + weight y) :
    forall x, x ∈ Icc (0 : Real) W ->
      weight x = (weight W / W) * x := by
  obtain ⟨beta, hbeta⟩ :=
    continuousOn_interval_additive_linear weight hW hcontinuous hadd
  have hAtEndpoint := hbeta W ⟨hW.le, le_rfl⟩
  have hbetaEq : beta = weight W / W := by
    rw [hAtEndpoint]
    field_simp
  simpa only [hbetaEq] using hbeta

end ArchonPhysics.ContinuousIntervalAdditiveRigidity
